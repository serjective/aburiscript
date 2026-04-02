#ifndef ABURI_SEMANTIC_STORE_H
#define ABURI_SEMANTIC_STORE_H

#include "ast_context.h"

class CollectSemanticStore {
public:
    explicit CollectSemanticStore(ASTContext* owner_ast_ctx);
    ~CollectSemanticStore();

    uint32_t registry_id() const { return registry_id_; }
    ASTContext* ast_context() const { return owner_ast_ctx_; }

    void set_func_decl_cxx_qualifier_prefix(const FuncDecl* decl,
                                            std::optional<std::string> prefix);
    const std::string* get_func_decl_cxx_qualifier_prefix(
        const FuncDecl* decl) const;
    void clear_func_decl_cxx_qualifier_prefixes();
    void set_func_decl_owner_record_type(const FuncDecl* decl,
                                         QualType owner_type);
    QualType get_func_decl_owner_record_type(const FuncDecl* decl) const;
    void clear_func_decl_owner_record_types();

    void set_func_decl_function_template_specialization(
        const FuncDecl* decl,
        FunctionTemplateSpecializationInfo info);
    const FunctionTemplateSpecializationInfo*
    get_func_decl_function_template_specialization(
        const FuncDecl* decl) const;
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

    void set_template_specialization_resolved_type(
        const TemplateSpecializationType* type,
        std::shared_ptr<CType> resolved_type);
    std::shared_ptr<CType> get_template_specialization_resolved_type(
        const TemplateSpecializationType* type) const;
    void clear_template_specialization_resolved_types();

    void set_dependent_name_resolved_type(
        const DependentNameType* type,
        std::shared_ptr<CType> resolved_type);
    std::shared_ptr<CType> get_dependent_name_resolved_type(
        const DependentNameType* type) const;
    void clear_dependent_name_resolved_types();

    void clear_record_semantics_cache();
    void set_record_semantics(const ObjectDecl* record_decl,
                              RecordSemanticState state);
    void erase_record_semantics(const ObjectDecl* record_decl);
    const RecordSemanticState* lookup_record_semantics(
        const ObjectDecl* record_decl) const;
    uint64_t record_semantics_cache_epoch() const {
        return record_semantics_cache_epoch_;
    }

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
    class_template_specializations() const {
        return class_template_specializations_;
    }

    FunctionTemplateSpecializationEntry* lookup_function_template_specialization(
        const FunctionTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments);
    const FunctionTemplateSpecializationEntry*
    lookup_function_template_specialization(
        const FunctionTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments) const;
    FunctionTemplateSpecializationEntry& get_or_create_function_template_specialization(
        const FunctionTemplateDecl* primary_template,
        std::vector<TemplateArgument> arguments,
        std::unique_ptr<FuncDecl> specialization_decl,
        std::shared_ptr<Symbol> specialization_symbol);
    const std::vector<std::unique_ptr<FunctionTemplateSpecializationEntry>>&
    function_template_specializations() const {
        return function_template_specializations_;
    }

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
    variable_template_specializations() const {
        return variable_template_specializations_;
    }

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
    concept_specializations() const {
        return concept_specializations_;
    }

    bool push_template_instantiation_frame(size_t max_depth = 64);
    void pop_template_instantiation_frame();
    size_t template_instantiation_depth() const {
        return template_instantiation_depth_;
    }

    void clear_translation_unit_semantic_state();
    void clear_all_semantic_state();

    void retain_external_decl(std::unique_ptr<Decl> decl);

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
        std::unordered_map<const TemplateSpecializationType*, std::shared_ptr<CType>>;
    using DependentNameResolvedTypeMap =
        std::unordered_map<const DependentNameType*, std::shared_ptr<CType>>;
    using RecordSemanticsCacheMap =
        std::unordered_map<const ObjectDecl*, RecordSemanticState>;
    using EnumSemanticsCacheMap =
        std::unordered_map<const EnumDecl*, EnumSemanticsCacheEntry>;

    ASTContext* owner_ast_ctx_ = nullptr;
    std::unordered_set<std::string> external_qualifier_pool_;
    FuncExternalSemanticInfoMap func_decl_semantic_info_map_;
    VariableExternalSemanticInfoMap variable_decl_semantic_info_map_;
    std::unordered_set<const TemplateDecl*> tracked_template_decls_;
    std::unordered_set<const TemplateParameterDecl*> tracked_template_parameter_decls_;
    ParamExternalSemanticInfoMap param_decl_semantic_info_map_;
    SymbolExternalSemanticInfoMap symbol_semantic_info_map_;
    TemplateSpecializationResolvedTypeMap template_specialization_resolved_type_map_;
    DependentNameResolvedTypeMap dependent_name_resolved_type_map_;
    RecordSemanticsCacheMap record_semantics_cache_;
    EnumSemanticsCacheMap enum_semantics_cache_;
    std::unordered_map<
        TemplateSpecializationSemanticKey,
        size_t,
        TemplateSpecializationSemanticKeyHash> class_template_specialization_lookup_;
    std::vector<std::unique_ptr<ClassTemplateSpecializationEntry>>
        class_template_specializations_;
    std::unordered_map<
        TemplateSpecializationSemanticKey,
        size_t,
        TemplateSpecializationSemanticKeyHash> function_template_specialization_lookup_;
    std::vector<std::unique_ptr<FunctionTemplateSpecializationEntry>>
        function_template_specializations_;
    std::unordered_map<
        TemplateSpecializationSemanticKey,
        size_t,
        TemplateSpecializationSemanticKeyHash> variable_template_specialization_lookup_;
    std::vector<std::unique_ptr<VariableTemplateSpecializationEntry>>
        variable_template_specializations_;
    std::unordered_map<
        TemplateSpecializationSemanticKey,
        size_t,
        TemplateSpecializationSemanticKeyHash> concept_specialization_lookup_;
    std::vector<std::unique_ptr<ConceptSpecializationEntry>>
        concept_specializations_;
    std::vector<std::unique_ptr<Decl>> retained_external_decls_;
    uint64_t record_semantics_cache_epoch_ = 1;
    size_t template_instantiation_depth_ = 0;
    uint32_t registry_id_ = 0;
};

CollectSemanticStore* get_active_collect_semantic_store();
void set_active_collect_semantic_store(CollectSemanticStore* store);
CollectSemanticStore* lookup_registered_collect_semantic_store(
    uint32_t registry_id);
const CollectSemanticStore* lookup_registered_collect_semantic_store_const(
    uint32_t registry_id);

#endif
