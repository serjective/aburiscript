#ifndef ABURI_COLLECT_TEMPLATES_INTERNAL_H
#define ABURI_COLLECT_TEMPLATES_INTERNAL_H

#include "collect.h"
#include "../ast/ast_clone.h"

namespace template_sema_internal {

struct TemplateSubstitutionPass {
    ASTCloneContext ctx;
    std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&,
        ASTCloneContext&,
        std::string*)> rewrite_template_arguments_callback;
    std::function<std::shared_ptr<Symbol>(
        const std::shared_ptr<Symbol>&,
        ASTCloneContext&)> rewrite_symbol_callback;

    TemplateSubstitutionPass();
    TemplateSubstitutionPass(const TemplateSubstitutionPass& other);
    TemplateSubstitutionPass(TemplateSubstitutionPass&& other) noexcept;
    TemplateSubstitutionPass& operator=(const TemplateSubstitutionPass& other);
    TemplateSubstitutionPass& operator=(TemplateSubstitutionPass&& other) noexcept;

    ASTCloneContext& context();
    const ASTCloneContext& context() const;

    void refresh_callbacks();
    QualType rewrite_type(QualType type) const;
    std::unique_ptr<Expr> clone_expr(const Expr* expr,
                                     std::string* error_out = nullptr);
    std::unique_ptr<Stmt> clone_stmt(const Stmt* stmt,
                                     std::string* error_out = nullptr);
    std::unique_ptr<Decl> clone_decl(const Decl* decl,
                                     std::string* error_out = nullptr);
};

struct TemplateDependentResolutionPass {
    ASTCloneContext ctx;

    ASTCloneContext& context();
    const ASTCloneContext& context() const;

    void sync_from_substitution_pass(
        const TemplateSubstitutionPass& substitution_pass);
    bool resolve_expr_in_place(std::unique_ptr<Expr>& expr,
                               std::string* error_out = nullptr);
    bool resolve_stmt_in_place(std::unique_ptr<Stmt>& stmt,
                               std::string* error_out = nullptr);
    bool resolve_decl_in_place(std::unique_ptr<Decl>& decl,
                               std::string* error_out = nullptr);
};

struct TemplateClonePassBuilder {
    ASTContext* ast_ctx = nullptr;
    std::function<QualType(QualType)> rewrite_type;
    std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&,
        ASTCloneContext&,
        std::string*)> rewrite_template_arguments;
    std::function<std::unique_ptr<Expr>(const VarRef*, std::string*)>
        rewrite_var_ref;
    std::function<std::shared_ptr<Symbol>(
        const std::shared_ptr<Symbol>&,
        ASTCloneContext&)> rewrite_symbol;
    std::function<void(const std::shared_ptr<Symbol>&)> register_symbol;
    std::function<bool(MemberExpr*, std::string*)> rewrite_member_expr;
    std::function<bool(const Expr*,
                       std::vector<std::unique_ptr<Expr>>&,
                       std::string*)> expand_pack_expansion;
    std::function<std::optional<size_t>(const SizeOfPackExpr*, std::string*)>
        lookup_pack_size;
    std::unordered_map<const Symbol*, std::shared_ptr<Symbol>> symbol_remap;
    std::unordered_map<const Scope*, std::shared_ptr<Scope>> scope_remap;

    TemplateSubstitutionPass build_substitution_pass() const;
    TemplateDependentResolutionPass build_dependent_resolution_pass(
        const std::function<bool(std::unique_ptr<Expr>&, std::string*)>&
            resolve_expr) const;
    TemplateDependentResolutionPass build_dependent_resolution_pass(
        const TemplateSubstitutionPass& substitution_pass,
        const std::function<bool(std::unique_ptr<Expr>&, std::string*)>&
            resolve_expr) const;
};

void append_type_cache_key(std::string& out, QualType type);

void append_template_argument_cache_key(std::string& out,
                                        const TemplateArgument& argument);

bool template_arguments_depend_on_template_parameters(
    const std::vector<TemplateArgument>& arguments);

struct TemplatePackExpansionShape {
    std::vector<const TemplateParameterDecl*> referenced_parameters;
    bool has_unsupported_dependency = false;

    bool empty() const { return referenced_parameters.empty(); }
    bool has_multiple_referenced_packs() const {
        return referenced_parameters.size() > 1;
    }
    std::optional<const TemplateParameterDecl*> unique_referenced_parameter()
        const {
        if (referenced_parameters.size() != 1) {
            return std::nullopt;
        }
        return referenced_parameters.front();
    }
};

std::optional<size_t> find_template_parameter_index_by_identity(
    const TemplateTypeParmType* parm_type,
    const TemplateParameterList& parameters);

bool collect_pack_expansion_shape_in_type(
    QualType type,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out);

bool collect_pack_expansion_shape_in_template_argument(
    const TemplateArgument& argument,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out);

bool collect_pack_expansion_shape_in_expr(
    const Expr* expr,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out);

bool collect_pack_expansion_shape_in_template_arguments(
    const std::vector<TemplateArgument>& arguments,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out);

bool find_unique_parameter_pack_index_in_type(
    QualType type,
    const TemplateParameterList& parameters,
    std::optional<size_t>& found_index);

std::optional<size_t> find_pack_expansion_arity_for_bindings(
    const TemplatePackExpansionShape& shape,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings,
    std::string* error_out);

bool build_pack_element_argument_bindings(
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings,
    size_t element_index,
    TemplateArgumentBindings& element_bindings,
    std::string* error_out);

std::string make_parameter_pack_element_name(const std::string& base_name,
                                             size_t element_index);

std::shared_ptr<Expr> clone_constexpr_variable_initializer_expr(
    const Symbol* sym,
    ASTContext* ast_ctx);

QualType replace_record_decl_in_type(QualType type,
                                     const ObjectDecl* pattern_decl,
                                     QualType replacement_type,
                                     const ASTContext* ast_ctx = nullptr);

const ObjectDecl* canonical_record_decl(const ObjectDecl* decl);

std::shared_ptr<Symbol> clone_symbol_shallow_for_specialization(
    const std::shared_ptr<Symbol>& sym,
    QualType cloned_type);

void rebind_specialized_function_owner(FuncDecl* decl,
                                       QualType specialized_owner_type,
                                       const ASTContext* ast_ctx);

void copy_cpp_member_decl_info(ASTContext* ast_ctx,
                               uint32_t from_node_id,
                               uint32_t to_node_id);

std::shared_ptr<Symbol> lookup_symbol_remap_in_clone_context(
    const std::shared_ptr<Symbol>& sym,
    ASTCloneContext& clone_ctx);

TemplateClonePassBuilder make_template_binding_clone_pass_builder(
    ASTContext* ast_ctx,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& argument_bindings,
    SrcLoc loc,
    std::string value_error_message,
    const std::function<QualType(QualType)>& rewrite_type,
    const std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&)>& rewrite_template_arguments,
    const std::function<void(const std::shared_ptr<Symbol>&)>& register_symbol,
    const std::function<bool(MemberExpr*, std::string*)>& rewrite_member_expr);

bool remap_template_argument_after_outer_substitution(
    TemplateArgument& argument,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds,
    ASTCloneContext& clone_ctx,
    std::string* error_out);

QualType remap_template_parameter_types_in_type(
    QualType type,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds);

std::vector<TemplateArgument> remap_template_parameter_types_in_arguments(
    const std::vector<TemplateArgument>& arguments,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds);

TemplateClonePassBuilder make_nested_template_clone_pass_builder(
    const TemplateClonePassBuilder& outer_builder,
    const TemplateSubstitutionPass& outer_pass,
    const std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&)>& rewrite_outer_template_arguments,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds,
    const std::unordered_map<const Symbol*, std::shared_ptr<Symbol>>&
        extra_symbol_remap);

size_t method_user_param_start(const std::shared_ptr<FunctionType>& fn_type);

std::string make_method_virtual_slot_key(const std::string& method_name,
                                         QualType method_type);

bool rebind_member_expr_for_specialized_record(MemberExpr* member,
                                               ASTContext* ast_ctx,
                                               std::string* error_out);

bool clone_function_parameters_for_specialization(
    const Collect& collect,
    const FuncDecl* pattern,
    const TemplateParameterList& template_parameters,
    const TemplateArgumentBindings& specialization_bindings,
    FuncDecl* specialization,
    TemplateSubstitutionPass& substitution_pass,
    TemplateDependentResolutionPass& resolution_pass,
    SrcLoc loc,
    const std::string& failure_context,
    const std::function<QualType(QualType, size_t, std::string*)>&
        rewrite_pack_element_type,
    std::unordered_map<const Symbol*, std::vector<std::shared_ptr<Symbol>>>*
        pack_param_symbol_remap_out,
    std::vector<const Expr*>& default_arguments_out,
    std::string* error_out);

bool clone_function_body_for_specialization(
    const Collect& collect,
    const FuncDecl* pattern,
    FuncDecl* specialization,
    TemplateSubstitutionPass& substitution_pass,
    TemplateDependentResolutionPass& resolution_pass,
    const std::string& failure_context,
    bool finalize_body_semantics,
    std::string* error_out);

bool clone_ctor_initializers_for_specialization(
    const CppConstructorDecl* pattern,
    CppConstructorDecl* specialization,
    TemplateSubstitutionPass& substitution_pass,
    TemplateDependentResolutionPass& resolution_pass,
    std::string* error_out);

bool deduce_class_template_partial_specialization_bindings(
    const ClassTemplatePartialSpecializationDecl* partial_specialization,
    const std::vector<TemplateArgument>& actual_arguments,
    TemplateArgumentBindings& deduced_bindings_out);

bool is_class_template_partial_specialization_more_specialized(
    const ClassTemplatePartialSpecializationDecl* lhs_partial,
    const ClassTemplatePartialSpecializationDecl* rhs_partial);

std::optional<size_t> find_template_parameter_index_by_decl(
    const TemplateParameterDecl* parameter,
    const TemplateParameterList& parameters);

std::optional<size_t> find_pack_binding_size_for_sizeof_expr(
    const SizeOfPackExpr* expr,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings,
    std::string* error_out);

const TemplateArgument* find_template_argument_for_non_type_parameter_symbol(
    const Symbol* sym,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings);

bool template_argument_has_known_payload(const TemplateArgument& argument);

bool normalize_concrete_template_value_argument(TemplateArgument& argument,
                                                QualType target_type,
                                                std::string* error_out);

std::unique_ptr<Expr> make_constant_expr_for_template_argument(
    const TemplateArgument& argument,
    ASTContext* ast_ctx,
    SrcLoc loc);

std::string make_class_template_specialization_cache_key(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments);

std::string make_class_template_specialization_name(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments);

std::string make_function_template_specialization_cache_key(
    const FunctionTemplateDecl* function_template,
    const std::vector<TemplateArgument>& arguments);

std::string make_function_template_specialization_name(
    const FunctionTemplateDecl* function_template,
    const std::vector<TemplateArgument>& arguments);

QualType implicit_this_type_for_specialized_function(const FuncDecl* decl);

bool finalize_specialized_decl_semantics(const Collect& collect,
                                         std::unique_ptr<Decl>& decl,
                                         std::string* error_out);

bool finalize_specialized_stmt_semantics(const Collect& collect,
                                         std::unique_ptr<Stmt>& stmt,
                                         QualType expected_return_type,
                                         std::string* error_out);

bool finalize_specialized_ctor_initializers(const Collect& collect,
                                            CppConstructorDecl* ctor_decl,
                                            std::string* error_out);

} // namespace template_sema_internal

#endif // ABURI_COLLECT_TEMPLATES_INTERNAL_H
