#ifndef ABURI_AST_CLONE_H
#define ABURI_AST_CLONE_H

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>

#include "ast.h"

class ASTContext;

struct ASTCloneContext {
    ASTContext* ast_ctx = nullptr;
    bool publish_type_resolution_to_persistent_store = false;
    bool preserve_unexpanded_pack_expansions = false;
    std::function<QualType(QualType)> rewrite_type;
    std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&,
        ASTCloneContext&,
        std::string*)> rewrite_template_arguments;
    std::function<std::unique_ptr<Expr>(const VarRef*, std::string*)>
        rewrite_var_ref;
    std::function<std::shared_ptr<Symbol>(const std::shared_ptr<Symbol>&)>
        rewrite_symbol;
    std::function<void(const std::shared_ptr<Symbol>&)> register_symbol;
    std::function<bool(MemberExpr*, std::string*)> rewrite_member_expr;
    std::function<bool(CppLambdaExpr&, std::string*)> finalize_lambda_expr;
    std::function<bool(BlockExpr&, std::string*)> finalize_block_expr;
    std::function<bool(std::unique_ptr<Expr>&, std::string*)> rewrite_expr;
    std::function<bool(const Expr*,
                       std::vector<std::unique_ptr<Expr>>&,
                       std::string*)> expand_pack_expansion;
    std::function<std::optional<size_t>(const SizeOfPackExpr*, std::string*)>
        lookup_pack_size;
    std::unordered_map<const Symbol*, std::shared_ptr<Symbol>> symbol_remap;
    std::unordered_map<const Scope*, std::shared_ptr<Scope>> scope_remap;
    std::unordered_map<const ObjectDecl*, QualType> record_type_remap;
    std::unordered_map<const TemplateParameterDecl*, TemplateParameterDecl*>
        template_parameter_remap;
    std::unordered_map<const TemplateDecl*, TemplateDecl*> template_decl_remap;
};

std::unique_ptr<Expr> clone_expr_with_substitution(
    const Expr* expr,
    ASTCloneContext& ctx,
    std::string* error_out = nullptr);

bool rewrite_expr_tree_in_place(std::unique_ptr<Expr>& expr,
                                ASTCloneContext& ctx,
                                std::string* error_out = nullptr);

std::unique_ptr<Stmt> clone_stmt_tree(const Stmt* stmt,
                                      ASTCloneContext& ctx,
                                      std::string* error_out = nullptr);

bool rewrite_stmt_tree_in_place(std::unique_ptr<Stmt>& stmt,
                                ASTCloneContext& ctx,
                                std::string* error_out = nullptr);

std::unique_ptr<Decl> clone_decl_tree(const Decl* decl,
                                      ASTCloneContext& ctx,
                                      std::string* error_out = nullptr);

bool copy_decl_side_tables(const Decl* source,
                           Decl* destination,
                           ASTCloneContext& ctx,
                           std::string* error_out = nullptr);

bool rewrite_decl_tree_in_place(std::unique_ptr<Decl>& decl,
                                ASTCloneContext& ctx,
                                std::string* error_out = nullptr);

#endif // ABURI_AST_CLONE_H
