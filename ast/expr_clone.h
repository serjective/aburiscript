#ifndef ABURI_EXPR_CLONE_H
#define ABURI_EXPR_CLONE_H

#include <memory>
#include <string>

#include "ast.h"

class ASTContext;

std::unique_ptr<Expr> clone_expr_tree(const Expr* expr,
                                      ASTContext* ast_ctx = nullptr,
                                      std::string* error_out = nullptr);

#endif // ABURI_EXPR_CLONE_H
