#ifndef ABURI_AST_MEMORY_REPORT_H
#define ABURI_AST_MEMORY_REPORT_H

#include <iosfwd>

struct Decl;
class ASTContext;

void print_ast_memory_report(std::ostream& os, const Decl* root, const ASTContext& ast_ctx);

#endif // ABURI_AST_MEMORY_REPORT_H
