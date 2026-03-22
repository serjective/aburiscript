#ifndef ABURI_LIBRARY_H
#define ABURI_LIBRARY_H
#include "lexer.h"
#include "parser/parser.h"
#include "ast2llvm/ast2llvm.h"
#include <fstream>
#include <cstdlib>
#include  <string>
int compile_run_program(std::string prg, LangOptions lang_opts = LangOptions());

#endif //ABURI_LIBRARY_H