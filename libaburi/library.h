#ifndef ABURI_LIBRARY_H
#define ABURI_LIBRARY_H

#include <string>

#include "../lang_options.h"

int compile_run_program(std::string prg, LangOptions lang_opts = LangOptions());

#endif // ABURI_LIBRARY_H
