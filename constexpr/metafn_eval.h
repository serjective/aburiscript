#ifndef ABURI_METAFN_EVAL_H
#define ABURI_METAFN_EVAL_H

#include <vector>

#include "../builtin_registry.h"
#include "../cir/file.h"
#include "const_value.h"
#include "consteval_result.h"
#include "eval_memory.h"
#include "metafn_kinds.h"

ConstEvalResult evaluate_metafunction(BuiltinKind kind,
                                      const aburi::cir::File& file,
                                      aburi::cir::File* mutable_file,
                                      EvalMemory& memory,
                                      const std::vector<ConstValue>& args,
                                      aburi::cir::TypeId result_type,
                                      SrcLoc loc);

#endif // ABURI_METAFN_EVAL_H
