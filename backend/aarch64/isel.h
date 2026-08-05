#ifndef ABURI_BACKEND_AARCH64_ISEL_H
#define ABURI_BACKEND_AARCH64_ISEL_H

#include <vector>

#include "../../air/module.h"
#include "../../diagnostics.h"
#include "../common/mir.h"

namespace aburi::backend::aarch64 {

bool select_function(const air::Module& module, const air::Function& function,
                     uint32_t function_index, MFunction& out,
                     std::vector<Diagnostic>& diagnostics, int opt_level = 0);

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_ISEL_H
