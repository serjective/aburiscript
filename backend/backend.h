#ifndef ABURI_BACKEND_BACKEND_H
#define ABURI_BACKEND_BACKEND_H

#include <ostream>
#include <vector>

#include "../air/module.h"
#include "../diagnostics.h"

namespace aburi::backend {

struct BackendOptions {
    int opt_level = 0;
    bool emit_unwind_tables = false;
    bool verify_mir = false;
};

struct EmitResult {
    std::vector<Diagnostic> diagnostics;

    bool ok() const {
        for (const Diagnostic& diag : diagnostics) {
            if (diag.level == DiagnosticLevel::Error) {
                return false;
            }
        }
        return true;
    }
};

EmitResult emit_assembly(air::Module& module, const TargetInfo& target,
                         std::ostream& out, BackendOptions options = {});

EmitResult emit_object(air::Module& module, const TargetInfo& target,
                       std::ostream& out, BackendOptions options = {});

} // namespace aburi::backend

#endif // ABURI_BACKEND_BACKEND_H
