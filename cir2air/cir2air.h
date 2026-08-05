#ifndef ABURI_CIR2AIR_CIR2AIR_H
#define ABURI_CIR2AIR_CIR2AIR_H

#include <memory>
#include <string>
#include <vector>

#include "../air/module.h"
#include "../cir/file.h"
#include "../diagnostics.h"

namespace aburi::cir2air {

struct AirLoweringOptions {
    std::shared_ptr<TargetInfo> target;
    std::string module_name;
    bool cxx_mangling = false;
};

struct AirLoweringResult {
    std::unique_ptr<air::Module> module;
    std::vector<Diagnostic> diagnostics;

    bool ok() const {
        if (!module) {
            return false;
        }
        for (const Diagnostic& diag : diagnostics) {
            if (diag.level == DiagnosticLevel::Error) {
                return false;
            }
        }
        return true;
    }
};

AirLoweringResult lower_cir_to_air(const cir::File& file, AirLoweringOptions options);

} // namespace aburi::cir2air

#endif // ABURI_CIR2AIR_CIR2AIR_H
