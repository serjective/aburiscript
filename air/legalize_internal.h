#ifndef ABURI_AIR_LEGALIZE_INTERNAL_H
#define ABURI_AIR_LEGALIZE_INTERNAL_H

#include "legalize.h"

#include <string_view>

namespace aburi::air::legalize_detail {

struct StageState {
    const LegalizeConfig& config;
    bool changed = false;
    bool ok = true;
    std::string error;

    explicit StageState(const LegalizeConfig& config) : config(config) {}
    void fail(std::string message) {
        if (ok) {
            ok = false;
            error = std::move(message);
        }
    }
};

const char* libcall_name(const LegalizeConfig& config, LibcallId id);

FuncId find_or_declare(Module& mod, std::string_view name, const SigData& sig);

void run_soft_float_stage(Module& mod, StageState& state);
void run_i64_stage(Module& mod, StageState& state);

} // namespace aburi::air::legalize_detail

#endif // ABURI_AIR_LEGALIZE_INTERNAL_H
