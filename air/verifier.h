#ifndef ABURI_AIR_VERIFIER_H
#define ABURI_AIR_VERIFIER_H

#include "module.h"

#include <string>
#include <vector>

namespace aburi::air {

struct VerifierDiag {
    enum class Severity : uint8_t {
        Error,
        Note,
    };
    Severity severity = Severity::Error;
    std::string message;
    SrcLoc loc;
};

struct VerifyResult {
    std::vector<VerifierDiag> diags;

    bool ok() const {
        for (const VerifierDiag& diag : diags) {
            if (diag.severity == VerifierDiag::Severity::Error) {
                return false;
            }
        }
        return true;
    }
    uint32_t error_count() const {
        uint32_t count = 0;
        for (const VerifierDiag& diag : diags) {
            if (diag.severity == VerifierDiag::Severity::Error) {
                ++count;
            }
        }
        return count;
    }
    std::string to_string() const;
};

VerifyResult verify_module(const Module& mod);
void verify_function(const Module& mod, const Function& func, VerifyResult& result);

} // namespace aburi::air

#endif // ABURI_AIR_VERIFIER_H
