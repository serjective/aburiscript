#ifndef ABURI_BACKEND_COMMON_SYMBOLS_H
#define ABURI_BACKEND_COMMON_SYMBOLS_H

#include <string>

#include "../../abi/target_info.h"

namespace aburi::backend {

inline bool target_uses_underscore_prefix(const TargetInfo& target) {
    return target.os == TargetOS::MACOS;
}

inline std::string target_symbol_name(const TargetInfo& target,
                                      const std::string& name,
                                      bool no_prefix) {
    if (no_prefix || !target_uses_underscore_prefix(target)) {
        return name;
    }
    return "_" + name;
}

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_SYMBOLS_H
