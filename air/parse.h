#ifndef ABURI_AIR_PARSE_H
#define ABURI_AIR_PARSE_H

#include "module.h"

#include <memory>
#include <string>
#include <string_view>
#include <vector>

namespace aburi::air {

struct ParseError {
    std::string message;
    uint32_t line = 0;
    uint32_t col = 0;
};

struct ParseResult {
    std::unique_ptr<Module> module;
    std::vector<ParseError> errors;

    bool ok() const { return module != nullptr && errors.empty(); }
};

ParseResult parse_module(std::string_view text,
                         std::shared_ptr<const TargetInfo> target);

} // namespace aburi::air

#endif // ABURI_AIR_PARSE_H
