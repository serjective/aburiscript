#ifndef ABURI_AIR_PRINT_H
#define ABURI_AIR_PRINT_H

#include "module.h"

#include <string>

namespace aburi::air {

struct PrintOptions {
    bool locs = false;
};

std::string print_module(const Module& mod, PrintOptions options = {});
std::string print_function(const Module& mod, const Function& func,
                           PrintOptions options = {});

void dump(const Module& mod);
void dump(const Module& mod, const Function& func);

} // namespace aburi::air

#endif // ABURI_AIR_PRINT_H
