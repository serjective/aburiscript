#ifndef ABURI_CIR_EXAMPLES_H
#define ABURI_CIR_EXAMPLES_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "file.h"

namespace aburi::cir {

std::vector<std::string> example_names();
std::optional<File> build_example(std::string_view name);

} // namespace aburi::cir

#endif // ABURI_CIR_EXAMPLES_H
