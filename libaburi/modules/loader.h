#ifndef ABURI_LIBABURI_MODULES_LOADER_H
#define ABURI_LIBABURI_MODULES_LOADER_H

#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "scan.h"

struct SourceManager;
struct Token;

namespace aburi::cir {
class File;
}

namespace aburi::modules {

struct LoadedModuleUnit {
    std::string module_name;
    std::string partition_name;
    ScannedUnitKind kind = ScannedUnitKind::NotModule;
    const std::vector<Token>* tokens = nullptr;
    std::shared_ptr<SourceManager> source_manager;
    const aburi::cir::File* cir = nullptr;
    std::shared_ptr<void> template_state;
};

class ModuleLoader {
public:
    virtual ~ModuleLoader() = default;
    virtual const LoadedModuleUnit* load(std::string_view module_name,
                                         std::string_view partition_name,
                                         std::string* error_out) = 0;
};

} // namespace aburi::modules

#endif // ABURI_LIBABURI_MODULES_LOADER_H
