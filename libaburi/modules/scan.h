#ifndef ABURI_LIBABURI_MODULES_SCAN_H
#define ABURI_LIBABURI_MODULES_SCAN_H

#include <string>
#include <string_view>
#include <vector>

#include "../../lang_options.h"

namespace aburi::modules {

enum class ScannedUnitKind {
    NotModule,
    PrimaryInterface,
    InterfacePartition,
    ImplementationPartition,
    Implementation,
};

struct ScannedImport {
    enum class Kind { Named, Partition, HeaderAngle, HeaderQuote };
    Kind kind = Kind::Named;
    std::string name;
    bool exported = false;
};

struct ModuleScanResult {
    ScannedUnitKind kind = ScannedUnitKind::NotModule;
    std::string module_name;
    std::string partition_name;
    bool has_global_module_fragment = false;
    bool has_private_module_fragment = false;
    std::vector<ScannedImport> imports;

    bool is_module_unit() const { return kind != ScannedUnitKind::NotModule; }
    bool is_interface_unit() const {
        return kind == ScannedUnitKind::PrimaryInterface ||
               kind == ScannedUnitKind::InterfacePartition;
    }
};

ModuleScanResult scan_module_directives(std::string_view source,
                                        const LangOptions& lang_options);

} // namespace aburi::modules

#endif // ABURI_LIBABURI_MODULES_SCAN_H
