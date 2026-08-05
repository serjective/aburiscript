#ifndef ABURI_LIBABURI_SERIALIZE_BMI_H
#define ABURI_LIBABURI_SERIALIZE_BMI_H

#include <memory>
#include <string>
#include <vector>

#include "../../lexer.h"
#include "../../source_mgnt.h"
#include "../modules/loader.h"
#include "compat.h"

struct TargetInfo;

namespace aburi::serialize {

std::string write_module_artifact(const aburi::modules::LoadedModuleUnit& unit,
                                  const SourceManager& source_manager,
                                  const CompatIdentity& identity);

struct SerializedUnit {
    SerializedUnit();
    ~SerializedUnit();
    bool valid = false;
    std::string error;
    aburi::modules::LoadedModuleUnit unit;
    std::vector<Token> tokens;
    std::string spelling_blob;
    std::shared_ptr<SourceManager> source_manager;
    std::string compat_text;
    uint64_t compat_hash = 0;
    std::vector<DependencyRecord> dependencies;
    std::unique_ptr<aburi::cir::File> graph;
    std::shared_ptr<void> template_state;
};

std::unique_ptr<SerializedUnit> read_module_artifact(
    std::string_view bytes, const CompatIdentity& expected,
    std::shared_ptr<TargetInfo> target = nullptr);

} // namespace aburi::serialize

#endif // ABURI_LIBABURI_SERIALIZE_BMI_H
