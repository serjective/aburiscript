#ifndef ABURI_LIBABURI_MODULES_SESSION_H
#define ABURI_LIBABURI_MODULES_SESSION_H

#include <functional>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include "../frontend.h"
#include "../serialize/bmi.h"
#include "../serialize/compat.h"
#include "loader.h"
#include "scan.h"

namespace aburi::modules {

class ModuleBuildSession : public ModuleLoader {
public:
    using CompileFn = std::function<aburi::frontend::FrontendResult(
        const std::string& path, ModuleLoader* loader)>;

    explicit ModuleBuildSession(CompileFn compile)
        : compile_(std::move(compile)) {}

    std::string register_module_source(const ModuleScanResult& scan,
                                       const std::string& path);
    void register_module_artifact(const std::string& module_key,
                                  const std::string& path) {
        artifact_resolver_[module_key] = path;
    }
    void add_prebuilt_module_path(const std::string& directory) {
        prebuilt_paths_.push_back(directory);
    }
    void set_target_info(std::shared_ptr<TargetInfo> target) {
        target_ = std::move(target);
    }
    void set_compat_identity(serialize::CompatIdentity identity) {
        compat_ = std::move(identity);
    }
    const serialize::CompatIdentity& compat_identity() const {
        return compat_;
    }

    bool owns_path(const std::string& path) const {
        return units_by_path_.find(path) != units_by_path_.end() ||
               paths_.find(path) != paths_.end();
    }
    aburi::frontend::FrontendResult* result_for_path(const std::string& path);

    const LoadedModuleUnit* load(std::string_view module_name,
                                 std::string_view partition_name,
                                 std::string* error_out) override;

private:
    struct CachedUnit {
        aburi::frontend::FrontendResult result;
        LoadedModuleUnit unit;
        bool compiled = false;
        std::unique_ptr<serialize::SerializedUnit> serialized;
    };

    CachedUnit* ensure_compiled(const std::string& path,
                                std::string* error_out);
    CachedUnit* ensure_artifact_loaded(const std::string& path,
                                       std::string* error_out);

    CompileFn compile_;
    serialize::CompatIdentity compat_;
    std::shared_ptr<TargetInfo> target_;
    std::map<std::string, std::string> resolver_;
    std::map<std::string, std::string> artifact_resolver_;
    std::vector<std::string> prebuilt_paths_;
    std::map<std::string, ModuleScanResult> paths_;
    std::map<std::string, std::unique_ptr<CachedUnit>> units_by_path_;
    std::vector<std::string> active_loads_;
};

} // namespace aburi::modules

#endif // ABURI_LIBABURI_MODULES_SESSION_H
