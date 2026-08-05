#include "session.h"

#include <algorithm>
#include <fstream>
#include <sstream>
#include <utility>

namespace aburi::modules {

namespace {

std::string module_key(std::string_view module_name,
                       std::string_view partition_name) {
    std::string key(module_name);
    if (!partition_name.empty()) {
        key += ':';
        key += partition_name;
    }
    return key;
}

} // namespace

std::string ModuleBuildSession::register_module_source(
    const ModuleScanResult& scan, const std::string& path) {
    paths_.emplace(path, scan);

    if (scan.kind != ScannedUnitKind::PrimaryInterface &&
        scan.kind != ScannedUnitKind::InterfacePartition) {
        return {};
    }
    std::string key = module_key(scan.module_name, scan.partition_name);
    auto [it, inserted] = resolver_.emplace(key, path);
    if (!inserted && it->second != path) {
        return "module '" + key + "' is provided by both '" + it->second +
               "' and '" + path + "'";
    }
    return {};
}

aburi::frontend::FrontendResult* ModuleBuildSession::result_for_path(
    const std::string& path) {
    CachedUnit* unit = ensure_compiled(path, nullptr);
    return unit ? &unit->result : nullptr;
}

ModuleBuildSession::CachedUnit* ModuleBuildSession::ensure_compiled(
    const std::string& path, std::string* error_out) {
    auto cached = units_by_path_.find(path);
    if (cached != units_by_path_.end()) {
        return cached->second.get();
    }
    if (std::find(active_loads_.begin(), active_loads_.end(), path) !=
        active_loads_.end()) {
        if (error_out) {
            std::string chain;
            for (const std::string& step : active_loads_) {
                chain += step;
                chain += " -> ";
            }
            chain += path;
            *error_out = "cyclic module interface dependency: " + chain;
        }
        return nullptr;
    }
    active_loads_.push_back(path);
    auto unit = std::make_unique<CachedUnit>();
    unit->result = compile_(path, this);
    active_loads_.pop_back();
    unit->compiled = true;

    auto scanned = paths_.find(path);
    if (scanned != paths_.end()) {
        unit->unit.module_name = scanned->second.module_name;
        unit->unit.partition_name = scanned->second.partition_name;
        unit->unit.kind = scanned->second.kind;
    }
    unit->unit.tokens = &unit->result.tokens;
    unit->unit.source_manager = unit->result.source_manager;
    unit->unit.cir = &unit->result.cir;
    unit->unit.template_state = unit->result.template_state;

    CachedUnit* out = unit.get();
    units_by_path_.emplace(path, std::move(unit));
    return out;
}

ModuleBuildSession::CachedUnit* ModuleBuildSession::ensure_artifact_loaded(
    const std::string& path, std::string* error_out) {
    auto cached = units_by_path_.find(path);
    if (cached != units_by_path_.end()) {
        return cached->second.get();
    }
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        if (error_out) {
            *error_out = "cannot read module artifact '" + path + "'";
        }
        return nullptr;
    }
    std::ostringstream buffer;
    buffer << in.rdbuf();
    std::string bytes = buffer.str();
    auto serialized = serialize::read_module_artifact(bytes, compat_, target_);
    if (!serialized->valid) {
        if (error_out) {
            *error_out = "module artifact '" + path + "': " +
                         serialized->error;
        }
        return nullptr;
    }
    auto unit = std::make_unique<CachedUnit>();
    unit->serialized = std::move(serialized);
    unit->unit = unit->serialized->unit;
    CachedUnit* out = unit.get();
    units_by_path_.emplace(path, std::move(unit));
    return out;
}

const LoadedModuleUnit* ModuleBuildSession::load(std::string_view module_name,
                                                 std::string_view partition_name,
                                                 std::string* error_out) {
    std::string key = module_key(module_name, partition_name);
    auto resolved = resolver_.find(key);
    if (resolved != resolver_.end()) {
        CachedUnit* unit = ensure_compiled(resolved->second, error_out);
        if (!unit) {
            return nullptr;
        }
        if (!unit->result.ok()) {
            if (error_out) {
                *error_out = "module '" + key + "' failed to compile";
            }
            return nullptr;
        }
        return &unit->unit;
    }
    std::string artifact_path;
    auto artifact = artifact_resolver_.find(key);
    if (artifact != artifact_resolver_.end()) {
        artifact_path = artifact->second;
    } else {
        std::string file_key = key;
        std::replace(file_key.begin(), file_key.end(), ':', '-');
        for (const std::string& directory : prebuilt_paths_) {
            std::string candidate = directory + "/" + file_key + ".abmi";
            if (std::ifstream(candidate, std::ios::binary)) {
                artifact_path = candidate;
                break;
            }
        }
    }
    if (artifact_path.empty()) {
        if (error_out) {
            *error_out = "module '" + key +
                         "' not found; add its interface unit to the "
                         "command line";
        }
        return nullptr;
    }
    CachedUnit* unit = ensure_artifact_loaded(artifact_path, error_out);
    return unit ? &unit->unit : nullptr;
}

} // namespace aburi::modules
