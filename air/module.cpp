#include "module.h"

#include <cassert>

namespace aburi::air {

Module::Module(std::shared_ptr<const TargetInfo> target)
    : target_(std::move(target)) {
    assert(target_ && "AIR module requires a target");
    functions_.emplace_back();
    globals_.emplace_back();
    if (!target_->triple.empty()) {
        triple_ = target_->triple;
    }
}

FuncId Module::create_function(std::string name, SigId sig, Linkage linkage) {
    assert(!find_function(name).is_valid() && "duplicate function name");
    FuncId id{static_cast<uint32_t>(functions_.size())};
    function_names_.emplace(name, id.index);
    functions_.push_back(std::make_unique<Function>(std::move(name), sig, linkage));
    return id;
}

Function& Module::function(FuncId id) {
    assert(is_valid(id));
    return *functions_[id.index];
}

const Function& Module::function(FuncId id) const {
    assert(is_valid(id));
    return *functions_[id.index];
}

FuncId Module::find_function(std::string_view name) const {
    auto it = function_names_.find(std::string(name));
    if (it == function_names_.end()) {
        return FuncId{};
    }
    return FuncId{it->second};
}

GlobalId Module::create_global(GlobalData data) {
    assert(!find_global(data.name).is_valid() && "duplicate global name");
    GlobalId id{static_cast<uint32_t>(globals_.size())};
    global_names_.emplace(data.name, id.index);
    globals_.push_back(std::make_unique<GlobalData>(std::move(data)));
    return id;
}

GlobalData& Module::global(GlobalId id) {
    assert(is_valid(id));
    return *globals_[id.index];
}

const GlobalData& Module::global(GlobalId id) const {
    assert(is_valid(id));
    return *globals_[id.index];
}

GlobalId Module::find_global(std::string_view name) const {
    auto it = global_names_.find(std::string(name));
    if (it == global_names_.end()) {
        return GlobalId{};
    }
    return GlobalId{it->second};
}

uint32_t Module::add_asm_payload(AsmPayload payload) {
    uint32_t index = static_cast<uint32_t>(asm_payloads_.size());
    asm_payloads_.push_back(std::move(payload));
    return index;
}

const AsmPayload& Module::asm_payload(uint32_t index) const {
    assert(index < asm_payloads_.size());
    return asm_payloads_[index];
}

uint32_t Module::add_eh_landing_pad_payload(EhLandingPadPayload payload) {
    uint32_t index = static_cast<uint32_t>(eh_landing_pad_payloads_.size());
    eh_landing_pad_payloads_.push_back(std::move(payload));
    return index;
}

const EhLandingPadPayload& Module::eh_landing_pad_payload(uint32_t index) const {
    assert(index < eh_landing_pad_payloads_.size());
    return eh_landing_pad_payloads_[index];
}

} // namespace aburi::air
