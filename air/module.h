#ifndef ABURI_AIR_MODULE_H
#define ABURI_AIR_MODULE_H

#include "function.h"
#include "ids.h"
#include "types.h"
#include "../abi/target_info.h"

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace aburi::air {

enum class GlobalInitKind : uint8_t {
    None,
    Zero,
    Bytes,
};

struct InitReloc {
    uint64_t offset = 0;
    bool is_function = false;
    uint32_t target_index = 0;
    int64_t addend = 0;
};

struct GlobalInit {
    GlobalInitKind kind = GlobalInitKind::None;
    std::vector<uint8_t> bytes;
    std::vector<InitReloc> relocs;

    static GlobalInit none() { return {}; }
    static GlobalInit zero() {
        GlobalInit init;
        init.kind = GlobalInitKind::Zero;
        return init;
    }
    static GlobalInit data(std::vector<uint8_t> bytes,
                           std::vector<InitReloc> relocs = {}) {
        GlobalInit init;
        init.kind = GlobalInitKind::Bytes;
        init.bytes = std::move(bytes);
        init.relocs = std::move(relocs);
        return init;
    }
};

enum class SectionKind : uint8_t {
    Data,
    Const,
    Cstring,
    Zerofill,
    Text,
    Custom,
};

struct GlobalData {
    std::string name;
    uint64_t size_bytes = 0;
    uint32_t align_bytes = 1;
    Linkage linkage = Linkage::External;
    SectionKind section = SectionKind::Data;
    SymbolAttrs attrs;
    std::string custom_section;
    bool is_thread_local = false;
    GlobalInit init;
    SrcLoc loc;
};

struct CtorEntry {
    uint32_t priority = 65535;
    FuncId func;
};

struct AsmPayload {
    std::string text;
    std::vector<std::string> constraints;
    std::vector<TypeId> operand_types;
    std::vector<std::string> clobbers;
    std::vector<std::string> register_bindings;
};

struct EhLandingPadPayload {
    bool is_cleanup = false;
    bool has_catch_all = false;
    std::vector<GlobalId> clause_typeinfos;
};

class Module {
public:
    explicit Module(std::shared_ptr<const TargetInfo> target);

    TypeTable& types() { return types_; }
    const TypeTable& types() const { return types_; }
    const TargetInfo& target() const { return *target_; }
    std::shared_ptr<const TargetInfo> target_ptr() const { return target_; }
    uint32_t ptr_size_bytes() const {
        return static_cast<uint32_t>(target_->pointer_width) / 8;
    }

    const std::string& triple() const { return triple_; }
    void set_triple(std::string triple) { triple_ = std::move(triple); }
    FuncId create_function(std::string name, SigId sig,
                           Linkage linkage = Linkage::External);
    Function& function(FuncId id);
    const Function& function(FuncId id) const;
    FuncId find_function(std::string_view name) const;
    uint32_t function_count() const {
        return static_cast<uint32_t>(functions_.size()) - 1;
    }
    bool is_valid(FuncId id) const {
        return id.index > 0 && id.index < functions_.size();
    }

    GlobalId create_global(GlobalData data);
    GlobalData& global(GlobalId id);
    const GlobalData& global(GlobalId id) const;
    GlobalId find_global(std::string_view name) const;
    uint32_t global_count() const {
        return static_cast<uint32_t>(globals_.size()) - 1;
    }
    bool is_valid(GlobalId id) const {
        return id.index > 0 && id.index < globals_.size();
    }

    void add_ctor(uint32_t priority, FuncId func) { ctors_.push_back({priority, func}); }
    std::span<const CtorEntry> ctors() const { return ctors_; }
    void add_module_asm(std::string text) { module_asm_.push_back(std::move(text)); }
    std::span<const std::string> module_asm() const { return module_asm_; }

    uint32_t add_asm_payload(AsmPayload payload);
    const AsmPayload& asm_payload(uint32_t index) const;
    uint32_t asm_payload_count() const {
        return static_cast<uint32_t>(asm_payloads_.size());
    }

    uint32_t add_eh_landing_pad_payload(EhLandingPadPayload payload);
    const EhLandingPadPayload& eh_landing_pad_payload(uint32_t index) const;
    uint32_t eh_landing_pad_payload_count() const {
        return static_cast<uint32_t>(eh_landing_pad_payloads_.size());
    }

private:
    TypeTable types_;
    std::shared_ptr<const TargetInfo> target_;
    std::string triple_;
    std::vector<std::unique_ptr<Function>> functions_;
    std::vector<std::unique_ptr<GlobalData>> globals_;
    std::vector<CtorEntry> ctors_;
    std::vector<std::string> module_asm_;
    std::vector<AsmPayload> asm_payloads_;
    std::vector<EhLandingPadPayload> eh_landing_pad_payloads_;
    std::unordered_map<std::string, uint32_t> function_names_;
    std::unordered_map<std::string, uint32_t> global_names_;
};

} // namespace aburi::air

#endif // ABURI_AIR_MODULE_H
