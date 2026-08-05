#ifndef ABURI_BACKEND_COMMON_EH_METADATA_H
#define ABURI_BACKEND_COMMON_EH_METADATA_H

#include <cstdint>
#include <unordered_map>
#include <vector>

#include "../../air/module.h"
#include "../../diagnostics.h"
#include "mir.h"

namespace aburi::backend {

class EhMetadataBuilder {
public:
    EhMetadataBuilder(const air::Module& mod, const air::Function& func,
                      MFunction& out, std::vector<Diagnostic>& diagnostics,
                      bool& failed)
        : mod_(mod),
          func_(func),
          out_(out),
          diagnostics_(diagnostics),
          failed_(failed) {}

    void build(const std::vector<air::BlockId>& layout,
               const std::unordered_map<uint32_t, uint32_t>& block_map);

    uint32_t action_for_block(uint32_t mir_block) const;
    uint32_t typeinfo_filter_for_value(air::ValueId value, SrcLoc loc);

private:
    void error(const std::string& message, SrcLoc loc);
    uint32_t typeinfo_filter_for(air::GlobalId global, SrcLoc loc);
    uint32_t action_for_landing_pad(uint32_t payload_index);

    const air::Module& mod_;
    const air::Function& func_;
    MFunction& out_;
    std::vector<Diagnostic>& diagnostics_;
    bool& failed_;

    std::unordered_map<uint32_t, uint32_t> typeinfo_filters_;
    std::unordered_map<uint32_t, uint32_t> actions_by_payload_;
    std::unordered_map<uint32_t, uint32_t> actions_by_block_;
};

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_EH_METADATA_H
