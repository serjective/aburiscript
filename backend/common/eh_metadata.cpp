#include "eh_metadata.h"

#include "symbols.h"

namespace aburi::backend {

void EhMetadataBuilder::error(const std::string& message, SrcLoc loc) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "air backend: " + message;
    diag.location = loc.isInvalid() ? func_.loc() : loc;
    diagnostics_.push_back(std::move(diag));
    failed_ = true;
}

uint32_t EhMetadataBuilder::typeinfo_filter_for(air::GlobalId global,
                                                SrcLoc loc) {
    auto found = typeinfo_filters_.find(global.index);
    if (found == typeinfo_filters_.end()) {
        error("exception typeinfo is not present in this function's LSDA", loc);
        return 0;
    }
    return found->second;
}

uint32_t EhMetadataBuilder::typeinfo_filter_for_value(air::ValueId value,
                                                      SrcLoc loc) {
    const air::ValueData& data = func_.value(value);
    if (data.kind != air::ValueKind::GlobalAddr) {
        error("eh_typeid_for expects a typeinfo global address", loc);
        return 0;
    }
    return typeinfo_filter_for(
        air::GlobalId{static_cast<uint32_t>(data.payload)}, loc);
}

uint32_t EhMetadataBuilder::action_for_landing_pad(uint32_t payload_index) {
    auto found = actions_by_payload_.find(payload_index);
    if (found != actions_by_payload_.end()) {
        return found->second;
    }

    const air::EhLandingPadPayload& payload =
        mod_.eh_landing_pad_payload(payload_index);
    std::vector<int32_t> filters;
    filters.reserve(payload.clause_typeinfos.size() + 2);
    for (air::GlobalId global : payload.clause_typeinfos) {
        filters.push_back(
            static_cast<int32_t>(typeinfo_filter_for(global, SrcLoc{})));
    }
    if (payload.has_catch_all) {
        filters.push_back(1);
    }

    if (payload.is_cleanup && !filters.empty()) {
        filters.push_back(0);
    }

    uint32_t first_label = 0;
    uint32_t next_label = 0;
    for (auto it = filters.rbegin(); it != filters.rend(); ++it) {
        uint32_t label = out_.new_eh_label();
        out_.eh_actions.push_back(MEhAction{label, *it, next_label});
        next_label = label;
        first_label = label;
    }
    actions_by_payload_[payload_index] = first_label;
    return first_label;
}

void EhMetadataBuilder::build(
    const std::vector<air::BlockId>& layout,
    const std::unordered_map<uint32_t, uint32_t>& block_map) {

    bool has_catch_all = false;
    std::vector<air::GlobalId> typeinfo_order;
    auto note_typeinfo = [&](air::GlobalId global) {
        for (air::GlobalId existing : typeinfo_order) {
            if (existing.index == global.index) {
                return;
            }
        }
        typeinfo_order.push_back(global);
    };

    auto for_each_landing_pad = [&](auto&& visit) {
        for (air::BlockId block_id : layout) {
            const air::BlockData& block = func_.block(block_id);
            for (air::InstId inst_id = block.first; inst_id.is_valid();
                 inst_id = func_.inst(inst_id).next) {
                const air::InstData& inst = func_.inst(inst_id);
                if (inst.op == air::Opcode::EhLandingPad) {
                    visit(block_id, static_cast<uint32_t>(inst.aux));
                }
            }
        }
    };

    for_each_landing_pad([&](air::BlockId, uint32_t payload_index) {
        const air::EhLandingPadPayload& payload =
            mod_.eh_landing_pad_payload(payload_index);
        has_catch_all = has_catch_all || payload.has_catch_all;
        for (air::GlobalId global : payload.clause_typeinfos) {
            note_typeinfo(global);
        }
    });

    uint32_t filter_base = has_catch_all ? 1 : 0;
    if (has_catch_all) {
        out_.eh_typeinfos.push_back(MEhTypeInfo{1, {}});
    }
    uint32_t type_count = static_cast<uint32_t>(typeinfo_order.size());
    for (uint32_t i = 0; i < type_count; ++i) {
        air::GlobalId global = typeinfo_order[i];
        uint32_t filter = filter_base + type_count - i;
        const air::GlobalData& data = mod_.global(global);
        typeinfo_filters_[global.index] = filter;
        out_.eh_typeinfos.push_back(MEhTypeInfo{
            filter, target_symbol_name(mod_.target(), data.name,
                                       data.attrs.no_prefix)});
    }

    for_each_landing_pad([&](air::BlockId block_id, uint32_t payload_index) {
        auto mapped = block_map.find(block_id.index);
        if (mapped == block_map.end()) {
            return;
        }
        actions_by_block_[mapped->second] =
            action_for_landing_pad(payload_index);
    });
}

uint32_t EhMetadataBuilder::action_for_block(uint32_t mir_block) const {
    auto found = actions_by_block_.find(mir_block);
    return found == actions_by_block_.end() ? 0 : found->second;
}

} // namespace aburi::backend
