#ifndef ABURI_PARSER_ANNOTATION_STORE_H
#define ABURI_PARSER_ANNOTATION_STORE_H

#include "tentative_syntax_probe.h"

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

namespace aburi::syntax {

class ParserAnnotationStore {
public:
    enum class ResultKind : uint8_t {
        DeclarationStatementStart,
        ExpressionStatementStart,
        Count
    };

    std::optional<tentative_syntax_probe::Result>
    lookup_result(size_t cooked_token,
                  ResultKind kind,
                  uint32_t config_key,
                  uint64_t lookup_generation,
                  uint64_t scope) const {
        size_t kind_index = static_cast<size_t>(kind);
        if (cooked_token >= slots_.size() ||
            kind_index >= static_cast<size_t>(ResultKind::Count)) {
            return std::nullopt;
        }
        const SlotSet& candidates = slots_[cooked_token][kind_index];
        for (const Slot& slot : candidates) {
            if (slot.valid &&
                slot.config_key == config_key &&
                slot.lookup_generation == lookup_generation &&
                slot.scope == scope) {
                return slot.result;
            }
        }
        return std::nullopt;
    }

    void store_result(size_t cooked_token,
                      ResultKind kind,
                      uint32_t config_key,
                      uint64_t lookup_generation,
                      uint64_t scope,
                      tentative_syntax_probe::Result result) {
        size_t kind_index = static_cast<size_t>(kind);
        if (kind_index >= static_cast<size_t>(ResultKind::Count)) {
            return;
        }
        if (cooked_token >= slots_.size()) {
            slots_.resize(cooked_token + 1);
        }
        SlotSet& candidates = slots_[cooked_token][kind_index];
        for (Slot& slot : candidates) {
            if (slot.valid &&
                slot.config_key == config_key &&
                slot.lookup_generation == lookup_generation &&
                slot.scope == scope) {
                fill_slot(slot, config_key, lookup_generation, scope, result);
                return;
            }
        }
        for (Slot& slot : candidates) {
            if (!slot.valid) {
                fill_slot(slot, config_key, lookup_generation, scope, result);
                return;
            }
        }

        size_t replacement = lookup_generation == 0 && scope == 0 ? 0 : 1;
        fill_slot(candidates[replacement],
                  config_key,
                  lookup_generation,
                  scope,
                  result);
    }

private:
    static constexpr size_t SlotsPerKind = 2;

    struct Slot {
        bool valid = false;
        uint32_t config_key = 0;
        uint64_t lookup_generation = 0;
        uint64_t scope = 0;
        tentative_syntax_probe::Result result =
            tentative_syntax_probe::Result::NoMatch;
    };

    using SlotSet = std::array<Slot, SlotsPerKind>;

    static void fill_slot(Slot& slot,
                          uint32_t config_key,
                          uint64_t lookup_generation,
                          uint64_t scope,
                          tentative_syntax_probe::Result result) {
        slot.valid = true;
        slot.config_key = config_key;
        slot.lookup_generation = lookup_generation;
        slot.scope = scope;
        slot.result = result;
    }

    std::vector<std::array<SlotSet, static_cast<size_t>(ResultKind::Count)>> slots_;
};

} // namespace aburi::syntax

#endif // ABURI_PARSER_ANNOTATION_STORE_H
