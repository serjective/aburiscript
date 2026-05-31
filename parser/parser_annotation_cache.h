#ifndef ABURI_PARSER_ANNOTATION_CACHE_H
#define ABURI_PARSER_ANNOTATION_CACHE_H

#include "tentative_syntax_probe.h"

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

class ParserAnnotationCache {
public:
    enum class ResultKind : uint8_t {
        TypeName,
        Declarator,
        CxxConstrainedPlaceholder,
        CppQualifiedIdStart,
        CppQualifiedDeclarator,
        CppTemplateNameArgumentPrefix,
        ParenthesizedTypeName,
        Count
    };

    ParserAnnotationCache() = default;
    explicit ParserAnnotationCache(size_t token_count) {
        reset(token_count);
    }

    void reset(size_t token_count) {
        slots_.clear();
        slots_.resize(token_count);
    }

    static uint32_t make_config_key(const tentative_syntax_probe::Config& cfg) {
        uint32_t key = 0;
        if (cfg.cxx_mode) {
            key |= 1u << 0;
        }
        if (cfg.blocks_enabled) {
            key |= 1u << 1;
        }
        return key;
    }

    std::optional<tentative_syntax_probe::Result>
    lookup_result(size_t token_idx, ResultKind kind, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->results[static_cast<size_t>(kind)];
        if (!entry.valid || entry.key != key) {
            return std::nullopt;
        }
        return entry.value;
    }

    void store_result(size_t token_idx,
                      ResultKind kind,
                      uint32_t key,
                      tentative_syntax_probe::Result value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        auto& entry = slot->results[static_cast<size_t>(kind)];
        entry.valid = true;
        entry.key = key;
        entry.value = value;
    }

    std::optional<tentative_syntax_probe::TemplateArgumentListScan>
    lookup_template_argument_list_scan(size_t token_idx, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot || !slot->template_argument_list_scan.valid ||
            slot->template_argument_list_scan.key != key) {
            return std::nullopt;
        }
        return slot->template_argument_list_scan.value;
    }

    void store_template_argument_list_scan(
        size_t token_idx,
        uint32_t key,
        tentative_syntax_probe::TemplateArgumentListScan value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        slot->template_argument_list_scan.valid = true;
        slot->template_argument_list_scan.key = key;
        slot->template_argument_list_scan.value = value;
    }

    std::optional<tentative_syntax_probe::CxxTypeConstructionScan>
    lookup_type_construction_scan(size_t token_idx, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot || !slot->type_construction_scan.valid ||
            slot->type_construction_scan.key != key) {
            return std::nullopt;
        }
        return slot->type_construction_scan.value;
    }

    void store_type_construction_scan(
        size_t token_idx,
        uint32_t key,
        tentative_syntax_probe::CxxTypeConstructionScan value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        slot->type_construction_scan.valid = true;
        slot->type_construction_scan.key = key;
        slot->type_construction_scan.value = value;
    }

    std::optional<tentative_syntax_probe::CxxParameterClauseShape>
    lookup_parameter_clause_shape(size_t token_idx, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot || !slot->parameter_clause_shape.valid ||
            slot->parameter_clause_shape.key != key) {
            return std::nullopt;
        }
        return slot->parameter_clause_shape.value;
    }

    void store_parameter_clause_shape(
        size_t token_idx,
        uint32_t key,
        tentative_syntax_probe::CxxParameterClauseShape value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        slot->parameter_clause_shape.valid = true;
        slot->parameter_clause_shape.key = key;
        slot->parameter_clause_shape.value = value;
    }

private:
    struct ResultEntry {
        bool valid = false;
        uint32_t key = 0;
        tentative_syntax_probe::Result value =
            tentative_syntax_probe::Result::NoMatch;
    };

    template <typename T>
    struct Entry {
        bool valid = false;
        uint32_t key = 0;
        T value{};
    };

    struct TokenSlots {
        std::array<ResultEntry, static_cast<size_t>(ResultKind::Count)> results;
        Entry<tentative_syntax_probe::TemplateArgumentListScan>
            template_argument_list_scan;
        Entry<tentative_syntax_probe::CxxTypeConstructionScan>
            type_construction_scan;
        Entry<tentative_syntax_probe::CxxParameterClauseShape>
            parameter_clause_shape;
    };

    TokenSlots* slot_for(size_t token_idx) {
        if (token_idx >= slots_.size()) {
            return nullptr;
        }
        return &slots_[token_idx];
    }

    const TokenSlots* slot_for(size_t token_idx) const {
        if (token_idx >= slots_.size()) {
            return nullptr;
        }
        return &slots_[token_idx];
    }

    std::vector<TokenSlots> slots_;
};

#endif
