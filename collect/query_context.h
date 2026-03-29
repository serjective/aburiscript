#ifndef ABURI_QUERY_CONTEXT_H
#define ABURI_QUERY_CONTEXT_H

#include <cstdint>
#include <iosfwd>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "../ast/semantic_store.h"

class CollectQueryContext {
public:
    struct Metrics {
        uint64_t record_semantics_hits = 0;
        uint64_t record_semantics_misses = 0;
        uint64_t record_semantics_publications = 0;
        uint64_t enum_semantics_hits = 0;
        uint64_t enum_semantics_misses = 0;
        uint64_t enum_semantics_publications = 0;
        uint64_t template_specialization_type_hits = 0;
        uint64_t template_specialization_type_misses = 0;
        uint64_t template_specialization_type_publications = 0;
        uint64_t dependent_name_type_hits = 0;
        uint64_t dependent_name_type_misses = 0;
        uint64_t dependent_name_type_publications = 0;
        uint64_t overlay_begins = 0;
        uint64_t overlay_commits = 0;
        uint64_t overlay_rollbacks = 0;
        uint64_t overlay_merges = 0;
    };

    void clear();

    void begin_tentative_overlay();
    void commit_tentative_overlay(CollectSemanticStore& store);
    void rollback_tentative_overlay();
    bool has_tentative_overlay() const { return !tentative_overlays_.empty(); }

    const RecordSemanticState* lookup_record_semantics(
        const ObjectDecl* record_decl,
        const CollectSemanticStore& store) const;
    const RecordSemanticState* publish_record_semantics(
        const ObjectDecl* record_decl,
        RecordSemanticState state,
        CollectSemanticStore& store);
    void erase_record_semantics(const ObjectDecl* record_decl,
                                CollectSemanticStore& store);

    bool lookup_enum_semantics(const EnumDecl* enum_decl,
                               bool& is_incomplete_out,
                               std::shared_ptr<CType>& underlying_type_out,
                               bool& has_negative_values_out,
                               const CollectSemanticStore& store) const;
    void publish_enum_semantics(const EnumDecl* enum_decl,
                                bool is_incomplete,
                                std::shared_ptr<CType> underlying_type,
                                bool has_negative_values,
                                CollectSemanticStore& store);
    void erase_enum_semantics(const EnumDecl* enum_decl,
                              CollectSemanticStore& store);

    std::shared_ptr<CType> lookup_template_specialization_resolved_type(
        const TemplateSpecializationType* type,
        const CollectSemanticStore& store) const;
    void publish_template_specialization_resolved_type(
        const TemplateSpecializationType* type,
        std::shared_ptr<CType> resolved_type,
        CollectSemanticStore& store);

    std::shared_ptr<CType> lookup_dependent_name_resolved_type(
        const DependentNameType* type,
        const CollectSemanticStore& store) const;
    void publish_dependent_name_resolved_type(
        const DependentNameType* type,
        std::shared_ptr<CType> resolved_type,
        CollectSemanticStore& store);

    const Metrics& metrics() const { return metrics_; }
    void emit_metrics(std::ostream& os) const;

private:
    struct TentativeOverlay {
        std::unordered_map<const ObjectDecl*, std::unique_ptr<RecordSemanticState>>
            record_semantics;
        std::unordered_set<const ObjectDecl*> erased_record_semantics;

        std::unordered_map<const EnumDecl*, EnumSemanticsCacheEntry>
            enum_semantics;
        std::unordered_set<const EnumDecl*> erased_enum_semantics;

        std::unordered_map<const TemplateSpecializationType*, std::shared_ptr<CType>>
            template_specialization_resolved_types;
        std::unordered_map<const DependentNameType*, std::shared_ptr<CType>>
            dependent_name_resolved_types;
    };

    static void merge_overlay_into_parent(TentativeOverlay& parent,
                                          TentativeOverlay child);
    static void apply_overlay_to_store(TentativeOverlay& overlay,
                                       CollectSemanticStore& store);

    std::vector<TentativeOverlay> tentative_overlays_;
    mutable Metrics metrics_;
};

CollectQueryContext* get_active_collect_query_context();
void set_active_collect_query_context(CollectQueryContext* context);

#endif // ABURI_QUERY_CONTEXT_H
