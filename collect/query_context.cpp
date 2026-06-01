#include "query_context.h"

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <utility>

#include "collect.h"
#include "../perf_stats.h"

namespace {
thread_local CollectQueryContext* g_active_collect_query_context = nullptr;

bool refactor_metrics_enabled() {
    static const bool enabled = []() {
        const char* env = std::getenv("ABURI_REFACTOR_METRICS");
        return env && env[0] != '\0' && env[0] != '0';
    }();
    return enabled;
}

const ObjectDecl* canonical_record_owner_decl(const ObjectDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto record_type = decl->get_record_type()) {
        if (auto* canonical_decl =
                dyn_cast<ObjectDecl>(record_type->get_decl())) {
            return canonical_decl;
        }
    }
    return decl;
}

} // namespace

CollectQueryContext* get_active_collect_query_context() {
    return g_active_collect_query_context;
}

void set_active_collect_query_context(CollectQueryContext* context) {
    g_active_collect_query_context = context;
}

void CollectQueryContext::clear() {
    tentative_overlays_.clear();
    metrics_ = Metrics{};
    bump_revision();
}

void CollectQueryContext::bump_revision() {
    ++revision_;
    if (revision_ == 0) {
        revision_ = 1;
    }
}

void CollectQueryContext::begin_tentative_overlay() {
    tentative_overlays_.push_back(nullptr);
    ++metrics_.overlay_begins;
}

CollectQueryContext::TentativeOverlay&
CollectQueryContext::ensure_current_tentative_overlay() {
    assert(!tentative_overlays_.empty() &&
           "query overlay materialization requires speculative context");
    auto& overlay = tentative_overlays_.back();
    if (!overlay) {
        overlay = std::make_unique<TentativeOverlay>();
        ++metrics_.overlay_materializations;
    }
    return *overlay;
}

void CollectQueryContext::merge_overlay_into_parent(TentativeOverlay& parent,
                                                    TentativeOverlay child) {
    for (auto* record_decl : child.erased_record_semantics) {
        parent.record_semantics.erase(record_decl);
        parent.erased_record_semantics.insert(record_decl);
    }
    for (auto& [record_decl, state] : child.record_semantics) {
        parent.erased_record_semantics.erase(record_decl);
        parent.record_semantics[record_decl] = std::move(state);
    }

    for (auto* enum_decl : child.erased_enum_semantics) {
        parent.enum_semantics.erase(enum_decl);
        parent.erased_enum_semantics.insert(enum_decl);
    }
    for (auto& [enum_decl, state] : child.enum_semantics) {
        parent.erased_enum_semantics.erase(enum_decl);
        parent.enum_semantics[enum_decl] = std::move(state);
    }

    for (auto& [type, entry] :
         child.template_specialization_resolved_types) {
        parent.template_specialization_resolved_types[type] =
            std::move(entry);
    }
    for (auto& [type, entry] : child.dependent_name_resolved_types) {
        parent.dependent_name_resolved_types[type] = std::move(entry);
    }
}

void CollectQueryContext::apply_overlay_to_store(TentativeOverlay& overlay,
                                                 CollectSemanticStore& store) {
    for (auto* record_decl : overlay.erased_record_semantics) {
        store.erase_record_semantics(record_decl);
    }
    for (auto& [record_decl, state] : overlay.record_semantics) {
        if (state) {
            store.set_record_semantics(record_decl, std::move(*state));
        }
    }

    for (auto* enum_decl : overlay.erased_enum_semantics) {
        store.erase_enum_semantics(enum_decl);
    }
    for (auto& [enum_decl, state] : overlay.enum_semantics) {
        store.set_enum_semantics(enum_decl, std::move(state));
    }

    for (auto& overlay_entry : overlay.template_specialization_resolved_types) {
        auto& entry = overlay_entry.second;
        store.set_template_specialization_resolved_type(
            std::move(entry.key_type),
            std::move(entry.resolved_type));
    }
    for (auto& overlay_entry : overlay.dependent_name_resolved_types) {
        auto& entry = overlay_entry.second;
        store.set_dependent_name_resolved_type(std::move(entry.key_type),
                                               std::move(entry.resolved_type));
    }
}

void CollectQueryContext::commit_tentative_overlay(CollectSemanticStore& store) {
    if (tentative_overlays_.empty()) {
        return;
    }
    auto overlay = std::move(tentative_overlays_.back());
    tentative_overlays_.pop_back();
    ++metrics_.overlay_commits;
    if (!overlay) {
        return;
    }
    if (!tentative_overlays_.empty()) {
        merge_overlay_into_parent(
            ensure_current_tentative_overlay(),
            std::move(*overlay));
        ++metrics_.overlay_merges;
        return;
    }
    apply_overlay_to_store(*overlay, store);
    bump_revision();
}

void CollectQueryContext::rollback_tentative_overlay() {
    if (tentative_overlays_.empty()) {
        return;
    }
    bool had_materialized_overlay =
        static_cast<bool>(tentative_overlays_.back());
    tentative_overlays_.pop_back();
    ++metrics_.overlay_rollbacks;
    if (had_materialized_overlay) {
        bump_revision();
    }
}

const RecordSemanticState* CollectQueryContext::lookup_record_semantics(
    const ObjectDecl* record_decl,
    const CollectSemanticStore& store) const {
    if (!record_decl) {
        return nullptr;
    }
    for (auto it = tentative_overlays_.rbegin();
         it != tentative_overlays_.rend();
         ++it) {
        if (!*it) {
            continue;
        }
        const auto& overlay = **it;
        if (overlay.erased_record_semantics.contains(record_decl)) {
            ++metrics_.record_semantics_misses;
            return nullptr;
        }
        auto overlay_it = overlay.record_semantics.find(record_decl);
        if (overlay_it != overlay.record_semantics.end()) {
            ++metrics_.record_semantics_hits;
            return overlay_it->second.get();
        }
    }
    if (const auto* state = store.lookup_record_semantics(record_decl)) {
        ++metrics_.record_semantics_hits;
        return state;
    }
    ++metrics_.record_semantics_misses;
    return nullptr;
}

const RecordSemanticState* CollectQueryContext::publish_record_semantics(
    const ObjectDecl* record_decl,
    RecordSemanticState state,
    CollectSemanticStore& store) {
    if (!record_decl) {
        return nullptr;
    }
    ++metrics_.record_semantics_publications;
    bump_revision();
    if (tentative_overlays_.empty()) {
        store.set_record_semantics(record_decl, std::move(state));
        return store.lookup_record_semantics(record_decl);
    }
    auto& overlay = ensure_current_tentative_overlay();
    overlay.erased_record_semantics.erase(record_decl);
    auto& slot = overlay.record_semantics[record_decl];
    slot = std::make_unique<RecordSemanticState>(std::move(state));
    return slot.get();
}

void CollectQueryContext::erase_record_semantics(const ObjectDecl* record_decl,
                                                 CollectSemanticStore& store) {
    if (!record_decl) {
        return;
    }
    bump_revision();
    if (tentative_overlays_.empty()) {
        store.erase_record_semantics(record_decl);
        return;
    }
    auto& overlay = ensure_current_tentative_overlay();
    overlay.record_semantics.erase(record_decl);
    overlay.erased_record_semantics.insert(record_decl);
}

bool CollectQueryContext::lookup_enum_semantics(
    const EnumDecl* enum_decl,
    EnumSemanticState& state_out,
    const CollectSemanticStore& store) const {
    if (!enum_decl) {
        return false;
    }
    for (auto it = tentative_overlays_.rbegin();
         it != tentative_overlays_.rend();
         ++it) {
        if (!*it) {
            continue;
        }
        const auto& overlay = **it;
        if (overlay.erased_enum_semantics.contains(enum_decl)) {
            ++metrics_.enum_semantics_misses;
            return false;
        }
        auto overlay_it = overlay.enum_semantics.find(enum_decl);
        if (overlay_it != overlay.enum_semantics.end()) {
            state_out = overlay_it->second;
            ++metrics_.enum_semantics_hits;
            return true;
        }
    }
    if (store.lookup_enum_semantics(enum_decl, state_out)) {
        ++metrics_.enum_semantics_hits;
        return true;
    }
    ++metrics_.enum_semantics_misses;
    return false;
}

void CollectQueryContext::publish_enum_semantics(
    const EnumDecl* enum_decl,
    EnumSemanticState state,
    CollectSemanticStore& store) {
    if (!enum_decl) {
        return;
    }
    ++metrics_.enum_semantics_publications;
    if (tentative_overlays_.empty()) {
        store.set_enum_semantics(enum_decl, std::move(state));
        return;
    }
    auto& overlay = ensure_current_tentative_overlay();
    overlay.erased_enum_semantics.erase(enum_decl);
    overlay.enum_semantics[enum_decl] = std::move(state);
}

void CollectQueryContext::erase_enum_semantics(const EnumDecl* enum_decl,
                                               CollectSemanticStore& store) {
    if (!enum_decl) {
        return;
    }
    if (tentative_overlays_.empty()) {
        store.erase_enum_semantics(enum_decl);
        return;
    }
    auto& overlay = ensure_current_tentative_overlay();
    overlay.enum_semantics.erase(enum_decl);
    overlay.erased_enum_semantics.insert(enum_decl);
}

QualType
CollectQueryContext::lookup_template_specialization_resolved_type(
    const TemplateSpecializationType* type,
    const CollectSemanticStore& store) const {
    if (!type) {
        return QualType();
    }
    if (type->external_semantic_owner_id != 0 &&
        type->external_semantic_owner_id != store.registry_id()) {
        ++metrics_.template_specialization_type_misses;
        return QualType();
    }
    for (auto it = tentative_overlays_.rbegin();
         it != tentative_overlays_.rend();
         ++it) {
        if (!*it) {
            continue;
        }
        const auto& overlay = **it;
        auto overlay_it =
            overlay.template_specialization_resolved_types.find(type);
        if (overlay_it !=
            overlay.template_specialization_resolved_types.end()) {
            ++metrics_.template_specialization_type_hits;
            return overlay_it->second.resolved_type;
        }
    }
    if (auto resolved_type = store.get_template_specialization_resolved_type(type)) {
        ++metrics_.template_specialization_type_hits;
        return resolved_type;
    }
    ++metrics_.template_specialization_type_misses;
    return QualType();
}

void CollectQueryContext::publish_template_specialization_resolved_type(
    QualType key_type,
    QualType resolved_type,
    CollectSemanticStore& store) {
    auto* type = key_type.as<TemplateSpecializationType>();
    if (!type) {
        return;
    }
    ++metrics_.template_specialization_type_publications;
    type->external_semantic_owner_id = store.registry_id();
    if (tentative_overlays_.empty()) {
        store.set_template_specialization_resolved_type(
            std::move(key_type),
            std::move(resolved_type));
        return;
    }
    auto& overlay = ensure_current_tentative_overlay();
    overlay.template_specialization_resolved_types[type] =
        ResolvedTypeCacheEntry{std::move(key_type), std::move(resolved_type)};
}

QualType CollectQueryContext::lookup_dependent_name_resolved_type(
    const DependentNameType* type,
    const CollectSemanticStore& store) const {
    if (!type) {
        return QualType();
    }
    if (type->external_semantic_owner_id != 0 &&
        type->external_semantic_owner_id != store.registry_id()) {
        ++metrics_.dependent_name_type_misses;
        return QualType();
    }
    for (auto it = tentative_overlays_.rbegin();
         it != tentative_overlays_.rend();
         ++it) {
        if (!*it) {
            continue;
        }
        const auto& overlay = **it;
        auto overlay_it = overlay.dependent_name_resolved_types.find(type);
        if (overlay_it != overlay.dependent_name_resolved_types.end()) {
            ++metrics_.dependent_name_type_hits;
            return overlay_it->second.resolved_type;
        }
    }
    if (auto resolved_type = store.get_dependent_name_resolved_type(type)) {
        ++metrics_.dependent_name_type_hits;
        return resolved_type;
    }
    ++metrics_.dependent_name_type_misses;
    return QualType();
}

void CollectQueryContext::publish_dependent_name_resolved_type(
    QualType key_type,
    QualType resolved_type,
    CollectSemanticStore& store) {
    auto* type = key_type.as<DependentNameType>();
    if (!type) {
        return;
    }
    ++metrics_.dependent_name_type_publications;
    type->external_semantic_owner_id = store.registry_id();
    if (tentative_overlays_.empty()) {
        store.set_dependent_name_resolved_type(std::move(key_type),
                                               std::move(resolved_type));
        return;
    }
    auto& overlay = ensure_current_tentative_overlay();
    overlay.dependent_name_resolved_types[type] =
        ResolvedTypeCacheEntry{std::move(key_type), std::move(resolved_type)};
}

void CollectQueryContext::emit_metrics(std::ostream& os) const {
    os << "[refactor-metrics] collect.query "
       << "record_hits=" << metrics_.record_semantics_hits
       << " record_misses=" << metrics_.record_semantics_misses
       << " record_publishes=" << metrics_.record_semantics_publications
       << " enum_hits=" << metrics_.enum_semantics_hits
       << " enum_misses=" << metrics_.enum_semantics_misses
       << " enum_publishes=" << metrics_.enum_semantics_publications
       << " tstype_hits=" << metrics_.template_specialization_type_hits
       << " tstype_misses=" << metrics_.template_specialization_type_misses
       << " tstype_publishes=" << metrics_.template_specialization_type_publications
       << " depname_hits=" << metrics_.dependent_name_type_hits
       << " depname_misses=" << metrics_.dependent_name_type_misses
       << " depname_publishes=" << metrics_.dependent_name_type_publications
       << " overlay_begins=" << metrics_.overlay_begins
       << " overlay_materializations=" << metrics_.overlay_materializations
       << " overlay_commits=" << metrics_.overlay_commits
       << " overlay_rollbacks=" << metrics_.overlay_rollbacks
       << " overlay_merges=" << metrics_.overlay_merges
       << '\n';
}

Collect::Collect(std::shared_ptr<ASTContext> ast_ctx,
                 std::shared_ptr<SourceManager> sm,
                 std::shared_ptr<DiagnosticEngine> diag_engine,
                 LangOptions lang_opts)
    : ast_ctx_(std::move(ast_ctx)),
      previous_active_query_context_(get_active_collect_query_context()),
      side_table_scope_(ast_ctx_.get()),
      sm_(std::move(sm)),
      diag_engine_(std::move(diag_engine)),
      lang_opts_(lang_opts) {
    set_active_collect_query_context(&query_context_);
}

Collect::~Collect() {
    if (auto* profiler = active_perf_profiler()) {
        const auto& metrics = query_context_.metrics();
        profiler->add_counter(PerfCounter::CollectQueryRecordHits,
            metrics.record_semantics_hits);
        profiler->add_counter(PerfCounter::CollectQueryRecordMisses,
            metrics.record_semantics_misses);
        profiler->add_counter(PerfCounter::CollectQueryRecordPublishes,
            metrics.record_semantics_publications);
        profiler->add_counter(PerfCounter::CollectQueryEnumHits,
            metrics.enum_semantics_hits);
        profiler->add_counter(PerfCounter::CollectQueryEnumMisses,
            metrics.enum_semantics_misses);
        profiler->add_counter(PerfCounter::CollectQueryEnumPublishes,
            metrics.enum_semantics_publications);
        profiler->add_counter(PerfCounter::CollectQueryTemplateTypeHits,
            metrics.template_specialization_type_hits);
        profiler->add_counter(PerfCounter::CollectQueryTemplateTypeMisses,
            metrics.template_specialization_type_misses);
        profiler->add_counter(PerfCounter::CollectQueryTemplateTypePublishes,
            metrics.template_specialization_type_publications);
        profiler->add_counter(PerfCounter::CollectQueryDependentNameHits,
            metrics.dependent_name_type_hits);
        profiler->add_counter(PerfCounter::CollectQueryDependentNameMisses,
            metrics.dependent_name_type_misses);
        profiler->add_counter(PerfCounter::CollectQueryDependentNamePublishes,
            metrics.dependent_name_type_publications);
        profiler->add_counter(PerfCounter::CollectQueryOverlayBegins,
            metrics.overlay_begins);
        profiler->add_counter(PerfCounter::CollectQueryOverlayMaterializations,
            metrics.overlay_materializations);
        profiler->add_counter(PerfCounter::CollectQueryOverlayCommits,
            metrics.overlay_commits);
        profiler->add_counter(PerfCounter::CollectQueryOverlayRollbacks,
            metrics.overlay_rollbacks);
        profiler->add_counter(PerfCounter::CollectQueryOverlayMerges,
            metrics.overlay_merges);
    }
    if (refactor_metrics_enabled()) {
        query_context_.emit_metrics(std::cerr);
    }
    if (get_active_collect_query_context() == &query_context_) {
        set_active_collect_query_context(previous_active_query_context_);
    }
}

const RecordSemanticState* Collect::query_lookup_record_semantics(
    const ObjectDecl* record_decl) const {
    if (!ast_ctx_ || !record_decl) {
        return nullptr;
    }
    return query_context_.lookup_record_semantics(
        record_decl,
        ast_ctx_->semantic_store());
}

const RecordSemanticState* Collect::ensure_record_semantics_available(
    QualType owner_type,
    SrcLoc loc) {
    if (!ast_ctx_ || !owner_type) {
        return nullptr;
    }

    auto record_type =
        desugar_type(owner_type, ast_ctx_.get()).as_shared<ObjectType>();
    if (!record_type) {
        return nullptr;
    }
    auto* owner_decl = dyn_cast<ObjectDecl>(record_type->get_decl());
    if (!owner_decl) {
        return nullptr;
    }
    owner_decl = const_cast<ObjectDecl*>(canonical_record_owner_decl(owner_decl));

    const RecordSemanticState* state = query_lookup_record_semantics(owner_decl);
    bool needs_specialization_instantiation =
        record_type->is_class_template_specialization() &&
        (!state ||
         state->is_incomplete ||
         state->is_template_pattern_provisional);
    if (state && !state->is_incomplete && !needs_specialization_instantiation) {
        return state;
    }
    if (!record_type->is_class_template_specialization()) {
        return state;
    }

    const ClassTemplateDecl* primary_template =
        record_type->get_primary_class_template();
    if (!primary_template) {
        return state;
    }

    ObjectDecl* realized_decl = try_instantiate_class_template_specialization(
        primary_template,
        record_type->get_template_specialization_arguments(),
        loc);
    if (!realized_decl) {
        return state;
    }

    auto* canonical_realized =
        const_cast<ObjectDecl*>(canonical_record_owner_decl(realized_decl));
    if (const RecordSemanticState* realized_state =
            query_lookup_record_semantics(canonical_realized)) {
        return realized_state;
    }
    return query_lookup_record_semantics(owner_decl);
}

Collect::ObjectInitializationRecordSemantics
Collect::collect_object_initialization_record_semantics(
    QualType object_type,
    SrcLoc loc) {
    ObjectInitializationRecordSemantics result;
    if (!ast_ctx_ || !object_type) {
        return result;
    }

    result.record_type =
        desugar_type(object_type, ast_ctx_.get()).as_shared<ObjectType>();
    if (!result.record_type) {
        return result;
    }

    auto* owner_decl = dyn_cast<ObjectDecl>(result.record_type->get_decl());
    if (!owner_decl) {
        return result;
    }

    result.record_decl = canonical_record_owner_decl(owner_decl);
    result.state = query_lookup_record_semantics(result.record_decl);

    bool needs_specialization_instantiation =
        result.record_type->is_class_template_specialization() &&
        (!result.state ||
         result.state->is_incomplete ||
         result.state->is_template_pattern_provisional);
    if (!needs_specialization_instantiation) {
        return result;
    }

    const ClassTemplateDecl* primary_template =
        result.record_type->get_primary_class_template();
    if (!primary_template) {
        return result;
    }

    ObjectDecl* realized_decl = try_instantiate_class_template_specialization(
        primary_template,
        result.record_type->get_template_specialization_arguments(),
        loc);
    if (!realized_decl) {
        return result;
    }

    result.record_decl = canonical_record_owner_decl(realized_decl);
    if (result.record_decl) {
        if (auto realized_type = result.record_decl->get_record_type()) {
            result.record_type = realized_type;
        }
        if (const RecordSemanticState* realized_state =
                query_lookup_record_semantics(result.record_decl)) {
            result.state = realized_state;
        }
    }
    return result;
}

const RecordSemanticState* Collect::query_publish_record_semantics(
    const ObjectDecl* record_decl,
    RecordSemanticState state) {
    if (!ast_ctx_ || !record_decl) {
        return nullptr;
    }
    return query_context_.publish_record_semantics(
        record_decl,
        std::move(state),
        ast_ctx_->semantic_store());
}

void Collect::query_erase_record_semantics(const ObjectDecl* record_decl) {
    if (!ast_ctx_ || !record_decl) {
        return;
    }
    query_context_.erase_record_semantics(record_decl, ast_ctx_->semantic_store());
}

bool Collect::query_lookup_enum_semantics(
    const EnumDecl* enum_decl,
    EnumSemanticState& state_out) const {
    if (!ast_ctx_ || !enum_decl) {
        return false;
    }
    return query_context_.lookup_enum_semantics(enum_decl,
                                                state_out,
                                                ast_ctx_->semantic_store());
}

void Collect::query_publish_enum_semantics(const EnumDecl* enum_decl,
                                           EnumSemanticState state) {
    if (!ast_ctx_ || !enum_decl) {
        return;
    }
    query_context_.publish_enum_semantics(enum_decl,
                                          std::move(state),
                                          ast_ctx_->semantic_store());
}

QualType
Collect::query_lookup_template_specialization_resolved_type(
    const TemplateSpecializationType* type) const {
    if (!ast_ctx_ || !type) {
        return QualType();
    }
    return query_context_.lookup_template_specialization_resolved_type(
        type,
        ast_ctx_->semantic_store());
}

void Collect::query_publish_template_specialization_resolved_type(
    QualType type,
    QualType resolved_type) {
    if (!ast_ctx_ || !type) {
        return;
    }
    query_context_.publish_template_specialization_resolved_type(
        std::move(type),
        std::move(resolved_type),
        ast_ctx_->semantic_store());
}

QualType Collect::query_lookup_dependent_name_resolved_type(
    const DependentNameType* type) const {
    if (!ast_ctx_ || !type) {
        return QualType();
    }
    return query_context_.lookup_dependent_name_resolved_type(
        type,
        ast_ctx_->semantic_store());
}

void Collect::query_publish_dependent_name_resolved_type(
    QualType type,
    QualType resolved_type) {
    if (!ast_ctx_ || !type) {
        return;
    }
    query_context_.publish_dependent_name_resolved_type(
        std::move(type),
        std::move(resolved_type),
        ast_ctx_->semantic_store());
}
