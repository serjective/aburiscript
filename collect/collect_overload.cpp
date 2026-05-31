#include "collect.h"
#include "collect_internal.h"
#include "collect_templates_internal.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"
#include <algorithm>
#include <cstdlib>
#include <cstdint>
#include <functional>
#include <iostream>
#include <unordered_set>

using namespace collect_internal;

namespace {
struct OverloadMetrics {
    uint64_t resolve_calls = 0;
    uint64_t candidate_evaluations = 0;
    uint64_t best_candidate_pairwise_comparisons = 0;
    uint64_t best_candidate_frontier_prunes = 0;
    uint64_t viable_candidates = 0;
    uint64_t conversion_cache_hits = 0;
    uint64_t conversion_cache_misses = 0;
};

bool refactor_metrics_enabled() {
    static const bool enabled = []() {
        const char* env = std::getenv("ABURI_REFACTOR_METRICS");
        return env && env[0] != '\0' && env[0] != '0';
    }();
    return enabled;
}

void repair_member_candidate_symbol_owner_type(
    const RecordSemanticState::Method& method,
    const ObjectDecl* owner_record_decl,
    const ASTContext* ast_ctx) {
    if (method.is_static || !method.symbol || !owner_record_decl || !ast_ctx) {
        return;
    }
    auto owner_type = owner_record_decl->get_record_type();
    if (!owner_type) {
        return;
    }
    auto function_type =
        desugar_type(method.symbol->type, ast_ctx).as_shared<FunctionType>();
    if (!function_type || function_type->parameters.empty()) {
        return;
    }
    auto this_ptr =
        desugar_type(
            remove_reference(function_type->parameters.front(), ast_ctx),
            ast_ctx)
            .as_shared<PointerType>();
    auto this_record = this_ptr
        ? desugar_type(
              remove_reference(this_ptr->pointed_type, ast_ctx),
              ast_ctx)
              .as_shared<ObjectType>()
        : nullptr;
    auto* this_decl = this_record
        ? canonical_record_decl(dyn_cast<ObjectDecl>(this_record->get_decl()))
        : nullptr;
    auto* canonical_owner = canonical_record_decl(owner_record_decl);
    if (!this_decl || !canonical_owner || this_decl == canonical_owner) {
        return;
    }

    QualType rewritten_type = collect_template_internal::replace_record_decl_in_type(
        method.symbol->type,
        this_decl,
        QualType(owner_type),
        ast_ctx);
    if (rewritten_type) {
        method.symbol->type = desugar_type(rewritten_type, ast_ctx);
    }
}

OverloadMetrics& overload_metrics() {
    static OverloadMetrics metrics;
    return metrics;
}

void emit_overload_metrics_at_exit() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    const auto& metrics = overload_metrics();
    std::cerr
        << "[refactor-metrics] collect.overload "
        << "resolve_calls=" << metrics.resolve_calls
        << " candidate_evals=" << metrics.candidate_evaluations
        << " pairwise_compares=" << metrics.best_candidate_pairwise_comparisons
        << " frontier_prunes=" << metrics.best_candidate_frontier_prunes
        << " viable_candidates=" << metrics.viable_candidates
        << " conversion_cache_hits=" << metrics.conversion_cache_hits
        << " conversion_cache_misses=" << metrics.conversion_cache_misses
        << '\n';
}

struct OverloadMetricsReporter {
    ~OverloadMetricsReporter() {
        emit_overload_metrics_at_exit();
    }
};

OverloadMetricsReporter g_overload_metrics_reporter;

void bump_overload_resolve_calls() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().resolve_calls;
}

void bump_overload_candidate_evaluations() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().candidate_evaluations;
}

void bump_overload_pairwise_comparisons() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().best_candidate_pairwise_comparisons;
}

void bump_overload_frontier_prunes() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().best_candidate_frontier_prunes;
}

void bump_overload_viable_candidates(size_t count) {
    if (!refactor_metrics_enabled()) {
        return;
    }
    overload_metrics().viable_candidates += count;
}

void bump_overload_conversion_cache_hit() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().conversion_cache_hits;
}

void bump_overload_conversion_cache_miss() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().conversion_cache_misses;
}

size_t hash_combine(size_t seed, size_t value) {
    seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6U) + (seed >> 2U);
    return seed;
}

bool is_non_variadic_prototype(const std::shared_ptr<FunctionType>& fn_type) {
    return fn_type && fn_type->has_prototype && !fn_type->is_variadic;
}

bool exception_spec_compatible_for_function_pointer_conversion(
    FunctionExceptionSpecKind source_spec,
    FunctionExceptionSpecKind target_spec) {
    if (source_spec == target_spec) {
        return true;
    }
    return source_spec == FunctionExceptionSpecKind::NonThrowing &&
           target_spec == FunctionExceptionSpecKind::PotentiallyThrowing;
}

bool function_types_compatible_for_lambda_pointer_conversion(
    const std::shared_ptr<FunctionType>& source_fn,
    const std::shared_ptr<FunctionType>& target_fn,
    const ASTContext* ast_ctx) {
    if (!source_fn || !target_fn) {
        return false;
    }
    if (source_fn->is_variadic != target_fn->is_variadic ||
        source_fn->has_prototype != target_fn->has_prototype ||
        source_fn->parameters.size() != target_fn->parameters.size()) {
        return false;
    }
    if (!source_fn->ret_type.equals_qualified(target_fn->ret_type)) {
        return false;
    }
    for (size_t index = 0; index < source_fn->parameters.size(); ++index) {
        QualType source_param =
            desugar_type(source_fn->parameters[index], ast_ctx);
        QualType target_param =
            desugar_type(target_fn->parameters[index], ast_ctx);
        if (!source_param.equals_qualified(target_param)) {
            return false;
        }
    }
    return exception_spec_compatible_for_function_pointer_conversion(
        source_fn->exception_spec,
        target_fn->exception_spec);
}

bool is_strictly_better_conversion_profile(
    const std::vector<Collect::ImplicitConversionSequence>& lhs_conversions,
    const std::shared_ptr<FunctionType>& lhs_function_type,
    const std::vector<Collect::ImplicitConversionSequence>& rhs_conversions,
    const std::shared_ptr<FunctionType>& rhs_function_type) {
    bool strictly_better = false;
    size_t compare_count = std::min(lhs_conversions.size(), rhs_conversions.size());
    for (size_t i = 0; i < compare_count; ++i) {
        auto lhs_rank = static_cast<int>(lhs_conversions[i].rank);
        auto rhs_rank = static_cast<int>(rhs_conversions[i].rank);
        if (lhs_rank > rhs_rank) {
            return false;
        }
        if (lhs_rank < rhs_rank) {
            strictly_better = true;
            continue;
        }
        if (lhs_conversions[i].rank == Collect::ConversionSequenceRank::ExactMatch) {
            int qualification_order =
                compare_qualification_conversion_sequences(
                    lhs_conversions[i],
                    rhs_conversions[i],
                    get_active_side_table_ast_context());
            if (qualification_order < 0) {
                strictly_better = true;
                continue;
            }
            if (qualification_order > 0) {
                return false;
            }
            int lhs_subrank = exact_match_subrank(lhs_conversions[i]);
            int rhs_subrank = exact_match_subrank(rhs_conversions[i]);
            if (lhs_subrank > rhs_subrank) {
                return false;
            }
            if (lhs_subrank < rhs_subrank) {
                strictly_better = true;
            }
        }
        if (lhs_conversions[i].rank == Collect::ConversionSequenceRank::Conversion) {
            int derived_binding_order =
                compare_derived_to_base_pointer_conversion_sequences(
                    lhs_conversions[i],
                    rhs_conversions[i],
                    get_active_side_table_ast_context());
            if (derived_binding_order < 0) {
                strictly_better = true;
                continue;
            }
            if (derived_binding_order > 0) {
                return false;
            }
            int lhs_tiebreak = conversion_rank_tiebreak(lhs_conversions[i]);
            int rhs_tiebreak = conversion_rank_tiebreak(rhs_conversions[i]);
            if (lhs_tiebreak > rhs_tiebreak) {
                return false;
            }
            if (lhs_tiebreak < rhs_tiebreak) {
                strictly_better = true;
            }
        }
    }

    bool lhs_non_variadic = is_non_variadic_prototype(lhs_function_type);
    bool rhs_non_variadic = is_non_variadic_prototype(rhs_function_type);
    if (!strictly_better && lhs_non_variadic && !rhs_non_variadic) {
        strictly_better = true;
    } else if (!lhs_non_variadic && rhs_non_variadic) {
        return false;
    }
    return strictly_better;
}

bool is_function_template_specialization_symbol(
    const std::shared_ptr<Symbol>& symbol) {
    return symbol &&
        get_symbol_function_template_specialization(symbol.get()) != nullptr;
}

OverloadCandidateProvenance function_candidate_provenance(
    const std::shared_ptr<Symbol>& symbol) {
    return is_function_template_specialization_symbol(symbol)
        ? OverloadCandidateProvenance::FunctionTemplateSpecialization
        : OverloadCandidateProvenance::OrdinaryFunction;
}

OverloadCandidateProvenance constructor_candidate_provenance(
    const RecordSemanticState::Constructor& ctor) {
    if (ctor.is_implicit) {
        return OverloadCandidateProvenance::ImplicitSpecialMember;
    }
    if (ctor.function_template ||
        (ctor.symbol &&
         get_symbol_function_template_specialization(ctor.symbol.get()))) {
        return OverloadCandidateProvenance::ConstructorTemplateSpecialization;
    }
    return OverloadCandidateProvenance::Constructor;
}

bool overload_candidate_is_template_specialization(
    OverloadCandidateProvenance provenance) {
    return provenance ==
               OverloadCandidateProvenance::FunctionTemplateSpecialization ||
           provenance ==
               OverloadCandidateProvenance::ConstructorTemplateSpecialization;
}

std::vector<Expr*> make_raw_explicit_args(
    const std::vector<std::unique_ptr<Expr>>& explicit_args) {
    std::vector<Expr*> raw_args;
    raw_args.reserve(explicit_args.size());
    for (const auto& arg : explicit_args) {
        raw_args.push_back(arg.get());
    }
    return raw_args;
}

void append_unique_function_template_candidate(
    std::vector<const FunctionTemplateDecl*>& candidates,
    const Decl* decl) {
    auto* function_template = dyn_cast<FunctionTemplateDecl>(decl);
    if (!function_template) {
        return;
    }
    if (function_template->is_hidden_friend) {
        return;
    }
    for (auto*& existing : candidates) {
        if (!template_decls_share_lookup_identity(existing, function_template)) {
            continue;
        }
        if (template_decl_is_preferred_lookup_representative(
                existing,
                function_template)) {
            existing = function_template;
        }
        return;
    }
    candidates.push_back(function_template);
}

std::vector<const FunctionTemplateDecl*> lookup_unqualified_function_templates(
    std::string_view callee_name,
    const std::shared_ptr<Scope>& current_scope) {
    std::vector<const FunctionTemplateDecl*> template_candidates;
    if (!current_scope) {
        return template_candidates;
    }

    const DeclBinding* template_binding =
        LookupEngine::lookup_unqualified_template_binding(
            std::string(callee_name),
            current_scope,
            true,
            LookupNamespace::Ordinary);
    if (!template_binding) {
        return template_candidates;
    }

    append_unique_function_template_candidate(
        template_candidates,
        template_binding->template_decl);
    for (const auto* decl : template_binding->template_overload_candidates) {
        append_unique_function_template_candidate(template_candidates, decl);
    }
    return template_candidates;
}

const FunctionTemplateDecl* function_template_primary_for_symbol(
    const std::shared_ptr<Symbol>& symbol) {
    const auto* specialization_info =
        symbol ? get_symbol_function_template_specialization(symbol.get()) : nullptr;
    const auto* primary_template =
        specialization_info ? specialization_info->primary_template : nullptr;
    if (const auto* canonical = get_template_decl_canonical_decl(primary_template)) {
        if (auto* canonical_function_template =
                dyn_cast<FunctionTemplateDecl>(
                    const_cast<TemplateDecl*>(canonical))) {
            return canonical_function_template;
        }
    }
    return primary_template;
}

bool overload_symbols_refer_to_same_candidate(
    const std::shared_ptr<Symbol>& lhs,
    const std::shared_ptr<Symbol>& rhs) {
    if (!lhs || !rhs) {
        return false;
    }
    if (lhs == rhs) {
        return true;
    }
    const auto* lhs_template = function_template_primary_for_symbol(lhs);
    const auto* rhs_template = function_template_primary_for_symbol(rhs);
    return lhs_template &&
           rhs_template &&
           template_decls_share_lookup_identity(lhs_template, rhs_template);
}

const DeclContext* canonical_adl_decl_context(const DeclContext* context) {
    if (!context) {
        return nullptr;
    }
    return context->primary_context() ? context->primary_context() : context;
}

bool binding_references_decl(const DeclBinding& binding, const Decl* decl) {
    if (!decl) {
        return false;
    }
    if (binding.ast_decl == decl || binding.template_decl == decl) {
        return true;
    }
    return std::find(
               binding.template_overload_candidates.begin(),
               binding.template_overload_candidates.end(),
               decl) != binding.template_overload_candidates.end();
}

const DeclContext* find_decl_context_for_decl(const DeclContext* root,
                                              const Decl* decl) {
    if (!root || !decl) {
        return nullptr;
    }
    root = canonical_adl_decl_context(root);
    if (!root) {
        return nullptr;
    }
    if (root->owner_decl() == decl) {
        return root;
    }
    for (const auto& binding : root->declarations()) {
        if (binding_references_decl(binding, decl)) {
            return root;
        }
    }
    for (const auto& child : root->lexical_children()) {
        if (const auto* found = find_decl_context_for_decl(child.get(), decl)) {
            return found;
        }
    }
    return nullptr;
}

const DeclContext* enclosing_non_inline_namespace_context(
    const DeclContext* context) {
    for (const DeclContext* current = canonical_adl_decl_context(context);
         current;
         current = current->semantic_parent()) {
        current = canonical_adl_decl_context(current);
        if (!current) {
            return nullptr;
        }
        if (current->kind() != DeclContextKind::Namespace &&
            current->kind() != DeclContextKind::TranslationUnit) {
            continue;
        }
        while (current &&
               current->kind() == DeclContextKind::Namespace &&
               current->is_inline_namespace()) {
            current = current->inline_enclosing_namespace()
                          ? current->inline_enclosing_namespace()
                          : current->semantic_parent();
            current = canonical_adl_decl_context(current);
        }
        return current;
    }
    return nullptr;
}

struct AdlAssociatedEntities {
    std::vector<const ObjectDecl*> records;
    std::vector<const DeclContext*> namespaces;
    std::unordered_set<const ObjectDecl*> seen_records;
    std::unordered_set<const DeclContext*> seen_namespaces;
    std::unordered_set<const CType*> active_types;

    void append_namespace(const DeclContext* context) {
        context = canonical_adl_decl_context(context);
        if (!context || seen_namespaces.contains(context)) {
            return;
        }
        seen_namespaces.insert(context);
        namespaces.push_back(context);
    }

    void append_record(const ObjectDecl* record_decl) {
        record_decl = canonical_record_decl(record_decl);
        if (!record_decl || seen_records.contains(record_decl)) {
            return;
        }
        seen_records.insert(record_decl);
        records.push_back(record_decl);
    }
};

struct AdlActiveTypeGuard {
    AdlAssociatedEntities& entities;
    const CType* active = nullptr;
    bool inserted = false;

    AdlActiveTypeGuard(AdlAssociatedEntities& entities, const CType* active)
        : entities(entities), active(active) {
        inserted = active && entities.active_types.insert(active).second;
    }

    ~AdlActiveTypeGuard() {
        if (inserted) {
            entities.active_types.erase(active);
        }
    }
};

void collect_adl_associated_entities_for_type(
    QualType type,
    const ASTContext* ast_ctx,
    const DeclContext* translation_unit_context,
    AdlAssociatedEntities& entities);

void append_associated_namespace_for_decl(
    const Decl* decl,
    const DeclContext* translation_unit_context,
    AdlAssociatedEntities& entities) {
    const auto* decl_context =
        find_decl_context_for_decl(translation_unit_context, decl);
    entities.append_namespace(enclosing_non_inline_namespace_context(decl_context));
}

void collect_adl_associated_entities_for_template_arguments(
    const std::vector<TemplateArgument>& arguments,
    const ASTContext* ast_ctx,
    const DeclContext* translation_unit_context,
    AdlAssociatedEntities& entities) {
    for (const auto& argument : arguments) {
        if (argument.expands_parameter_pack) {
            continue;
        }
        switch (argument.kind) {
            case TemplateArgumentKind::Type:
                collect_adl_associated_entities_for_type(
                    argument.type,
                    ast_ctx,
                    translation_unit_context,
                    entities);
                break;
            case TemplateArgumentKind::Template:
                if (!argument.is_dependent && argument.template_decl) {
                    append_associated_namespace_for_decl(
                        argument.template_decl,
                        translation_unit_context,
                        entities);
                }
                break;
            case TemplateArgumentKind::Value:
                break;
        }
    }
}

void collect_adl_associated_entities_for_record(
    const ObjectDecl* record_decl,
    const ASTContext* ast_ctx,
    const DeclContext* translation_unit_context,
    AdlAssociatedEntities& entities) {
    record_decl = canonical_record_decl(record_decl);
    if (!record_decl) {
        return;
    }
    entities.append_record(record_decl);
    append_associated_namespace_for_decl(
        record_decl,
        translation_unit_context,
        entities);

    const auto* state = record_semantics_cache_lookup(record_decl, ast_ctx);
    if (!state || state->is_incomplete) {
        return;
    }
    for (const auto& base : state->bases) {
        collect_adl_associated_entities_for_record(
            base.record_decl,
            ast_ctx,
            translation_unit_context,
            entities);
    }
    for (const auto& base : state->virtual_bases) {
        collect_adl_associated_entities_for_record(
            base.record_decl,
            ast_ctx,
            translation_unit_context,
            entities);
    }
}

void collect_adl_associated_entities_for_type(
    QualType type,
    const ASTContext* ast_ctx,
    const DeclContext* translation_unit_context,
    AdlAssociatedEntities& entities) {
    if (!type) {
        return;
    }

    QualType no_ref = remove_reference(type, ast_ctx);
    if (!no_ref) {
        no_ref = type;
    }
    auto raw = no_ref.get_shared().get();
    AdlActiveTypeGuard type_guard(entities, raw);
    if (raw && !type_guard.inserted) {
        return;
    }

    if (auto specialization =
            no_ref.as_shared<TemplateSpecializationType>()) {
        append_associated_namespace_for_decl(
            specialization->primary_template,
            translation_unit_context,
            entities);
        collect_adl_associated_entities_for_template_arguments(
            specialization->arguments,
            ast_ctx,
            translation_unit_context,
            entities);
    }

    QualType semantic_type = desugar_type(no_ref, ast_ctx);
    if (!semantic_type) {
        return;
    }

    if (auto object_type = semantic_type.as_shared<ObjectType>()) {
        if (const auto* primary_template =
                object_type->get_primary_class_template()) {
            append_associated_namespace_for_decl(
                primary_template,
                translation_unit_context,
                entities);
            collect_adl_associated_entities_for_template_arguments(
                object_type->get_template_specialization_arguments(),
                ast_ctx,
                translation_unit_context,
                entities);
        }
        collect_adl_associated_entities_for_record(
            dyn_cast<ObjectDecl>(object_type->get_decl()),
            ast_ctx,
            translation_unit_context,
            entities);
        return;
    }

    if (auto enum_type = semantic_type.as_shared<EnumType>()) {
        append_associated_namespace_for_decl(
            enum_type->get_decl(),
            translation_unit_context,
            entities);
        return;
    }

    if (auto pointer_type = semantic_type.as_shared<PointerType>()) {
        collect_adl_associated_entities_for_type(
            pointer_type->pointed_type,
            ast_ctx,
            translation_unit_context,
            entities);
        return;
    }

    if (auto block_pointer = semantic_type.as_shared<BlockPointerType>()) {
        collect_adl_associated_entities_for_type(
            block_pointer->pointed_type,
            ast_ctx,
            translation_unit_context,
            entities);
        return;
    }

    if (auto array_type = semantic_type.as_shared<ArrayType>()) {
        collect_adl_associated_entities_for_type(
            array_type->element_type,
            ast_ctx,
            translation_unit_context,
            entities);
        return;
    }

    if (auto member_pointer = semantic_type.as_shared<MemberPointerType>()) {
        collect_adl_associated_entities_for_type(
            member_pointer->class_type,
            ast_ctx,
            translation_unit_context,
            entities);
        collect_adl_associated_entities_for_type(
            member_pointer->member_type,
            ast_ctx,
            translation_unit_context,
            entities);
        return;
    }

    if (auto function_type = semantic_type.as_shared<FunctionType>()) {
        collect_adl_associated_entities_for_type(
            function_type->ret_type,
            ast_ctx,
            translation_unit_context,
            entities);
        for (const auto& parameter : function_type->parameters) {
            collect_adl_associated_entities_for_type(
                parameter,
                ast_ctx,
                translation_unit_context,
                entities);
        }
    }
}

AdlAssociatedEntities collect_adl_associated_entities(
    const std::vector<Expr*>& associated_args,
    const ASTContext* ast_ctx,
    const DeclContext* translation_unit_context) {
    AdlAssociatedEntities entities;
    for (auto* arg : associated_args) {
        if (!arg) {
            continue;
        }
        collect_adl_associated_entities_for_type(
            arg->get_type(),
            ast_ctx,
            translation_unit_context,
            entities);
    }
    return entities;
}
} // namespace

size_t Collect::OverloadConversionMemoKeyHash::operator()(
    const OverloadConversionMemoKey& key) const {
    size_t seed = 0;
    seed = hash_combine(seed, std::hash<const Expr*>{}(key.arg));
    seed = hash_combine(seed, std::hash<const CType*>{}(key.to_type));
    seed = hash_combine(seed, std::hash<uint8_t>{}(key.to_qualifiers));
    seed = hash_combine(seed, std::hash<bool>{}(key.allow_user_defined));
    return seed;
}

Collect::ImplicitConversionSequence
Collect::build_cpp_overload_conversion_sequence_cached(
    Expr* arg,
    QualType to,
    bool allow_user_defined,
    OverloadConversionMemoCache* conversion_cache) {
    if (!conversion_cache || !arg || !to) {
        return build_cpp_overload_conversion_sequence(
            arg, to, allow_user_defined);
    }
    OverloadConversionMemoKey key;
    key.arg = arg;
    key.to_type = to.get_shared().get();
    key.to_qualifiers = to.get_qualifiers();
    key.allow_user_defined = allow_user_defined;
    auto it = conversion_cache->find(key);
    if (it != conversion_cache->end()) {
        bump_overload_conversion_cache_hit();
        return it->second;
    }
    bump_overload_conversion_cache_miss();
    auto seq = build_cpp_overload_conversion_sequence(
        arg, to, allow_user_defined);
    conversion_cache->emplace(key, seq);
    return seq;
}

std::unique_ptr<Expr> Collect::append_member_overload_candidates(
    const ObjectType* record_type,
    std::string_view member_name,
    Expr* access_expr,
    OverloadImplicitObjectArgKind static_member_arg_kind,
    std::vector<OverloadCallCandidate>& candidates_out,
    bool& had_member_match_out,
    bool& saw_private_member_out,
    bool& saw_protected_member_out,
    SrcLoc loc) const {

    had_member_match_out = false;
    if (!record_type) {
        return nullptr;
    }

    auto methods = find_record_methods(record_type, std::string(member_name));
    if (methods.empty()) {
        return nullptr;
    }

    had_member_match_out = true;
    const ObjectDecl* object_record_decl = record_decl_from_record_type(record_type);
    const ObjectDecl* access_context_decl =
        lang_opts_.is_cxx_mode()
            ? current_access_context_record_decl(
                  session_.func_state_.current_function_is_cpp_member,
                  session_.func_state_.current_function_cpp_this_type,
                  session_.func_state_.current_function_cpp_friend_access_type,
                  session_.current_cpp_record_lookup_type_,
                  ast_ctx_.get(),
                  session_.func_state_.current_function_cpp_access_context_type)
            : nullptr;
    QualType access_context_type =
        lang_opts_.is_cxx_mode()
            ? current_access_context_record_type(
                  session_.func_state_.current_function_is_cpp_member,
                  session_.func_state_.current_function_cpp_this_type,
                  session_.func_state_.current_function_cpp_friend_access_type,
                  session_.current_cpp_record_lookup_type_,
                  ast_ctx_.get(),
                  session_.func_state_.current_function_cpp_access_context_type)
            : QualType(nullptr);

    candidates_out.reserve(candidates_out.size() + methods.size());
    for (const auto& method_match : methods) {
        const auto* method = method_match.method;
        if (!method) {
            continue;
        }
        if (lang_opts_.is_cxx_mode()) {
            if (method->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_match.owner_record_decl,
                        access_context_decl,
                        ast_ctx_.get(),
                        access_context_type)) {
                    saw_private_member_out = true;
                    continue;
                }
            }
            if (method->declared_access == RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_match.owner_record_decl,
                    access_context_decl,
                    object_record_decl,
                    method->is_static,
                    ast_ctx_.get(),
                    access_context_type);
                if (!protected_ok) {
                    saw_protected_member_out = true;
                    continue;
                }
            }
        }
        if (!method->symbol) {
            report_error(
                "internal error: unresolved member function symbol '" +
                    std::string(member_name) + "'",
                loc);
            return collect_make<ErrorExpr>(
                "unresolved member function symbol", loc);
        }
        repair_member_candidate_symbol_owner_type(
            *method,
            method_match.owner_record_decl,
            ast_ctx_.get());

        OverloadCallCandidate call_candidate;
        call_candidate.symbol = method->symbol;
        call_candidate.implicit_object_arg_kind = method->is_static
            ? static_member_arg_kind
            : OverloadImplicitObjectArgKind::MemberObject;
        candidates_out.push_back(std::move(call_candidate));
    }

    return nullptr;
}

std::unique_ptr<Expr> Collect::append_member_template_overload_candidates(
    const ObjectType* record_type,
    std::string_view member_name,
    Expr* access_expr,
    bool access_expr_is_arrow,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    std::vector<OverloadCallCandidate>& candidates_out,
    bool& had_member_match_out,
    bool& had_template_member_match_out,
    bool& saw_private_member_out,
    bool& saw_protected_member_out,
    bool& saw_template_instantiation_out,
    SrcLoc loc) {
    had_template_member_match_out = false;
    if (!record_type) {
        return nullptr;
    }

    auto method_templates =
        find_record_method_templates(record_type, std::string(member_name));
    if (method_templates.empty()) {
        return nullptr;
    }

    had_member_match_out = true;
    had_template_member_match_out = true;
    const ObjectDecl* object_record_decl = record_decl_from_record_type(record_type);
    const ObjectDecl* access_context_decl =
        lang_opts_.is_cxx_mode()
            ? current_access_context_record_decl(
                  session_.func_state_.current_function_is_cpp_member,
                  session_.func_state_.current_function_cpp_this_type,
                  session_.func_state_.current_function_cpp_friend_access_type,
                  session_.current_cpp_record_lookup_type_,
                  ast_ctx_.get(),
                  session_.func_state_.current_function_cpp_access_context_type)
            : nullptr;
    QualType access_context_type =
        lang_opts_.is_cxx_mode()
            ? current_access_context_record_type(
                  session_.func_state_.current_function_is_cpp_member,
                  session_.func_state_.current_function_cpp_this_type,
                  session_.func_state_.current_function_cpp_friend_access_type,
                  session_.current_cpp_record_lookup_type_,
                  ast_ctx_.get(),
                  session_.func_state_.current_function_cpp_access_context_type)
            : QualType(nullptr);

    for (const auto& method_template_match : method_templates) {
        const auto* method_template = method_template_match.method_template;
        const auto* function_template =
            method_template ? method_template->decl : nullptr;
        if (!method_template || !function_template) {
            continue;
        }
        if (lang_opts_.is_cxx_mode()) {
            if (method_template->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_template_match.owner_record_decl,
                        access_context_decl,
                        ast_ctx_.get(),
                        access_context_type)) {
                    saw_private_member_out = true;
                    continue;
                }
            }
            if (method_template->declared_access ==
                RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_template_match.owner_record_decl,
                    access_context_decl,
                    object_record_decl,
                    method_template->is_static,
                    ast_ctx_.get(),
                    access_context_type);
                if (!protected_ok) {
                    saw_protected_member_out = true;
                    continue;
                }
            }
        }

        std::unique_ptr<Expr> deduction_object_arg;
        std::vector<Expr*> deduction_args;
        deduction_args.reserve(
            explicit_args.size() + (method_template->is_static ? 0u : 1u));
        if (!method_template->is_static) {
            std::string clone_error;
            auto cloned_access_expr =
                clone_expr_tree(access_expr, ast_ctx_.get(), &clone_error);
            if (access_expr && !cloned_access_expr) {
                std::string message = clone_error.empty()
                    ? "member template implicit object argument is not clonable"
                    : "member template implicit object argument is not clonable: " +
                        clone_error;
                report_error(message, loc);
                return collect_make<ErrorExpr>(
                    "unsupported member template implicit object argument",
                    loc);
            }
            deduction_object_arg = build_overload_implicit_object_arg(
                OverloadImplicitObjectArgKind::MemberObject,
                std::move(cloned_access_expr),
                access_expr_is_arrow,
                loc);
            if (!deduction_object_arg) {
                report_error(
                    "failed to build member template implicit object argument",
                    loc);
                return collect_make<ErrorExpr>(
                    "invalid member template implicit object argument",
                    loc);
            }
            if (isa<ErrorExpr>(deduction_object_arg.get())) {
                return std::move(deduction_object_arg);
            }
            deduction_args.push_back(deduction_object_arg.get());
        }
        for (const auto& arg : explicit_args) {
            deduction_args.push_back(arg.get());
        }

        std::shared_ptr<Symbol> specialization_symbol = nullptr;
        if (!probe_function_template_call_specialization(
                function_template,
                deduction_args,
                loc,
                specialization_symbol)) {
            continue;
        }
        saw_template_instantiation_out = true;

        OverloadCallCandidate candidate;
        candidate.symbol = std::move(specialization_symbol);
        candidate.implicit_object_arg_kind = method_template->is_static
            ? OverloadImplicitObjectArgKind::None
            : OverloadImplicitObjectArgKind::MemberObject;
        candidates_out.push_back(std::move(candidate));
    }

    return nullptr;
}


void Collect::append_unqualified_overload_candidates(
    std::string_view function_name,
    OverloadImplicitObjectArgKind implicit_arg_kind,
    std::vector<OverloadCallCandidate>& candidates_out) {

    if (!session_.current_scope_) {
        return;
    }
    auto function_candidates = LookupEngine::lookup_unqualified_function_candidates(
        std::string(function_name), session_.current_scope_, true);
    candidates_out.reserve(candidates_out.size() + function_candidates.size());
    for (const auto& fn_sym : function_candidates) {
        if (fn_sym && get_symbol_owner_record_type(fn_sym.get())) {
            continue;
        }
        OverloadCallCandidate call_candidate;
        call_candidate.symbol = fn_sym;
        call_candidate.implicit_object_arg_kind = implicit_arg_kind;
        candidates_out.push_back(std::move(call_candidate));
    }
}

void Collect::append_adl_friend_overload_candidates(
    std::string_view function_name,
    OverloadImplicitObjectArgKind implicit_arg_kind,
    const std::vector<Expr*>& associated_args,
    std::vector<OverloadCallCandidate>& candidates_out,
    SrcLoc loc) {

    if (!lang_opts_.is_cxx_mode()) {
        return;
    }

    auto entities = collect_adl_associated_entities(
        associated_args,
        ast_ctx_.get(),
        get_translation_unit_decl_context().get());
    if (entities.records.empty()) {
        return;
    }

    std::unordered_set<const Symbol*> existing_symbols;
    for (const auto& candidate : candidates_out) {
        if (candidate.symbol) {
            existing_symbols.insert(candidate.symbol.get());
        }
    }
    auto candidate_already_present =
        [&](const std::shared_ptr<Symbol>& symbol) {
        for (const auto& candidate : candidates_out) {
            if (overload_symbols_refer_to_same_candidate(
                    candidate.symbol,
                    symbol)) {
                return true;
            }
        }
        return false;
    };
    for (const auto* record_decl : entities.records) {
        const auto* state =
            record_semantics_cache_lookup(record_decl, ast_ctx_.get());
        if (!state) {
            continue;
        }
        for (const auto& friend_function : state->friend_functions) {
            if (friend_function.name != function_name ||
                !friend_function.symbol ||
                friend_function.symbol->kind != SymbolKind::FUNCTION ||
                existing_symbols.contains(friend_function.symbol.get())) {
                continue;
            }
            OverloadCallCandidate call_candidate;
            call_candidate.symbol = friend_function.symbol;
            call_candidate.implicit_object_arg_kind = implicit_arg_kind;
            candidates_out.push_back(std::move(call_candidate));
            existing_symbols.insert(friend_function.symbol.get());
        }
        for (const auto& friend_function : state->friend_functions) {
            if (friend_function.name != function_name ||
                !friend_function.function_template) {
                continue;
            }
            std::shared_ptr<Symbol> specialization_symbol = nullptr;
            if (!probe_function_template_call_specialization(
                    friend_function.function_template,
                    associated_args,
                    loc,
                    specialization_symbol)) {
                continue;
            }
            if (!specialization_symbol ||
                existing_symbols.contains(specialization_symbol.get()) ||
                candidate_already_present(specialization_symbol)) {
                continue;
            }
            OverloadCallCandidate call_candidate;
            call_candidate.symbol = std::move(specialization_symbol);
            call_candidate.implicit_object_arg_kind = implicit_arg_kind;
            existing_symbols.insert(call_candidate.symbol.get());
            candidates_out.push_back(std::move(call_candidate));
        }
    }
}

void Collect::append_adl_overload_candidates(
    std::string_view function_name,
    Expr* implicit_object_arg,
    OverloadImplicitObjectArgKind implicit_arg_kind,
    const std::vector<Expr*>& explicit_args,
    std::vector<OverloadCallCandidate>& candidates_out,
    SrcLoc loc) {

    if (!lang_opts_.is_cxx_mode()) {
        return;
    }

    std::vector<Expr*> associated_args;
    associated_args.reserve(
        explicit_args.size() +
        (implicit_arg_kind == OverloadImplicitObjectArgKind::None ? 0u : 1u));
    if (implicit_arg_kind != OverloadImplicitObjectArgKind::None &&
        implicit_object_arg) {
        associated_args.push_back(implicit_object_arg);
    }
    for (Expr* arg : explicit_args) {
        associated_args.push_back(arg);
    }

    auto entities = collect_adl_associated_entities(
        associated_args,
        ast_ctx_.get(),
        get_translation_unit_decl_context().get());
    if (entities.namespaces.empty() && entities.records.empty()) {
        return;
    }

    std::unordered_set<const Symbol*> existing_symbols;
    for (const auto& candidate : candidates_out) {
        if (candidate.symbol) {
            existing_symbols.insert(candidate.symbol.get());
        }
    }

    auto candidate_already_present =
        [&](const std::shared_ptr<Symbol>& symbol) {
        for (const auto& candidate : candidates_out) {
            if (overload_symbols_refer_to_same_candidate(
                    candidate.symbol,
                    symbol)) {
                return true;
            }
        }
        return false;
    };

    auto append_symbol_candidate =
        [&](const std::shared_ptr<Symbol>& symbol) {
        if (!symbol ||
            symbol->kind != SymbolKind::FUNCTION ||
            symbol->is_hidden_friend ||
            get_symbol_owner_record_type(symbol.get()) ||
            existing_symbols.contains(symbol.get()) ||
            candidate_already_present(symbol)) {
            return;
        }
        OverloadCallCandidate candidate;
        candidate.symbol = symbol;
        candidate.implicit_object_arg_kind = implicit_arg_kind;
        candidates_out.push_back(std::move(candidate));
        existing_symbols.insert(symbol.get());
    };

    std::vector<const FunctionTemplateDecl*> template_candidates;
    auto append_template_candidates_from_binding =
        [&](const DeclBinding* binding) {
        if (!binding) {
            return;
        }
        append_unique_function_template_candidate(
            template_candidates,
            binding->template_decl);
        for (const auto* decl : binding->template_overload_candidates) {
            append_unique_function_template_candidate(
                template_candidates,
                decl);
        }
    };

    for (const auto* namespace_context : entities.namespaces) {
        auto binding_matches =
            LookupEngine::lookup_qualified_ordinary_bindings(
                std::string(function_name),
                namespace_context,
                nullptr,
                LookupEngine::OrdinaryFilter::Any,
                LookupEngine::NamespaceReachability::InlineVisible);
        for (const auto& match : binding_matches) {
            const auto* binding = match.binding;
            if (!binding) {
                continue;
            }
            append_symbol_candidate(binding->symbol);
            for (const auto& overload : binding->overload_candidates) {
                append_symbol_candidate(overload);
            }
            append_template_candidates_from_binding(binding);
        }
    }

    std::vector<Expr*> deduction_args;
    deduction_args.reserve(associated_args.size());
    if (implicit_arg_kind != OverloadImplicitObjectArgKind::None) {
        deduction_args.push_back(implicit_object_arg);
    }
    for (Expr* arg : explicit_args) {
        deduction_args.push_back(arg);
    }

    for (const auto* function_template : template_candidates) {
        if (!function_template) {
            continue;
        }

        std::shared_ptr<Symbol> specialization_symbol = nullptr;
        if (!probe_function_template_call_specialization(
                function_template,
                deduction_args,
                loc,
                specialization_symbol)) {
            continue;
        }
        if (!specialization_symbol ||
            existing_symbols.contains(specialization_symbol.get()) ||
            candidate_already_present(specialization_symbol)) {
            continue;
        }

        OverloadCallCandidate candidate;
        candidate.symbol = std::move(specialization_symbol);
        candidate.implicit_object_arg_kind = implicit_arg_kind;
        existing_symbols.insert(candidate.symbol.get());
        candidates_out.push_back(std::move(candidate));
    }

    for (const auto* record_decl : entities.records) {
        const auto* state =
            record_semantics_cache_lookup(record_decl, ast_ctx_.get());
        if (!state) {
            continue;
        }
        for (const auto& friend_function : state->friend_functions) {
            if (friend_function.name != function_name ||
                !friend_function.symbol ||
                friend_function.symbol->kind != SymbolKind::FUNCTION ||
                existing_symbols.contains(friend_function.symbol.get())) {
                continue;
            }
            OverloadCallCandidate candidate;
            candidate.symbol = friend_function.symbol;
            candidate.implicit_object_arg_kind = implicit_arg_kind;
            candidates_out.push_back(std::move(candidate));
            existing_symbols.insert(friend_function.symbol.get());
        }
        for (const auto& friend_function : state->friend_functions) {
            if (friend_function.name != function_name ||
                !friend_function.function_template) {
                continue;
            }
            std::shared_ptr<Symbol> specialization_symbol = nullptr;
            if (!probe_function_template_call_specialization(
                    friend_function.function_template,
                    deduction_args,
                    loc,
                    specialization_symbol)) {
                continue;
            }
            if (!specialization_symbol ||
                existing_symbols.contains(specialization_symbol.get()) ||
                candidate_already_present(specialization_symbol)) {
                continue;
            }
            OverloadCallCandidate candidate;
            candidate.symbol = std::move(specialization_symbol);
            candidate.implicit_object_arg_kind = implicit_arg_kind;
            existing_symbols.insert(candidate.symbol.get());
            candidates_out.push_back(std::move(candidate));
        }
    }
}

void Collect::append_unqualified_function_template_overload_candidates(
    std::string_view function_name,
    Expr* implicit_object_arg,
    OverloadImplicitObjectArgKind implicit_arg_kind,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    std::vector<OverloadCallCandidate>& candidates_out,
    SrcLoc loc) {
    append_unqualified_function_template_overload_candidates(
        function_name,
        implicit_object_arg,
        implicit_arg_kind,
        make_raw_explicit_args(explicit_args),
        candidates_out,
        loc);
}

void Collect::append_unqualified_function_template_overload_candidates(
    std::string_view function_name,
    Expr* implicit_object_arg,
    OverloadImplicitObjectArgKind implicit_arg_kind,
    const std::vector<Expr*>& explicit_args,
    std::vector<OverloadCallCandidate>& candidates_out,
    SrcLoc loc) {
    if (!session_.current_scope_) {
        return;
    }
    if (implicit_arg_kind != OverloadImplicitObjectArgKind::None &&
        !implicit_object_arg) {
        return;
    }

    auto template_candidates =
        lookup_unqualified_function_templates(function_name, session_.current_scope_);
    if (template_candidates.empty()) {
        return;
    }

    std::vector<Expr*> deduction_args;
    deduction_args.reserve(
        explicit_args.size() +
        (implicit_arg_kind == OverloadImplicitObjectArgKind::None ? 0u : 1u));
    if (implicit_arg_kind != OverloadImplicitObjectArgKind::None) {
        deduction_args.push_back(implicit_object_arg);
    }
    for (Expr* arg : explicit_args) {
        deduction_args.push_back(arg);
    }

    candidates_out.reserve(candidates_out.size() + template_candidates.size());
    for (const auto* function_template : template_candidates) {
        if (!function_template) {
            continue;
        }

        std::shared_ptr<Symbol> specialization_symbol = nullptr;
        if (!probe_function_template_call_specialization(
                function_template,
                deduction_args,
                loc,
                specialization_symbol)) {
            continue;
        }
        bool duplicate = false;
        for (const auto& existing : candidates_out) {
            if (overload_symbols_refer_to_same_candidate(
                    existing.symbol,
                    specialization_symbol)) {
                duplicate = true;
                break;
            }
        }
        if (duplicate) {
            continue;
        }

        OverloadCallCandidate candidate;
        candidate.symbol = std::move(specialization_symbol);
        candidate.implicit_object_arg_kind = implicit_arg_kind;
        candidates_out.push_back(std::move(candidate));
    }
}

bool Collect::probe_function_template_call_specialization(
    const FunctionTemplateDecl* function_template,
    const std::vector<Expr*>& call_args,
    SrcLoc loc,
    std::shared_ptr<Symbol>& specialization_symbol_out,
    const TemplateArgumentBindings* initial_bindings,
    std::vector<TemplateArgument>* specialization_arguments_out) {

    specialization_symbol_out = nullptr;
    if (specialization_arguments_out) {
        specialization_arguments_out->clear();
    }
    if (!function_template) {
        return false;
    }

    auto try_probe =
        [&](std::vector<TemplateArgument>& specialization_arguments) {
            if (!deduce_function_template_call_arguments(
                    function_template,
                    call_args,
                    specialization_arguments,
                    initial_bindings)) {
                return false;
            }
            if (!are_template_constraints_satisfied(
                    function_template,
                    specialization_arguments,
                    loc)) {
                return false;
            }

            auto* specialization_decl =
                instantiate_function_template_specialization(
                    function_template,
                    specialization_arguments,
                    loc,
                    &specialization_symbol_out,
                    /*instantiate_definition=*/false);
            return specialization_decl && specialization_symbol_out;
        };

    std::vector<TemplateArgument> specialization_arguments;
    // technically we should always have a diag_engine
    if (!diag_engine_) {
        if (!try_probe(specialization_arguments)) {
            specialization_symbol_out = nullptr;
            return false;
        }
        if (specialization_arguments_out) {
            *specialization_arguments_out = std::move(specialization_arguments);
        }
        return true;
    }

    auto checkpoint = diag_engine_->checkpoint();
    bool success = try_probe(specialization_arguments);
    bool probe_reported_diagnostic =
        diag_engine_->error_count > checkpoint.error_count ||
        diag_engine_->diagnostics.size() > checkpoint.diagnostics_size;
    diag_engine_->restore(checkpoint);
    if (!success || probe_reported_diagnostic) {
        specialization_symbol_out = nullptr;
        return false;
    }

    if (specialization_arguments_out) {
        *specialization_arguments_out = std::move(specialization_arguments);
    }
    return true;
}

std::unique_ptr<Expr> Collect::append_explicit_function_template_overload_candidate(
    const FunctionTemplateDecl* function_template,
    const std::vector<TemplateArgument>& explicit_template_args,
    const std::function<bool(
        std::vector<Expr*>&,
        std::unique_ptr<Expr>&)>& build_deduction_args,
    OverloadImplicitObjectArgKind implicit_object_arg_kind,
    std::vector<OverloadCallCandidate>& candidates_out,
    SrcLoc loc,
    ExplicitTemplateCandidateProbeResult& result_out,
    std::string* binding_error_out) {

    result_out = ExplicitTemplateCandidateProbeResult::InvalidTemplate;
    if (binding_error_out) {
        binding_error_out->clear();
    }
    if (!function_template) {
        return nullptr;
    }

    TemplateArgumentBindings explicit_bindings;
    std::string binding_error;
    if (!bind_explicit_template_arguments_prefix_to_parameters(
            function_template->parameters,
            explicit_template_args,
            explicit_bindings,
            &binding_error)) {
        result_out =
            ExplicitTemplateCandidateProbeResult::ExplicitArgumentsRejected;
        if (binding_error_out) {
            *binding_error_out = std::move(binding_error);
        }
        return nullptr;
    }

    std::vector<Expr*> deduction_args;
    std::unique_ptr<Expr> build_error;
    if (!build_deduction_args(deduction_args, build_error)) {
        result_out =
            ExplicitTemplateCandidateProbeResult::DeductionArgumentsUnavailable;
        return build_error;
    }

    std::shared_ptr<Symbol> specialization_symbol = nullptr;
    if (!probe_function_template_call_specialization(
            function_template,
            deduction_args,
            loc,
            specialization_symbol,
            &explicit_bindings)) {
        result_out =
            ExplicitTemplateCandidateProbeResult::SpecializationRejected;
        return nullptr;
    }

    OverloadCallCandidate candidate;
    candidate.symbol = std::move(specialization_symbol);
    candidate.implicit_object_arg_kind = implicit_object_arg_kind;
    candidates_out.push_back(std::move(candidate));
    result_out = ExplicitTemplateCandidateProbeResult::CandidateAdded;
    return nullptr;
}


std::unique_ptr<Expr> Collect::select_overload_candidate(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    std::shared_ptr<Symbol>& selected_symbol_out,
    OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) {
    OverloadCandidateSelection selection;
    if (auto error = select_overload_candidate(
            callee_name,
            candidates,
            explicit_args,
            implicit_object_arg,
            loc,
            selection)) {
        return error;
    }
    selected_symbol_out = selection.symbol;
    selected_implicit_object_arg_kind_out =
        selection.implicit_object_arg_kind;
    return nullptr;
}

std::unique_ptr<Expr> Collect::select_overload_candidate(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    OverloadCandidateSelection& selection_out) {
    return select_overload_candidate(
        callee_name,
        candidates,
        make_raw_explicit_args(explicit_args),
        implicit_object_arg,
        loc,
        selection_out);
}

std::unique_ptr<Expr> Collect::select_overload_candidate(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<Expr*>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    std::shared_ptr<Symbol>& selected_symbol_out,
    OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) {
    OverloadCandidateSelection selection;
    if (auto error = select_overload_candidate(
            callee_name,
            candidates,
            explicit_args,
            implicit_object_arg,
            loc,
            selection)) {
        return error;
    }
    selected_symbol_out = selection.symbol;
    selected_implicit_object_arg_kind_out =
        selection.implicit_object_arg_kind;
    return nullptr;
}

std::unique_ptr<Expr> Collect::select_overload_candidate(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<Expr*>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    OverloadCandidateSelection& selection_out) {

    selection_out = OverloadCandidateSelection{};
    if (candidates.empty()) {
        return nullptr;
    }
    if (candidates.size() == 1 && !lang_opts_.is_cxx_mode()) {
        selection_out.symbol = candidates.front().symbol;
        selection_out.implicit_object_arg_kind =
            candidates.front().implicit_object_arg_kind;
        selection_out.operator_rewrite_kind =
            candidates.front().operator_rewrite_kind;
        selection_out.is_synthesized_reversed_operator_candidate =
            candidates.front().is_synthesized_reversed_operator_candidate;
        return nullptr;
    }
    return resolve_overloaded_call_candidates(
        callee_name,
        candidates,
        explicit_args,
        implicit_object_arg,
        loc,
        selection_out);
}


std::unique_ptr<Expr> Collect::report_inaccessible_member(
    std::string_view member_name,
    bool saw_private_member,
    bool saw_protected_member,
    SrcLoc loc) const {

    if (saw_protected_member) {
        report_error(
            "member '" + std::string(member_name) +
                "' is protected within this context",
            loc);
        return collect_make<ErrorExpr>(
            "inaccessible protected member function", loc);
    }
    if (saw_private_member) {
        report_error(
            "member '" + std::string(member_name) +
                "' is private within this context",
            loc);
        return collect_make<ErrorExpr>(
            "inaccessible private member function", loc);
    }
    return nullptr;
}


std::unique_ptr<Expr> Collect::make_hidden_overload_callee(
    std::shared_ptr<Symbol> selected_symbol,
    SrcLoc loc) const {

    const std::string* internal_call_name =
        ast_ctx_ ? ast_ctx_->intern_identifier("__aburi_overload_call")
                 : nullptr;
    if (internal_call_name) {
        return collect_make<VarRef>(internal_call_name, selected_symbol, loc);
    }
    return collect_make<VarRef>(std::move(selected_symbol), loc);
}

Collect::OverloadCandidateEval Collect::evaluate_conversion_constructor_candidate(
    const RecordSemanticState::Constructor& ctor,
    Expr* arg,
    QualType target_type,
    bool allow_explicit_constructors,
    OverloadConversionMemoCache* conversion_cache) {

    bump_overload_candidate_evaluations();
    OverloadCandidateEval eval;
    eval.candidate_kind = OverloadCandidateKind::ConversionConstructor;
    eval.symbol = ctor.symbol;
    eval.provenance = constructor_candidate_provenance(ctor);
    eval.constructor = &ctor;
    eval.function_type =
        desugar_type(ctor.type, ast_ctx_.get()).as_shared<FunctionType>();
    if (!eval.function_type || !ctor.symbol) {
        eval.failure.kind = OverloadFailureKind::InvalidCandidateState;
        eval.failure.note = "conversion constructor is missing type or symbol";
        return eval;
    }

    CppConstructorUserParamInfo param_info =
        cpp_compute_constructor_user_param_info(ctor);
    eval.user_param_start = param_info.user_param_start;
    eval.max_user_param_count = param_info.max_user_param_count;
    eval.required_user_param_count = param_info.required_user_param_count;

    if (ctor.is_deleted) {
        eval.failure.kind = OverloadFailureKind::DeletedCandidate;
        eval.failure.note = "conversion constructor is deleted";
        return eval;
    }
    if (!allow_explicit_constructors && ctor.is_explicit) {
        eval.failure.kind = OverloadFailureKind::InaccessibleCandidate;
        eval.failure.note = "explicit conversion constructor is not allowed";
        return eval;
    }
    if (!cpp_access_allows_member(ctor.declared_access, false)) {
        eval.failure.kind = OverloadFailureKind::InaccessibleCandidate;
        eval.failure.note = "conversion constructor is not accessible";
        return eval;
    }

    constexpr size_t provided_arg_count = 1;
    if (provided_arg_count < eval.required_user_param_count) {
        eval.failure.kind = OverloadFailureKind::ArityTooFew;
        eval.failure.required_arg_count = eval.required_user_param_count;
        eval.failure.provided_arg_count = provided_arg_count;
        eval.failure.arity_is_minimum =
            eval.required_user_param_count != eval.max_user_param_count;
        return eval;
    }
    if (provided_arg_count > eval.max_user_param_count) {
        eval.failure.kind = OverloadFailureKind::ArityTooMany;
        eval.failure.required_arg_count = eval.max_user_param_count;
        eval.failure.provided_arg_count = provided_arg_count;
        return eval;
    }

    eval.viable = true;
    eval.conversions.reserve(provided_arg_count);
    size_t param_index = eval.user_param_start;
    if (param_index >= eval.function_type->parameters.size()) {
        eval.viable = false;
        eval.failure.kind = OverloadFailureKind::InvalidCandidateState;
        eval.failure.note = "conversion constructor parameter index out of range";
        return eval;
    }

    QualType param_type =
        decay_parameter_type(eval.function_type->parameters[param_index]);
    auto seq = build_cpp_overload_conversion_sequence_cached(
        arg,
        param_type,
        /*allow_user_defined=*/false,
        conversion_cache);
    eval.conversions.push_back(seq);
    if (!seq.viable) {
        eval.viable = false;
        eval.failure.kind = OverloadFailureKind::ArgumentConversionFailure;
        eval.failure.argument_index = 1;
        eval.failure.from = seq.from ? seq.from : (arg ? arg->get_type() : QualType());
        eval.failure.to = param_type;
        eval.failure.note = seq.note;
        return eval;
    }

    auto produced_expr = collect_make<CppConstructExpr>(
        ctor.symbol,
        std::vector<std::unique_ptr<Expr>>{},
        remove_reference(target_type, ast_ctx_.get()),
        false,
        arg ? arg->location : SrcLoc());
    auto final_seq = build_cpp_overload_conversion_sequence(
        produced_expr.get(),
        target_type,
        /*allow_user_defined=*/false);
    eval.conversions.push_back(final_seq);
    if (!final_seq.viable) {
        eval.viable = false;
        eval.failure.kind = OverloadFailureKind::ArgumentConversionFailure;
        eval.failure.argument_index = 2;
        eval.failure.from = produced_expr->get_type();
        eval.failure.to = target_type;
        eval.failure.note = final_seq.note;
    }

    return eval;
}

Collect::OverloadCandidateEval Collect::evaluate_conversion_function_candidate(
    const RecordSemanticState::Method& method,
    const ObjectDecl* owner_record_decl,
    Expr* arg,
    QualType target_type,
    bool allow_explicit_conversion_functions,
    OverloadConversionMemoCache* conversion_cache) {

    bump_overload_candidate_evaluations();
    OverloadCandidateEval eval;
    eval.candidate_kind = OverloadCandidateKind::ConversionFunction;
    eval.symbol = method.symbol;
    eval.provenance = OverloadCandidateProvenance::ConversionFunction;
    eval.conversion_function = &method;
    eval.owner_record_decl = owner_record_decl;
    eval.implicit_object_arg_kind = OverloadImplicitObjectArgKind::MemberObject;
    eval.function_type =
        desugar_type(method.type, ast_ctx_.get()).as_shared<FunctionType>();
    if (!eval.function_type || !method.symbol) {
        eval.failure.kind = OverloadFailureKind::InvalidCandidateState;
        eval.failure.note = "conversion function is missing type or symbol";
        return eval;
    }

    if (!method.is_conversion_function) {
        eval.failure.kind = OverloadFailureKind::InvalidCandidateState;
        eval.failure.note = "candidate is not a conversion function";
        return eval;
    }
    if (method.is_static) {
        eval.failure.kind = OverloadFailureKind::InvalidCandidateState;
        eval.failure.note = "conversion function must be non-static";
        return eval;
    }
    if (!allow_explicit_conversion_functions && method.is_explicit) {
        eval.failure.kind = OverloadFailureKind::InaccessibleCandidate;
        eval.failure.note = "explicit conversion function is not allowed";
        return eval;
    }

    auto source_record_type =
        remove_reference_and_desugar(arg ? arg->get_type() : QualType(), ast_ctx_.get())
            .as_shared<ObjectType>();
    const ObjectDecl* source_record_decl =
        source_record_type
            ? canonical_record_decl(dyn_cast<ObjectDecl>(source_record_type->get_decl()))
            : nullptr;
    const ObjectDecl* access_context_decl =
        lang_opts_.is_cxx_mode()
            ? current_access_context_record_decl(
                  session_.func_state_.current_function_is_cpp_member,
                  session_.func_state_.current_function_cpp_this_type,
                  session_.func_state_.current_function_cpp_friend_access_type,
                  session_.current_cpp_record_lookup_type_,
                  ast_ctx_.get(),
                  session_.func_state_.current_function_cpp_access_context_type)
            : nullptr;
    QualType access_context_type =
        lang_opts_.is_cxx_mode()
            ? current_access_context_record_type(
                  session_.func_state_.current_function_is_cpp_member,
                  session_.func_state_.current_function_cpp_this_type,
                  session_.func_state_.current_function_cpp_friend_access_type,
                  session_.current_cpp_record_lookup_type_,
                  ast_ctx_.get(),
                  session_.func_state_.current_function_cpp_access_context_type)
            : QualType(nullptr);
    if (lang_opts_.is_cxx_mode()) {
        if (method.declared_access == RecordMemberAccess::Private &&
            !can_access_private_member_in_context(
                owner_record_decl,
                access_context_decl,
                ast_ctx_.get(),
                access_context_type)) {
            eval.failure.kind = OverloadFailureKind::InaccessibleCandidate;
            eval.failure.note = "conversion function is not accessible";
            return eval;
        }
        if (method.declared_access == RecordMemberAccess::Protected &&
            !can_access_protected_member_in_context(
                owner_record_decl,
                access_context_decl,
                source_record_decl,
                false,
                ast_ctx_.get(),
                access_context_type)) {
            eval.failure.kind = OverloadFailureKind::InaccessibleCandidate;
            eval.failure.note = "conversion function is not accessible";
            return eval;
        }
    }

    if (eval.function_type->parameters.empty()) {
        eval.failure.kind = OverloadFailureKind::InvalidCandidateState;
        eval.failure.note = "conversion function is missing implicit object parameter";
        return eval;
    }
    if (eval.function_type->parameters.size() != 1) {
        eval.failure.kind = OverloadFailureKind::InvalidCandidateState;
        eval.failure.note = "conversion function must not have user parameters";
        return eval;
    }

    eval.viable = true;
    eval.conversions.reserve(2);

    QualType implicit_object_type =
        decay_parameter_type(eval.function_type->parameters.front());
    auto object_seq = evaluate_overload_implicit_object_conversion(
        arg,
        implicit_object_type,
        OverloadImplicitObjectArgKind::MemberObject,
        eval.function_type->member_ref_qualifier,
        conversion_cache);
    eval.conversions.push_back(object_seq);
    if (!object_seq.viable) {
        eval.viable = false;
        eval.failure.kind =
            object_seq.detail_kind ==
                    ConversionSequenceDetailKind::ReferenceRefQualifierMismatch
                ? OverloadFailureKind::ImplicitObjectRefQualifierMismatch
                : OverloadFailureKind::ImplicitObjectConversionFailure;
        eval.failure.argument_index = 1;
        eval.failure.from = object_seq.from ? object_seq.from
                                            : (arg ? arg->get_type() : QualType());
        eval.failure.to = implicit_object_type;
        eval.failure.ref_qualifier = eval.function_type->member_ref_qualifier;
        eval.failure.note = object_seq.note;
        return eval;
    }

    auto dummy_callee = make_hidden_overload_callee(method.symbol, arg ? arg->location : SrcLoc());
    auto produced_expr = collect_make<FuncCall>(std::move(dummy_callee), arg ? arg->location : SrcLoc());
    produced_expr->ctype = eval.function_type->ret_type;
    auto final_seq = build_cpp_overload_conversion_sequence(
        produced_expr.get(),
        target_type,
        /*allow_user_defined=*/false);
    eval.conversions.push_back(final_seq);
    if (!final_seq.viable) {
        eval.viable = false;
        eval.failure.kind = OverloadFailureKind::ArgumentConversionFailure;
        eval.failure.argument_index = 2;
        eval.failure.from = produced_expr->get_type();
        eval.failure.to = target_type;
        eval.failure.note = final_seq.note;
    }

    return eval;
}

std::optional<Collect::CppConversionConstructorMatch>
Collect::select_cpp_conversion_constructor(Expr* arg,
                                                   QualType target_object_type,
                                                   bool allow_explicit_constructors) {

    if (!lang_opts_.is_cxx_mode() || !arg || !target_object_type) {
        return std::nullopt;
    }

    auto canonical_target =
        desugar_type(remove_reference(target_object_type, ast_ctx_.get()), ast_ctx_.get())
            .as_shared<ObjectType>();
    if (!canonical_target) {
        return std::nullopt;
    }
    const ObjectDecl* record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(canonical_target->get_decl()));
    if (!record_decl) {
        return std::nullopt;
    }
    const RecordSemanticState* record_state =
        record_semantics_cache_lookup(record_decl);
    if (!record_state ||
        (record_state->constructors.empty() &&
         record_state->method_templates.empty())) {
        return std::nullopt;
    }

    OverloadConversionMemoCache conversion_cache;
    std::vector<Expr*> ctor_args{arg};
    std::vector<RecordSemanticState::Constructor> template_constructors =
        instantiate_constructor_template_candidates(
            *record_state,
            ctor_args,
            arg ? arg->location : SrcLoc());
    conversion_cache.reserve(
        record_state->constructors.size() + template_constructors.size());

    OverloadCandidateSet candidate_set;
    candidate_set.evaluated.reserve(
        record_state->constructors.size() + template_constructors.size());
    for (const auto& ctor : record_state->constructors) {
        candidate_set.evaluated.push_back(evaluate_conversion_constructor_candidate(
            ctor,
            arg,
            target_object_type,
            allow_explicit_constructors,
            &conversion_cache));
    }
    for (const auto& ctor : template_constructors) {
        candidate_set.evaluated.push_back(evaluate_conversion_constructor_candidate(
            ctor,
            arg,
            target_object_type,
            allow_explicit_constructors,
            &conversion_cache));
    }

    collect_viable_overload_candidates(candidate_set);
    if (candidate_set.viable_indices.empty()) {
        return std::nullopt;
    }

    auto best_index = select_best_overload_candidate_index(candidate_set);
    if (!best_index.has_value()) {
        return std::nullopt;
    }

    const auto& chosen = candidate_set.evaluated[*best_index];
    if (!chosen.constructor || !chosen.constructor->symbol || !chosen.function_type) {
        return std::nullopt;
    }

    CppConversionConstructorMatch result;
    result.ctor_symbol = chosen.constructor->symbol;
    result.ctor_function_type = chosen.function_type;
    result.user_param_start = chosen.user_param_start;
    result.max_user_param_count = chosen.max_user_param_count;
    return result;
}

std::optional<Collect::CppUserDefinedConversionMatch>
Collect::select_cpp_user_defined_conversion(
    Expr* arg,
    QualType target_type,
    bool allow_explicit_constructors,
    bool allow_explicit_conversion_functions) {

    if (!lang_opts_.is_cxx_mode() || !arg || !target_type || !ast_ctx_) {
        return std::nullopt;
    }

    QualType conversion_target =
        desugar_type(remove_reference(target_type, ast_ctx_.get()), ast_ctx_.get());
    if (!conversion_target) {
        return std::nullopt;
    }

    auto source_record_type =
        remove_reference_and_desugar(arg->get_type(), ast_ctx_.get())
            .as_shared<ObjectType>();
    const ObjectDecl* source_record_decl =
        source_record_type
            ? dyn_cast<ObjectDecl>(source_record_type->get_decl())
            : nullptr;
    if (source_record_decl &&
        ast_ctx_->has_cpp_lambda_closure_decl_info(source_record_decl->node_id)) {
        const auto* lambda_info =
            ast_ctx_->get_cpp_lambda_closure_decl_info(source_record_decl->node_id);
        auto target_pointer =
            conversion_target.as_shared<PointerType>();
        auto target_function =
            target_pointer
                ? desugar_type(target_pointer->pointed_type, ast_ctx_.get())
                      .as_shared<FunctionType>()
                : nullptr;
        auto invoker_function =
            (lambda_info && lambda_info->function_pointer_invoker_decl)
                ? desugar_type(
                      QualType(lambda_info->function_pointer_invoker_decl->type),
                      ast_ctx_.get())
                      .as_shared<FunctionType>()
                : nullptr;
        if (lambda_info &&
            !lambda_info->has_syntactic_captures &&
            lambda_info->function_pointer_invoker_decl &&
            target_function &&
            function_types_compatible_for_lambda_pointer_conversion(
                invoker_function,
                target_function,
                ast_ctx_.get())) {
            CppUserDefinedConversionMatch result;
            result.kind =
                CppUserDefinedConversionKind::LambdaFunctionPointer;
            result.lambda_function_pointer.closure_owner = source_record_decl;
            result.lambda_function_pointer.invoker_decl =
                lambda_info->function_pointer_invoker_decl;
            result.lambda_function_pointer.invoker_function_type =
                std::move(invoker_function);
            return result;
        }
    }

    OverloadConversionMemoCache conversion_cache;
    OverloadCandidateSet candidate_set;
    std::vector<RecordSemanticState::Constructor> target_constructor_templates;

    if (source_record_decl) {
        auto conversion_methods =
            find_record_conversion_methods(source_record_type.get());
        candidate_set.evaluated.reserve(
            candidate_set.evaluated.size() + conversion_methods.size());
        for (const auto& method_candidate : conversion_methods) {
            if (!method_candidate.method) {
                continue;
            }
            candidate_set.evaluated.push_back(
                evaluate_conversion_function_candidate(
                    *method_candidate.method,
                    method_candidate.owner_record_decl,
                    arg,
                    target_type,
                    allow_explicit_conversion_functions,
                    &conversion_cache));
        }
    }

    auto conversion_target_kind = canonical_type_kind(
        conversion_target,
        ast_ctx_.get());
    if (conversion_target_kind == TypeKind::Object) {
        auto canonical_target =
            conversion_target.as_shared<ObjectType>();
        const ObjectDecl* record_decl = canonical_target
            ? canonical_record_decl(dyn_cast<ObjectDecl>(canonical_target->get_decl()))
            : nullptr;
        const RecordSemanticState* record_state =
            record_decl ? record_semantics_cache_lookup(record_decl) : nullptr;
        if (record_state &&
            (!record_state->constructors.empty() ||
             !record_state->method_templates.empty())) {
            std::vector<Expr*> ctor_args{arg};
            target_constructor_templates =
                instantiate_constructor_template_candidates(
                    *record_state,
                    ctor_args,
                    arg ? arg->location : SrcLoc());
            candidate_set.evaluated.reserve(
                candidate_set.evaluated.size() +
                    record_state->constructors.size() +
                    target_constructor_templates.size());
            for (const auto& ctor : record_state->constructors) {
                candidate_set.evaluated.push_back(
                    evaluate_conversion_constructor_candidate(
                        ctor,
                        arg,
                        target_type,
                        allow_explicit_constructors,
                        &conversion_cache));
            }
            for (const auto& ctor : target_constructor_templates) {
                candidate_set.evaluated.push_back(
                    evaluate_conversion_constructor_candidate(
                        ctor,
                        arg,
                        target_type,
                        allow_explicit_constructors,
                        &conversion_cache));
            }
        }
    }

    if (candidate_set.evaluated.empty()) {
        return std::nullopt;
    }

    collect_viable_overload_candidates(candidate_set);
    if (candidate_set.viable_indices.empty()) {
        return std::nullopt;
    }

    auto best_index = select_best_overload_candidate_index(candidate_set);
    if (!best_index.has_value()) {
        return std::nullopt;
    }

    const auto& chosen = candidate_set.evaluated[*best_index];
    CppUserDefinedConversionMatch result;
    switch (chosen.candidate_kind) {
        case OverloadCandidateKind::ConversionFunction:
            if (!chosen.conversion_function || !chosen.symbol || !chosen.function_type) {
                return std::nullopt;
            }
            result.kind = CppUserDefinedConversionKind::ConversionFunction;
            result.conversion_function.method = chosen.conversion_function;
            result.conversion_function.owner_record_decl = chosen.owner_record_decl;
            result.conversion_function.method_symbol = chosen.symbol;
            result.conversion_function.method_function_type = chosen.function_type;
            result.conversion_function.conversion_target_type =
                chosen.conversion_function->conversion_target_type
                    ? chosen.conversion_function->conversion_target_type
                    : chosen.function_type->ret_type;
            return result;
        case OverloadCandidateKind::ConversionConstructor:
            if (!chosen.constructor || !chosen.constructor->symbol ||
                !chosen.function_type) {
                return std::nullopt;
            }
            result.kind = CppUserDefinedConversionKind::Constructor;
            result.constructor.ctor_symbol = chosen.constructor->symbol;
            result.constructor.ctor_function_type = chosen.function_type;
            result.constructor.user_param_start = chosen.user_param_start;
            result.constructor.max_user_param_count = chosen.max_user_param_count;
            return result;
        case OverloadCandidateKind::Function:
            break;
    }
    return std::nullopt;
}

std::unique_ptr<Expr> Collect::build_cpp_user_defined_conversion_expr(
    std::unique_ptr<Expr> arg,
    QualType target_type,
    SrcLoc loc) {

    if (!arg || !target_type) {
        return arg;
    }

    QualType target_object_type = remove_reference(target_type, ast_ctx_.get());
    target_object_type = desugar_type(target_object_type, ast_ctx_.get());
    if (canonical_type_kind(target_object_type, ast_ctx_.get()) == TypeKind::Object &&
        dyn_cast<InitListExpr>(Collect::strip_implicit_casts(arg.get()))) {
        auto converted = convert_cpp_braced_init_argument(
            std::move(arg), target_object_type, loc);
        if (!converted) {
            report_error(
                "internal error: missing user-defined conversion constructor for '" +
                    target_object_type.to_string() + "'",
                loc);
            return collect_make<ErrorExpr>(
                "missing user-defined conversion constructor", loc);
        }
        return converted;
    }

    auto conversion_match = select_cpp_user_defined_conversion(
        arg.get(),
        target_type,
        /*allow_explicit_constructors=*/false,
        /*allow_explicit_conversion_functions=*/false);
    if (!conversion_match.has_value()) {
        return arg;
    }

    return build_cpp_selected_user_defined_conversion_expr(
        std::move(arg),
        target_type,
        *conversion_match,
        loc);
}

std::unique_ptr<Expr> Collect::build_cpp_selected_user_defined_conversion_expr(
    std::unique_ptr<Expr> arg,
    QualType target_type,
    const CppUserDefinedConversionMatch& conversion_match,
    SrcLoc loc) {
    if (!arg || !target_type) {
        return arg;
    }

    QualType target_object_type = remove_reference(target_type, ast_ctx_.get());
    target_object_type = desugar_type(target_object_type, ast_ctx_.get());

    if (conversion_match.kind ==
        CppUserDefinedConversionKind::LambdaFunctionPointer) {
        QualType conversion_target = remove_reference(target_type, ast_ctx_.get());
        return collect_make<ImplicitCast>(
            ImplicitCastTypes::LAMBDA_TO_FUNCTION_POINTER,
            std::move(arg),
            conversion_target);
    }

    if (dyn_cast<InitListExpr>(Collect::strip_implicit_casts(arg.get()))) {
        auto converted = convert_cpp_braced_init_argument(
            std::move(arg), target_object_type, loc);
        if (!converted) {
            report_error(
                "internal error: missing user-defined conversion constructor for '" +
                    target_object_type.to_string() + "'",
                loc);
            return collect_make<ErrorExpr>(
                "missing user-defined conversion constructor", loc);
        }
        return converted;
    }

    if (conversion_match.kind ==
        CppUserDefinedConversionKind::ConversionFunction) {
        if (!conversion_match.conversion_function.method_symbol ||
            !conversion_match.conversion_function.method_function_type) {
            report_error(
                "internal error: missing conversion-function symbol metadata",
                loc);
            return collect_make<ErrorExpr>(
                "missing conversion-function metadata", loc);
        }

        auto call_callee = make_hidden_overload_callee(
            conversion_match.conversion_function.method_symbol,
            loc);
        auto call = collect_make<FuncCall>(std::move(call_callee), loc);

        MemberCallSelection member_call_selection;
        member_call_selection.selected = true;
        member_call_selection.is_arrow = false;
        member_call_selection.suppress_virtual_dispatch = false;
        member_call_selection.has_implicit_object_argument = true;
        member_call_selection.name =
            conversion_match.conversion_function.method
                ? conversion_match.conversion_function.method->name
                : "operator";
        member_call_selection.symbol =
            conversion_match.conversion_function.method_symbol;
        member_call_selection.record_decl =
            conversion_match.conversion_function.owner_record_decl;

        auto implicit_object_arg = build_overload_implicit_object_arg(
            OverloadImplicitObjectArgKind::MemberObject,
            std::move(arg),
            false,
            loc);
        if (!implicit_object_arg) {
            report_error(
                "internal error: failed to build conversion-function object argument",
                loc);
            return collect_make<ErrorExpr>(
                "missing conversion-function object argument", loc);
        }
        call->args.push_back(std::move(implicit_object_arg));

        auto converted_call = finalize_call_expression(
            std::move(call),
            member_call_selection,
            loc);
        if (!converted_call || isa<ErrorExpr>(converted_call.get())) {
            return converted_call;
        }

        auto final_seq = build_cpp_overload_conversion_sequence(
            converted_call.get(),
            target_type,
            /*allow_user_defined=*/false);
        if (!final_seq.viable) {
            report_conversion_failure(
                "conversion function result",
                converted_call->get_type(),
                target_type,
                loc);
            return collect_make<ErrorExpr>(
                "invalid conversion-function result", loc);
        }

        if (canonical_type_kind(target_type, ast_ctx_.get()) == TypeKind::Reference) {
            return collect_make<ImplicitCast>(
                std::move(converted_call),
                target_type);
        }

        converted_call = collect_apply_standard_conversions(
            std::move(converted_call),
            ExprUseContext::CallArgument);
        return cast_if_needed(std::move(converted_call), target_type);
    }

    if (conversion_match.kind !=
        CppUserDefinedConversionKind::Constructor) {
        report_error(
            "internal error: unsupported user-defined conversion kind",
            loc);
        return collect_make<ErrorExpr>(
            "unsupported user-defined conversion kind", loc);
    }

    std::shared_ptr<Symbol> ctor_symbol =
        conversion_match.constructor.ctor_symbol;
    if (!ctor_symbol ||
        !conversion_match.constructor.ctor_function_type) {
        report_error(
            "internal error: missing user-defined conversion constructor for '" +
                target_object_type.to_string() + "'",
            loc);
        return collect_make<ErrorExpr>(
            "missing user-defined conversion constructor", loc);
    }

    note_specialization_use_for_symbol(ctor_symbol, loc);
    if (auto completion_error =
            complete_selected_function_template_specialization_symbol(
                ctor_symbol,
                loc,
                "failed to instantiate selected conversion-constructor template specialization")) {
        return completion_error;
    }
    if (!collect_ensure_defaulted_special_member_body(ctor_symbol, loc)) {
        report_error(
            "failed to materialize defaulted constructor '" +
                ctor_symbol->name + "'",
            loc);
        return collect_make<ErrorExpr>(
            "failed to materialize defaulted constructor", loc);
    }
    if (ctor_symbol->is_deleted) {
        report_error(
            "call to deleted constructor '" + ctor_symbol->name + "'",
            loc);
        return collect_make<ErrorExpr>("deleted constructor call", loc);
    }

    std::vector<std::unique_ptr<Expr>> ctor_args;
    ctor_args.reserve(conversion_match.constructor.max_user_param_count);
    ctor_args.push_back(std::move(arg));

    for (size_t arg_index = ctor_args.size();
         arg_index < conversion_match.constructor.max_user_param_count;
         ++arg_index) {
        size_t param_index =
            conversion_match.constructor.user_param_start + arg_index;
        const Expr* default_expr = lookup_default_argument_for_param(
            conversion_match.constructor.ctor_symbol, param_index);
        if (!default_expr) {
            report_error(
                "internal error: missing conversion-constructor default argument metadata",
                loc);
            return collect_make<ErrorExpr>(
                "missing conversion-constructor default argument", loc);
        }
        std::string clone_error;
        auto cloned_default = clone_expr_tree(
            default_expr, ast_ctx_.get(), &clone_error);
        if (!cloned_default) {
            std::string message =
                clone_error.empty()
                    ? "default argument expression is not supported"
                    : "default argument expression is not supported: " +
                          clone_error;
            report_error(message, default_expr->location);
            return collect_make<ErrorExpr>(
                "unsupported conversion-constructor default argument expression",
                loc);
        }
        ctor_args.push_back(std::move(cloned_default));
    }

    std::vector<std::unique_ptr<Expr>> converted_ctor_args;
    converted_ctor_args.reserve(ctor_args.size());
    for (size_t arg_index = 0; arg_index < ctor_args.size(); ++arg_index) {
        size_t param_index =
            conversion_match.constructor.user_param_start + arg_index;
        if (param_index >=
            conversion_match.constructor.ctor_function_type->parameters.size()) {
            report_error(
                "internal error: conversion-constructor parameter index out of range",
                loc);
            return collect_make<ErrorExpr>(
                "conversion-constructor parameter index out of range", loc);
        }
        QualType param_type = decay_parameter_type(
            conversion_match.constructor.ctor_function_type->parameters[param_index]);
        auto ctor_arg = std::move(ctor_args[arg_index]);
        if (canonical_type_kind(param_type, ast_ctx_.get()) ==
            TypeKind::Reference) {
            auto seq = build_cpp_overload_conversion_sequence(
                ctor_arg.get(), param_type, /*allow_user_defined=*/false);
            if (!seq.viable) {
                report_conversion_failure(
                    "conversion constructor argument",
                    ctor_arg ? ctor_arg->get_type() : QualType(),
                    param_type,
                    ctor_arg ? ctor_arg->location : loc);
                return collect_make<ErrorExpr>(
                    "invalid conversion-constructor argument", loc);
            }
        } else {
            ctor_arg = collect_apply_standard_conversions(
                std::move(ctor_arg), ExprUseContext::CallArgument);
            ctor_arg = cast_if_needed(std::move(ctor_arg), param_type);
        }
        converted_ctor_args.push_back(std::move(ctor_arg));
    }

    auto constructed = collect_make<CppConstructExpr>(
        ctor_symbol,
        std::move(converted_ctor_args),
        target_object_type,
        false,
        loc);
    if (canonical_type_kind(target_type, ast_ctx_.get()) == TypeKind::Reference) {
        return collect_make<ImplicitCast>(std::move(constructed), target_type);
    }
    return constructed;
}

std::unique_ptr<Expr> Collect::convert_cpp_braced_init_argument(
    std::unique_ptr<Expr> arg,
    QualType target_type,
    SrcLoc loc) {

    if (!lang_opts_.is_cxx_mode() || !arg || !target_type) {
        return arg;
    }

    if (canonical_type_kind(target_type, ast_ctx_.get()) != TypeKind::Object) {
        return arg;
    }

    std::unique_ptr<Expr> working = std::move(arg);
    while (working &&
           !isa<InitListExpr>(working.get()) &&
           (isa<ImplicitCast>(working.get()) ||
            isa<ExplicitCast>(working.get()))) {
        if (auto* implicit_cast = dyn_cast<ImplicitCast>(working.get())) {
            auto inner = std::move(implicit_cast->expr);
            working = std::move(inner);
            continue;
        }
        if (auto* explicit_cast = dyn_cast<ExplicitCast>(working.get())) {
            auto inner = std::move(explicit_cast->expr);
            working = std::move(inner);
            continue;
        }
    }

    auto* init_list = dyn_cast<InitListExpr>(working.get());
    if (!init_list) {
        return working;
    }

    if (init_list_has_lowered_semantics_for_type(
            init_list, target_type, ast_ctx_.get())) {
        return working;
    }

    bool is_list_init = !init_list->is_paren_init;
    auto owned_list = std::unique_ptr<InitListExpr>(
        static_cast<InitListExpr*>(working.release()));
    std::vector<std::unique_ptr<Expr>> ctor_args;
    ctor_args.reserve(owned_list->elements.size());
    for (auto& elem : owned_list->elements) {
        if (!elem.designators.empty()) {
            report_error(
                "designated initializers are not supported in constructor initialization",
                elem.loc);
        }
        if (!elem.value) {
            report_error(
                "missing initializer expression in constructor argument list",
                elem.loc);
            continue;
        }
        ctor_args.push_back(std::move(elem.value));
    }

    auto converted = collect_member_initializer_expression(
        std::move(ctor_args),
        target_type,
        is_list_init,
        loc,
        false);
    if (!converted) {
        report_error(
            "failed to build braced-initializer conversion for '" +
                target_type.to_string() + "'",
            loc);
        return collect_make<ErrorExpr>("invalid braced-initializer argument", loc);
    }
    return converted;
}

bool Collect::probe_cpp_braced_init_argument_conversion(
    Expr* arg,
    QualType target_type,
    SrcLoc loc,
    ImplicitConversionSequence& seq_out) {

    seq_out = ImplicitConversionSequence{};
    seq_out.from = arg ? arg->get_type() : QualType();
    seq_out.to = target_type;

    if (!lang_opts_.is_cxx_mode() || !arg || !target_type) {
        return false;
    }
    if (!dyn_cast<InitListExpr>(strip_implicit_casts(arg)) ||
        canonical_type_kind(target_type, ast_ctx_.get()) != TypeKind::Object) {
        return false;
    }

    std::string clone_error;
    auto cloned = clone_expr_tree(arg, ast_ctx_.get(), &clone_error);
    if (!cloned) {
        seq_out.kind = ConversionSequenceKind::Failed;
        seq_out.rank = ConversionSequenceRank::NoMatch;
        seq_out.detail_kind = ConversionSequenceDetailKind::BracedInit;
        seq_out.viable = false;
        seq_out.note = clone_error.empty()
            ? "braced-init argument clone failed"
            : clone_error;
        return true;
    }

    if (!diag_engine_) {
        seq_out.kind = ConversionSequenceKind::Failed;
        seq_out.rank = ConversionSequenceRank::NoMatch;
        seq_out.detail_kind = ConversionSequenceDetailKind::BracedInit;
        seq_out.viable = false;
        seq_out.note = "missing diagnostic engine for braced-init conversion probe";
        return true;
    }

    auto checkpoint = diag_engine_->checkpoint();
    auto converted = convert_cpp_braced_init_argument(
        std::move(cloned), target_type, loc);
    diag_engine_->restore(checkpoint);

    if (!converted || isa<ErrorExpr>(converted.get())) {
        seq_out.kind = ConversionSequenceKind::Failed;
        seq_out.rank = ConversionSequenceRank::NoMatch;
        seq_out.detail_kind = ConversionSequenceDetailKind::BracedInit;
        seq_out.viable = false;
        seq_out.note = "braced-init argument cannot initialize target type";
        return true;
    }

    if (isa<CppConstructExpr>(converted.get())) {
        seq_out.kind = ConversionSequenceKind::UserDefined;
        seq_out.rank = ConversionSequenceRank::Conversion;
        seq_out.detail_kind = ConversionSequenceDetailKind::BracedInit;
        seq_out.exact_subrank = -1;
    } else {
        seq_out.kind = ConversionSequenceKind::Identity;
        seq_out.rank = ConversionSequenceRank::ExactMatch;
        seq_out.detail_kind = ConversionSequenceDetailKind::BracedInit;
        seq_out.exact_subrank = 0;
    }
    seq_out.viable = true;
    seq_out.note.clear();
    return true;
}

std::unique_ptr<Expr> Collect::build_overload_implicit_object_arg(
    OverloadImplicitObjectArgKind implicit_arg_kind,
    std::unique_ptr<Expr> object_expr,
    bool object_expr_is_pointer,
    SrcLoc loc) {

    if (implicit_arg_kind == OverloadImplicitObjectArgKind::None) {
        return nullptr;
    }
    if (!object_expr) {
        return nullptr;
    }
    if (implicit_arg_kind == OverloadImplicitObjectArgKind::Regular) {
        return object_expr;
    }

    if (object_expr_is_pointer ||
        canonical_type_kind(remove_reference(object_expr->get_type(), ast_ctx_.get()),
                            ast_ctx_.get()) ==
            TypeKind::Pointer) {
        return collect_apply_standard_conversions(
            std::move(object_expr), ExprUseContext::RValue);
    }

    Expr* raw_object = strip_implicit_casts(object_expr.get());
    ValueCategory category = classify_value_category(
        raw_object ? raw_object : object_expr.get());
    if (category == ValueCategory::LValue) {
        while (auto* cast = dyn_cast<ImplicitCast>(object_expr.get())) {
            if (!cast->expr || !cast->expr->isLValue()) {
                break;
            }
            switch (cast->kind) {
                case ImplicitCastTypes::LVALUE_TO_RVALUE:
                case ImplicitCastTypes::ARITH_CAST:
                case ImplicitCastTypes::RAW_CAST: {
                    auto owned_cast = std::unique_ptr<ImplicitCast>(
                        static_cast<ImplicitCast*>(object_expr.release()));
                    object_expr = std::move(owned_cast->expr);
                    continue;
                }
                default:
                    break;
            }
            break;
        }
        return collect_unary_operation(
            UnaryOpTypes::ADDRESS_OF, std::move(object_expr), loc);
    }

    QualType object_type = remove_reference(object_expr->get_type(), ast_ctx_.get());
    if (!object_type) {
        report_error("internal error: missing implicit-object type", loc);
        return collect_make<ErrorExpr>("missing implicit-object type", loc);
    }

    QualType reference_type(
        std::make_shared<ReferenceType>(object_type, ReferenceKind::LValue));
    auto temporary_reference = collect_make<ImplicitCast>(
        ImplicitCastTypes::ARITH_CAST, std::move(object_expr), reference_type);
    auto address_of_temporary = collect_make<UnaryOperation>(
        UnaryOpTypes::ADDRESS_OF, std::move(temporary_reference), loc);
    address_of_temporary->ctype =
        QualType(std::make_shared<PointerType>(object_type));
    return address_of_temporary;
}



Collect::ImplicitConversionSequence
Collect::evaluate_overload_implicit_object_conversion(
    Expr* object_arg,
    QualType param_type,
    OverloadImplicitObjectArgKind implicit_object_arg_kind,
    FunctionRefQualifierKind ref_qualifier,
    OverloadConversionMemoCache* conversion_cache) {

    auto classify_implicit_object_value_category =
        [&](Expr* arg) -> ValueCategory {
        if (!arg) {
            return ValueCategory::Unknown;
        }
        if (implicit_object_arg_kind == OverloadImplicitObjectArgKind::MemberObject) {
            auto canonical_arg_type =
                remove_reference_and_desugar(
                    arg->get_type(),
                    ast_ctx_.get());
            if (canonical_type_kind(canonical_arg_type, ast_ctx_.get()) ==
                TypeKind::Pointer) {
                // For `ptr->method()`, the implicit object expression is `*ptr`
                // and is therefore an lvalue.
                return ValueCategory::LValue;
            }
        }
        return classify_value_category(strip_implicit_casts(arg));
    };

    auto object_arg_category = classify_implicit_object_value_category(object_arg);
    if (ref_qualifier == FunctionRefQualifierKind::LValue &&
        object_arg_category != ValueCategory::LValue) {
        ImplicitConversionSequence rejected;
        rejected.kind = ConversionSequenceKind::Numeric;
        rejected.rank = ConversionSequenceRank::NoMatch;
        rejected.detail_kind =
            ConversionSequenceDetailKind::ReferenceRefQualifierMismatch;
        rejected.from = object_arg ? object_arg->get_type() : QualType();
        rejected.to = param_type;
        rejected.viable = false;
        rejected.note =
            "implicit object argument is not an lvalue for '&'-qualified method";
        return rejected;
    }
    if (ref_qualifier == FunctionRefQualifierKind::RValue &&
        object_arg_category == ValueCategory::LValue) {
        ImplicitConversionSequence rejected;
        rejected.kind = ConversionSequenceKind::Numeric;
        rejected.rank = ConversionSequenceRank::NoMatch;
        rejected.detail_kind =
            ConversionSequenceDetailKind::ReferenceRefQualifierMismatch;
        rejected.from = object_arg ? object_arg->get_type() : QualType();
        rejected.to = param_type;
        rejected.viable = false;
        rejected.note =
            "implicit object argument is not an rvalue for '&&'-qualified method";
        return rejected;
    }

    // The implicit object parameter for a member call only participates in
    // standard conversions. Allowing user-defined conversions here recurses
    // through the same conversion-function set while we are still evaluating
    // a candidate.
    auto seq = build_cpp_overload_conversion_sequence_cached(
        object_arg,
        param_type,
        /*allow_user_defined=*/false,
        conversion_cache);
    if (seq.viable || !object_arg || !param_type) {
        return seq;
    }

    // Dot-call member candidates lower to a hidden object-pointer argument.
    // Ranking must still model object/pointer compatibility even when the
    // source object is a temporary (materialized later during rewriting).
    QualType object_type =
        remove_reference_and_desugar(object_arg->get_type(), ast_ctx_.get());
    if (!object_type) {
        return seq;
    }
    auto object_kind = canonical_type_kind(object_type, ast_ctx_.get());
    auto param_ptr =
        desugar_type(param_type, ast_ctx_.get()).as_shared<PointerType>();
    QualType pointed_type = param_ptr ? param_ptr->pointed_type : QualType();
    auto pointed_kind = canonical_type_kind(pointed_type, ast_ctx_.get());
    if (object_kind != TypeKind::Object || pointed_kind != TypeKind::Object) {
        return seq;
    }
    if (has_qualification_preserving_match(object_type, pointed_type)) {
        seq.kind = object_type.equals_qualified(pointed_type)
            ? ConversionSequenceKind::Identity
            : ConversionSequenceKind::Qualification;
        seq.rank = ConversionSequenceRank::ExactMatch;
        seq.from = object_type;
        seq.to = param_type;
        seq.viable = true;
        seq.detail_kind = ConversionSequenceDetailKind::ReferenceDirectBinding;
        seq.exact_subrank =
            seq.kind == ConversionSequenceKind::Identity
                ? 0
                : qualification_conversion_exact_subrank(
                      object_type,
                      pointed_type,
                      ast_ctx_.get());
        seq.note.clear();
        return seq;
    }
    if (can_convert_derived_to_base_object(object_type, pointed_type)) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::ReferenceDirectBinding;
        seq.from = object_type;
        seq.to = param_type;
        seq.viable = true;
        seq.exact_subrank = -1;
        seq.note.clear();
        return seq;
    }
    return seq;
}

Collect::OverloadCandidateEval Collect::evaluate_overload_call_candidate(
    const OverloadCallCandidate& candidate_info,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    OverloadConversionMemoCache* conversion_cache) {
    return evaluate_overload_call_candidate(
        candidate_info,
        make_raw_explicit_args(explicit_args),
        implicit_object_arg,
        conversion_cache);
}

Collect::OverloadCandidateEval Collect::evaluate_overload_call_candidate(
    const OverloadCallCandidate& candidate_info,
    const std::vector<Expr*>& explicit_args,
    Expr* implicit_object_arg,
    OverloadConversionMemoCache* conversion_cache) {

    bump_overload_candidate_evaluations();
    OverloadCandidateEval eval;
    eval.candidate_kind = OverloadCandidateKind::Function;
    eval.symbol = candidate_info.symbol;
    eval.provenance = function_candidate_provenance(candidate_info.symbol);
    eval.implicit_object_arg_kind = candidate_info.implicit_object_arg_kind;
    eval.operator_rewrite_kind = candidate_info.operator_rewrite_kind;
    eval.is_synthesized_reversed_operator_candidate =
        candidate_info.is_synthesized_reversed_operator_candidate;

    std::vector<Expr*> operator_explicit_args;
    const std::vector<Expr*>* effective_explicit_args = &explicit_args;
    Expr* effective_implicit_object_arg = implicit_object_arg;
    if (candidate_info.has_operator_operand_overrides) {
        effective_implicit_object_arg =
            candidate_info.operator_implicit_object_arg;
        operator_explicit_args.push_back(candidate_info.operator_explicit_arg);
        effective_explicit_args = &operator_explicit_args;
    }
    const std::vector<Expr*>& call_explicit_args = *effective_explicit_args;

    if (!candidate_info.symbol ||
        candidate_info.symbol->kind != SymbolKind::FUNCTION) {
        eval.failure.kind = OverloadFailureKind::NotCallable;
        eval.failure.note = "candidate is not a function";
        return eval;
    }

    auto candidate_canonical_type =
        desugar_type(candidate_info.symbol->type, ast_ctx_.get());
    auto candidate_fn = candidate_canonical_type.as_shared<FunctionType>();
    if (!candidate_fn) {
        auto candidate_ptr = candidate_canonical_type.as_shared<PointerType>();
        if (candidate_ptr) {
            candidate_fn =
                desugar_type(candidate_ptr->pointed_type, ast_ctx_.get())
                    .as_shared<FunctionType>();
        }
    }
    if (!candidate_fn) {
        eval.failure.kind = OverloadFailureKind::NotCallable;
        eval.failure.note = "candidate has non-callable type";
        return eval;
    }

    eval.function_type = candidate_fn;
    eval.viable = true;
    eval.is_deleted = candidate_info.symbol->is_deleted != 0;

    bool has_implicit_object_arg =
        eval.implicit_object_arg_kind != OverloadImplicitObjectArgKind::None;
    size_t implicit_arg_count = has_implicit_object_arg ? 1 : 0;
    size_t provided_arg_count = call_explicit_args.size() + implicit_arg_count;
    bool has_void_param = (candidate_fn->parameters.size() == 1 &&
                           candidate_fn->parameters[0]->isVoid());
    size_t named_param_count = has_void_param ? 0 : candidate_fn->parameters.size();
    // Default arguments reduce the minimum required arity but not the maximum
    // for non-variadic prototype candidates.
    size_t trailing_default_arg_count = count_trailing_default_arguments_for_call(
        candidate_info.symbol, named_param_count, implicit_arg_count);
    if (trailing_default_arg_count > named_param_count) {
        trailing_default_arg_count = named_param_count;
    }
    size_t min_required_param_count =
        named_param_count >= trailing_default_arg_count
            ? named_param_count - trailing_default_arg_count
            : 0;

    if (candidate_fn->has_prototype) {
        if (candidate_fn->is_variadic) {
            if (provided_arg_count < min_required_param_count) {
                eval.viable = false;
                eval.failure.kind = OverloadFailureKind::ArityTooFew;
                eval.failure.required_arg_count = min_required_param_count;
                eval.failure.provided_arg_count = provided_arg_count;
                eval.failure.arity_is_minimum = true;
            }
        } else if (provided_arg_count < min_required_param_count) {
            eval.viable = false;
            eval.failure.kind = OverloadFailureKind::ArityTooFew;
            eval.failure.required_arg_count =
                trailing_default_arg_count == 0
                    ? named_param_count
                    : min_required_param_count;
            eval.failure.provided_arg_count = provided_arg_count;
            eval.failure.arity_is_minimum = trailing_default_arg_count != 0;
        } else if (provided_arg_count > named_param_count) {
            eval.viable = false;
            eval.failure.kind = OverloadFailureKind::ArityTooMany;
            eval.failure.required_arg_count = named_param_count;
            eval.failure.provided_arg_count = provided_arg_count;
        }
    }

    if (!eval.viable) {
        return eval;
    }

    eval.conversions.reserve(provided_arg_count);

    if (has_implicit_object_arg) {
        if (!effective_implicit_object_arg) {
            eval.viable = false;
            eval.failure.kind = OverloadFailureKind::ImplicitObjectMissing;
            eval.failure.argument_index = 1;
            eval.failure.note = "missing implicit object argument";
        } else if (candidate_fn->has_prototype && named_param_count > 0) {
            QualType param_type = decay_parameter_type(candidate_fn->parameters[0]);
            // Member-object calls use stricter object-parameter compatibility
            // than a regular explicit argument conversion sequence.
            auto seq = (eval.implicit_object_arg_kind ==
                        OverloadImplicitObjectArgKind::MemberObject)
                ? evaluate_overload_implicit_object_conversion(
                      effective_implicit_object_arg,
                      param_type,
                      eval.implicit_object_arg_kind,
                      candidate_fn->member_ref_qualifier,
                      conversion_cache)
                : build_cpp_overload_conversion_sequence_cached(
                      effective_implicit_object_arg,
                      param_type,
                      /*allow_user_defined=*/true,
                      conversion_cache);
            if (!seq.viable) {
                eval.viable = false;
                eval.failure.kind =
                    seq.detail_kind ==
                            ConversionSequenceDetailKind::ReferenceRefQualifierMismatch
                        ? OverloadFailureKind::ImplicitObjectRefQualifierMismatch
                        : OverloadFailureKind::ImplicitObjectConversionFailure;
                eval.failure.argument_index = 1;
                eval.failure.from =
                    seq.from ? seq.from
                             : effective_implicit_object_arg->get_type();
                eval.failure.to = param_type;
                eval.failure.ref_qualifier = candidate_fn->member_ref_qualifier;
                eval.failure.note = seq.note;
            }
            eval.conversions.push_back(seq);
        } else {
            ImplicitConversionSequence seq;
            seq.kind = ConversionSequenceKind::Numeric;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.detail_kind = ConversionSequenceDetailKind::None;
            seq.from = effective_implicit_object_arg->get_type();
            seq.to = nullptr;
            seq.viable = true;
            eval.conversions.push_back(seq);
        }
    }

    for (size_t i = 0; eval.viable && i < call_explicit_args.size(); ++i) {
        size_t param_index = i + implicit_arg_count;
        if (candidate_fn->has_prototype && param_index < named_param_count) {
            QualType param_type =
                decay_parameter_type(candidate_fn->parameters[param_index]);
            auto seq = build_cpp_overload_conversion_sequence_cached(
                call_explicit_args[i],
                param_type,
                /*allow_user_defined=*/true,
                conversion_cache);
            if (!seq.viable) {
                eval.viable = false;
                eval.failure.kind = OverloadFailureKind::ArgumentConversionFailure;
                eval.failure.argument_index = param_index + 1;
                eval.failure.from =
                    seq.from ? seq.from
                             : (call_explicit_args[i]
                                    ? call_explicit_args[i]->get_type()
                                    : QualType());
                eval.failure.to = param_type;
                eval.failure.note = seq.note;
                eval.conversions.push_back(seq);
                break;
            }
            eval.conversions.push_back(seq);
        } else {
            // Variadic/no-prototype arguments are treated as generic conversion
            // quality for this first-cut overload ranking.
            ImplicitConversionSequence seq;
            seq.kind = ConversionSequenceKind::Numeric;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.detail_kind = ConversionSequenceDetailKind::None;
            seq.from = call_explicit_args[i]
                ? call_explicit_args[i]->get_type()
                : QualType();
            seq.to = nullptr;
            seq.viable = true;
            eval.conversions.push_back(seq);
        }
    }

    if (eval.is_synthesized_reversed_operator_candidate &&
        eval.conversions.size() == 2) {
        std::swap(eval.conversions[0], eval.conversions[1]);
    }
    return eval;
}

void Collect::collect_viable_overload_candidates(
    OverloadCandidateSet& candidate_set) const {

    candidate_set.viable_indices.clear();
    candidate_set.viable_indices.reserve(candidate_set.evaluated.size());
    for (size_t idx = 0; idx < candidate_set.evaluated.size(); ++idx) {
        auto& evaluated = candidate_set.evaluated[idx];
        if (evaluated.viable &&
            !are_function_constraints_satisfied(evaluated.symbol.get(),
                                                SrcLoc())) {
            evaluated.viable = false;
            evaluated.failure.kind = OverloadFailureKind::NotCallable;
            evaluated.failure.note = "constraints not satisfied";
        }
        if (evaluated.viable) {
            candidate_set.viable_indices.push_back(idx);
        }
    }
    bump_overload_viable_candidates(candidate_set.viable_indices.size());
}

std::string Collect::overload_failure_reason(
    const OverloadFailure& failure) const {

    switch (failure.kind) {
    case OverloadFailureKind::None:
        return "not viable";
    case OverloadFailureKind::NotCallable:
    case OverloadFailureKind::InvalidCandidateState:
    case OverloadFailureKind::DeletedCandidate:
    case OverloadFailureKind::InaccessibleCandidate:
        return failure.note.empty() ? "not viable" : failure.note;
    case OverloadFailureKind::ArityTooFew:
    case OverloadFailureKind::ArityTooMany: {
        std::string requirement_text =
            failure.arity_is_minimum ? "requires at least "
                                     : "requires ";
        return requirement_text +
            std::to_string(failure.required_arg_count) +
            " argument(s), but " + std::to_string(failure.provided_arg_count) +
            " provided";
    }
    case OverloadFailureKind::ImplicitObjectMissing:
        return failure.note.empty()
            ? "missing implicit object argument"
            : failure.note;
    case OverloadFailureKind::ImplicitObjectRefQualifierMismatch:
    case OverloadFailureKind::ImplicitObjectConversionFailure:
    case OverloadFailureKind::ArgumentConversionFailure: {
        size_t argument_number =
            failure.argument_index == std::numeric_limits<size_t>::max()
                ? 0
                : failure.argument_index;
        std::string from_name =
            failure.from ? failure.from.to_string() : "<unknown>";
        std::string to_name =
            failure.to ? failure.to.to_string() : "<unknown>";
        return "cannot convert argument " + std::to_string(argument_number) +
            " from '" + from_name + "' to '" + to_name + "'";
    }
    }
    return failure.note.empty() ? "not viable" : failure.note;
}

std::string Collect::overload_candidate_type_name(
    const OverloadCandidateEval& candidate) const {

    return (candidate.symbol && candidate.symbol->type)
        ? candidate.symbol->type.to_string()
        : std::string("<unknown>");
}

int Collect::overload_failure_category(const OverloadFailure& failure) const {

    switch (failure.kind) {
    case OverloadFailureKind::ArityTooFew:
    case OverloadFailureKind::ArityTooMany:
        return 0;
    case OverloadFailureKind::ImplicitObjectMissing:
    case OverloadFailureKind::ImplicitObjectRefQualifierMismatch:
    case OverloadFailureKind::ImplicitObjectConversionFailure:
    case OverloadFailureKind::ArgumentConversionFailure:
        return 1;
    case OverloadFailureKind::DeletedCandidate:
    case OverloadFailureKind::InaccessibleCandidate:
        return 2;
    case OverloadFailureKind::NotCallable:
    case OverloadFailureKind::InvalidCandidateState:
    case OverloadFailureKind::None:
        return 3;
    }
    return 3;
}

bool Collect::overload_note_order_less(
    const OverloadCandidateSet& candidate_set,
    size_t lhs_idx,
    size_t rhs_idx) const {

    const auto& lhs = candidate_set.evaluated[lhs_idx];
    const auto& rhs = candidate_set.evaluated[rhs_idx];

    if (lhs.viable != rhs.viable) {
        return lhs.viable && !rhs.viable;
    }

    if (lhs.viable && rhs.viable) {
        size_t compare_count = std::min(lhs.conversions.size(), rhs.conversions.size());
        for (size_t i = 0; i < compare_count; ++i) {
            int lhs_rank = static_cast<int>(lhs.conversions[i].rank);
            int rhs_rank = static_cast<int>(rhs.conversions[i].rank);
            if (lhs_rank != rhs_rank) {
                return lhs_rank < rhs_rank;
            }
            if (lhs.conversions[i].rank == ConversionSequenceRank::ExactMatch) {
                int qualification_order =
                    compare_qualification_conversion_sequences(
                        lhs.conversions[i],
                        rhs.conversions[i],
                        get_active_side_table_ast_context());
                if (qualification_order != 0) {
                    return qualification_order < 0;
                }
                int lhs_subrank = exact_match_subrank(lhs.conversions[i]);
                int rhs_subrank = exact_match_subrank(rhs.conversions[i]);
                if (lhs_subrank != rhs_subrank) {
                    return lhs_subrank < rhs_subrank;
                }
            }
            if (lhs.conversions[i].rank == ConversionSequenceRank::Conversion) {
                int derived_binding_order =
                    compare_derived_to_base_pointer_conversion_sequences(
                        lhs.conversions[i],
                        rhs.conversions[i],
                        get_active_side_table_ast_context());
                if (derived_binding_order != 0) {
                    return derived_binding_order < 0;
                }
                int lhs_tiebreak = conversion_rank_tiebreak(lhs.conversions[i]);
                int rhs_tiebreak = conversion_rank_tiebreak(rhs.conversions[i]);
                if (lhs_tiebreak != rhs_tiebreak) {
                    return lhs_tiebreak < rhs_tiebreak;
                }
            }
        }

        bool lhs_non_variadic = lhs.function_type &&
            lhs.function_type->has_prototype &&
            !lhs.function_type->is_variadic;
        bool rhs_non_variadic = rhs.function_type &&
            rhs.function_type->has_prototype &&
            !rhs.function_type->is_variadic;
        if (lhs_non_variadic != rhs_non_variadic) {
            return lhs_non_variadic && !rhs_non_variadic;
        }

        bool lhs_has_prototype = lhs.function_type && lhs.function_type->has_prototype;
        bool rhs_has_prototype = rhs.function_type && rhs.function_type->has_prototype;
        if (lhs_has_prototype != rhs_has_prototype) {
            return lhs_has_prototype && !rhs_has_prototype;
        }

        bool lhs_is_template_specialization =
            overload_candidate_is_template_specialization(lhs.provenance);
        bool rhs_is_template_specialization =
            overload_candidate_is_template_specialization(rhs.provenance);
        if (lhs_is_template_specialization != rhs_is_template_specialization) {
            return !lhs_is_template_specialization &&
                rhs_is_template_specialization;
        }

        bool lhs_rewritten =
            lhs.operator_rewrite_kind != OverloadOperatorRewriteKind::None;
        bool rhs_rewritten =
            rhs.operator_rewrite_kind != OverloadOperatorRewriteKind::None;
        if (lhs_rewritten != rhs_rewritten) {
            return !lhs_rewritten && rhs_rewritten;
        }
        if (lhs_rewritten && rhs_rewritten &&
            lhs.is_synthesized_reversed_operator_candidate !=
                rhs.is_synthesized_reversed_operator_candidate) {
            return !lhs.is_synthesized_reversed_operator_candidate &&
                rhs.is_synthesized_reversed_operator_candidate;
        }
    } else {
        int lhs_reason_category = overload_failure_category(lhs.failure);
        int rhs_reason_category = overload_failure_category(rhs.failure);
        if (lhs_reason_category != rhs_reason_category) {
            return lhs_reason_category < rhs_reason_category;
        }
        if (lhs_reason_category == 1) {
            size_t lhs_arg_idx = lhs.failure.argument_index;
            size_t rhs_arg_idx = rhs.failure.argument_index;
            if (lhs_arg_idx != rhs_arg_idx) {
                return lhs_arg_idx < rhs_arg_idx;
            }
        }
    }

    std::string lhs_type_name = overload_candidate_type_name(lhs);
    std::string rhs_type_name = overload_candidate_type_name(rhs);
    if (lhs_type_name != rhs_type_name) {
        return lhs_type_name < rhs_type_name;
    }
    return lhs_idx < rhs_idx;
}

void Collect::emit_overload_candidate_notes(
    std::string_view callee_name,
    const OverloadCandidateSet& candidate_set,
    bool include_non_viable,
    SrcLoc loc) const {

    if (!diag_engine_) {
        return;
    }
    std::vector<size_t> note_indices;
    note_indices.reserve(candidate_set.evaluated.size());
    for (size_t idx = 0; idx < candidate_set.evaluated.size(); ++idx) {
        if (!include_non_viable && !candidate_set.evaluated[idx].viable) {
            continue;
        }
        note_indices.push_back(idx);
    }
    std::stable_sort(
        note_indices.begin(),
        note_indices.end(),
        [&](size_t lhs_idx, size_t rhs_idx) {
            return overload_note_order_less(candidate_set, lhs_idx, rhs_idx);
        });
    std::string callee_name_str(callee_name);
    for (size_t idx : note_indices) {
        const auto& candidate = candidate_set.evaluated[idx];
        std::string type_name = overload_candidate_type_name(candidate);
        if (candidate.viable) {
            if (candidate.is_deleted) {
                diag_engine_->report_note(
                    "candidate function '" + callee_name_str + "' has type '" +
                        type_name + "' (deleted)",
                    loc);
                continue;
            }
            diag_engine_->report_note(
                "candidate function '" + callee_name_str + "' has type '" +
                    type_name + "'",
                loc);
            continue;
        }
        std::string reason = overload_failure_reason(candidate.failure);
        diag_engine_->report_note(
            "candidate function '" + callee_name_str + "' has type '" + type_name +
                "' (" + reason + ")",
            loc);
    }
}

bool Collect::is_better_overload_candidate(
    const OverloadCandidateEval& lhs,
    const OverloadCandidateEval& rhs) {
    bool lhs_strictly_better = is_strictly_better_conversion_profile(
        lhs.conversions,
        lhs.function_type,
        rhs.conversions,
        rhs.function_type);
    if (lhs_strictly_better) {
        return true;
    }

    bool rhs_strictly_better = is_strictly_better_conversion_profile(
        rhs.conversions,
        rhs.function_type,
        lhs.conversions,
        lhs.function_type);
    if (rhs_strictly_better) {
        return false;
    }

    bool lhs_is_template_specialization =
        overload_candidate_is_template_specialization(lhs.provenance);
    bool rhs_is_template_specialization =
        overload_candidate_is_template_specialization(rhs.provenance);
    if (lhs_is_template_specialization != rhs_is_template_specialization) {
        return !lhs_is_template_specialization && rhs_is_template_specialization;
    }

    bool lhs_has_constraints =
        lhs.symbol && lhs.symbol->function_trailing_requires_clause;
    bool rhs_has_constraints =
        rhs.symbol && rhs.symbol->function_trailing_requires_clause;
    if (lhs_has_constraints != rhs_has_constraints) {
        return lhs_has_constraints && !rhs_has_constraints;
    }

    if (lhs.provenance ==
            OverloadCandidateProvenance::FunctionTemplateSpecialization &&
        rhs.provenance ==
            OverloadCandidateProvenance::FunctionTemplateSpecialization) {
        auto* lhs_template = function_template_primary_for_symbol(lhs.symbol);
        auto* rhs_template = function_template_primary_for_symbol(rhs.symbol);
        if (lhs_template != rhs_template) {
            auto ordering =
                compare_function_template_partial_ordering(
                    lhs_template,
                    rhs_template);
            if (ordering == TemplatePartialOrderingResult::LhsMoreSpecialized) {
                return true;
            }
            if (ordering == TemplatePartialOrderingResult::RhsMoreSpecialized) {
                return false;
            }
        }
    }

    bool lhs_rewritten =
        lhs.operator_rewrite_kind != OverloadOperatorRewriteKind::None;
    bool rhs_rewritten =
        rhs.operator_rewrite_kind != OverloadOperatorRewriteKind::None;
    if (lhs_rewritten != rhs_rewritten) {
        return !lhs_rewritten && rhs_rewritten;
    }
    if (lhs_rewritten && rhs_rewritten &&
        lhs.is_synthesized_reversed_operator_candidate !=
            rhs.is_synthesized_reversed_operator_candidate) {
        return !lhs.is_synthesized_reversed_operator_candidate &&
            rhs.is_synthesized_reversed_operator_candidate;
    }

    return false;
}

std::optional<size_t> Collect::select_best_overload_candidate_index(
    const OverloadCandidateSet& candidate_set) {

    if (candidate_set.viable_indices.empty()) {
        return std::nullopt;
    }

    std::vector<size_t> frontier;
    frontier.reserve(candidate_set.viable_indices.size());
    for (size_t idx : candidate_set.viable_indices) {
        bool dominated = false;
        for (auto it = frontier.begin(); it != frontier.end();) {
            size_t other = *it;
            bump_overload_pairwise_comparisons();
            bool idx_better = is_better_overload_candidate(
                candidate_set.evaluated[idx],
                candidate_set.evaluated[other]);
            if (idx_better) {
                bump_overload_frontier_prunes();
                it = frontier.erase(it);
                continue;
            }

            bump_overload_pairwise_comparisons();
            bool other_better = is_better_overload_candidate(
                candidate_set.evaluated[other],
                candidate_set.evaluated[idx]);
            if (other_better) {
                dominated = true;
                break;
            }
            ++it;
        }
        if (!dominated) {
            frontier.push_back(idx);
        }
    }

    if (frontier.size() != 1) {
        return std::nullopt;
    }
    return frontier.front();
}

std::unique_ptr<Expr> Collect::resolve_overloaded_call_candidates(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    std::shared_ptr<Symbol>& selected_symbol_out,
    OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) {
    OverloadCandidateSelection selection;
    if (auto error = resolve_overloaded_call_candidates(
            callee_name,
            candidates,
            explicit_args,
            implicit_object_arg,
            loc,
            selection)) {
        return error;
    }
    selected_symbol_out = selection.symbol;
    selected_implicit_object_arg_kind_out =
        selection.implicit_object_arg_kind;
    return nullptr;
}

std::unique_ptr<Expr> Collect::resolve_overloaded_call_candidates(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    OverloadCandidateSelection& selection_out) {
    return resolve_overloaded_call_candidates(
        callee_name,
        candidates,
        make_raw_explicit_args(explicit_args),
        implicit_object_arg,
        loc,
        selection_out);
}

std::unique_ptr<Expr> Collect::resolve_overloaded_call_candidates(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<Expr*>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    std::shared_ptr<Symbol>& selected_symbol_out,
    OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) {
    OverloadCandidateSelection selection;
    if (auto error = resolve_overloaded_call_candidates(
            callee_name,
            candidates,
            explicit_args,
            implicit_object_arg,
            loc,
            selection)) {
        return error;
    }
    selected_symbol_out = selection.symbol;
    selected_implicit_object_arg_kind_out =
        selection.implicit_object_arg_kind;
    return nullptr;
}

std::unique_ptr<Expr> Collect::resolve_overloaded_call_candidates(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<Expr*>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    OverloadCandidateSelection& selection_out) {

    selection_out = OverloadCandidateSelection{};
    if (!lang_opts_.is_cxx_mode() || candidates.empty()) {
        return nullptr;
    }
    bump_overload_resolve_calls();

    OverloadConversionMemoCache conversion_cache;
    conversion_cache.reserve(candidates.size() * 2);

    OverloadCandidateSet candidate_set;
    candidate_set.evaluated.reserve(candidates.size());
    for (const auto& candidate_info : candidates) {
        candidate_set.evaluated.push_back(evaluate_overload_call_candidate(
            candidate_info, explicit_args, implicit_object_arg, &conversion_cache));
    }

    collect_viable_overload_candidates(candidate_set);

    if (candidate_set.viable_indices.empty()) {
        report_error(
            "no matching function for call to '" + std::string(callee_name) + "'",
            loc);
        emit_overload_candidate_notes(callee_name, candidate_set, true, loc);
        return collect_make<ErrorExpr>("no matching overload", loc);
    }

    auto best_index = select_best_overload_candidate_index(candidate_set);
    if (!best_index.has_value()) {
        report_error("call to '" + std::string(callee_name) + "' is ambiguous", loc);
        emit_overload_candidate_notes(callee_name, candidate_set, false, loc);
        return collect_make<ErrorExpr>("ambiguous overload", loc);
    }

    const auto& chosen = candidate_set.evaluated[*best_index];
    if (chosen.is_deleted) {
        report_error(
            "call to deleted function '" + std::string(callee_name) + "'",
            loc);
        emit_overload_candidate_notes(callee_name, candidate_set, false, loc);
        return collect_make<ErrorExpr>("deleted overload", loc);
    }

    selection_out.symbol = chosen.symbol;
    selection_out.implicit_object_arg_kind =
        chosen.implicit_object_arg_kind;
    selection_out.operator_rewrite_kind = chosen.operator_rewrite_kind;
    selection_out.is_synthesized_reversed_operator_candidate =
        chosen.is_synthesized_reversed_operator_candidate;
    return nullptr;
}
