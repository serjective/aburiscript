#include "collect.h"
#include "../helpers/auto_type_utils.h"
#include "lookup_engine.h"
#include <cassert>
#include <cstdlib>
#include <iostream>

namespace {
struct CollectTentativeMetrics {
    uint64_t tentative_begins = 0;
    uint64_t tentative_commits = 0;
    uint64_t tentative_rollbacks = 0;
    uint64_t snapshot_materializations = 0;
    uint64_t decl_context_clone_roots = 0;
    uint64_t decl_context_nodes_cloned = 0;
    uint64_t scope_nodes_cloned = 0;
};

bool refactor_metrics_enabled() {
    static const bool enabled = []() {
        const char* env = std::getenv("ABURI_REFACTOR_METRICS");
        return env && env[0] != '\0' && env[0] != '0';
    }();
    return enabled;
}

CollectTentativeMetrics& collect_tentative_metrics() {
    static CollectTentativeMetrics metrics;
    return metrics;
}

void emit_collect_tentative_metrics_at_exit() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    const auto& metrics = collect_tentative_metrics();
    std::cerr
        << "[refactor-metrics] collect.tentative "
        << "begins=" << metrics.tentative_begins
        << " commits=" << metrics.tentative_commits
        << " rollbacks=" << metrics.tentative_rollbacks
        << " materializations=" << metrics.snapshot_materializations
        << " clone_roots=" << metrics.decl_context_clone_roots
        << " cloned_context_nodes=" << metrics.decl_context_nodes_cloned
        << " cloned_scope_nodes=" << metrics.scope_nodes_cloned
        << '\n';
}

struct CollectTentativeMetricsReporter {
    ~CollectTentativeMetricsReporter() {
        emit_collect_tentative_metrics_at_exit();
    }
};

CollectTentativeMetricsReporter g_collect_tentative_metrics_reporter;

bool nested_type_matches_equivalent(
    const RecordSemanticState::NestedType& lhs,
    const RecordSemanticState::NestedType& rhs) {
    if (lhs.decl && rhs.decl) {
        return lhs.decl == rhs.decl;
    }
    if (lhs.symbol && rhs.symbol) {
        return lhs.symbol.get() == rhs.symbol.get();
    }
    return lhs.name == rhs.name && lhs.type.equals_qualified(rhs.type);
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

void collect_record_base_nested_type_matches(
    const ObjectDecl* owner_decl,
    const std::string& name,
    std::unordered_set<const ObjectDecl*>& active_stack,
    std::vector<RecordSemanticState::NestedType>& matches) {
    if (!owner_decl || name.empty()) {
        return;
    }
    if (!active_stack.insert(owner_decl).second) {
        return;
    }

    const RecordSemanticState* state = record_semantics_cache_lookup(owner_decl);
    if (!state) {
        active_stack.erase(owner_decl);
        return;
    }

    for (auto it = state->nested_types.rbegin();
         it != state->nested_types.rend();
         ++it) {
        if (it->name != name) {
            continue;
        }
        bool duplicate = false;
        for (const auto& existing_match : matches) {
            if (nested_type_matches_equivalent(existing_match, *it)) {
                duplicate = true;
                break;
            }
        }
        if (!duplicate) {
            matches.push_back(*it);
        }
    }

    auto visit_base = [&](const ObjectDecl* base_decl) {
        if (!base_decl) {
            return;
        }
        collect_record_base_nested_type_matches(
            base_decl,
            name,
            active_stack,
            matches);
    };

    for (const auto& base : state->bases) {
        visit_base(base.record_decl);
    }
    for (const auto& virtual_base : state->virtual_bases) {
        visit_base(virtual_base.record_decl);
    }

    active_stack.erase(owner_decl);
}

void bump_snapshot_materializations() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++collect_tentative_metrics().snapshot_materializations;
}

void bump_tentative_begins() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++collect_tentative_metrics().tentative_begins;
}

void bump_tentative_commits() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++collect_tentative_metrics().tentative_commits;
}

void bump_tentative_rollbacks() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++collect_tentative_metrics().tentative_rollbacks;
}

std::shared_ptr<DeclContext> find_decl_context_in_subtree(
    const std::shared_ptr<DeclContext>& root, const DeclContext* target) {
    if (!root || !target) {
        return nullptr;
    }
    if (root.get() == target) {
        return root;
    }
    for (const auto& child : root->lexical_children()) {
        auto found = find_decl_context_in_subtree(child, target);
        if (found) {
            return found;
        }
    }
    return nullptr;
}

DeclContextKind context_kind_for_scope_flags(ScopeFlags flags) {
    if (scope_flags_contains(flags, ScopeFlags::NamespaceScope)) {
        return DeclContextKind::Namespace;
    }
    if (scope_flags_contains(flags, ScopeFlags::RecordScope)) {
        return DeclContextKind::Record;
    }
    if (scope_flags_contains(flags, ScopeFlags::TemplateParameterScope)) {
        return DeclContextKind::TemplateParameter;
    }
    if (scope_flags_contains(flags, ScopeFlags::FunctionScope)) {
        return DeclContextKind::Function;
    }
    if (scope_flags_contains(flags, ScopeFlags::PrototypeScope)) {
        return DeclContextKind::FunctionPrototype;
    }
    return DeclContextKind::Block;
}

bool lookup_trace_enabled() {
    static const bool enabled = []() {
        const char* env = std::getenv("ABURI_LOOKUP_TRACE");
        return env && env[0] != '\0' && env[0] != '0';
    }();
    return enabled;
}

void emit_lookup_trace(const char* lookup_kind,
                       const std::string& name,
                       const LookupEngine::LookupTrace& trace,
                       bool found) {
    if (!lookup_trace_enabled()) {
        return;
    }
    std::cerr << "[lookup] kind=" << lookup_kind
              << " name=" << name
              << " result=" << (found ? "hit" : "miss") << '\n';
    for (const auto& step : trace.steps) {
        std::cerr << "  " << step << '\n';
    }
}
} // namespace

void Collect::set_lang_options(LangOptions lang_opts) {

    lang_opts_ = lang_opts;
}

void Collect::materialize_tentative_snapshot(TentativeSnapshot& snapshot) {
    if (snapshot.materialized) {
        return;
    }
    bump_snapshot_materializations();
    snapshot.materialized = true;
    snapshot.current_scope = session_.current_scope_;
    snapshot.translation_unit_decl_context = session_.translation_unit_decl_context_;
    snapshot.current_decl_context = session_.current_decl_context_;
    snapshot.current_global_scope_ptr = session_.current_global_scope_;
    snapshot.func_state = session_.func_state_;
    snapshot.current_cpp_record_lookup_type = session_.current_cpp_record_lookup_type_;
    snapshot.function_definition_stack = session_.function_definition_stack_;
}

void Collect::materialize_tentative_snapshot_if_needed() {
    if (session_.tentative_snapshots_.empty()) {
        return;
    }
    bool needs_materialization = false;
    for (const auto& snapshot : session_.tentative_snapshots_) {
        if (!snapshot.materialized) {
            needs_materialization = true;
            break;
        }
    }
    if (!needs_materialization) {
        return;
    }
    for (auto& snapshot : session_.tentative_snapshots_) {
        materialize_tentative_snapshot(snapshot);
    }
}

void Collect::record_decl_context_mutation(
    const std::shared_ptr<DeclContext>& context) {
    if (!context || session_.tentative_snapshots_.empty()) {
        return;
    }
    materialize_tentative_snapshot_if_needed();
    const DeclContext* context_key = context.get();
    for (auto& snapshot : session_.tentative_snapshots_) {
        if (snapshot.decl_context_mutations.contains(context_key)) {
            continue;
        }
        TentativeSnapshot::DeclContextMutationCheckpoint checkpoint;
        checkpoint.context = context;
        checkpoint.declaration_count = context->declaration_count();
        checkpoint.lexical_child_count = context->lexical_child_count();
        checkpoint.namespace_binding_count = context->namespace_binding_count();
        checkpoint.namespace_alias_count = context->namespace_alias_count();
        checkpoint.namespace_nomination_count =
            context->namespace_nomination_count();
        checkpoint.is_inline_namespace = context->is_inline_namespace();
        checkpoint.inline_enclosing_namespace =
            context->inline_enclosing_namespace();
        checkpoint.next_lookup_event_index = context->next_lookup_event_index();
        snapshot.decl_context_mutations.emplace(context_key, std::move(checkpoint));
    }
}

void Collect::record_scope_mutation(const std::shared_ptr<Scope>& scope) {
    if (!scope || session_.tentative_snapshots_.empty()) {
        return;
    }
    materialize_tentative_snapshot_if_needed();
    const Scope* scope_key = scope.get();
    for (auto& snapshot : session_.tentative_snapshots_) {
        if (snapshot.scope_mutations.contains(scope_key)) {
            continue;
        }
        TentativeSnapshot::ScopeMutationCheckpoint checkpoint;
        checkpoint.scope = scope;
        checkpoint.state = *scope;
        snapshot.scope_mutations.emplace(scope_key, std::move(checkpoint));
    }
}

void Collect::record_global_scope_mutation(
    const std::shared_ptr<GlobalIdentTracker>& global_scope) {
    if (!global_scope || session_.tentative_snapshots_.empty()) {
        return;
    }
    materialize_tentative_snapshot_if_needed();
    const GlobalIdentTracker* global_scope_key = global_scope.get();
    for (auto& snapshot : session_.tentative_snapshots_) {
        if (snapshot.global_scope_mutations.contains(global_scope_key)) {
            continue;
        }
        TentativeSnapshot::GlobalScopeMutationCheckpoint checkpoint;
        checkpoint.scope = global_scope;
        checkpoint.all_variables = global_scope->all_variables;
        snapshot.global_scope_mutations.emplace(
            global_scope_key, std::move(checkpoint));
    }
}

void Collect::collect_begin_session_isolation() {
    TentativeSnapshot snapshot;
    session_.tentative_snapshots_.push_back(std::move(snapshot));
}

void Collect::collect_commit_session_isolation() {
    if (session_.tentative_snapshots_.empty()) {
        return;
    }
    session_.tentative_snapshots_.pop_back();
}

void Collect::collect_rollback_session_isolation() {
    if (session_.tentative_snapshots_.empty()) {
        return;
    }
    TentativeSnapshot snapshot = std::move(session_.tentative_snapshots_.back());
    session_.tentative_snapshots_.pop_back();
    if (!snapshot.materialized) {
        return;
    }

    for (auto& entry : snapshot.global_scope_mutations) {
        auto& checkpoint = entry.second;
        if (checkpoint.scope) {
            checkpoint.scope->all_variables = std::move(checkpoint.all_variables);
        }
    }
    for (auto& entry : snapshot.scope_mutations) {
        auto& checkpoint = entry.second;
        if (checkpoint.scope) {
            *checkpoint.scope = std::move(checkpoint.state);
        }
    }
    for (auto& entry : snapshot.decl_context_mutations) {
        auto& checkpoint = entry.second;
        if (!checkpoint.context) {
            continue;
        }
        checkpoint.context->truncate_declarations(checkpoint.declaration_count);
        checkpoint.context->truncate_lexical_children(checkpoint.lexical_child_count);
        checkpoint.context->truncate_namespace_bindings(
            checkpoint.namespace_binding_count);
        checkpoint.context->truncate_namespace_aliases(
            checkpoint.namespace_alias_count);
        checkpoint.context->truncate_namespace_nominations(
            checkpoint.namespace_nomination_count);
        checkpoint.context->set_inline_namespace(
            checkpoint.is_inline_namespace,
            checkpoint.inline_enclosing_namespace);
        checkpoint.context->set_next_lookup_event_index(
            checkpoint.next_lookup_event_index);
    }

    session_.current_scope_ = std::move(snapshot.current_scope);
    session_.translation_unit_decl_context_ = std::move(snapshot.translation_unit_decl_context);
    session_.current_decl_context_ = std::move(snapshot.current_decl_context);
    session_.current_global_scope_ = snapshot.current_global_scope_ptr;
    session_.func_state_ = std::move(snapshot.func_state);
    session_.current_cpp_record_lookup_type_ =
        std::move(snapshot.current_cpp_record_lookup_type);
    session_.function_definition_stack_ = std::move(snapshot.function_definition_stack);
    sync_decl_context_from_current_scope();
}

bool Collect::collect_is_session_isolating() const {
    return !session_.tentative_snapshots_.empty();
}

void Collect::collect_begin_speculative_parse() {
    bump_tentative_begins();
    collect_begin_session_isolation();
    query_context_.begin_tentative_overlay();
}

void Collect::collect_commit_speculative_parse() {
    if (session_.tentative_snapshots_.empty() ||
        !query_context_.has_tentative_overlay()) {
        return;
    }
    bump_tentative_commits();
    query_context_.commit_tentative_overlay(ast_ctx_->semantic_store());
    collect_commit_session_isolation();
}

void Collect::collect_rollback_speculative_parse() {
    if (session_.tentative_snapshots_.empty() ||
        !query_context_.has_tentative_overlay()) {
        return;
    }
    bump_tentative_rollbacks();
    query_context_.rollback_tentative_overlay();
    collect_rollback_session_isolation();
}

bool Collect::collect_is_speculative_parsing() const {
    return query_context_.has_tentative_overlay();
}


void Collect::collect_start_translation_unit() {
    query_context_.clear();

    session_.func_state_.in_function = false;
    session_.current_scope_ = std::make_shared<Scope>();
    session_.translation_unit_decl_context_ =
        DeclContext::create_translation_unit(ast_ctx_);
    session_.current_decl_context_ = session_.translation_unit_decl_context_;
    session_.current_scope_->flags = ScopeFlags::FileScope;
    session_.current_scope_->associated_decl_context = session_.current_decl_context_.get();
    session_.current_global_scope_ = ast_ctx_ ? ast_ctx_->global_tracker : nullptr;
    session_.func_state_.current_function_name.clear();
    session_.func_state_.current_pretty_function_name.clear();
    session_.func_state_.current_function_type = nullptr;
    session_.func_state_.current_function_return_type = nullptr;
    session_.func_state_.current_function_has_return_statement = false;
    session_.func_state_.current_function_has_cxx_auto_return_deduction = false;
    session_.func_state_.current_function_has_deferred_cxx_auto_return_deduction = false;
    session_.func_state_.current_function_cxx_auto_return_pattern = nullptr;
    session_.func_state_.loop_depth = 0;
    session_.func_state_.switch_depth = 0;
    session_.func_state_.delayed_diagnostics.clear();
    session_.func_state_.unevaluated_depth = 0;
    session_.func_state_.unevaluated_context_stack.clear();
    session_.func_state_.constexpr_if_branch_stack.clear();
    session_.func_state_.switch_context_stack.clear();
    session_.func_state_.labels_defined.clear();
    session_.func_state_.labels_referenced.clear();
    session_.func_state_.label_definition_locs.clear();
    session_.func_state_.label_reference_locs.clear();
    session_.func_state_.current_function_is_cpp_member = false;
    session_.func_state_.current_function_is_static_cpp_member = false;
    session_.func_state_.current_function_cpp_this_type = nullptr;
    session_.func_state_.current_function_cpp_friend_access_type = nullptr;
    session_.func_state_.current_function_cpp_access_context_type = nullptr;
    session_.current_cpp_record_lookup_type_ = nullptr;
    session_.tentative_snapshots_.clear();
    session_.function_definition_stack_.clear();
    session_.function_tentative_snapshot_stack_.clear();
    record_semantics_cache_clear(ast_ctx_.get());
    enum_semantics_cache_clear(ast_ctx_.get());
}


std::unique_ptr<TranslationUnit> Collect::collect_finish_translation_unit(std::vector<std::unique_ptr<Decl>> decls, SrcLoc loc) {

    auto tu = collect_make<TranslationUnit>(std::move(decls), loc);

    // Finalize tentative definitions for linkage objects.
    // If a linkage-visible object has at least one non-extern declaration,
    // and its symbol type is an incomplete array, complete it as size 1.
    std::unordered_set<Symbol*> has_non_extern_decl;
    for (auto& d : tu->declarations) {
        auto* var = dyn_cast<VariableDecl>(d.get());
        if (!var || !var->sym) {
            continue;
        }
        if (var->sym->linkage == VariableLinkage::NONE) {
            continue;
        }
        if (var->storage_class != StorageClass::EXTERN) {
            has_non_extern_decl.insert(var->sym.get());
        }
    }

    for (auto& d : tu->declarations) {
        auto* var = dyn_cast<VariableDecl>(d.get());
        if (!var || !var->sym) {
            continue;
        }
        if (var->sym->linkage == VariableLinkage::NONE) {
            continue;
        }
        if (!has_non_extern_decl.contains(var->sym.get())) {
            continue;
        }
        auto sym_arr = var->sym->type.as_shared<ArrayType>();
        if (sym_arr && (sym_arr->size_kind != ArraySizeKind::Constant || !sym_arr->size.has_value())) {
            sym_arr->size_kind = ArraySizeKind::Constant;
            sym_arr->size = 1;
        }
    }

    // Keep declaration node types synchronized with finalized symbol types.
    // Preserve typedef sugar on declaration nodes when possible so AST-level
    // spelling remains explicit, while still propagating finalized tentative
    // array bounds.
    for (auto& d : tu->declarations) {
        auto* var = dyn_cast<VariableDecl>(d.get());
        if (!var || !var->sym) {
            continue;
        }
        if (var->sym->linkage != VariableLinkage::NONE) {
            if (var->type && var->type->kind == TypeKind::Typedef) {
                auto decl_arr =
                    desugar_type(var->type, ast_ctx_.get()).as_shared<ArrayType>();
                auto sym_arr = var->sym->type.as_shared<ArrayType>();
                if (decl_arr && sym_arr) {
                    decl_arr->size_kind = sym_arr->size_kind;
                    decl_arr->size = sym_arr->size;
                    decl_arr->size_expr = sym_arr->size_expr;
                }
                continue;
            }
            var->type = var->sym->type;
        }
    }

    instantiate_pending_required_function_template_specializations();
    flush_delayed_diagnostics();
    return tu;
}


void Collect::collect_start_function_definition(const std::string& name,
                                                QualType function_type,
                                                CppThisContext cpp_this_context) {

    if (session_.func_state_.in_function) {
        session_.function_definition_stack_.push_back(
            capture_current_function_definition_state());
        session_.function_tentative_snapshot_stack_.push_back(
            std::move(session_.tentative_snapshots_));
        session_.tentative_snapshots_.clear();
    }

    session_.func_state_.in_function = true;
    session_.func_state_.current_function_name = name;
    session_.func_state_.current_pretty_function_name = name;
    session_.func_state_.current_function_type = function_type;
    session_.func_state_.current_function_return_type = nullptr;
    session_.func_state_.current_function_has_return_statement = false;
    session_.func_state_.current_function_has_cxx_auto_return_deduction = false;
    session_.func_state_.current_function_has_deferred_cxx_auto_return_deduction = false;
    session_.func_state_.current_function_cxx_auto_return_pattern = nullptr;
    session_.func_state_.current_function_is_cpp_member = cpp_this_context.is_member_function;
    session_.func_state_.current_function_is_static_cpp_member =
        cpp_this_context.is_static_member_function;
    session_.func_state_.current_function_cpp_this_type = cpp_this_context.this_type;
    session_.func_state_.current_function_cpp_friend_access_type =
        cpp_this_context.friend_access_type;
    session_.func_state_.current_function_cpp_access_context_type =
        cpp_this_context.access_context_type;
    if (auto func_ty = function_type.as_shared<FunctionType>()) {
        session_.func_state_.current_function_return_type = func_ty->ret_type;
        if (session_.func_state_.current_function_return_type &&
            auto_type_utils::has_cxx_auto_type(
                session_.func_state_.current_function_return_type.get_shared())) {
            session_.func_state_.current_function_has_cxx_auto_return_deduction = true;
            session_.func_state_.current_function_cxx_auto_return_pattern = session_.func_state_.current_function_return_type;
        }
        std::string pretty;
        pretty += func_ty->ret_type ? func_ty->ret_type.to_string() : "int";
        pretty += " ";
        pretty += name;
        pretty += "(";
        bool printed = false;
        if (func_ty->parameters.size() == 1 &&
            func_ty->parameters[0] &&
            func_ty->parameters[0]->isVoid() &&
            !func_ty->is_variadic) {
            pretty += "void";
            printed = true;
        } else {
            for (size_t i = 0; i < func_ty->parameters.size(); ++i) {
                if (i) pretty += ", ";
                pretty += func_ty->parameters[i].to_string();
                printed = true;
            }
        }
        if (func_ty->is_variadic) {
            if (printed) pretty += ", ";
            pretty += "...";
        }
        pretty += ")";
        session_.func_state_.current_pretty_function_name = std::move(pretty);
    }
    session_.func_state_.loop_depth = 0;
    session_.func_state_.switch_depth = 0;
    session_.func_state_.delayed_diagnostics.clear();
    session_.func_state_.unevaluated_depth = 0;
    session_.func_state_.unevaluated_context_stack.clear();
    session_.func_state_.switch_context_stack.clear();
    session_.func_state_.labels_defined.clear();
    session_.func_state_.labels_referenced.clear();
    session_.func_state_.label_definition_locs.clear();
    session_.func_state_.label_reference_locs.clear();
    session_.tentative_snapshots_.clear();
}


void Collect::collect_finish_function_definition(const std::shared_ptr<Scope>& function_scope) {

    if (session_.func_state_.current_function_has_cxx_auto_return_deduction &&
        session_.func_state_.current_function_return_type &&
        auto_type_utils::has_cxx_auto_type(session_.func_state_.current_function_return_type.get_shared())) {
        if (session_.func_state_.current_function_has_return_statement &&
            session_.func_state_.current_function_has_deferred_cxx_auto_return_deduction) {
            if (auto func_ty = session_.func_state_.current_function_type.as_shared<FunctionType>()) {
                func_ty->ret_type = session_.func_state_.current_function_return_type;
            }
        } else {
            QualType implicit_void(get_builtin_void());
            QualType finalized_return = implicit_void;

            auto deduced = auto_type_utils::extract_auto_placeholder_replacement(
                session_.func_state_.current_function_cxx_auto_return_pattern,
                implicit_void);
            bool can_finalize = deduced.has_value() &&
                deduced->get_shared() &&
                auto_type_utils::auto_type_flavors_in(deduced->get_shared()) == 0;
            if (can_finalize) {
                auto replacement_raw =
                    desugar_type(*deduced, ast_ctx_.get()).get_shared();
                if (replacement_raw) {
                    auto finalized_raw = replace_auto_type(
                        session_.func_state_.current_function_cxx_auto_return_pattern.get_shared(),
                        replacement_raw);
                    finalized_return = QualType(
                        finalized_raw,
                        session_.func_state_.current_function_cxx_auto_return_pattern.get_qualifiers());
                }
            } else {
                report_error(
                    "cannot deduce return type '" +
                        session_.func_state_.current_function_cxx_auto_return_pattern.to_string() +
                        "' for function '" + session_.func_state_.current_function_name +
                        "' with no return statements",
                    SrcLoc());
                auto fallback_raw = replace_auto_type(
                    session_.func_state_.current_function_cxx_auto_return_pattern.get_shared(),
                    implicit_void.get_shared());
                if (fallback_raw) {
                    finalized_return = QualType(
                        fallback_raw,
                        session_.func_state_.current_function_cxx_auto_return_pattern.get_qualifiers());
                }
            }

            session_.func_state_.current_function_return_type = finalized_return;
            if (auto func_ty = session_.func_state_.current_function_type.as_shared<FunctionType>()) {
                func_ty->ret_type = finalized_return;
            }
        }
    }

    auto label_lookup_scope = function_scope
        ? function_scope
        : find_enclosing_scope_with_flags(ScopeFlags::FunctionScope);
    for (const auto& label : session_.func_state_.labels_referenced) {
        if (label_lookup_scope &&
            LookupEngine::lookup_label(label, label_lookup_scope, true)) {
            continue;
        }
        SrcLoc loc;
        auto ref_it = session_.func_state_.label_reference_locs.find(label);
        if (ref_it != session_.func_state_.label_reference_locs.end()) {
            loc = ref_it->second;
        }
        queue_delayed_error("use of undeclared label '" + label + "'", loc);
    }
    flush_delayed_diagnostics();
    session_.tentative_snapshots_.clear();
    if (!session_.function_definition_stack_.empty()) {
        restore_current_function_definition_state(
            std::move(session_.function_definition_stack_.back()));
        session_.function_definition_stack_.pop_back();
        if (!session_.function_tentative_snapshot_stack_.empty()) {
            session_.tentative_snapshots_ =
                std::move(session_.function_tentative_snapshot_stack_.back());
            session_.function_tentative_snapshot_stack_.pop_back();
        }
        return;
    }
    reset_current_function_definition_state();
}


void Collect::collect_abort_function_definition() {

    session_.tentative_snapshots_.clear();
    if (!session_.function_definition_stack_.empty()) {
        restore_current_function_definition_state(
            std::move(session_.function_definition_stack_.back()));
        session_.function_definition_stack_.pop_back();
        if (!session_.function_tentative_snapshot_stack_.empty()) {
            session_.tentative_snapshots_ =
                std::move(session_.function_tentative_snapshot_stack_.back());
            session_.function_tentative_snapshot_stack_.pop_back();
        }
        return;
    }
    reset_current_function_definition_state();
}

bool Collect::collect_is_in_function_definition() const {

    return session_.func_state_.in_function;
}


std::shared_ptr<Scope> Collect::collect_current_scope() const {

    return session_.current_scope_;
}

std::shared_ptr<DeclContext> Collect::get_translation_unit_decl_context() const {

    return session_.translation_unit_decl_context_;
}

std::shared_ptr<DeclContext> Collect::get_current_decl_context() const {

    return session_.current_decl_context_;
}

void Collect::collect_register_namespace_binding(
    const std::shared_ptr<DeclContext>& owner_context,
    NamespaceBindingEntry binding) {

    if (!owner_context) {
        return;
    }
    record_decl_context_mutation(owner_context);
    owner_context->add_namespace_binding(std::move(binding));
}

void Collect::collect_register_namespace_alias(
    const std::shared_ptr<DeclContext>& owner_context,
    NamespaceBindingEntry alias) {

    if (!owner_context) {
        return;
    }
    record_decl_context_mutation(owner_context);
    owner_context->add_namespace_alias(std::move(alias));
}

void Collect::collect_register_namespace_nomination(
    const std::shared_ptr<DeclContext>& owner_context,
    NamespaceNominationRecord nomination) {

    if (!owner_context) {
        return;
    }
    record_decl_context_mutation(owner_context);
    owner_context->add_namespace_nomination(std::move(nomination));
}

void Collect::collect_set_namespace_inline_metadata(
    const std::shared_ptr<DeclContext>& namespace_context,
    bool is_inline,
    DeclContext* enclosing_namespace) {

    if (!namespace_context) {
        return;
    }

    auto target_context = namespace_context;
    if (target_context->primary_context() &&
        target_context->primary_context() != target_context.get()) {
        target_context = target_context->primary_context()->shared_from_this();
    }

    DeclContext* effective_enclosing = is_inline ? enclosing_namespace : nullptr;
    if (target_context->is_inline_namespace() == is_inline &&
        target_context->inline_enclosing_namespace() == effective_enclosing) {
        return;
    }

    record_decl_context_mutation(target_context);
    target_context->set_inline_namespace(is_inline, effective_enclosing);
}

CppThisContext Collect::collect_current_cpp_this_context() const {

    return CppThisContext{
        session_.func_state_.current_function_is_cpp_member,
        session_.func_state_.current_function_is_static_cpp_member,
        session_.func_state_.current_function_cpp_this_type,
        session_.func_state_.current_function_cpp_friend_access_type,
        session_.func_state_.current_function_cpp_access_context_type
    };
}

QualType Collect::collect_current_cpp_record_lookup_type() const {

    return session_.current_cpp_record_lookup_type_;
}

void Collect::collect_set_current_cpp_record_lookup_type(QualType record_type) {

    materialize_tentative_snapshot_if_needed();
    session_.current_cpp_record_lookup_type_ = record_type;
}

bool Collect::with_function_definition_state(
    const FuncDecl* function_decl,
    const std::function<bool()>& action,
    QualType friend_access_type) {
    if (!action) {
        return false;
    }

    auto saved_state = capture_current_function_definition_state();
    QualType saved_record_lookup_type = session_.current_cpp_record_lookup_type_;
    struct FunctionStateGuard {
        Collect* collect = nullptr;
        FunctionDefinitionState saved_state;
        QualType saved_record_lookup_type = nullptr;
        ~FunctionStateGuard() {
            if (collect) {
                collect->restore_current_function_definition_state(
                    std::move(saved_state));
                collect->session_.current_cpp_record_lookup_type_ =
                    saved_record_lookup_type;
            }
        }
    } state_guard{this, std::move(saved_state), saved_record_lookup_type};

    FunctionDefinitionState new_state;
    QualType function_record_lookup_type = nullptr;
    new_state.in_function = function_decl != nullptr;
    new_state.current_function_cpp_friend_access_type = friend_access_type;
    if (function_decl) {
        new_state.current_function_name = function_decl->name;
        new_state.current_pretty_function_name = function_decl->name;
        new_state.current_function_type = QualType(function_decl->type);
        auto function_type =
            QualType(function_decl->type).as_shared<FunctionType>();
        if (function_type) {
            new_state.current_function_return_type = function_type->ret_type;
            if (auto_type_utils::has_cxx_auto_type(
                    function_type->ret_type.get_shared())) {
                new_state.current_function_has_cxx_auto_return_deduction =
                    true;
                new_state.current_function_cxx_auto_return_pattern =
                    function_type->ret_type;
            }
            bool is_cpp_member_function =
                isa<CppMethodDecl>(const_cast<FuncDecl*>(function_decl)) ||
                isa<CppConstructorDecl>(const_cast<FuncDecl*>(function_decl)) ||
                isa<CppDestructorDecl>(const_cast<FuncDecl*>(function_decl));
            bool is_static_cpp_member_function = false;
            if (auto* method = dyn_cast<CppMethodDecl>(
                    const_cast<FuncDecl*>(function_decl))) {
                is_static_cpp_member_function =
                    method->storage_class == StorageClass::STATIC;
            }
            if (is_cpp_member_function) {
                new_state.current_function_is_cpp_member = true;
                new_state.current_function_is_static_cpp_member =
                    is_static_cpp_member_function;
                QualType this_type = nullptr;
                if (!is_static_cpp_member_function &&
                    !function_type->parameters.empty()) {
                    this_type = function_type->parameters.front();
                }
                if (QualType owner_type =
                        get_func_decl_owner_record_type(function_decl)) {
                    function_record_lookup_type = owner_type;
                    uint8_t pointee_quals = QUAL_NONE;
                    if (auto this_ptr = this_type.as_shared<PointerType>()) {
                        pointee_quals = this_ptr->pointed_type.get_qualifiers();
                    }
                    QualType qualified_owner(
                        owner_type.get_shared(),
                        static_cast<uint8_t>(
                            owner_type.get_qualifiers() | pointee_quals));
                    this_type = QualType(
                        std::make_shared<PointerType>(qualified_owner));
                }
                new_state.current_function_cpp_this_type = this_type;
            }
        }
    }

    restore_current_function_definition_state(std::move(new_state));
    session_.current_cpp_record_lookup_type_ = function_record_lookup_type;
    return action();
}

bool Collect::with_cpp_declarator_expression_context(
    CppThisContext cpp_this_context,
    QualType record_lookup_type,
    const std::function<bool()>& action) {
    if (!action) {
        return false;
    }

    auto saved_state = capture_current_function_definition_state();
    QualType saved_record_lookup_type = session_.current_cpp_record_lookup_type_;
    struct FunctionStateGuard {
        Collect* collect = nullptr;
        FunctionDefinitionState saved_state;
        QualType saved_record_lookup_type = nullptr;
        ~FunctionStateGuard() {
            if (!collect) {
                return;
            }
            collect->restore_current_function_definition_state(
                std::move(saved_state));
            collect->session_.current_cpp_record_lookup_type_ =
                saved_record_lookup_type;
        }
    } state_guard{this, std::move(saved_state), saved_record_lookup_type};

    FunctionDefinitionState new_state;
    new_state.in_function = cpp_this_context.is_member_function;
    new_state.current_function_is_cpp_member =
        cpp_this_context.is_member_function;
    new_state.current_function_is_static_cpp_member =
        cpp_this_context.is_static_member_function;
    new_state.current_function_cpp_this_type = cpp_this_context.this_type;
    new_state.current_function_cpp_friend_access_type =
        cpp_this_context.friend_access_type;
    new_state.current_function_cpp_access_context_type =
        cpp_this_context.access_context_type;

    restore_current_function_definition_state(std::move(new_state));
    session_.current_cpp_record_lookup_type_ = record_lookup_type;
    return action();
}

Collect::FunctionDefinitionState
Collect::capture_current_function_definition_state() const {

    return session_.func_state_;
}

void Collect::restore_current_function_definition_state(
    FunctionDefinitionState state) {

    session_.func_state_ = std::move(state);
}

void Collect::reset_current_function_definition_state() {

    restore_current_function_definition_state(FunctionDefinitionState{});
}

CppConstexprIfBranchState Collect::current_constexpr_if_branch_state() const {
    CppConstexprIfBranchState effective = CppConstexprIfBranchState::Active;
    for (CppConstexprIfBranchState state :
         session_.func_state_.constexpr_if_branch_stack) {
        if (state == CppConstexprIfBranchState::Discarded) {
            return CppConstexprIfBranchState::Discarded;
        }
        if (state == CppConstexprIfBranchState::Deferred) {
            effective = CppConstexprIfBranchState::Deferred;
        }
    }
    return effective;
}

bool Collect::current_constexpr_if_branch_suppresses_returns() const {
    return current_constexpr_if_branch_state() !=
           CppConstexprIfBranchState::Active;
}

void Collect::set_current_decl_context(std::shared_ptr<DeclContext> decl_context) {

    materialize_tentative_snapshot_if_needed();
    session_.current_decl_context_ = std::move(decl_context);
    if (session_.current_scope_) {
        session_.current_scope_->associated_decl_context = session_.current_decl_context_.get();
    }
}


void Collect::collect_set_current_scope(std::shared_ptr<Scope> scope) {

    materialize_tentative_snapshot_if_needed();
    session_.current_scope_ = std::move(scope);
    sync_decl_context_from_current_scope();
}

std::shared_ptr<DeclContext> Collect::find_decl_context(const DeclContext* target) const {

    return find_decl_context_in_subtree(session_.translation_unit_decl_context_, target);
}

std::shared_ptr<DeclContext> Collect::resolve_scope_decl_context(const std::shared_ptr<Scope>& scope) const {

    if (!scope) {
        return nullptr;
    }
    for (auto it = scope; it; it = it->parent) {
        if (!it->associated_decl_context) {
            continue;
        }
        auto resolved = find_decl_context(it->associated_decl_context);
        if (resolved) {
            return resolved;
        }
    }
    if (scope.get() == session_.current_scope_.get()) {
        return session_.current_decl_context_;
    }
    return session_.translation_unit_decl_context_;
}

std::shared_ptr<Scope> Collect::find_enclosing_scope_with_flags(ScopeFlags flags) const {

    for (auto scope = session_.current_scope_; scope; scope = scope->parent) {
        if (scope_flags_contains(scope->flags, flags)) {
            return scope;
        }
    }
    return nullptr;
}

void Collect::bind_symbol_in_scope(const std::shared_ptr<Scope>& scope,
                                   const std::string& name,
                                   const std::shared_ptr<Symbol>& sym) {

    if (!scope || name.empty() || !sym) {
        return;
    }
    materialize_tentative_snapshot_if_needed();

    auto context = resolve_scope_decl_context(scope);
    if (!context) {
        return;
    }
    DeclBinding binding;
    binding.name = name;
    binding.lookup_namespace = LookupNamespace::Ordinary;
    binding.symbol_kind = sym->kind;
    binding.storage_class = sym->storage_class;
    binding.linkage = sym->linkage;
    binding.type = sym->type;
    binding.is_definition = (sym->kind == SymbolKind::FUNCTION) ? sym->is_defined : false;
    binding.symbol = sym;
    record_decl_context_mutation(context);
    context->add_declaration(std::move(binding));
}

void Collect::bind_template_decl_in_scope(const std::shared_ptr<Scope>& scope,
                                          const std::string& name,
                                          const Decl* decl,
                                          LookupNamespace lookup_namespace) {

    if (!scope || name.empty() || !decl) {
        return;
    }
    materialize_tentative_snapshot_if_needed();

    auto context = resolve_scope_decl_context(scope);
    if (!context) {
        return;
    }
    DeclBinding binding;
    binding.name = name;
    binding.lookup_namespace = lookup_namespace;
    binding.symbol_kind = SymbolKind::FUNCTION;
    if (lookup_namespace == LookupNamespace::Tag ||
        isa<TemplateTemplateParmDecl>(decl)) {
        binding.symbol_kind = SymbolKind::TYPE;
    } else if (isa<ConceptDecl>(decl)) {
        binding.symbol_kind = SymbolKind::TYPE;
    } else if (isa<VariableTemplateDecl>(decl)) {
        binding.symbol_kind = SymbolKind::VARIABLE;
    }
    binding.ast_decl = decl;
    binding.template_decl = decl;

    record_decl_context_mutation(context);
    context->add_declaration(std::move(binding));
}

void Collect::collect_bind_template_decl(const std::string& name,
                                         const Decl* decl,
                                         LookupNamespace lookup_namespace) {
    bind_template_decl_in_scope(session_.current_scope_, name, decl, lookup_namespace);
}

void Collect::collect_add_function_template_decl(const std::string& name,
                                                 const Decl* decl) {
    collect_bind_template_decl(name, decl, LookupNamespace::Ordinary);
}

void Collect::collect_add_class_template_decl(const std::string& name,
                                              const Decl* decl) {
    collect_bind_template_decl(name, decl, LookupNamespace::Tag);
}

void Collect::collect_add_alias_template_decl(const std::string& name,
                                              const Decl* decl) {
    collect_bind_template_decl(name, decl, LookupNamespace::Ordinary);
}

void Collect::collect_add_variable_template_decl(const std::string& name,
                                                 const Decl* decl) {
    collect_bind_template_decl(name, decl, LookupNamespace::Ordinary);
}

void Collect::collect_add_concept_decl(const std::string& name,
                                       const Decl* decl) {
    collect_bind_template_decl(name, decl, LookupNamespace::Ordinary);
}

void Collect::bind_tag_decl_in_scope(const std::shared_ptr<Scope>& scope,
                                     const std::string& tag,
                                     TagDecl* decl) {

    if (!scope || tag.empty() || !decl) {
        return;
    }
    materialize_tentative_snapshot_if_needed();
    record_scope_mutation(scope);

    auto context = resolve_scope_decl_context(scope);
    if (!context) {
        return;
    }
    DeclBinding binding;
    binding.name = tag;
    binding.lookup_namespace = LookupNamespace::Tag;
    binding.symbol_kind = SymbolKind::TYPE;
    binding.type = decl->get_tag_type();
    binding.is_definition = decl->is_complete_definition();
    binding.ast_decl = decl;
    record_decl_context_mutation(context);
    context->add_declaration(std::move(binding));
}

void Collect::bind_label_in_scope(const std::shared_ptr<Scope>& scope,
                                  const std::string& label,
                                  SrcLoc loc) {

    if (!scope || label.empty()) {
        return;
    }
    materialize_tentative_snapshot_if_needed();
    auto context = resolve_scope_decl_context(scope);
    if (!context) {
        return;
    }
    DeclBinding binding;
    binding.name = label;
    binding.lookup_namespace = LookupNamespace::Label;
    binding.symbol_kind = SymbolKind::VARIABLE;
    binding.type = QualType(get_builtin_void());
    binding.is_definition = true;
    binding.ast_decl = nullptr;
    record_decl_context_mutation(context);
    context->add_declaration(std::move(binding));
    (void)loc;
}

void Collect::sync_decl_context_from_current_scope() {

    if (!session_.current_scope_) {
        session_.current_decl_context_ = nullptr;
        return;
    }
    if (session_.current_scope_->associated_decl_context) {
        auto resolved = find_decl_context(session_.current_scope_->associated_decl_context);
        if (resolved) {
            session_.current_decl_context_ = resolved;
            session_.current_scope_->associated_decl_context = session_.current_decl_context_.get();
            return;
        }
    }
    if (!session_.current_decl_context_) {
        session_.current_decl_context_ = session_.translation_unit_decl_context_;
    }
    session_.current_scope_->associated_decl_context = session_.current_decl_context_.get();
}


bool Collect::collect_is_file_scope() const {
    auto scope = session_.current_scope_;
    while (scope &&
           scope_flags_contains(scope->flags, ScopeFlags::TemplateParameterScope) &&
           scope->parent) {
        scope = scope->parent;
    }
    return scope && scope_flags_contains(scope->flags, ScopeFlags::FileScope);
}


Collect::ScopeEnterResult Collect::collect_enter_scope(std::shared_ptr<Scope> current_scope, std::shared_ptr<Scope> use_scope) const {

    ScopeEnterResult result;
    if (use_scope) {
        result.scope = std::move(use_scope);
        result.created_new = false;
        return result;
    }
    auto new_scope = std::make_shared<Scope>();
    new_scope->parent = std::move(current_scope);
    new_scope->flags = ScopeFlags::BlockScope;
    result.scope = std::move(new_scope);
    result.created_new = true;
    return result;
}

Collect::ScopeEnterResult Collect::collect_enter_scope(ScopeFlags scope_flags, std::shared_ptr<Scope> use_scope) {

    auto result = collect_enter_scope(session_.current_scope_, std::move(use_scope));
    materialize_tentative_snapshot_if_needed();
    session_.current_scope_ = result.scope;
    if (!session_.current_scope_) {
        session_.current_decl_context_ = nullptr;
        return result;
    }
    if (result.created_new) {
        session_.current_scope_->flags = scope_flags;
        auto parent_context = session_.current_decl_context_ ? session_.current_decl_context_
                                                    : session_.translation_unit_decl_context_;
        if (parent_context) {
            record_decl_context_mutation(parent_context);
            auto entered_context = parent_context->add_lexical_child(
                context_kind_for_scope_flags(scope_flags));
            session_.current_decl_context_ = entered_context;
            session_.current_scope_->associated_decl_context = entered_context.get();
        } else {
            session_.current_scope_->associated_decl_context = nullptr;
        }
        return result;
    }

    if (session_.current_scope_->flags == ScopeFlags::None) {
        record_scope_mutation(session_.current_scope_);
        session_.current_scope_->flags = scope_flags;
    }
    sync_decl_context_from_current_scope();
    return result;
}


Collect::ScopeEnterResult Collect::collect_enter_scope(std::shared_ptr<Scope> use_scope) {

    return collect_enter_scope(ScopeFlags::BlockScope, std::move(use_scope));
}


std::shared_ptr<Scope> Collect::collect_leave_scope(std::shared_ptr<Scope> current_scope) const {

    if (!current_scope) {
        return nullptr;
    }
    return current_scope->parent;
}


std::shared_ptr<Scope> Collect::collect_leave_scope() {

    materialize_tentative_snapshot_if_needed();
    session_.current_scope_ = collect_leave_scope(session_.current_scope_);
    sync_decl_context_from_current_scope();
    return session_.current_scope_;
}


std::shared_ptr<Symbol> Collect::collect_lookup_typedef_symbol(const std::string& name, bool look_parents) const {

    if (!session_.current_scope_) {
        return nullptr;
    }
    LookupEngine::LookupTrace trace;
    auto* trace_ptr = lookup_trace_enabled() ? &trace : nullptr;
    auto lookup = LookupEngine::lookup_unqualified_ordinary(
        name, session_.current_scope_, look_parents, LookupEngine::OrdinaryFilter::TypedefOnly, trace_ptr);
    emit_lookup_trace("typedef", name, trace, lookup != nullptr);
    return lookup;
}

QualType Collect::collect_lookup_type_name(const std::string& name,
                                           bool look_parents,
                                           bool include_tag_types) const {

    if (name.empty()) {
        return QualType();
    }
    if (auto typedef_sym = collect_lookup_typedef_symbol(name, look_parents)) {
        return typedef_sym->type;
    }
    if (include_tag_types) {
        if (auto tag_type = collect_lookup_tag_type(name, look_parents)) {
            return QualType(tag_type);
        }
    }
    return QualType();
}


std::shared_ptr<Symbol> Collect::collect_lookup_variable_symbol(const std::string& name, bool look_parents) const {
    return collect_lookup_variable_symbol_result(name, look_parents).symbol;
}

LookupEngine::UnqualifiedOrdinaryLookupResult Collect::collect_lookup_variable_symbol_result(
    const std::string& name,
    bool look_parents) const {

    if (!session_.current_scope_) {
        return {};
    }
    LookupEngine::LookupTrace trace;
    auto* trace_ptr = lookup_trace_enabled() ? &trace : nullptr;
    auto lookup = LookupEngine::lookup_unqualified_ordinary_result(
        name, session_.current_scope_, look_parents, LookupEngine::OrdinaryFilter::Any, trace_ptr);
    emit_lookup_trace("ordinary", name, trace, lookup.found());
    return lookup;
}

TagDecl* Collect::collect_lookup_tag_decl(const std::string& tag, bool look_parents) const {

    if (!session_.current_scope_) {
        return nullptr;
    }
    LookupEngine::LookupTrace trace;
    auto* trace_ptr = lookup_trace_enabled() ? &trace : nullptr;
    auto* lookup = LookupEngine::lookup_tag_decl(tag, session_.current_scope_, look_parents, trace_ptr);
    emit_lookup_trace("tag", tag, trace, lookup != nullptr);
    return lookup;
}


std::shared_ptr<CType> Collect::collect_lookup_tag_type(const std::string& tag, bool look_parents) const {

    LookupEngine::LookupTrace trace;
    auto* trace_ptr = lookup_trace_enabled() ? &trace : nullptr;
    auto lookup = LookupEngine::lookup_tag_type(tag, session_.current_scope_, look_parents, trace_ptr);
    emit_lookup_trace("tag-type", tag, trace, lookup != nullptr);
    return lookup;
}

QualType Collect::collect_lookup_record_nested_type(QualType owner_type,
                                                    const std::string& name) const {
    if (!owner_type || name.empty()) {
        return QualType();
    }

    auto record_type =
        desugar_type(owner_type, ast_ctx_.get()).as_shared<ObjectType>();
    if (!record_type) {
        return QualType();
    }

    auto* owner_decl = dyn_cast<ObjectDecl>(record_type->get_decl());
    if (!owner_decl) {
        return QualType();
    }
    owner_decl = const_cast<ObjectDecl*>(canonical_record_owner_decl(owner_decl));

    const RecordSemanticState* state = record_semantics_cache_lookup(owner_decl);
    if (!state) {
        return QualType();
    }

    for (auto it = state->nested_types.rbegin(); it != state->nested_types.rend(); ++it) {
        if (it->name == name) {
            return it->type;
        }
    }

    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(owner_decl);
    std::vector<RecordSemanticState::NestedType> base_matches;
    auto visit_base = [&](const ObjectDecl* base_decl) {
        if (!base_decl) {
            return;
        }
        collect_record_base_nested_type_matches(
            base_decl,
            name,
            active_stack,
            base_matches);
    };
    for (const auto& base : state->bases) {
        visit_base(base.record_decl);
    }
    for (const auto& virtual_base : state->virtual_bases) {
        visit_base(virtual_base.record_decl);
    }
    if (base_matches.size() == 1) {
        return base_matches.front().type;
    }
    return QualType();
}

std::shared_ptr<Symbol> Collect::collect_lookup_record_enumerator(
    QualType owner_type,
    const std::string& name) const {
    if (!owner_type || name.empty()) {
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

    const RecordSemanticState* state = record_semantics_cache_lookup(owner_decl);
    if (!state) {
        return nullptr;
    }

    for (auto it = state->enumerator_members.rbegin();
         it != state->enumerator_members.rend();
         ++it) {
        if (it->name == name) {
            return it->symbol;
        }
    }
    return nullptr;
}

std::shared_ptr<Symbol> Collect::collect_lookup_enum_enumerator(
    QualType owner_type,
    const std::string& name) const {
    if (!owner_type || name.empty()) {
        return nullptr;
    }

    auto enum_type =
        desugar_type(owner_type, ast_ctx_.get()).as_shared<EnumType>();
    if (!enum_type) {
        return nullptr;
    }

    auto* owner_decl = dyn_cast<EnumDecl>(enum_type->get_decl());
    if (!owner_decl) {
        return nullptr;
    }

    EnumSemanticState state;
    if (!query_lookup_enum_semantics(owner_decl, state)) {
        return nullptr;
    }
    for (auto it = state.enumerators.rbegin();
         it != state.enumerators.rend();
         ++it) {
        if (it->name == name) {
            return it->symbol;
        }
    }
    return nullptr;
}

const RecordSemanticState::NestedTemplate*
Collect::collect_lookup_record_nested_template(QualType owner_type,
                                               const std::string& name) const {
    if (!owner_type || name.empty()) {
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

    const RecordSemanticState* state = record_semantics_cache_lookup(owner_decl);
    if (!state) {
        return nullptr;
    }

    for (auto it = state->nested_templates.rbegin();
         it != state->nested_templates.rend();
         ++it) {
        if (it->name == name) {
            return &(*it);
        }
    }
    return nullptr;
}


void Collect::collect_add_tag_decl(const std::string& tag, TagDecl* decl) {

    if (!session_.current_scope_ || tag.empty() || !decl) {
        return;
    }
    bind_tag_decl_in_scope(session_.current_scope_, tag, decl);
}


void Collect::collect_bind_symbol_in_current_scope(const std::string& name, std::shared_ptr<Symbol> sym) {

    if (!session_.current_scope_ || name.empty() || !sym) {
        return;
    }
    bind_symbol_in_scope(session_.current_scope_, name, sym);
}


void Collect::collect_add_global_symbol(std::shared_ptr<Symbol> sym) {

    if (!session_.current_global_scope_ || !sym) {
        return;
    }
    materialize_tentative_snapshot_if_needed();
    record_global_scope_mutation(session_.current_global_scope_);
    session_.current_global_scope_->add_to_global_scope(std::move(sym));
}


void Collect::collect_enter_loop() {

    materialize_tentative_snapshot_if_needed();
    ++session_.func_state_.loop_depth;
}


void Collect::collect_leave_loop() {

    if (session_.func_state_.loop_depth > 0) {
        materialize_tentative_snapshot_if_needed();
        --session_.func_state_.loop_depth;
    }
}


void Collect::collect_enter_switch() {

    materialize_tentative_snapshot_if_needed();
    session_.func_state_.switch_context_stack.push_back(SwitchContext{});
    ++session_.func_state_.switch_depth;
}


void Collect::collect_leave_switch() {

    if (!session_.func_state_.switch_context_stack.empty() || session_.func_state_.switch_depth > 0) {
        materialize_tentative_snapshot_if_needed();
    }
    if (!session_.func_state_.switch_context_stack.empty()) {
        session_.func_state_.switch_context_stack.pop_back();
    }
    if (session_.func_state_.switch_depth > 0) {
        --session_.func_state_.switch_depth;
    }
}


void Collect::collect_register_label_definition(const std::string& label, SrcLoc loc) {

    auto function_scope = find_enclosing_scope_with_flags(ScopeFlags::FunctionScope);
    if (function_scope &&
        LookupEngine::lookup_label(label, function_scope, false)) {
        report_error("redefinition of label '" + label + "'", loc);
        return;
    }
    materialize_tentative_snapshot_if_needed();
    session_.func_state_.labels_defined.insert(label);
    if (!loc.isInvalid()) {
        session_.func_state_.label_definition_locs[label] = loc;
    }
    if (function_scope) {
        bind_label_in_scope(function_scope, label, loc);
    }
}


void Collect::collect_register_label_reference(const std::string& label, SrcLoc loc) {

    materialize_tentative_snapshot_if_needed();
    session_.func_state_.labels_referenced.insert(label);
    if (!loc.isInvalid() && !session_.func_state_.label_reference_locs.contains(label)) {
        session_.func_state_.label_reference_locs[label] = loc;
    }
}
