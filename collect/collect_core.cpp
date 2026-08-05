#include "collect.h"
#include "collect_template_state.h"

#include "../perf_stats.h"

#include <cassert>
#include <utility>

namespace aburi::collect {

void Session::mark_generated_abi_entity(cir::EntityId entity,
                                        cir::EntityId owner,
                                        cir::GeneratedSymbolRole role) {
    if (!entity.valid() || !file_.valid(entity)) {
        return;
    }
    cir::Entity& generated = file_.entity_mut(entity);
    generated.abi_identity = cir::AbiIdentityKind::Generated;
    generated.abi_owner = owner;
    generated.generated_symbol_role = role;
    if (owner.valid() && file_.valid(owner)) {
        generated.is_template_pattern =
            file_.entity(owner).is_template_pattern;
    }
}

namespace {

void bump_collect_counter(PerfCounter counter) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(counter);
    }
}

} // namespace

Session::~Session() = default;

void Session::ClosureAbiContextScope::close() {
    if (!session_) {
        return;
    }
    if (!session_->closure_abi_context_stack_.empty()) {
        session_->closure_abi_context_stack_.pop_back();
    }
    session_ = nullptr;
}

Session::ClosureAbiContextScope
Session::enter_variable_initializer_closure_context(
    std::string_view variable_name) {
    ActiveClosureAbiContext context;
    context.kind = cir::ClosureAbiContextKind::VariableInitializer;
    context.name = file_.intern_name(variable_name);
    context.declaration_context = current_decl_context();
    closure_abi_context_stack_.push_back(context);
    return ClosureAbiContextScope(this);
}

Session::Session(LangOptions lang_opts, std::shared_ptr<TargetInfo> target)
    : lang_opts_(std::move(lang_opts)), builder_(file_),
      template_state_(std::make_unique<TemplateState>()) {
    file_.set_target_info(std::move(target));
    builder_.void_type();
    builder_.int_type();
    builder_.usize_type();
    cir::EntityId tu =
        builder_.add_entity(cir::EntityKind::TranslationUnit, "<translation-unit>");
    translation_unit_context_ =
        file_.create_decl_context(cir::DeclContextKind::TranslationUnit, {}, tu);
    file_.entity_mut(tu).lexical_context = translation_unit_context_;
    file_.entity_mut(tu).semantic_context = translation_unit_context_;

    scopes_.push_back({});
    ScopeFrame file_scope;
    file_scope.flags = ScopeFlags::FileScope;
    file_scope.context = translation_unit_context_;
    scopes_.push_back(file_scope);
    current_scope_ = 1;

    if (lang_opts_.is_objc()) {
        initialize_objc_mode();
    }
    if (file_.target_info().va_list_kind == VaListKind::CHAR_PTR) {
        cir::TypeId char_type = file_.builtin_type(cir::BuiltinTypeKind::Char);
        cir::TypeId va_list_type = pointer_type(type_ref(char_type));
        (void)declare_typedef("__builtin_va_list", va_list_type, SrcLoc());
    } else if (file_.target_info().va_list_kind == VaListKind::AARCH64_VA_LIST) {
        (void)declare_typedef("__builtin_va_list", make_aarch64_va_list_type(),
                              SrcLoc());
        declare_sve_builtin_types();
    } else if (file_.target_info().va_list_kind == VaListKind::X86_64_VA_LIST) {
        (void)declare_typedef("__builtin_va_list", make_x86_64_va_list_type(),
                              SrcLoc());
    } else {
        (void)declare_typedef("__builtin_va_list", file_.unknown_type(), SrcLoc());
    }
    file_.mark_prelude();
}

void Session::declare_sve_builtin_types() {
    static const char* const kSveTypeNames[] = {
        "__SVBool_t",     "__SVCount_t",    "__SVInt8_t",
        "__SVInt16_t",    "__SVInt32_t",    "__SVInt64_t",
        "__SVUint8_t",    "__SVUint16_t",   "__SVUint32_t",
        "__SVUint64_t",   "__SVFloat16_t",  "__SVBFloat16_t",
        "__SVFloat32_t",  "__SVFloat64_t",  "__SVMfloat8_t",
    };
    for (const char* name : kSveTypeNames) {
        RecordDeclResult record = create_record_tag(cir::RecordKind::Struct,
                                                    name,
                                                    SrcLoc(),
                                                    /*bind_tag=*/false);
        (void)declare_typedef(name, record.type, SrcLoc());
    }
}

cir::TypeId Session::make_aarch64_va_list_type() {
    RecordDeclResult record = create_record_tag(cir::RecordKind::Struct,
                                                "__va_list",
                                                SrcLoc(),
                                                /*bind_tag=*/false);
    cir::TypeId void_ptr = pointer_type(type_ref(builder_.void_type()));
    cir::TypeId int_type = builder_.int_type();
    struct FieldSpec {
        const char* name;
        cir::TypeId type;
        size_t offset;
    };
    const FieldSpec specs[] = {
        {"__stack", void_ptr, 0},
        {"__gr_top", void_ptr, 8},
        {"__vr_top", void_ptr, 16},
        {"__gr_offs", int_type, 24},
        {"__vr_offs", int_type, 28},
    };
    cir::RecordFacts facts = *file_.record_facts(record.entity);
    for (const FieldSpec& spec : specs) {
        cir::EntityId field = builder_.add_entity(cir::EntityKind::Field,
                                                  spec.name,
                                                  spec.type,
                                                  record.entity,
                                                  SrcLoc());
        cir::RecordFieldFact fact;
        fact.name = file_.intern_name(spec.name);
        fact.entity = field;
        fact.type = file_.type_ref(spec.type);
        fact.offset = spec.offset;
        facts.fields.push_back(std::move(fact));
    }
    facts.is_incomplete = false;
    facts.is_literal_class_type = true;
    facts.size_bits = 256;
    facts.alignment = 8;
    facts.non_virtual_size_bits = 256;
    facts.non_virtual_alignment = 8;
    file_.set_record_facts(record.entity, std::move(facts));
    return record.type;
}

cir::TypeId Session::make_x86_64_va_list_type() {
    RecordDeclResult record = create_record_tag(cir::RecordKind::Struct,
                                                "__va_list_tag",
                                                SrcLoc(),
                                                /*bind_tag=*/false);
    cir::TypeId void_ptr = pointer_type(type_ref(builder_.void_type()));
    cir::TypeId uint_type = file_.builtin_type(cir::BuiltinTypeKind::UInt);
    struct FieldSpec {
        const char* name;
        cir::TypeId type;
        size_t offset;
    };
    const FieldSpec specs[] = {
        {"gp_offset", uint_type, 0},
        {"fp_offset", uint_type, 4},
        {"overflow_arg_area", void_ptr, 8},
        {"reg_save_area", void_ptr, 16},
    };
    cir::RecordFacts facts = *file_.record_facts(record.entity);
    for (const FieldSpec& spec : specs) {
        cir::EntityId field = builder_.add_entity(cir::EntityKind::Field,
                                                  spec.name,
                                                  spec.type,
                                                  record.entity,
                                                  SrcLoc());
        cir::RecordFieldFact fact;
        fact.name = file_.intern_name(spec.name);
        fact.entity = field;
        fact.type = file_.type_ref(spec.type);
        fact.offset = spec.offset;
        facts.fields.push_back(std::move(fact));
    }
    facts.is_incomplete = false;
    facts.is_literal_class_type = true;
    facts.size_bits = 192;
    facts.alignment = 8;
    facts.non_virtual_size_bits = 192;
    facts.non_virtual_alignment = 8;
    file_.set_record_facts(record.entity, std::move(facts));
    return array_type(record.type, size_t{1});
}

cir::File Session::finish_file() {
    drain_weak_pragmas();
    check_deferred_incomplete_tentative_defs();
    return std::move(file_);
}

void Session::report_error(std::string message, SrcLoc loc) {
    file_.add_error(std::move(message), loc);
}

void Session::report_warning(std::string message, SrcLoc loc) {
    file_.add_warning(std::move(message), loc);
}

void Session::report_note(std::string message, SrcLoc loc) {
    file_.add_note(std::move(message), loc);
}

void Session::report_warning(WarningId id, std::string message, SrcLoc loc) {
    DiagnosticSeverity severity = DiagnosticSeverity::Warning;
    if (source_manager_) {
        severity = source_manager_->getDiagnosticState(loc).get(id);
    }
    if (severity == DiagnosticSeverity::Ignored) {
        return;
    }
    if (severity == DiagnosticSeverity::Error) {
        report_error(std::move(message), loc);
        return;
    }
    report_warning(std::move(message), loc);
}

Session::SpeculativeParseGuard::SpeculativeParseGuard(Session& session)
    : session_(&session) {
    session_->begin_speculative_parse();
    depth_ = session_->speculative_snapshots_.size();
}

Session::SpeculativeParseGuard::SpeculativeParseGuard(
    SpeculativeParseGuard&& other) noexcept
    : session_(other.session_), depth_(other.depth_) {
    other.session_ = nullptr;
    other.depth_ = 0;
}

Session::SpeculativeParseGuard::~SpeculativeParseGuard() {
    finish(false);
}

void Session::SpeculativeParseGuard::commit() {
    finish(true);
}

void Session::SpeculativeParseGuard::rollback() {
    finish(false);
}

void Session::SpeculativeParseGuard::finish(bool commit) {
    if (!session_) {
        return;
    }
    assert(session_->speculative_snapshots_.size() == depth_ &&
           "speculative parse guards must finish in LIFO order");
    if (session_->speculative_snapshots_.size() != depth_) {
        return;
    }
    Session* session = session_;
    session_ = nullptr;
    depth_ = 0;
    if (commit) {
        session->commit_speculative_parse();
    } else {
        session->rollback_speculative_parse();
    }
}

Session::SpeculativeParseGuard Session::speculative_parse() {
    return SpeculativeParseGuard(*this);
}

void Session::begin_speculative_parse() {
    bump_collect_counter(PerfCounter::CollectTentativeBegins);
    SpeculativeSnapshot snapshot;
    snapshot.file_transaction = file_.begin_transaction();
    snapshot.builder_checkpoint = builder_.checkpoint();
    snapshot.constraint_environment_revision =
        tstate().constraint_environment_revision_;
    snapshot.scopes_size = scopes_.size();
    snapshot.current_scope = current_scope_;
    snapshot.control_stack = control_stack_;
    snapshot.switch_stack_size = switch_stack_.size();
    snapshot.switch_contexts_size = switch_contexts_.size();
    snapshot.control_flow_regions = control_flow_regions_;
    snapshot.lambda_stack_size = lambda_stack_.size();
    snapshot.lambda_frame_states.reserve(lambda_stack_.size());
    for (const LambdaFrame& frame : lambda_stack_) {
        snapshot.lambda_frame_states.push_back(
            LambdaFrameRollbackState{frame.captures.size(),
                                     frame.capture_memo,
                                     frame.this_capture});
    }
    snapshot.lambda_context_stack_size = lambda_context_stack_.size();
    snapshot.anonymous_record_counter = anonymous_record_counter_;
    snapshot.current_prologue = current_prologue_;
    snapshot.current_result_type = current_result_type_;
    snapshot.current_function = current_function_;
    snapshot.unevaluated_operand_depth = unevaluated_operand_depth_;
    snapshot.typeid_capture_discovery_depth =
        typeid_capture_discovery_depth_;
    snapshot.default_argument_boundary_function =
        default_argument_boundary_function_;
    snapshot.compound_literal_counter = compound_literal_counter_;
    snapshot.global_init_counter = global_init_counter_;
    snapshot.global_init_functions_size = global_init_functions_.size();
    snapshot.function_labels = function_labels_;
    snapshot.local_label_scopes = local_label_scopes_;
    snapshot.pending_orphan_label_blocks = pending_orphan_label_blocks_;
    snapshot.cleanup_scopes = cleanup_scopes_;
    snapshot.eh_cleanup_steps = eh_cleanup_steps_;
    snapshot.destructor_lifecycle_region =
        current_destructor_lifecycle_region_;
    snapshot.lifetime_obligations = lifetime_obligations_;
    snapshot.active_lifetime_boundaries = active_lifetime_boundaries_;
    snapshot.active_try_move_boundaries = active_try_move_boundaries_;
    snapshot.nrvo_return_candidates = nrvo_return_candidates_;
    snapshot.nrvo_has_incompatible_return = nrvo_has_incompatible_return_;
    snapshot.active_catch_handlers = active_catch_handlers_;
    snapshot.active_constructor_function_try_handlers =
        active_constructor_function_try_handlers_;
    snapshot.discarded_statement_validation_depth =
        discarded_statement_validation_depth_;
    snapshot.expansion_label_region_depth =
        expansion_label_region_depth_;
    snapshot.collecting_pattern = collecting_pattern_;
    snapshot.pattern_usable = pattern_usable_;
    snapshot.pattern_taint = pattern_taint_;
    snapshot.member_pattern_active = member_pattern_active_;
    snapshot.member_pattern_taint_start = member_pattern_taint_start_;
    snapshot.member_pattern_holes_start = member_pattern_holes_start_;
    snapshot.member_pattern_events_start = member_pattern_events_start_;
    snapshot.pattern_holes = tstate().pattern_holes_;
    snapshot.pattern_events = pattern_events_;
    snapshot.pattern_members = tstate().pattern_members_;
    snapshot.pattern_holed_locals = tstate().pattern_holed_locals_;
    snapshot.function_parameter_pack_names =
        tstate().function_parameter_pack_names_;
    snapshot.function_parameter_pack_elements =
        tstate().function_parameter_pack_elements_;
    snapshot.function_parameter_pack_template_indices =
        tstate().function_parameter_pack_template_indices_;
    snapshot.function_parameter_pack_scope_stack =
        tstate().function_parameter_pack_scope_stack_;
    snapshot.access_captures_size = access_captures_.size();
    snapshot.active_access_captures_size = active_access_captures_.size();
    snapshot.active_access_obligation_sizes.reserve(
        active_access_captures_.size());
    for (uint32_t capture_index : active_access_captures_) {
        snapshot.active_access_obligation_sizes.push_back(
            capture_index < access_captures_.size()
                ? access_captures_[capture_index].obligations.size()
                : 0);
    }
    speculative_snapshots_.push_back(std::move(snapshot));
}

void Session::commit_speculative_parse() {
    if (speculative_snapshots_.empty()) {
        return;
    }
    bump_collect_counter(PerfCounter::CollectTentativeCommits);
    SpeculativeSnapshot snapshot = std::move(speculative_snapshots_.back());
    speculative_snapshots_.pop_back();
    file_.commit_transaction(snapshot.file_transaction);
    if (!speculative_snapshots_.empty()) {
        auto& outer = speculative_snapshots_.back().memo_rollbacks;
        outer.insert(outer.end(),
                     std::make_move_iterator(snapshot.memo_rollbacks.begin()),
                     std::make_move_iterator(snapshot.memo_rollbacks.end()));
    }
}

void Session::track_speculative_rollback(std::function<void()> undo) {
    track_speculative_rollback("custom speculative state", std::move(undo));
}

void Session::track_speculative_rollback(std::string_view label,
                                         std::function<void()> undo) {
    if (!speculative_snapshots_.empty()) {
        assert(!label.empty() && "rollback journal actions need a label");
        speculative_snapshots_.back().memo_rollbacks.push_back(
            RollbackAction{std::string(label), std::move(undo)});
    }
}

void Session::rollback_speculative_parse() {
    if (speculative_snapshots_.empty()) {
        return;
    }
    bump_collect_counter(PerfCounter::CollectTentativeRollbacks);
    SpeculativeSnapshot snapshot = std::move(speculative_snapshots_.back());
    speculative_snapshots_.pop_back();
    for (auto it = snapshot.memo_rollbacks.rbegin();
         it != snapshot.memo_rollbacks.rend(); ++it) {
        it->undo();
    }
    file_.rollback_transaction(snapshot.file_transaction);
    builder_.rollback_to(snapshot.builder_checkpoint);
    tstate().constraint_environment_revision_ =
        snapshot.constraint_environment_revision;
    scopes_.resize(snapshot.scopes_size);
    current_scope_ = snapshot.current_scope;
    bump_lookup_generation();
    control_stack_ = std::move(snapshot.control_stack);
    switch_stack_.resize(snapshot.switch_stack_size);
    switch_contexts_.resize(snapshot.switch_contexts_size);
    control_flow_regions_ = std::move(snapshot.control_flow_regions);
    while (lambda_context_stack_.size() > snapshot.lambda_context_stack_size) {
        std::unique_ptr<BlockContextState> saved =
            std::move(lambda_context_stack_.back());
        lambda_context_stack_.pop_back();
        restore_function_context(std::move(saved));
    }
    if (lambda_stack_.size() > snapshot.lambda_stack_size) {
        lambda_stack_.resize(snapshot.lambda_stack_size);
    }
    for (size_t i = 0;
         i < lambda_stack_.size() &&
         i < snapshot.lambda_frame_states.size();
         ++i) {
        const LambdaFrameRollbackState& state =
            snapshot.lambda_frame_states[i];
        lambda_stack_[i].captures.resize(state.captures_size);
        lambda_stack_[i].capture_memo = state.capture_memo;
        lambda_stack_[i].this_capture = state.this_capture;
    }
    anonymous_record_counter_ = snapshot.anonymous_record_counter;
    current_prologue_ = std::move(snapshot.current_prologue);
    current_result_type_ = snapshot.current_result_type;
    current_function_ = snapshot.current_function;
    unevaluated_operand_depth_ = snapshot.unevaluated_operand_depth;
    typeid_capture_discovery_depth_ =
        snapshot.typeid_capture_discovery_depth;
    default_argument_boundary_function_ =
        snapshot.default_argument_boundary_function;
    compound_literal_counter_ = snapshot.compound_literal_counter;
    global_init_counter_ = snapshot.global_init_counter;
    if (global_init_functions_.size() >
        snapshot.global_init_functions_size) {
        global_init_functions_.resize(snapshot.global_init_functions_size);
    }
    function_labels_ = std::move(snapshot.function_labels);
    local_label_scopes_ = std::move(snapshot.local_label_scopes);
    pending_orphan_label_blocks_ = std::move(snapshot.pending_orphan_label_blocks);
    cleanup_scopes_ = std::move(snapshot.cleanup_scopes);
    eh_cleanup_steps_ = std::move(snapshot.eh_cleanup_steps);
    current_destructor_lifecycle_region_ =
        std::move(snapshot.destructor_lifecycle_region);
    lifetime_obligations_ = std::move(snapshot.lifetime_obligations);
    active_lifetime_boundaries_ =
        std::move(snapshot.active_lifetime_boundaries);
    active_try_move_boundaries_ =
        std::move(snapshot.active_try_move_boundaries);
    nrvo_return_candidates_ =
        std::move(snapshot.nrvo_return_candidates);
    nrvo_has_incompatible_return_ =
        snapshot.nrvo_has_incompatible_return;
    active_catch_handlers_ = snapshot.active_catch_handlers;
    active_constructor_function_try_handlers_ =
        snapshot.active_constructor_function_try_handlers;
    discarded_statement_validation_depth_ =
        snapshot.discarded_statement_validation_depth;
    expansion_label_region_depth_ =
        snapshot.expansion_label_region_depth;
    collecting_pattern_ = snapshot.collecting_pattern;
    pattern_usable_ = snapshot.pattern_usable;
    pattern_taint_ = snapshot.pattern_taint;
    member_pattern_active_ = snapshot.member_pattern_active;
    member_pattern_taint_start_ = snapshot.member_pattern_taint_start;
    member_pattern_holes_start_ = snapshot.member_pattern_holes_start;
    member_pattern_events_start_ = snapshot.member_pattern_events_start;
    tstate().pattern_holes_ = std::move(snapshot.pattern_holes);
    pattern_events_ = std::move(snapshot.pattern_events);
    tstate().pattern_members_ = std::move(snapshot.pattern_members);
    tstate().pattern_holed_locals_ = std::move(snapshot.pattern_holed_locals);
    tstate().function_parameter_pack_names_ =
        std::move(snapshot.function_parameter_pack_names);
    tstate().function_parameter_pack_elements_ =
        std::move(snapshot.function_parameter_pack_elements);
    tstate().function_parameter_pack_template_indices_ =
        std::move(snapshot.function_parameter_pack_template_indices);
    tstate().function_parameter_pack_scope_stack_ =
        std::move(snapshot.function_parameter_pack_scope_stack);
    for (size_t i = 0;
         i < snapshot.active_access_captures_size &&
         i < active_access_captures_.size() &&
         i < snapshot.active_access_obligation_sizes.size();
         ++i) {
        uint32_t capture_index = active_access_captures_[i];
        if (capture_index < access_captures_.size()) {
            access_captures_[capture_index].obligations.resize(
                snapshot.active_access_obligation_sizes[i]);
        }
    }
    active_access_captures_.resize(
        snapshot.active_access_captures_size);
    access_captures_.resize(snapshot.access_captures_size);
    builder_.set_mark_template_pattern(collecting_pattern_);
}

size_t Session::begin_discarded_statement_validation() {
    ++discarded_statement_validation_depth_;
    return discarded_control_flow_events_.size();
}

void Session::end_discarded_statement_validation() {
    if (discarded_statement_validation_depth_ > 0) {
        --discarded_statement_validation_depth_;
    }
}

void Session::merge_discarded_control_flow_events(size_t event_watermark) {
    if (event_watermark > discarded_control_flow_events_.size()) {
        return;
    }
    for (size_t i = event_watermark;
         i < discarded_control_flow_events_.size(); ++i) {
        const DiscardedControlFlowEvent& event =
            discarded_control_flow_events_[i];
        if (event.declared_local || event.function != current_function_) {
            continue;
        }
        LabelInfo& label = function_label(event.name, event.loc);
        if (event.kind ==
            DiscardedControlFlowEvent::Kind::LabelDefinition) {
            if (!label.defined) {
                label.defined = true;
                label.loc = event.loc;
                label.control_flow_regions = event.control_flow_regions;
            }
            continue;
        }
        label.referenced = true;
        if (label.first_reference.isInvalid()) {
            label.first_reference = event.loc;
        }
        LabelReference reference;
        reference.loc = event.loc;
        reference.control_flow_regions = event.control_flow_regions;
        label.references.push_back(std::move(reference));
    }
    discarded_control_flow_events_.resize(event_watermark);
}

ScopeEnterResult Session::enter_scope(ScopeFlags flags) {
    return enter_scope_impl(flags);
}

ScopeEnterResult Session::enter_record_scope(cir::EntityId record_entity, SrcLoc loc) {
    if (!file_.valid(record_entity)) {
        return enter_scope_impl(ScopeFlags::RecordScope, record_entity, loc);
    }
    cir::DeclContextId record_context = file_.entity(record_entity).semantic_context;
    if (!record_context.valid()) {
        record_context =
            file_.create_decl_context(cir::DeclContextKind::Record,
                                      current_decl_context(),
                                      record_entity,
                                      loc);
        file_.entity_mut(record_entity).semantic_context = record_context;
    }

    cleanup_scopes_.push_back(CleanupScope{control_stack_.size(),
                                           {},
                                           builder_.current_unwind_target()});
    ScopeFrame frame;
    frame.parent = current_scope_;
    frame.flags = ScopeFlags::RecordScope;
    frame.context = record_context;
    scopes_.push_back(frame);
    current_scope_ = static_cast<ScopeId>(scopes_.size() - 1);
    return ScopeEnterResult{current_scope_, true};
}

void Session::set_current_record_pending_bases(
    const std::vector<RecordBaseInput>& bases) {
    if (current_scope_ == InvalidScopeId || current_scope_ >= scopes_.size()) {
        return;
    }
    scopes_[current_scope_].pending_bases = bases;
}

void Session::leave_scope() {
    if (!cleanup_scopes_.empty()) {

        if (cleanup_scopes_.back().suppress_lifetimes) {
            for (const LifetimeRecord& record :
                 cleanup_scopes_.back().lifetime_records) {
                if (record.start.valid()) {
                    file_.inst_mut(record.start).operands = cir::OperandRange{};
                }
            }
        }
        builder_.set_current_unwind_target(
            cleanup_scopes_.back().entry_unwind_target);
        cleanup_scopes_.pop_back();
    }
    if (current_scope_ == InvalidScopeId ||
        current_scope_ >= scopes_.size() ||
        scopes_[current_scope_].parent == InvalidScopeId) {
        return;
    }
    for (const auto& [name, declaration] :
         scopes_[current_scope_].structured_binding_packs) {
        auto elements = tstate().function_parameter_pack_elements_.find(name);
        if (elements != tstate().function_parameter_pack_elements_.end()) {
            for (const FunctionParameterPackElement& element :
                 elements->second) {
                tstate().function_parameter_pack_params_.erase(
                    static_cast<uint64_t>(element.entity.index));
            }
            tstate().function_parameter_pack_elements_.erase(elements);
        }
        tstate().function_parameter_pack_names_.erase(name);
        tstate().function_parameter_pack_params_.erase(
            static_cast<uint64_t>(declaration.index));
    }
    current_scope_ = scopes_[current_scope_].parent;
}

cir::DeclContextId Session::current_decl_context() const {
    if (current_scope_ == InvalidScopeId || current_scope_ >= scopes_.size()) {
        return {};
    }
    return scopes_[current_scope_].context;
}

ScopeId Session::find_enclosing_scope(ScopeFlags flags) const {
    for (ScopeId id = current_scope_;
         id != InvalidScopeId && id < scopes_.size();
         id = scopes_[id].parent) {
        if (scope_flags_contains(scopes_[id].flags, flags)) {
            return id;
        }
    }
    return InvalidScopeId;
}

bool Session::is_file_scope() const {
    ScopeId id = current_scope_;
    while (id != InvalidScopeId &&
           id < scopes_.size() &&
           scope_flags_contains(scopes_[id].flags, ScopeFlags::TemplateParameterScope)) {
        id = scopes_[id].parent;
    }
    return id != InvalidScopeId &&
           id < scopes_.size() &&
           scope_flags_contains(scopes_[id].flags, ScopeFlags::FileScope);
}

void Session::apply_visibility_pragma(bool is_push,
                                      std::string_view value,
                                      SrcLoc loc) {
    if (!is_push) {
        if (!pragma_visibility_stack_.empty()) {
            pragma_visibility_stack_.pop_back();
        }
        return;
    }

    if (value == "internal") {
        pragma_visibility_stack_.push_back("hidden");
    } else if (value == "default" || value == "hidden" || value == "protected") {
        pragma_visibility_stack_.emplace_back(value);
    } else {
        report_error("visibility pragma expects 'default', 'hidden', 'protected', or 'internal'",
                     loc);
    }
}

void Session::apply_pragma_visibility_default(cir::EntityId entity) {
    if (pragma_visibility_stack_.empty() || !entity.valid()) {
        return;
    }
    cir::Entity& record = file_.entity_mut(entity);
    if (!record.attr_facts.visibility.empty()) {
        return;
    }
    record.attr_facts.visibility = pragma_visibility_stack_.back();
}

void Session::begin_scope() {
    enter_scope(ScopeFlags::BlockScope);
    if (collecting_pattern_ && current_function_.valid()) {
        pattern_events_.push_back(
            PatternScopeEvent{PatternScopeEvent::Kind::EnterScope, {}, {}});
    }
}

void Session::end_scope() {
    if (collecting_pattern_ && current_function_.valid()) {
        pattern_events_.push_back(
            PatternScopeEvent{PatternScopeEvent::Kind::LeaveScope, {}, {}});
    }
    leave_scope();
}

ScopeEnterResult Session::enter_scope_impl(ScopeFlags flags,
                                           cir::EntityId owner,
                                           SrcLoc loc) {
    cleanup_scopes_.push_back(CleanupScope{control_stack_.size(),
                                           {},
                                           builder_.current_unwind_target()});
    ScopeFrame frame;
    frame.parent = current_scope_;
    frame.flags = flags;
    frame.context =
        file_.create_decl_context(context_kind_for_scope_flags(flags),
                                  current_decl_context(),
                                  owner,
                                  loc);
    scopes_.push_back(frame);
    current_scope_ = static_cast<ScopeId>(scopes_.size() - 1);
    return ScopeEnterResult{current_scope_, true};
}

cir::DeclContextKind Session::context_kind_for_scope_flags(ScopeFlags flags) const {
    if (scope_flags_contains(flags, ScopeFlags::NamespaceScope)) {
        return cir::DeclContextKind::Namespace;
    }
    if (scope_flags_contains(flags, ScopeFlags::RecordScope)) {
        return cir::DeclContextKind::Record;
    }
    if (scope_flags_contains(flags, ScopeFlags::EnumScope)) {
        return cir::DeclContextKind::Enum;
    }
    if (scope_flags_contains(flags, ScopeFlags::FunctionScope)) {
        return cir::DeclContextKind::Function;
    }
    if (scope_flags_contains(flags, ScopeFlags::PrototypeScope)) {
        return cir::DeclContextKind::Prototype;
    }
    if (scope_flags_contains(flags, ScopeFlags::TemplateParameterScope)) {
        return cir::DeclContextKind::TemplateParameter;
    }
    return cir::DeclContextKind::Block;
}

const cir::Binding* Session::lookup_ordinary_binding(std::string_view name,
                                                     bool include_parents) const {
    const cir::Binding* binding =
        file_.lookup_ordinary_binding(current_decl_context(),
                                      name,
                                      include_parents);
    if (binding || !include_parents) {
        return binding;
    }
    for (ScopeId id = current_scope_;
         id != InvalidScopeId && id < scopes_.size();
         id = scopes_[id].parent) {
        if (!scope_flags_contains(scopes_[id].flags,
                                  ScopeFlags::TemplateParameterScope)) {
            continue;
        }
        binding = file_.lookup_ordinary_binding(scopes_[id].context,
                                                name,
                                                /*include_parents=*/false);
        if (binding) {
            return binding;
        }
    }
    return nullptr;
}

const cir::Binding* Session::lookup_type_name_binding(std::string_view name,
                                                      bool include_parents) const {
    const cir::Binding* binding =
        file_.lookup_type_name_binding(current_decl_context(),
                                       name,
                                       include_parents);
    if (!binding && lang_opts_.is_cxx_mode()) {
        binding = file_.lookup_tag_binding(current_decl_context(),
                                           name,
                                           include_parents);
    }
    if (binding || !include_parents) {
        return binding;
    }
    for (ScopeId id = current_scope_;
         id != InvalidScopeId && id < scopes_.size();
         id = scopes_[id].parent) {
        if (!scope_flags_contains(scopes_[id].flags,
                                  ScopeFlags::TemplateParameterScope)) {
            continue;
        }
        binding = file_.lookup_type_name_binding(scopes_[id].context,
                                                 name,
                                                 /*include_parents=*/false);
        if (!binding && lang_opts_.is_cxx_mode()) {
            binding = file_.lookup_tag_binding(scopes_[id].context,
                                               name,
                                               /*include_parents=*/false);
        }
        if (binding) {
            return binding;
        }
    }
    return nullptr;
}

const cir::Binding*
Session::lookup_template_name_binding(std::string_view name,
                                      bool include_parents) const {
    const cir::Binding* binding =
        file_.lookup_template_name_binding(current_decl_context(),
                                           name,
                                           include_parents);
    if (binding || !include_parents) {
        return binding;
    }
    for (ScopeId id = current_scope_;
         id != InvalidScopeId && id < scopes_.size();
         id = scopes_[id].parent) {
        if (!scope_flags_contains(scopes_[id].flags,
                                  ScopeFlags::TemplateParameterScope)) {
            continue;
        }
        binding = file_.lookup_template_name_binding(scopes_[id].context,
                                                     name,
                                                     /*include_parents=*/false);
        if (binding) {
            return binding;
        }
    }
    return nullptr;
}

const cir::Binding* Session::lookup_tag_binding(std::string_view name,
                                                bool include_parents) const {
    const cir::Binding* binding = file_.lookup_tag_binding(
        current_decl_context(), name, include_parents);
    if ((!binding || binding->entities.empty()) && file_.has_module_units()) {

        cir::File::ModuleVisibilityBypass bypass(file_);
        const cir::Binding* merged = file_.lookup_tag_binding(
            current_decl_context(), name, include_parents);
        if (merged && !merged->entities.empty() &&
            file_.valid(merged->entities.back())) {
            const cir::Entity& candidate =
                file_.entity(merged->entities.back());
            if (!candidate.module_attachment.valid() &&
                candidate.origin_unit.valid()) {
                file_.note_module_entity_redeclared(merged->entities.back());
                binding = merged;
            }
        }
    }
    return binding;
}

void Session::bump_lookup_generation() {
    ++lookup_generation_;
    if (lookup_generation_ == 0) {
        lookup_generation_ = 1;
    }
}

uint64_t Session::current_point_lookup_generation() const {
    if (!active_instantiations_.empty()) {
        return active_instantiations_.back().point_lookup_generation;
    }
    return 0;
}

uint64_t Session::binding_entity_lookup_generation(
    const cir::Binding& binding,
    size_t index) const {
    uint64_t generation = index < binding.entity_generations.size()
        ? binding.entity_generations[index]
        : 0;
    if (generation == 0 && binding.generation != 0) {
        generation = binding.generation;
    }
    return generation;
}

bool Session::binding_entity_visible_at_generation(
    const cir::Binding& binding,
    size_t index,
    uint64_t ceiling) const {
    if (ceiling == 0) {
        return true;
    }
    if (binding_entity_lookup_generation(binding, index) <= ceiling) {
        return true;
    }

    if (index < binding.entities.size()) {
        cir::EntityId candidate = binding.entities[index];
        if (current_function_.valid() && file_.valid(current_function_) &&
            file_.function(current_function_).entity == candidate) {
            return true;
        }
        uint64_t entity_index = static_cast<uint64_t>(candidate.index);
        for (auto it = active_instantiations_.rbegin();
             it != active_instantiations_.rend(); ++it) {
            if (it->template_entity_index != 0) {
                return it->template_entity_index == entity_index;
            }
        }
    }
    return false;
}

void Session::record_member_declaration(cir::EntityId entity,
                                        cir::EntityId owner,
                                        cir::RecordMemberAccess access,
                                        SrcLoc loc) {
    if (!entity.valid() || !file_.valid(entity) || !owner.valid() ||
        !file_.valid(owner) || entity == owner) {
        return;
    }
    cir::Entity& declaration = file_.entity_mut(entity);
    if (declaration.is_record_member) {
        if (declaration.declaring_record == owner &&
            declaration.declared_member_access != access) {
            report_error("member '" +
                             std::string(declaration.name.valid()
                                             ? file_.name(declaration.name)
                                             : std::string_view("<anonymous>")) +
                             "' redeclared with different access",
                         loc);
        }
        return;
    }
    declaration.is_record_member = true;
    declaration.declaring_record = owner;
    declaration.declared_member_access = access;
}

void Session::set_current_record_member_access(
    std::optional<cir::RecordMemberAccess> access) {
    cir::DeclContextId context = current_decl_context();
    if (!context.valid() || !file_.valid(context) ||
        file_.decl_context(context).kind != cir::DeclContextKind::Record) {
        return;
    }
    uint64_t key = static_cast<uint64_t>(context.index);
    if (access.has_value()) {
        record_member_access_by_context_[key] = *access;
    } else {
        record_member_access_by_context_.erase(key);
    }
}

std::optional<cir::RecordMemberAccess>
Session::current_record_member_access() const {
    cir::DeclContextId context = current_decl_context();
    if (!context.valid() || !file_.valid(context) ||
        file_.decl_context(context).kind != cir::DeclContextKind::Record) {
        return std::nullopt;
    }
    auto found = record_member_access_by_context_.find(
        static_cast<uint64_t>(context.index));
    if (found == record_member_access_by_context_.end()) {
        return std::nullopt;
    }
    return found->second;
}

cir::BindingId Session::bind_entity(std::string_view name,
                                    cir::LookupNamespace lookup_namespace,
                                    cir::EntityId entity,
                                    cir::TypeId type,
                                    bool is_type_name,
                                    bool is_template_name,
                                    bool is_definition,
                                    cir::InstId place,
                                    SrcLoc loc) {
    cir::DeclContextId context = current_decl_context();
    if (!context.valid()) {
        return {};
    }
    diagnose_template_parameter_hiding(name, loc, context);
    cir::NameId name_id = file_.intern_name(name);
    cir::TypeRef type_ref = type.valid() ? file_.type_ref(type) : cir::TypeRef{};
    if (lookup_namespace == cir::LookupNamespace::Ordinary &&
        file_.decl_context(context).kind == cir::DeclContextKind::Record &&
        entity.valid() && file_.valid(entity)) {
        cir::EntityId owner = file_.decl_context(context).owner;
        cir::EntityKind entity_kind = file_.entity(entity).kind;
        bool member_declaration_kind =
            entity_kind == cir::EntityKind::TypeAlias ||
            entity_kind == cir::EntityKind::Record ||
            entity_kind == cir::EntityKind::Enum ||
            entity_kind == cir::EntityKind::Enumerator ||
            entity_kind == cir::EntityKind::Field ||
            entity_kind == cir::EntityKind::Method ||
            entity_kind == cir::EntityKind::Constructor ||
            entity_kind == cir::EntityKind::Destructor ||
            (entity_kind == cir::EntityKind::Variable &&
             file_.entity(entity).parent == owner);
        auto active_access = record_member_access_by_context_.find(
            static_cast<uint64_t>(context.index));
        if (active_access != record_member_access_by_context_.end() &&
            member_declaration_kind) {
            record_member_declaration(entity, owner,
                                      active_access->second, loc);
        }
        bool prohibited_member_category =
            entity_kind == cir::EntityKind::TypeAlias ||
            entity_kind == cir::EntityKind::Record ||
            entity_kind == cir::EntityKind::Enum ||
            entity_kind == cir::EntityKind::Enumerator ||
            is_template_name;
        if (prohibited_member_category && owner.valid() &&
            file_.valid(owner) && entity != owner &&
            file_.entity(owner).kind == cir::EntityKind::Record &&
            file_.entity(owner).name.valid() &&
            file_.name(file_.entity(owner).name) == name) {
            report_error("member '" + std::string(name) +
                             "' has the same name as its class",
                         loc);
        }
    }
    cir::BindingId binding =
        file_.bind_entity(context,
                          name_id,
                          lookup_namespace,
                          entity,
                          type_ref,
                          is_type_name,
                          is_template_name,
                          is_definition,
                          place,
                          loc);
    if (binding.valid()) {
        file_.entity_mut(entity).lexical_context = context;

        cir::EntityKind kind = file_.entity(entity).kind;
        if (kind != cir::EntityKind::NamespaceAlias &&
            ((kind != cir::EntityKind::Record &&
              kind != cir::EntityKind::Enum &&
              kind != cir::EntityKind::Namespace) ||
             !file_.entity(entity).semantic_context.valid())) {
            file_.entity_mut(entity).semantic_context = context;
        }
        cir::EntityKind bound_kind = file_.entity(entity).kind;
        if (bound_kind == cir::EntityKind::Variable ||
            bound_kind == cir::EntityKind::Parameter ||
            bound_kind == cir::EntityKind::StructuredBinding) {
            cir::DeclContextId owner_context = context;
            while (owner_context.valid() && file_.valid(owner_context)) {
                const cir::DeclContext& declaration_context =
                    file_.decl_context(owner_context);
                if (declaration_context.kind ==
                    cir::DeclContextKind::Function) {
                    file_.entity_mut(entity).owning_function =
                        declaration_context.owner;
                    break;
                }
                owner_context = declaration_context.parent;
            }
        }
        bump_lookup_generation();
        cir::Binding* record = file_.binding_mut(binding);
        record->generation = lookup_generation_;
        if (!record->entity_generations.empty()) {
            record->entity_generations.back() = lookup_generation_;
        }
    }
    return binding;
}

void Session::diagnose_template_parameter_hiding(std::string_view name,
                                                 SrcLoc loc,
                                                 cir::DeclContextId context) {
    if (name.empty() || !context.valid()) {
        return;
    }
    if (binding_out_of_line_member_head_) {
        return;
    }
    const cir::Binding* hidden_template_parameter =
        file_.lookup_ordinary_binding(context,
                                      name,
                                      /*include_parents=*/true);
    if (hidden_template_parameter &&
        hidden_template_parameter->context != context &&
        file_.valid(hidden_template_parameter->context) &&
        file_.decl_context(hidden_template_parameter->context).kind ==
            cir::DeclContextKind::TemplateParameter) {
        report_error("declaration of '" + std::string(name) +
                         "' shadows template parameter",
                     loc);
    }
}

cir::BlockId Session::begin_fragment_block(std::string_view name) {
    cir::BlockId block = builder_.create_detached_block(name);
    builder_.switch_to_block(block);
    return block;
}

cir::Fragment Session::finish_fragment_block(cir::BlockId block, cir::BlockId previous) {
    cir::Fragment fragment = builder_.block_fragment(block);
    builder_.switch_to_block(previous);
    return fragment;
}

cir::Fragment Session::adopt_or_create_fragment_entry(cir::Fragment fragment, std::string_view name) {
    if (fragment.empty()) {
        cir::BlockId block = builder_.create_detached_block(name);
        return builder_.block_fragment(block);
    }
    builder_.rename_block(fragment.entry, name);
    return fragment;
}

cir::Fragment Session::chain(cir::Fragment first, cir::Fragment second, SrcLoc loc) {
    return builder_.concat(std::move(first), std::move(second), loc);
}

StmtResult Session::make_stmt_result(cir::Fragment fragment,
                                     bool always_returns,
                                     bool has_error) const {
    StmtResult result;
    result.falls_through = fragment.empty() ? true : fragment.falls_through;
    result.always_returns = always_returns;
    result.has_error = has_error;
    result.fragment = std::move(fragment);
    return result;
}

} // namespace aburi::collect
