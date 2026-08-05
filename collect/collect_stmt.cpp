#include "collect.h"

#include "../asm_constraints.h"
#include "../constexpr/consteval_engine.h"
#include "../cir/layout.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <sstream>
#include <unordered_set>
#include <utility>
#include <vector>

namespace aburi::collect {

namespace {

void append_fragment_blocks(cir::Fragment& target, const cir::Fragment& source) {
    if (source.empty()) {
        return;
    }
    if (target.empty()) {
        target.entry = source.entry;
    }
    target.blocks.insert(target.blocks.end(), source.blocks.begin(), source.blocks.end());
    target.exit = source.exit;
}

bool is_integer_like_switch_type(const cir::File& file, cir::TypeId type) {
    if (!file.valid(type)) {
        return false;
    }
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return false;
    }
    if (file.type(resolved).kind == cir::TypeKind::Enum) {
        return true;
    }
    cir::OperatorValueDomain domain = file.operator_value_domain(file.type_ref(resolved));
    return domain == cir::OperatorValueDomain::Bool ||
           domain == cir::OperatorValueDomain::SignedInteger ||
           domain == cir::OperatorValueDomain::UnsignedInteger;
}

int64_t convert_case_value_to_switch_type(const cir::File& file,
                                          cir::TypeId type,
                                          int64_t value) {
    cir::IntegerTypeShape shape = cir::integer_shape_for_type(file, type);
    if (shape.bit_width == 0 || shape.bit_width >= 64) {
        return value;
    }

    uint64_t mask = (uint64_t{1} << shape.bit_width) - 1;
    uint64_t raw = static_cast<uint64_t>(value) & mask;
    cir::OperatorValueDomain domain =
        file.operator_value_domain(file.type_ref(type));
    if (domain == cir::OperatorValueDomain::SignedInteger) {
        uint64_t sign_bit = uint64_t{1} << (shape.bit_width - 1);
        if ((raw & sign_bit) != 0) {
            raw |= ~mask;
        }
    }
    return static_cast<int64_t>(raw);
}

std::string asm_clobber_constraint(std::string_view clobber) {
    return "~{" + std::string(clobber) + "}";
}

bool asm_constraint_uses_memory_operand(std::string_view constraint) {
    return constraint.find('m') != std::string_view::npos;
}

bool asm_input_requires_memory_place(std::string_view constraint,
                                     TargetArch arch) {
    bool has_memory = false;
    bool has_other = false;
    for (char ch : constraint) {
        switch (ch) {
            case '=': case '+': case '&': case '%': case '#': case '*':
            case ' ':
                continue;
            default:
                break;
        }
        if (aburi::classify_asm_letter(arch, ch) == AsmLetterClass::Memory) {
            has_memory = true;
        } else {

            has_other = true;
        }
    }
    return has_memory && !has_other;
}

bool asm_constraint_prefers_immediate_operand(std::string_view constraint) {
    return constraint.find('i') != std::string_view::npos ||
           constraint.find('n') != std::string_view::npos;
}

bool asm_constraint_requires_immediate_operand(std::string_view constraint) {
    bool has_immediate = false;
    bool has_non_immediate_alternative = false;
    for (char ch : constraint) {
        if (ch == 'i' || ch == 'n') {
            has_immediate = true;
            continue;
        }
        if (ch == 'r' || ch == 'm' || ch == 'p' || ch == 'o' || ch == 'V' ||
            std::isdigit(static_cast<unsigned char>(ch))) {
            has_non_immediate_alternative = true;
        }
    }
    return has_immediate && !has_non_immediate_alternative;
}

void append_joined_constraint(std::ostringstream& out,
                              bool& first,
                              std::string_view constraint) {
    if (!first) {
        out << ',';
    }
    first = false;
    out << constraint;
}

std::string preview_asm_constraints(const cir::InlineAsmPayload& payload) {
    std::ostringstream out;
    bool first = true;
    bool has_template_text =
        payload.asm_string.find_first_not_of(" \t\r\n") != std::string::npos;
    bool needs_implicit_memory_clobber = false;
    bool has_memory_clobber = false;
    std::vector<bool> skipped_memory_output(payload.outputs.size(), false);
    for (const cir::InlineAsmOperandPayload& output : payload.outputs) {
        std::string constraint = output.constraint;
        if (!has_template_text && asm_constraint_uses_memory_operand(constraint)) {
            needs_implicit_memory_clobber = true;
            skipped_memory_output[&output - payload.outputs.data()] = true;
            continue;
        }
        if (!constraint.empty() && constraint[0] == '+') {
            constraint[0] = '=';
        }
        append_joined_constraint(out, first, constraint);
    }
    for (const cir::InlineAsmOperandPayload& input : payload.inputs) {
        append_joined_constraint(out, first, input.constraint);
    }
    for (size_t index = 0; index < payload.outputs.size(); ++index) {
        const cir::InlineAsmOperandPayload& output = payload.outputs[index];
        if (skipped_memory_output[index]) {
            continue;
        }
        if (!output.constraint.empty() && output.constraint[0] == '+') {
            append_joined_constraint(out, first, std::to_string(index));
        }
    }
    for (size_t index = 0; index < payload.goto_labels.size(); ++index) {
        (void)index;
        append_joined_constraint(out, first, "!i");
    }
    for (const std::string& clobber : payload.clobbers) {
        if (clobber == "memory") {
            has_memory_clobber = true;
        }
        append_joined_constraint(out, first, asm_clobber_constraint(clobber));
    }
    if (needs_implicit_memory_clobber && !has_memory_clobber) {
        append_joined_constraint(out, first, asm_clobber_constraint("memory"));
    }
    return out.str();
}

} // namespace

StmtResult Session::collect_decl_stmt(DeclResult decl, SrcLoc loc) {
    (void)loc;
    return make_stmt_result(std::move(decl.fragment), false, decl.has_error);
}

StmtResult Session::collect_expr_stmt(ExprResult expr,
                                      SrcLoc loc,
                                      const FullExpressionWatermark* mark) {
    if (expr.nodiscard_callee.valid()) {
        const cir::Entity& callee = file_.entity(expr.nodiscard_callee);
        std::string callee_name =
            callee.name.valid() ? file_.name(callee.name) : "<function>";
        report_warning("ignoring return value of '" + callee_name +
                           "' declared with attribute 'nodiscard'",
                       loc);
    }
    if (expr.category != ValueCategory::LValue &&
        expr.category != ValueCategory::XValue) {
        expr = require_value(std::move(expr), UseContext::Discard, loc);
    }
    if (arc_enabled() && expr.arc_plus_one) {

        expr = arc_release_discarded(std::move(expr), loc);
    }

    bool transfers_control = expr.fragment.exit.valid() &&
        file_.valid(expr.fragment.exit) &&
        file_.block(expr.fragment.exit).terminator.kind !=
            cir::TerminatorKind::Invalid;
    if (mark) {
        if (!transfers_control) {
            cir::Fragment cleanup = finish_lifetime_boundary(*mark, loc);
            expr.fragment =
                chain(std::move(expr.fragment), std::move(cleanup), loc);
        } else {
            close_lifetime_boundary_without_cleanup(*mark);
        }
    }
    StmtResult result = make_stmt_result(expr.fragment, false, expr.has_error);
    result.result_expr = std::move(expr);
    return result;
}

Session::LifetimeBoundary Session::begin_lifetime_boundary() {
    LifetimeBoundary mark;

    if (!lang_opts_.is_cxx_mode() && !arc_enabled()) {
        return mark;
    }
    if (cleanup_scopes_.empty()) {
        // Namespace-scope constant-expression declarations have no lexical
        // cleanup scope, but their full-expression temporaries still require
        // destruction before evaluation completes.
        cleanup_scopes_.push_back(CleanupScope{
            control_stack_.size(),
            {},
            builder_.current_unwind_target()});
        mark.owns_cleanup_scope = true;
    }
    mark.active = true;
    mark.id = next_lifetime_boundary_id_++;
    mark.scope_depth = cleanup_scopes_.size();
    active_lifetime_boundaries_.push_back(mark.id);
    return mark;
}

void Session::close_lifetime_boundary_without_cleanup(
    const LifetimeBoundary& mark) {
    if (!mark.active) {
        return;
    }
    auto found = std::find(active_lifetime_boundaries_.begin(),
                           active_lifetime_boundaries_.end(), mark.id);
    if (found != active_lifetime_boundaries_.end()) {
        active_lifetime_boundaries_.erase(found);
    }
    arc_drop_boundary_releases(mark.id);
    if (mark.owns_cleanup_scope && !cleanup_scopes_.empty()) {
        builder_.set_current_unwind_target(
            cleanup_scopes_.back().entry_unwind_target);
        cleanup_scopes_.pop_back();
    }
}

void Session::discard_lifetime_boundary(const LifetimeBoundary& mark) {
    if (!mark.active) {
        return;
    }
    close_lifetime_boundary_without_cleanup(mark);
    std::vector<cir::LifetimeId> discarded;
    for (const LifetimeObligation& obligation : lifetime_obligations_) {
        if (obligation.owner == LifetimeOwnerKind::FullExpression &&
            obligation.owner_id == mark.id) {
            discarded.push_back(obligation.id);
        }
    }
    for (cir::LifetimeId lifetime : discarded) {
        retire_lifetime(lifetime);
    }
}

cir::Fragment Session::extend_lifetime_boundary_to_scope(
    const LifetimeBoundary& mark,
    SrcLoc loc) {
    if (!mark.active) {
        return {};
    }

    std::vector<cir::LifetimeId> extended;
    for (const LifetimeObligation& obligation : lifetime_obligations_) {
        if (obligation.owner != LifetimeOwnerKind::FullExpression ||
            obligation.owner_id != mark.id ||
            !obligation.entity.valid() ||
            !file_.valid(obligation.entity) ||
            file_.entity(obligation.entity).is_parameter_argument_object) {
            continue;
        }
        extended.push_back(obligation.id);
    }
    for (cir::LifetimeId lifetime : extended) {
        transfer_lifetime(lifetime, LifetimeOwnerKind::LexicalScope);
    }

    return finish_lifetime_boundary(mark, loc);
}

cir::Fragment Session::finish_lifetime_boundary(
    const LifetimeBoundary& mark,
    SrcLoc loc) {
    cir::Fragment fragment;
    if (!mark.active) {
        return fragment;
    }
    auto active = std::find(active_lifetime_boundaries_.begin(),
                            active_lifetime_boundaries_.end(), mark.id);
    if (active != active_lifetime_boundaries_.end()) {
        active_lifetime_boundaries_.erase(active);
    }
    if (cleanup_scopes_.size() < mark.scope_depth) {

        for (CleanupScope& scope : cleanup_scopes_) {
            for (CleanupRecord& record : scope.records) {
                if (record.owner == LifetimeOwnerKind::FullExpression &&
                    record.owner_id == mark.id) {
                    transfer_lifetime(record.lifetime,
                                      LifetimeOwnerKind::LexicalScope);
                }
            }
        }
        for (const LifetimeObligation& obligation : lifetime_obligations_) {
            if (obligation.owner == LifetimeOwnerKind::FullExpression &&
                obligation.owner_id == mark.id) {
                transfer_lifetime(obligation.id,
                                  LifetimeOwnerKind::LexicalScope);
            }
        }
        arc_drop_boundary_releases(mark.id);
        return fragment;
    }

    std::vector<CleanupRecord> temporaries;
    for (size_t i = cleanup_scopes_.size(); i-- > 0;) {
        const CleanupScope& scope = cleanup_scopes_[i];
        for (size_t j = scope.records.size(); j-- > 0;) {
            const CleanupRecord& record = scope.records[j];
            if (record.owner == LifetimeOwnerKind::FullExpression &&
                record.owner_id == mark.id) {
                temporaries.push_back(record);
            }
        }
    }
    std::vector<cir::LifetimeId> boundary_lifetimes;
    for (const LifetimeObligation& obligation : lifetime_obligations_) {
        if (obligation.owner == LifetimeOwnerKind::FullExpression &&
            obligation.owner_id == mark.id) {
            boundary_lifetimes.push_back(obligation.id);
        }
    }
    fragment = emit_normal_cleanup_records(temporaries, loc);
    for (cir::LifetimeId lifetime : boundary_lifetimes) {
        retire_lifetime(lifetime);
    }
    fragment = chain(std::move(fragment),
                     arc_flush_boundary_releases(mark.id, loc), loc);
    if (mark.owns_cleanup_scope && !cleanup_scopes_.empty()) {
        builder_.set_current_unwind_target(
            cleanup_scopes_.back().entry_unwind_target);
        cleanup_scopes_.pop_back();
    }
    return fragment;
}

cir::Fragment Session::emit_normal_cleanup_records(
    const std::vector<CleanupRecord>& records,
    SrcLoc loc,
    cir::EntityId nrvo_candidate,
    std::vector<cir::InstId>* nrvo_cleanups) {
    cir::Fragment fragment;
    for (const CleanupRecord& record : records) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId saved_target = builder_.current_unwind_target();
        builder_.set_current_unwind_target(record.normal_unwind_target);
        cir::BlockId block = begin_fragment_block("cleanup.normal");
        cir::InstId place =
            builder_.local_place(record.variable, record.variable_type, loc);
        cir::InstId addr = builder_.addr_of(place, loc);
        cir::TypeId result_type = builder_.void_type();
        cir::TypeId fn_type =
            file_.resolved_type(file_.entity(record.function).type);
        if (const auto* fn_payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(fn_type))) {
            result_type = fn_payload->return_type.type;
        }
        cir::InstId cleanup =
            builder_.call(record.function, result_type, {addr}, loc);
        cir::Fragment one = finish_fragment_block(block, previous);
        builder_.set_current_unwind_target(saved_target);
        fragment = chain(std::move(fragment), std::move(one), loc);
        if (nrvo_cleanups && record.variable == nrvo_candidate) {
            nrvo_cleanups->push_back(cleanup);
        }
    }
    return fragment;
}

cir::Fragment Session::emit_cleanup_calls_from_depth(
    size_t min_control_depth,
    SrcLoc loc,
    cir::EntityId nrvo_candidate,
    std::vector<cir::InstId>* nrvo_cleanups) {
    std::vector<CleanupRecord> records;
    for (size_t i = cleanup_scopes_.size(); i-- > 0;) {
        const CleanupScope& scope = cleanup_scopes_[i];
        if (scope.control_depth_at_entry < min_control_depth) {
            continue;
        }
        for (size_t j = scope.records.size(); j-- > 0;) {
            records.push_back(scope.records[j]);
        }
    }
    return emit_normal_cleanup_records(records, loc, nrvo_candidate,
                                       nrvo_cleanups);
}

void Session::finalize_nrvo_for_current_function() {
    if (nrvo_has_incompatible_return_ || nrvo_return_candidates_.empty()) {
        return;
    }
    cir::EntityId candidate = nrvo_return_candidates_.front().source;
    if (!candidate.valid() || !file_.valid(candidate) ||
        std::any_of(nrvo_return_candidates_.begin(),
                    nrvo_return_candidates_.end(),
                    [&](const NrvoReturnCandidate& item) {
                        return item.source != candidate;
                    })) {
        return;
    }

    cir::Entity& entity = file_.entity_mut(candidate);
    entity.object_storage_alias = {};
    entity.object_storage_alias_place = {};
    entity.is_function_result_object = true;
    for (const NrvoReturnCandidate& item : nrvo_return_candidates_) {
        if (item.transfer.valid() && file_.valid(item.transfer)) {
            file_.inst_mut(item.transfer)
                .runtime_elided_object_operation = true;
        }
        for (cir::InstId cleanup : item.normal_cleanups) {
            if (cleanup.valid() && file_.valid(cleanup)) {
                file_.inst_mut(cleanup)
                    .runtime_elided_object_operation = true;
            }
        }
    }
}

void Session::emit_active_catch_ends(SrcLoc loc) {
    for (uint32_t index = 0; index < active_catch_handlers_; ++index) {
        builder_.catch_end(loc);
    }
}

void Session::note_local_lifetime_start(cir::EntityId entity,
                                        cir::TypeId type,
                                        cir::InstId place,
                                        const DeclFlags& flags,
                                        SrcLoc loc) {
    if (cleanup_scopes_.empty() || !current_function_.valid()) {
        return;
    }

    cir::TypeId resolved_type = file_.resolved_type(type);
    const auto* array = file_.valid(resolved_type) &&
            file_.type(resolved_type).kind == cir::TypeKind::Array
        ? std::get_if<cir::ArrayTypePayload>(
              &file_.type_payload(resolved_type))
        : nullptr;
    bool bound_completes_after_place =
        array && array->size_kind == cir::ArraySizeKind::Incomplete;
    if (flags.is_static || flags.is_thread_local || flags.is_extern ||
        flags.is_block_byref || !flags.asm_label.empty() ||
        bound_completes_after_place ||
        is_dependent_type(type) || variably_modified_type(type) ||
        is_reference_type(type) || statement_expr_depth_ > 0) {
        return;
    }
    CleanupScope& scope = cleanup_scopes_.back();
    cir::InstId start = builder_.lifetime_start(place, loc);
    scope.lifetime_records.push_back(LifetimeRecord{start, entity, type});
}

void Session::suppress_open_scope_lifetimes() {
    for (CleanupScope& scope : cleanup_scopes_) {
        scope.suppress_lifetimes = true;
    }
}

StmtResult Session::collect_scope_cleanups(SrcLoc loc) {
    if (cleanup_scopes_.empty()) {
        return StmtResult{};
    }
    const CleanupScope& scope = cleanup_scopes_.back();
    bool emit_lifetime_ends =
        !scope.suppress_lifetimes && !scope.lifetime_records.empty();
    if (scope.records.empty() && !emit_lifetime_ends) {
        return StmtResult{};
    }
    std::vector<CleanupRecord> records;
    records.reserve(scope.records.size());
    for (size_t j = scope.records.size(); j-- > 0;) {
        records.push_back(scope.records[j]);
    }
    cir::Fragment fragment = emit_normal_cleanup_records(records, loc);
    if (emit_lifetime_ends) {

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("scope.lifetime.end");
        for (size_t j = scope.lifetime_records.size(); j-- > 0;) {
            const LifetimeRecord& record = scope.lifetime_records[j];
            cir::InstId place =
                builder_.local_place(record.variable, record.variable_type, loc);
            builder_.lifetime_end(place, loc);
        }
        fragment = chain(std::move(fragment),
                         finish_fragment_block(block, previous), loc);
    }
    StmtResult result = make_stmt_result(std::move(fragment), false, false);
    result.preserves_result_expr = true;
    return result;
}

StmtResult Session::collect_return_stmt(std::optional<ExprResult> expr,
                                        SrcLoc loc,
                                        LifetimeBoundary boundary) {

    if (coroutine_state_) {
        report_error(
            "a coroutine cannot contain a plain 'return' statement; use "
            "'co_return'",
            loc);
        if (expr) {
            expr->has_error = true;
        }
    } else if (!has_plain_return_) {
        has_plain_return_ = true;
        first_plain_return_loc_ = loc;
    }
    bool forbidden_constructor_handler_return =
        active_constructor_function_try_handlers_ > 0;
    if (forbidden_constructor_handler_return) {
        report_error("return statement is not allowed in a constructor "
                     "function-try handler",
                     loc);
        if (expr) {
            expr->has_error = true;
        }
    }
    if (deduce_return_type_) {
        bool deferred_pattern_candidate = false;
        bool deduced = record_placeholder_return(
            expr.has_value() ? &*expr : nullptr, loc,
            &deferred_pattern_candidate);
        if (!deduced && expr.has_value()) {
            expr->has_error = true;
        } else if (!deduced) {
            cir::Fragment operand_cleanup =
                finish_lifetime_boundary(boundary, loc);
            cir::Fragment function_cleanup =
                emit_cleanup_calls_from_depth(0, loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("stmt.return.error");
            builder_.unreachable(loc);
            cir::Fragment fragment = chain(
                std::move(operand_cleanup), std::move(function_cleanup), loc);
            fragment = chain(std::move(fragment),
                             finish_fragment_block(block, previous), loc);
            return make_stmt_result(std::move(fragment), true, true);
        }
        if (deferred_pattern_candidate) {

            cir::Fragment fragment;
            if (expr.has_value()) {
                fragment = std::move(expr->fragment);
            }
            fragment = chain(std::move(fragment),
                             finish_lifetime_boundary(boundary, loc), loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("stmt.return.pattern.deferred");
            builder_.unreachable(loc);
            fragment = chain(std::move(fragment),
                             finish_fragment_block(block, previous), loc);
            return make_stmt_result(
                std::move(fragment), true,
                expr.has_value() && expr->has_error);
        }
        if (in_discarded_statement_validation()) {
            cir::Fragment fragment;
            if (expr.has_value()) {
                fragment = std::move(expr->fragment);
            }
            fragment = chain(std::move(fragment),
                             finish_lifetime_boundary(boundary, loc), loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("stmt.return.discarded");
            builder_.unreachable(loc);
            fragment = chain(std::move(fragment),
                             finish_fragment_block(block, previous), loc);
            return make_stmt_result(
                std::move(fragment), true,
                expr.has_value() && expr->has_error);
        }
    }
    if (expr.has_value() && lang_opts_.is_cxx_mode() &&
        file_.valid(current_function_)) {
        cir::EntityId function_entity =
            file_.function(current_function_).entity;
        if (function_entity.valid() && file_.valid(function_entity) &&
            file_.valid(file_.entity(function_entity).placeholder_result)) {
            ImplicitMoveEligibility move = classify_implicit_move_operand(
                *expr, ImplicitMoveContext::Return);
            if (move.eligible) {
                expr->category = ValueCategory::XValue;
            }
        }
    }
    if (!expr.has_value()) {
        cir::Fragment operand_cleanup =
            finish_lifetime_boundary(boundary, loc);
        cir::Fragment function_cleanup =
            emit_cleanup_calls_from_depth(0, loc);
        cir::Fragment destructor_cleanup;
        if (current_destructor_lifecycle_region_.active) {
            destructor_cleanup = collect_destructor_epilogue(loc).fragment;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("stmt.return");
        emit_active_catch_ends(loc);
        builder_.return_void(loc);
        cir::Fragment fragment = chain(std::move(operand_cleanup),
                                       std::move(function_cleanup), loc);
        fragment = chain(std::move(fragment),
                         std::move(destructor_cleanup), loc);
        fragment = chain(std::move(fragment),
                         finish_fragment_block(block, previous), loc);
        return make_stmt_result(std::move(fragment), true,
                                forbidden_constructor_handler_return);
    }

    if (expr.has_value() && expr->name == ".block.stack.literal") {
        if (arc_enabled() && expr->value.valid()) {

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("arc.retain_block");
            cir::InstId copied = builder_.objc_arc_op(
                cir::ObjCArcOpKind::RetainBlock, {expr->value},
                file_.resolved_type(expr->type), loc);
            expr->value = builder_.objc_arc_op(
                cir::ObjCArcOpKind::Autorelease, {copied},
                file_.resolved_type(expr->type), loc);
            expr->fragment = chain(std::move(expr->fragment),
                                   finish_fragment_block(block, previous),
                                   loc);
            expr->name.clear();
        } else {
            report_error("returning a block that lives on the stack frame",
                         loc);
            expr->has_error = true;
        }
    }
    if (is_void_type(current_result_type_)) {

        bool dependent_pattern_operand =
            collecting_pattern_ &&
            (expr_is_dependent(*expr) ||
             expr_is_value_dependent(*expr));
        if (dependent_pattern_operand) {

            bump_pattern_taint();
        }
        if (!expr->has_error && expr->type.valid() &&
            !is_void_type(expr->type) &&
            !dependent_pattern_operand) {
            report_error("a void function cannot return a value", loc);
            expr->has_error = true;
        }
        cir::Fragment operand_cleanup =
            finish_lifetime_boundary(boundary, loc);
        cir::Fragment function_cleanup =
            emit_cleanup_calls_from_depth(0, loc);
        cir::Fragment destructor_cleanup;
        if (current_destructor_lifecycle_region_.active) {
            destructor_cleanup = collect_destructor_epilogue(loc).fragment;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("stmt.return");
        emit_active_catch_ends(loc);
        builder_.return_void(loc);
        cir::Fragment return_fragment =
            finish_fragment_block(block, previous);
        cir::Fragment fragment = chain(
            std::move(expr->fragment),
            std::move(operand_cleanup), loc);
        fragment = chain(std::move(fragment),
                         std::move(function_cleanup), loc);
        fragment = chain(std::move(fragment),
                         std::move(destructor_cleanup), loc);
        fragment = chain(std::move(fragment), std::move(return_fragment), loc);
        return make_stmt_result(std::move(fragment), true, expr->has_error);
    }
    if (!deduce_return_type_ && current_result_type_.valid() &&
        expr->init_list && expr->category == ValueCategory::InitList) {
        *expr = materialize_list_initialization(
            std::move(*expr), current_result_type_,
            UseContext::Assignment, loc);
    }
    auto collect_error_return = [&](ExprResult value) {
        cir::Fragment operand_cleanup =
            finish_lifetime_boundary(boundary, loc);
        cir::Fragment function_cleanup =
            emit_cleanup_calls_from_depth(0, loc);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("stmt.return.error");
        builder_.unreachable(loc);
        cir::Fragment return_fragment =
            finish_fragment_block(block, previous);
        cir::Fragment fragment = chain(
            std::move(value.fragment),
            std::move(operand_cleanup), loc);
        fragment = chain(std::move(fragment),
                         std::move(function_cleanup), loc);
        fragment = chain(std::move(fragment), std::move(return_fragment), loc);
        return make_stmt_result(std::move(fragment), true, true);
    };
    bool unresolved_overload =
        expr->category == ValueCategory::OverloadDesignator ||
        (expr->category == ValueCategory::FunctionDesignator &&
         (!expr->candidates.empty() || expr->overload_designator));
    if (expr->has_error || (!expr->type.valid() && !unresolved_overload) ||
        !current_result_type_.valid()) {
        return collect_error_return(std::move(*expr));
    }
    if (lang_opts_.is_cxx_mode() &&
        !validate_potentially_invoked_destructor(current_result_type_, loc)) {
        expr->has_error = true;
    }
    if (expr->has_error) {
        return collect_error_return(std::move(*expr));
    }

    if (lang_opts_.is_cxx_mode() && !expr_is_dependent(*expr) &&
        !is_dependent_type(current_result_type_)) {
        cir::TypeId result_resolved = file_.resolved_type(current_result_type_);
        const cir::RecordFacts* result_record =
            file_.valid(result_resolved) &&
                    file_.type(result_resolved).kind == cir::TypeKind::Record
                ? file_.record_facts_for_type(result_resolved)
                : nullptr;
        bool same_type =
            file_.resolved_type(expr->type) == result_resolved;
        if (result_record) {
            if (same_type && expr->category == ValueCategory::PrValue) {
                nrvo_has_incompatible_return_ = true;

                adopt_materialized_result_storage(*expr);
                if (!expr->materialized_lifetimes.empty()) {
                    for (cir::LifetimeId lifetime :
                         expr->materialized_lifetimes) {
                        transfer_lifetime(lifetime,
                                          LifetimeOwnerKind::Result);
                    }
                } else {
                    remove_destructor_cleanup(
                        temporary_entity_of_value(expr->value));
                }
                ExprResult value = std::move(*expr);
                cir::Fragment operand_cleanup =
                    finish_lifetime_boundary(boundary, loc);
                cir::Fragment function_cleanup =
                    emit_cleanup_calls_from_depth(0, loc);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("stmt.return");
                emit_active_catch_ends(loc);
                builder_.return_value(value.value, loc);
                cir::Fragment return_fragment =
                    finish_fragment_block(block, previous);
                cir::Fragment fragment = chain(
                    std::move(value.fragment),
                    std::move(operand_cleanup), loc);
                fragment = chain(std::move(fragment),
                                 std::move(function_cleanup), loc);
                fragment = chain(std::move(fragment),
                                 std::move(return_fragment), loc);
                return make_stmt_result(std::move(fragment), true,
                                        value.has_error);
            }
            cir::EntityId constructor;
            cir::EntityId nrvo_candidate;
            ExprResult source;
            if (same_type) {
                ObjectTransferSelection selection =
                    select_object_transfer_constructor(
                        result_resolved, *expr,
                        ImplicitMoveContext::Return, loc);
                nrvo_candidate =
                    selection.move.nrvo_eligible ? selection.move.entity
                                                 : cir::EntityId{};
                if (!nrvo_candidate.valid()) {
                    nrvo_has_incompatible_return_ = true;
                }
                if (!selection.constructor.valid()) {
                    report_error(
                        selection.ambiguous
                            ? "return object construction is ambiguous"
                            : "no matching constructor for returned object",
                        loc);
                    expr->has_error = true;
                    return collect_error_return(std::move(*expr));
                }
                constructor = selection.constructor;
                source = std::move(*expr);
                source.category = selection.selected_category;
            } else {
                UserConversionSequence sequence =
                    resolve_initialization_user_conversion(
                        *expr, result_resolved,
                        UserConversionContext::CopyInitialization, loc);
                if (sequence.kind ==
                    UserConversionSequence::Kind::Ambiguous) {
                    report_error("return object construction is ambiguous",
                                 loc);
                    report_overload_ambiguity_notes(sequence.ambiguity, loc);
                    expr->has_error = true;
                    return collect_error_return(std::move(*expr));
                }
                if (sequence.kind !=
                    UserConversionSequence::Kind::Constructor) {

                    constructor = {};
                } else {
                    nrvo_has_incompatible_return_ = true;
                    constructor = sequence.callable;
                    source = std::move(*expr);
                }
            }
            if (constructor.valid()) {
                std::vector<ExprResult> arguments;
                arguments.push_back(std::move(source));
                ConstructorCallMaterialization materialized =
                    materialize_selected_constructor_call(
                        constructor, std::move(arguments), loc);
                if (materialized.has_error) {
                    ExprResult error;
                    error.fragment =
                        std::move(materialized.argument_fragment);
                    error.type = current_result_type_;
                    error.category = ValueCategory::PrValue;
                    error.has_error = true;
                    return collect_error_return(std::move(error));
                }

                cir::Fragment fragment =
                    std::move(materialized.argument_fragment);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("stmt.return.object.construct");
                cir::EntityId temp_entity = builder_.add_entity(
                    cir::EntityKind::Variable, ".ret.temp",
                    current_result_type_, {}, loc,
                    cir::StorageDuration::Temporary);
                file_.entity_mut(temp_entity).is_function_result_object = true;
                cir::InstId temp_place = builder_.local_place(
                    temp_entity, current_result_type_, loc);
                cir::InstId transfer = emit_construct_in_place(
                    temp_place,
                    structor_complete_variant(constructor),
                    materialized.argument_values, loc);
                cir::InstId value =
                    builder_.lvalue_to_rvalue(temp_place, loc);
                cir::Fragment construct_fragment =
                    finish_fragment_block(block, previous);
                fragment = chain(std::move(fragment),
                                 std::move(construct_fragment), loc);
                fragment = chain(
                    std::move(fragment),
                    finish_lifetime_boundary(boundary, loc), loc);

                std::vector<cir::InstId> nrvo_cleanups;
                cir::Fragment function_cleanup =
                    emit_cleanup_calls_from_depth(
                        0, loc, nrvo_candidate,
                        nrvo_candidate.valid() ? &nrvo_cleanups : nullptr);
                fragment = chain(std::move(fragment),
                                 std::move(function_cleanup), loc);
                previous = builder_.current_block();
                block = begin_fragment_block("stmt.return.copy");
                emit_active_catch_ends(loc);
                builder_.return_value(value, loc);
                cir::Fragment return_fragment =
                    finish_fragment_block(block, previous);
                fragment = chain(std::move(fragment),
                                 std::move(return_fragment), loc);
                if (nrvo_candidate.valid()) {
                    nrvo_return_candidates_.push_back(NrvoReturnCandidate{
                        nrvo_candidate, transfer,
                        std::move(nrvo_cleanups)});
                }
                return make_stmt_result(std::move(fragment), true, false);
            }
        }
    }

    nrvo_has_incompatible_return_ = true;

    ExprResult value = convert_to(std::move(*expr), current_result_type_, UseContext::Return, loc);

    if (collecting_pattern_ && expr_is_dependent(value)) {

        bump_pattern_taint();
        discard_lifetime_boundary(boundary);
        return make_stmt_result(std::move(value.fragment), true,
                                value.has_error);
    }
    if (value.has_error || !value.value.valid()) {
        return collect_error_return(std::move(value));
    }

    if (arc_enabled()) {

        value = arc_adjust_return_value(std::move(value), loc);
    }

    cir::Fragment operand_cleanup =
        finish_lifetime_boundary(boundary, loc);
    cir::Fragment function_cleanup = emit_cleanup_calls_from_depth(0, loc);
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("stmt.return");
    emit_active_catch_ends(loc);
    builder_.return_value(value.value, loc);
    cir::Fragment return_fragment = finish_fragment_block(block, previous);
    cir::Fragment fragment = chain(
        std::move(value.fragment),
        std::move(operand_cleanup), loc);
    fragment = chain(std::move(fragment), std::move(function_cleanup), loc);
    fragment = chain(std::move(fragment), std::move(return_fragment), loc);
    return make_stmt_result(std::move(fragment), true, value.has_error);
}

StmtResult Session::collect_compound_stmt(std::vector<StmtResult> children, SrcLoc loc) {
    cir::Fragment fragment;
    std::optional<ExprResult> result_expr;
    bool has_error = false;
    bool always_returns = false;
    bool contains_switch_label = false;
    bool reachable = true;
    std::vector<cir::BlockId> break_exits;
    std::vector<cir::BlockId> continue_exits;

    for (StmtResult& child : children) {
        break_exits.insert(break_exits.end(),
                           child.break_exits.begin(),
                           child.break_exits.end());
        continue_exits.insert(continue_exits.end(),
                              child.continue_exits.begin(),
                              child.continue_exits.end());
        if (child.result_expr.has_value()) {
            result_expr = std::move(child.result_expr);
        } else if (!child.preserves_result_expr) {
            result_expr.reset();
        }
        has_error = has_error || child.has_error;
        bool child_reachable = reachable || child.contains_switch_label;
        if (!child_reachable &&
            !child.fragment.empty() &&
            child.falls_through &&
            !builder_.block_terminated(child.fragment.exit)) {
            builder_.unreachable_from(child.fragment.exit, loc);
        }
        if (child_reachable && child.always_returns && !child.falls_through) {
            always_returns = true;
        }
        if (child.contains_switch_label) {
            reachable = child.falls_through;
        } else if (reachable && !child.falls_through) {
            reachable = false;
        }
        contains_switch_label = contains_switch_label || child.contains_switch_label;

        if (!fragment.empty() &&
            !fragment.falls_through &&
            child.contains_switch_label &&
            !child.fragment.empty()) {
            append_fragment_blocks(fragment, child.fragment);
            fragment.falls_through = child.falls_through;
        } else {
            fragment = chain(std::move(fragment), std::move(child.fragment), loc);
        }
    }

    StmtResult result = make_stmt_result(std::move(fragment), always_returns, has_error);
    if (result_expr.has_value()) {
        result_expr->fragment = result.fragment;
        result.result_expr = std::move(result_expr);
    }
    result.contains_switch_label = contains_switch_label;
    result.break_exits = std::move(break_exits);
    result.continue_exits = std::move(continue_exits);
    return result;
}

Session::LabelInfo& Session::function_label(std::string_view name, SrcLoc loc) {
    std::string key(name);
    auto [it, inserted] = function_labels_.try_emplace(key);
    if (inserted) {
        it->second.name = key;
        it->second.loc = loc;
    }
    return it->second;
}

Session::LabelInfo* Session::find_local_label(std::string_view name) {
    for (auto it = local_label_scopes_.rbegin(); it != local_label_scopes_.rend(); ++it) {
        auto found = it->find(std::string(name));
        if (found != it->end()) {
            return &found->second;
        }
    }
    return nullptr;
}

Session::LabelInfo& Session::label_for_reference(std::string_view name, SrcLoc loc) {
    if (LabelInfo* local = find_local_label(name)) {
        return *local;
    }
    return function_label(name, loc);
}

Session::LabelInfo& Session::label_for_definition(std::string_view name, SrcLoc loc) {
    if (LabelInfo* local = find_local_label(name)) {
        return *local;
    }
    return function_label(name, loc);
}

void Session::begin_control_flow_limited_statement() {
    control_flow_regions_.push_back(next_control_flow_region_++);
}

void Session::end_control_flow_limited_statement() {
    if (!control_flow_regions_.empty()) {
        control_flow_regions_.pop_back();
    }
}

void Session::begin_expansion_statement(cir::BlockId continue_target,
                                        cir::BlockId break_target) {
    control_stack_.push_back(ControlTargets{
        ControlKind::Expansion, continue_target, break_target});
}

Session::ExpansionControlSummary Session::end_expansion_statement() {
    ExpansionControlSummary summary;
    if (!control_stack_.empty() &&
        control_stack_.back().kind == ControlKind::Expansion) {
        summary.has_break = control_stack_.back().observed_break;
        summary.has_continue = control_stack_.back().observed_continue;
        control_stack_.pop_back();
    }
    return summary;
}

cir::BlockId Session::create_statement_target(std::string name) {
    return builder_.create_detached_block(std::move(name));
}

StmtResult Session::collect_statement_target(cir::BlockId target,
                                             SrcLoc loc) {
    (void)loc;
    return make_stmt_result(builder_.block_fragment(target), false, false);
}

StmtResult Session::collect_expansion_element(DeclResult declaration,
                                              StmtResult body,
                                              StmtResult normal_cleanups,
                                              cir::BlockId continue_target,
                                              SrcLoc loc) {
    cir::Fragment fragment = chain(std::move(declaration.fragment),
                                   std::move(body.fragment), loc);
    bool reaches_continue = body.falls_through ||
                            !body.continue_exits.empty();
    if (body.falls_through) {
        fragment = chain(std::move(fragment),
                         std::move(normal_cleanups.fragment), loc);
    }
    if (reaches_continue) {
        cir::Fragment target = builder_.block_fragment(continue_target);
        fragment = chain(std::move(fragment), std::move(target), loc);

        fragment.exit = continue_target;
        fragment.falls_through = true;
    }

    StmtResult result = make_stmt_result(
        std::move(fragment),
        body.always_returns && body.continue_exits.empty(),
        declaration.has_error || body.has_error || normal_cleanups.has_error);
    result.break_exits = std::move(body.break_exits);
    result.contains_switch_label = body.contains_switch_label;
    return result;
}

StmtResult Session::collect_expansion_sequence(
    std::vector<StmtResult> children,
    cir::BlockId break_target,
    SrcLoc loc) {
    cir::Fragment fragment;
    bool has_error = false;
    bool has_break = false;
    bool all_return = !children.empty();
    bool reachable = true;
    for (StmtResult& child : children) {
        has_error = has_error || child.has_error;
        if (reachable) {
            has_break = has_break || !child.break_exits.empty();
            reachable = child.falls_through;
        }
        all_return = all_return && child.always_returns;
        fragment = chain(std::move(fragment),
                         std::move(child.fragment), loc);
    }

    if (fragment.falls_through || has_break) {
        cir::Fragment target = builder_.block_fragment(break_target);
        fragment = chain(std::move(fragment), std::move(target), loc);
        fragment.exit = break_target;
        fragment.falls_through = true;
        all_return = false;
    }
    return make_stmt_result(std::move(fragment), all_return, has_error);
}

void Session::begin_expansion_label_region() {
    ++expansion_label_region_depth_;
    begin_control_flow_limited_statement();
}

void Session::end_expansion_label_region() {
    end_control_flow_limited_statement();
    if (expansion_label_region_depth_ != 0) {
        --expansion_label_region_depth_;
    }
}

void Session::validate_label_control_flow(
    const LabelInfo& label,
    const LabelReference& reference) {

    bool contained =
        label.control_flow_regions == reference.control_flow_regions;
    if (!contained) {
        report_error("goto target '" + label.name +
                         "' crosses a control-flow-limited statement boundary",
                     reference.loc);
    }
}

void Session::record_label_reference(LabelInfo& label,
                                     std::string_view name,
                                     SrcLoc loc) {
    label.referenced = true;
    if (label.first_reference.isInvalid()) {
        label.first_reference = loc;
    }
    LabelReference reference;
    reference.loc = loc;
    reference.control_flow_regions = control_flow_regions_;
    label.references.push_back(reference);
    if (label.defined) {
        validate_label_control_flow(label, reference);
    }
    if (in_discarded_statement_validation()) {
        DiscardedControlFlowEvent event;
        event.kind = DiscardedControlFlowEvent::Kind::LabelReference;
        event.name = std::string(name);
        event.loc = loc;
        event.function = current_function_;
        event.control_flow_regions = control_flow_regions_;
        event.declared_local = label.declared_local;
        discarded_control_flow_events_.push_back(std::move(event));
    }
}

void Session::ensure_label_block(LabelInfo& label) {
    if (!label.block.valid()) {
        label.block = builder_.create_detached_block(std::string("label.") + label.name);
    }
}

void Session::diagnose_unresolved_label(LabelInfo& label, SrcLoc fallback_loc) {
    SrcLoc loc = label.first_reference.isInvalid() ? fallback_loc : label.first_reference;
    report_error("use of undeclared label '" + label.name + "'", loc);
    if (label.block.valid() && !builder_.block_terminated(label.block)) {
        builder_.unreachable_from(label.block, loc);
    }
}

std::optional<int64_t> Session::try_evaluate_asm_immediate(const ExprResult& expr) const {
    if (!expr.value.valid()) {
        return std::nullopt;
    }

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::c_ice();
    request.loc = SrcLoc();
    request.required = false;
    ConstEvalResult result =
        engine.evaluate_fragment(expr.fragment, cir::ValueRef(expr.value), request);
    if (result.status == ConstEvalStatus::Constant && result.value.has_value()) {
        return result.value->try_as_int64();
    }

    auto integer_literal_value = [&](cir::InstId inst_id) -> std::optional<int64_t> {
        if (!file_.valid(inst_id)) {
            return std::nullopt;
        }
        const cir::Inst& inst = file_.inst(inst_id);
        if (inst.kind != cir::InstKind::IntegerLiteral) {
            return std::nullopt;
        }
        const auto* literal =
            std::get_if<cir::LiteralPayload>(&file_.payload(inst.payload_index));
        if (!literal) {
            return std::nullopt;
        }
        const auto* value =
            std::get_if<cir::IntegerValue>(&literal->value);
        return value ? value->try_as_int64() : std::nullopt;
    };

    struct PointerIndexExpr {
        cir::InstId base{};
        int64_t index = 0;
    };

    auto pointer_index_expr = [&](auto&& self, cir::InstId inst_id) -> std::optional<PointerIndexExpr> {
        if (!file_.valid(inst_id)) {
            return std::nullopt;
        }
        const cir::Inst& inst = file_.inst(inst_id);
        std::vector<cir::ValueRef> operands = file_.value_operands(inst.operands);
        if (inst.kind == cir::InstKind::Cast && !operands.empty()) {
            return self(self, operands[0].inst);
        }
        if (inst.kind != cir::InstKind::AddrOf || operands.empty()) {
            return std::nullopt;
        }

        cir::InstId place = operands[0].inst;
        if (!file_.valid(place)) {
            return std::nullopt;
        }
        const cir::Inst& place_inst = file_.inst(place);
        if (place_inst.kind != cir::InstKind::ArrayElementPlace) {
            return PointerIndexExpr{place, 0};
        }
        std::vector<cir::ValueRef> place_operands = file_.value_operands(place_inst.operands);
        if (place_operands.size() != 2) {
            return std::nullopt;
        }
        std::optional<int64_t> index = integer_literal_value(place_operands[1].inst);
        if (!index.has_value()) {
            return std::nullopt;
        }
        return PointerIndexExpr{place_operands[0].inst, *index};
    };

    const cir::Inst& inst = file_.inst(expr.value);
    const auto* binary = std::get_if<cir::BinaryOpDescriptor>(&file_.payload(inst.payload_index));
    if (!binary || binary->op != cir::BinaryOpKind::Sub) {
        return std::nullopt;
    }
    std::vector<cir::ValueRef> operands = file_.value_operands(inst.operands);
    if (operands.size() != 2) {
        return std::nullopt;
    }
    std::optional<PointerIndexExpr> lhs = pointer_index_expr(pointer_index_expr, operands[0].inst);
    std::optional<PointerIndexExpr> rhs = pointer_index_expr(pointer_index_expr, operands[1].inst);
    if (!lhs.has_value() || !rhs.has_value() || lhs->base != rhs->base) {
        return std::nullopt;
    }
    return lhs->index - rhs->index;
}

void Session::begin_local_label_scope() {
    local_label_scopes_.push_back({});
}

void Session::end_local_label_scope(SrcLoc loc) {
    if (local_label_scopes_.empty()) {
        return;
    }
    LabelMap labels = std::move(local_label_scopes_.back());
    local_label_scopes_.pop_back();
    for (auto& [name, label] : labels) {
        (void)name;
        if (label.referenced && !label.defined) {
            diagnose_unresolved_label(label, loc);
            if (label.block.valid()) {
                pending_orphan_label_blocks_.push_back(label.block);
            }
        }
    }
}

StmtResult Session::declare_local_labels(std::vector<std::string> names, SrcLoc loc) {
    bool has_error = false;
    if (local_label_scopes_.empty()) {
        report_error("__label__ declaration is not inside a block scope", loc);
        has_error = true;
    } else {
        LabelMap& current = local_label_scopes_.back();
        for (std::string& name : names) {
            if (name.empty()) {
                continue;
            }
            auto [it, inserted] = current.try_emplace(name);
            if (!inserted) {
                report_error("duplicate local label declaration '" + name + "'", loc);
                has_error = true;
                continue;
            }
            it->second.name = std::move(name);
            it->second.declared_local = true;
            it->second.loc = loc;
        }
    }
    StmtResult result = collect_compound_stmt({}, loc);
    result.has_error = result.has_error || has_error;
    return result;
}

StmtResult Session::collect_label_stmt(std::string_view name, StmtResult child, SrcLoc loc) {

    suppress_open_scope_lifetimes();
    LabelInfo& label = label_for_definition(name, loc);
    ensure_label_block(label);
    cir::BlockId label_block = label.block;
    bool has_error = child.has_error;
    if (label.defined) {
        report_error("duplicate label '" + std::string(name) + "'", loc);
        label_block = builder_.create_detached_block("label.duplicate");
        has_error = true;
    } else {
        label.defined = true;
        label.loc = loc;
        label.control_flow_regions = control_flow_regions_;
        for (const LabelReference& reference : label.references) {
            validate_label_control_flow(label, reference);
        }
        if (in_discarded_statement_validation()) {
            DiscardedControlFlowEvent event;
            event.kind =
                DiscardedControlFlowEvent::Kind::LabelDefinition;
            event.name = std::string(name);
            event.loc = loc;
            event.function = current_function_;
            event.control_flow_regions = control_flow_regions_;
            event.declared_local = label.declared_local;
            discarded_control_flow_events_.push_back(std::move(event));
        }
    }

    cir::Fragment fragment = builder_.block_fragment(label_block);
    if (!child.fragment.empty()) {
        if (!builder_.block_terminated(label_block)) {
            builder_.branch_from(label_block, child.fragment.entry, {}, loc);
        }
        append_fragment_blocks(fragment, child.fragment);
        fragment.exit = child.fragment.exit;
        fragment.falls_through = child.falls_through;
    }

    StmtResult result = make_stmt_result(std::move(fragment), child.always_returns, has_error);
    result.contains_switch_label = true;
    result.break_exits = std::move(child.break_exits);
    result.continue_exits = std::move(child.continue_exits);

    result.result_expr = std::move(child.result_expr);
    return result;
}

StmtResult Session::collect_goto_stmt(std::string_view name, SrcLoc loc) {
    bool has_error = false;
    if (!current_function_.valid()) {
        report_error("goto statement is not inside a function", loc);
        has_error = true;
    }
    LabelInfo& label = label_for_reference(name, loc);
    ensure_label_block(label);
    record_label_reference(label, name, loc);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("stmt.goto");
    if (has_error) {
        builder_.unreachable(loc);
    } else {
        if (label.defined && vla_sp_slot_place_.valid()) {

            cir::InstId saved = builder_.load(vla_sp_slot_place_, loc);
            builder_.stack_restore(saved, loc);
        }
        builder_.branch(label.block, {}, loc);
    }
    cir::Fragment fragment = finish_fragment_block(block, previous);
    return make_stmt_result(std::move(fragment), false, has_error);
}

StmtResult Session::collect_computed_goto_stmt(ExprResult target, SrcLoc loc) {
    ExprResult value = require_value(std::move(target), UseContext::RValue, loc);
    bool has_error = value.has_error;
    if (!is_pointer_type(value.type)) {
        report_error("computed goto target must have pointer type", loc);
        has_error = true;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("stmt.computed_goto");
    if (has_error || !value.value.valid()) {
        builder_.unreachable(loc);
    } else {
        builder_.indirect_branch(value.value, loc);
    }
    cir::Fragment goto_fragment = finish_fragment_block(block, previous);
    cir::Fragment fragment = chain(std::move(value.fragment), std::move(goto_fragment), loc);
    return make_stmt_result(std::move(fragment), false, has_error);
}

StmtResult Session::collect_asm_stmt(std::string asm_string,
                                     std::vector<AsmOperand> outputs,
                                     std::vector<AsmOperand> inputs,
                                     std::vector<std::string> clobbers,
                                     std::vector<std::string> goto_labels,
                                     bool is_volatile,
                                     bool is_inline,
                                     bool is_goto,
                                     SrcLoc loc) {
    bool has_error = false;
    cir::Fragment fragment;
    std::vector<cir::InstId> operands;
    operands.reserve(outputs.size() + inputs.size());

    if (in_dead_branch()) {

        return make_stmt_result({}, false, false);
    }

    cir::InlineAsmPayload payload;
    payload.asm_string = std::move(asm_string);
    payload.has_side_effects = is_volatile || outputs.empty() || is_goto;
    payload.is_inline = is_inline;
    payload.is_goto = is_goto;

    std::unordered_set<std::string> symbolic_names;
    auto check_symbolic_name = [&](const AsmOperand& operand) {
        if (operand.symbolic_name.empty()) {
            return;
        }
        if (!symbolic_names.insert(operand.symbolic_name).second) {
            report_error("duplicate asm operand symbolic name '[" +
                             operand.symbolic_name + "]'",
                         operand.loc);
            has_error = true;
        }
    };

    auto register_binding_for = [&](cir::EntityId entity) -> std::string {
        if (entity.valid() && file_.valid(entity)) {
            const cir::Entity& e = file_.entity(entity);
            if (e.attr_facts.is_named_register && !e.attr_facts.asm_label.empty()) {
                return e.attr_facts.asm_label;
            }
        }
        return {};
    };

    for (AsmOperand& output : outputs) {
        if (output.constraint.empty() ||
            (output.constraint[0] != '=' && output.constraint[0] != '+')) {
            report_error("asm output constraint must begin with '=' or '+'", output.loc);
            has_error = true;
        }
        check_symbolic_name(output);
        std::string output_register = register_binding_for(output.expr.entity);
        bool output_is_lvalue = output.expr.category == ValueCategory::LValue &&
                                output.expr.place.valid();
        ExprResult place = require_place(std::move(output.expr), UseContext::Assignment, output.loc);
        if (!output_is_lvalue || !place.place.valid()) {
            report_error("asm output operand must be an lvalue", output.loc);
            has_error = true;
        }
        has_error = has_error || place.has_error;
        operands.push_back(place.place);
        fragment = chain(std::move(fragment), std::move(place.fragment), output.loc);

        cir::InlineAsmOperandPayload operand_payload;
        operand_payload.symbolic_name = file_.intern_name(output.symbolic_name);
        operand_payload.constraint = std::move(output.constraint);
        operand_payload.is_output = true;
        operand_payload.register_binding = std::move(output_register);
        payload.outputs.push_back(std::move(operand_payload));
    }

    for (AsmOperand& input : inputs) {
        if (!input.constraint.empty() &&
            (input.constraint[0] == '=' || input.constraint[0] == '+')) {
            report_error("asm input constraint cannot begin with '=' or '+'", input.loc);
            has_error = true;
        }
        if (!input.constraint.empty() &&
            input.constraint.find_first_not_of("0123456789") == std::string::npos) {

            size_t reference = 0;
            for (char digit : input.constraint) {
                reference = reference * 10 + static_cast<size_t>(digit - '0');
            }
            if (reference >= outputs.size()) {
                report_error("asm matching constraint '" + input.constraint +
                                 "' references a nonexistent output operand",
                             input.loc);
                has_error = true;
            }
        }
        check_symbolic_name(input);
        std::string input_register = register_binding_for(input.expr.entity);
        bool memory_operand = asm_input_requires_memory_place(
            input.constraint, file_.target_info().arch);
        bool prefer_immediate = asm_constraint_prefers_immediate_operand(input.constraint);
        bool require_immediate = asm_constraint_requires_immediate_operand(input.constraint);
        ExprResult operand;
        if (memory_operand) {
            operand = require_place(std::move(input.expr), UseContext::LValue, input.loc);
            operands.push_back(operand.place);
        } else {
            ExprResult value = require_value(std::move(input.expr), UseContext::RValue, input.loc);
            if (prefer_immediate) {
                if (std::optional<int64_t> immediate = try_evaluate_asm_immediate(value)) {
                    cir::TypeId literal_type = value.type.valid() ? value.type : builder_.int_type();
                    value = make_integer_literal(*immediate,
                                                 std::to_string(*immediate),
                                                 literal_type,
                                                 input.loc);
                }

            }
            operand = std::move(value);
            operands.push_back(operand.value);
        }
        has_error = has_error || operand.has_error;
        fragment = chain(std::move(fragment), std::move(operand.fragment), input.loc);

        cir::InlineAsmOperandPayload operand_payload;
        operand_payload.symbolic_name = file_.intern_name(input.symbolic_name);
        operand_payload.constraint = std::move(input.constraint);
        operand_payload.is_output = false;
        operand_payload.register_binding = std::move(input_register);
        payload.inputs.push_back(std::move(operand_payload));
    }

    payload.clobbers = std::move(clobbers);
    for (std::string& label_name : goto_labels) {
        LabelInfo& label = label_for_reference(label_name, loc);
        ensure_label_block(label);
        record_label_reference(label, label_name, loc);
        payload.goto_labels.push_back(file_.intern_name(label_name));
        payload.goto_targets.push_back(label.block);
    }
    payload.constraints = preview_asm_constraints(payload);

    if (!has_error) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("stmt.asm");
        if (is_goto) {
            cir::BlockId fallthrough = builder_.create_detached_block("asm.fallthrough");
            builder_.asm_goto_from(block,
                                   std::move(payload),
                                   operands,
                                   fallthrough,
                                   loc);
            cir::Fragment asm_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(asm_fragment), loc);
            append_fragment_blocks(fragment, builder_.block_fragment(fallthrough));
            fragment.exit = fallthrough;
            fragment.falls_through = true;
        } else {
            builder_.inline_asm(std::move(payload), operands, loc);
            cir::Fragment asm_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(asm_fragment), loc);
        }
    }

    return make_stmt_result(std::move(fragment), false, has_error);
}

ExprResult Session::collect_label_address_expr(std::string_view name, SrcLoc loc) {
    LabelInfo& label = label_for_reference(name, loc);
    ensure_label_block(label);
    record_label_reference(label, name, loc);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.label_address");
    cir::InstId value = builder_.label_address(name, label.block, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = value;
    result.type = file_.inst(value).result_type;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::collect_statement_expr(StmtResult body, SrcLoc loc) {
    if (body.result_expr.has_value()) {
        ExprResult result = std::move(*body.result_expr);
        result.fragment = std::move(body.fragment);
        result.has_error = result.has_error || body.has_error;
        return result;
    }

    ExprResult result;
    result.fragment = std::move(body.fragment);
    result.type = builder_.void_type();
    result.category = ValueCategory::PrValue;
    result.has_error = body.has_error;
    (void)loc;
    return result;
}

ExprResult Session::collect_block_literal_expr(SrcLoc loc) {
    return collect_unsupported_expr("block literals are parsed but not lowered yet", {}, loc);
}

StmtResult Session::collect_break_stmt(SrcLoc loc) {
    cir::Fragment cleanups;
    if (!control_stack_.empty()) {
        cleanups = emit_cleanup_calls_from_depth(control_stack_.size(), loc);
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("stmt.break");
    bool has_error = false;
    if (control_stack_.empty()) {
        report_error("break statement is not inside a loop or switch", loc);
        builder_.unreachable(loc);
        has_error = true;
    } else {
        control_stack_.back().observed_break = true;
        builder_.branch(control_stack_.back().break_target, {}, loc);
    }
    cir::Fragment fragment = chain(
        std::move(cleanups), finish_fragment_block(block, previous), loc);

    StmtResult result = make_stmt_result(std::move(fragment), false, has_error);
    if (!control_stack_.empty()) {
        result.break_exits.push_back(block);
    }
    return result;
}

StmtResult Session::collect_continue_stmt(SrcLoc loc) {
    cir::Fragment cleanups;
    size_t loop_index = 0;
    bool found_loop = false;
    for (size_t i = control_stack_.size(); i-- > 0;) {
        if (control_stack_[i].kind == ControlKind::Loop ||
            control_stack_[i].kind == ControlKind::Expansion) {
            loop_index = i;
            found_loop = true;
            cleanups = emit_cleanup_calls_from_depth(i + 1, loc);
            break;
        }
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("stmt.continue");
    bool has_error = true;
    if (found_loop) {
        control_stack_[loop_index].observed_continue = true;
        builder_.branch(control_stack_[loop_index].continue_target, {}, loc);
        has_error = false;
    }
    if (has_error) {
        report_error("continue statement is not inside a loop", loc);
        builder_.unreachable(loc);
    }
    cir::Fragment fragment = chain(
        std::move(cleanups), finish_fragment_block(block, previous), loc);

    StmtResult result = make_stmt_result(std::move(fragment), false, has_error);
    if (!has_error) {
        result.continue_exits.push_back(block);
    }
    return result;
}

StmtResult Session::collect_if_stmt(ExprResult condition,
                                    StmtResult then_result,
                                    std::optional<StmtResult> else_result,
                                    SrcLoc loc,
                                    LifetimeBoundary condition_boundary) {
    ExprResult cond = require_value(std::move(condition), UseContext::Condition, loc);
    cond.fragment = chain(std::move(cond.fragment),
                          finish_lifetime_boundary(condition_boundary, loc),
                          loc);
    cir::Fragment fragment = adopt_or_create_fragment_entry(std::move(cond.fragment), "if.cond");

    cir::BlockId then_empty_block = builder_.create_detached_block("if.then");
    cir::BlockId else_empty_block = builder_.create_detached_block("if.else");
    cir::BlockId continuation_block = builder_.create_detached_block("if.end");
    cir::BlockId then_entry = then_empty_block;
    cir::BlockId else_entry = else_result.has_value()
        ? else_empty_block
        : continuation_block;

    builder_.cond_branch_from(fragment.exit, cond.value, then_entry, else_entry, {}, loc);

    append_fragment_blocks(fragment, builder_.block_fragment(then_empty_block));
    if (then_result.fragment.empty()) {
        builder_.branch_from(then_empty_block, continuation_block, {}, loc);
    } else {
        builder_.branch_from(then_empty_block, then_result.fragment.entry, {}, loc);
        append_fragment_blocks(fragment, then_result.fragment);
        if (then_result.falls_through && !builder_.block_terminated(then_result.fragment.exit)) {
            builder_.branch_from(then_result.fragment.exit, continuation_block, {}, loc);
        }
    }

    if (else_result.has_value()) {
        append_fragment_blocks(fragment, builder_.block_fragment(else_empty_block));
        if (else_result->fragment.empty()) {
            builder_.branch_from(else_empty_block, continuation_block, {}, loc);
        } else {
            builder_.branch_from(else_empty_block, else_result->fragment.entry, {}, loc);
            append_fragment_blocks(fragment, else_result->fragment);
            if (else_result->falls_through && !builder_.block_terminated(else_result->fragment.exit)) {
                builder_.branch_from(else_result->fragment.exit, continuation_block, {}, loc);
            }
        }
    }

    append_fragment_blocks(fragment, builder_.block_fragment(continuation_block));
    fragment.exit = continuation_block;
    bool all_return = then_result.always_returns &&
        else_result.has_value() && else_result->always_returns;
    fragment.falls_through = !all_return;

    if (all_return && !builder_.block_terminated(continuation_block)) {
        builder_.unreachable_from(continuation_block, loc);
    }
    StmtResult result = make_stmt_result(std::move(fragment), all_return, cond.has_error ||
        then_result.has_error || (else_result.has_value() && else_result->has_error));
    result.contains_switch_label =
        then_result.contains_switch_label ||
        (else_result.has_value() && else_result->contains_switch_label);
    result.break_exits = std::move(then_result.break_exits);
    result.continue_exits = std::move(then_result.continue_exits);
    if (else_result.has_value()) {
        result.break_exits.insert(result.break_exits.end(),
                                  else_result->break_exits.begin(),
                                  else_result->break_exits.end());
        result.continue_exits.insert(result.continue_exits.end(),
                                     else_result->continue_exits.begin(),
                                     else_result->continue_exits.end());
    }
    return result;
}

WhileControl Session::begin_while(SrcLoc loc) {
    WhileControl control;
    control.body_block = builder_.create_detached_block("while.body");
    control.continuation_block =
        builder_.create_detached_block("while.end");
    control.loc = loc;
    control_stack_.push_back(ControlTargets{
        ControlKind::Loop,
        {},
        control.continuation_block});
    return control;
}

void Session::begin_while_body(WhileControl& control,
                               ExprResult condition,
                               LifetimeBoundary condition_boundary) {
    control.condition = require_value(std::move(condition), UseContext::Condition, control.loc);
    control.condition.fragment = chain(
        std::move(control.condition.fragment),
        finish_lifetime_boundary(condition_boundary, control.loc),
        control.loc);
    control.condition.fragment =
        adopt_or_create_fragment_entry(std::move(control.condition.fragment), "while.cond");
    control.condition_exit = control.condition.fragment.exit;
    control.condition_entry = control.condition.fragment.entry;
    if (!control_stack_.empty()) {
        control_stack_.back().continue_target = control.condition_entry;
    }
}

StmtResult Session::finish_while(WhileControl& control, const StmtResult& body_result) {
    StmtResult repeat_cleanups;
    StmtResult exit_cleanups;
    if (control.has_condition_scope) {

        repeat_cleanups = collect_scope_cleanups(control.loc);
        exit_cleanups = collect_scope_cleanups(control.loc);
        end_scope();
    }
    if (!control_stack_.empty()) {
        control_stack_.pop_back();
    }

    cir::Fragment fragment = control.condition.fragment;

    cir::BlockId body_entry = control.body_block;
    cir::BlockId false_target = exit_cleanups.fragment.empty()
        ? control.continuation_block
        : exit_cleanups.fragment.entry;
    builder_.cond_branch_from(control.condition_exit, control.condition.value,
        body_entry, false_target, {}, control.loc);

    append_fragment_blocks(fragment, builder_.block_fragment(control.body_block));
    cir::BlockId repeat_target = repeat_cleanups.fragment.empty()
        ? control.condition_entry
        : repeat_cleanups.fragment.entry;
    if (body_result.fragment.empty()) {
        builder_.branch_from(control.body_block, repeat_target, {}, control.loc);
    } else {
        builder_.branch_from(control.body_block, body_result.fragment.entry, {}, control.loc);
        append_fragment_blocks(fragment, body_result.fragment);
        if (body_result.falls_through && !builder_.block_terminated(body_result.fragment.exit)) {
            builder_.branch_from(body_result.fragment.exit, repeat_target, {}, control.loc);
        }
    }

    if (!repeat_cleanups.fragment.empty()) {
        append_fragment_blocks(fragment, repeat_cleanups.fragment);
        if (repeat_cleanups.falls_through &&
            !builder_.block_terminated(repeat_cleanups.fragment.exit)) {
            builder_.branch_from(repeat_cleanups.fragment.exit,
                                 control.condition_entry,
                                 {},
                                 control.loc);
        }
    }
    if (!exit_cleanups.fragment.empty()) {
        append_fragment_blocks(fragment, exit_cleanups.fragment);
        if (exit_cleanups.falls_through &&
            !builder_.block_terminated(exit_cleanups.fragment.exit)) {
            builder_.branch_from(exit_cleanups.fragment.exit,
                                 control.continuation_block,
                                 {},
                                 control.loc);
        }
    }
    append_fragment_blocks(fragment, builder_.block_fragment(control.continuation_block));
    fragment.exit = control.continuation_block;
    fragment.falls_through = true;
    StmtResult result = make_stmt_result(std::move(fragment), false,
        control.condition.has_error || body_result.has_error);
    result.contains_switch_label = body_result.contains_switch_label;
    return result;
}

ForControl Session::begin_for(SrcLoc loc) {
    enter_scope(ScopeFlags::BlockScope | ScopeFlags::LoopScope);
    ForControl control;
    control.body_block = builder_.create_detached_block("for.body");
    control.continuation_block = builder_.create_detached_block("for.end");
    control.loc = loc;
    return control;
}

RangeEndpointPlan Session::plan_range_endpoints(
    const ExprResult& range_object,
    bool allow_array,
    bool diagnose_missing,
    SrcLoc loc) {
    RangeEndpointPlan plan;
    if (range_object.has_error) {
        plan.has_error = true;
        return plan;
    }
    if (expr_is_dependent(range_object)) {
        plan.kind = RangeEndpointKind::Dependent;
        return plan;
    }

    cir::TypeId object_type = file_.resolved_type(range_object.type);
    while (file_.valid(object_type) &&
           (file_.type(object_type).kind == cir::TypeKind::LValueReference ||
            file_.type(object_type).kind == cir::TypeKind::RValueReference)) {
        object_type = file_.resolved_type(
            file_.reference_referred_ref(object_type).type);
    }

    if (file_.valid(object_type) &&
        file_.type(object_type).kind == cir::TypeKind::Array) {
        if (!allow_array) {
            return plan;
        }
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(object_type));
        if (!array || !array->size.has_value()) {
            if (diagnose_missing) {
                report_error(
                    "range-based for cannot iterate an array of unknown bound",
                    loc);
            }
            plan.has_error = diagnose_missing;
            return plan;
        }
        plan.kind = RangeEndpointKind::Array;
        plan.array_element = file_.array_element_ref(object_type);
        plan.array_extent = *array->size;
        return plan;
    }

    if (file_.valid(object_type) &&
        file_.type(object_type).kind == cir::TypeKind::Record &&
        record_has_member_name(object_type, "begin") &&
        record_has_member_name(object_type, "end")) {

        plan.kind = RangeEndpointKind::Member;
        return plan;
    }

    std::vector<ExprResult> arguments{range_object};
    add_adl_candidates("begin", arguments, plan.begin_candidates);
    add_adl_candidates("end", arguments, plan.end_candidates);

    auto select_endpoint = [&](std::string_view name,
                               std::vector<cir::EntityId>& candidates) {
        bool ambiguous = false;
        OverloadAmbiguityInfo ambiguity_info;
        cir::EntityId selected = select_overload(
            candidates,
            arguments,
            /*member_object_leading=*/false,
            &ambiguous,
            {},
            &ambiguity_info);
        if (selected.valid() && !ambiguous) {
            candidates = {selected};
            return true;
        }
        if (diagnose_missing) {
            if (ambiguous) {
                report_error("call to '" + std::string(name) +
                                 "' is ambiguous while resolving a range",
                             loc);
                report_overload_ambiguity_notes(ambiguity_info, loc);
            } else {
                report_error("no viable argument-dependent '" +
                                 std::string(name) +
                                 "' function for range initializer",
                             loc);
            }
        }
        return false;
    };

    bool has_begin = select_endpoint("begin", plan.begin_candidates);
    bool has_end = select_endpoint("end", plan.end_candidates);
    if (has_begin && has_end) {
        plan.kind = RangeEndpointKind::ArgumentDependent;
    } else if (diagnose_missing) {
        plan.has_error = true;
    }
    return plan;
}

ExprResult Session::collect_range_endpoint(const RangeEndpointPlan& plan,
                                           ExprResult range_object,
                                           bool begin,
                                           SrcLoc loc) {
    switch (plan.kind) {
        case RangeEndpointKind::Array:
            if (begin) {
                return range_object;
            }
            return collect_binary_expr(
                syntax::BinaryOperator::Add,
                std::move(range_object),
                make_integer_literal(static_cast<int64_t>(plan.array_extent),
                                     std::to_string(plan.array_extent),
                                     loc),
                loc);
        case RangeEndpointKind::Member: {
            ExprResult member = collect_member_access_expr(
                std::move(range_object), begin ? "begin" : "end", false, loc);
            return collect_call_expr(std::move(member), {}, loc);
        }
        case RangeEndpointKind::ArgumentDependent: {
            const std::vector<cir::EntityId>& candidates = begin
                ? plan.begin_candidates
                : plan.end_candidates;
            if (candidates.empty()) {
                ExprResult error;
                error.type = builder_.unknown_type();
                error.category = ValueCategory::PrValue;
                error.has_error = true;
                return error;
            }
            std::string_view name = begin ? "begin" : "end";
            ExprResult callee = make_entity_reference(
                candidates.front(), name, loc);
            callee.candidates = candidates;

            callee.suppress_argument_dependent_lookup = true;
            std::vector<ExprResult> arguments;
            arguments.push_back(std::move(range_object));
            return collect_call_expr(
                std::move(callee), std::move(arguments), loc);
        }
        case RangeEndpointKind::Dependent:
            range_object.name = begin ? ".range.begin" : ".range.end";
            return make_dependent_expr(std::move(range_object), loc);
        case RangeEndpointKind::Invalid:
            break;
    }
    ExprResult error;
    error.type = builder_.unknown_type();
    error.category = ValueCategory::PrValue;
    error.has_error = true;
    return error;
}

void Session::begin_for_body(ForControl& control,
                             std::optional<StmtResult> init,
                             std::optional<ExprResult> condition,
                             std::optional<ExprResult> step,
                             LifetimeBoundary condition_boundary,
                             LifetimeBoundary step_boundary) {
    if (init.has_value()) {
        control.init = std::move(*init);
    }

    if (condition.has_value()) {
        control.condition = require_value(std::move(*condition), UseContext::Condition, control.loc);
        control.condition.fragment = chain(
            std::move(control.condition.fragment),
            finish_lifetime_boundary(condition_boundary, control.loc),
            control.loc);
        control.condition.fragment =
            adopt_or_create_fragment_entry(std::move(control.condition.fragment), "for.cond");
    } else {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("for.cond");
        cir::InstId value = builder_.boolean_literal(true, "true", control.loc);
        control.condition.fragment = finish_fragment_block(block, previous);
        control.condition.value = value;
        control.condition.type = builder_.bool_type();
        control.condition.category = ValueCategory::PrValue;
    }
    control.condition_entry = control.condition.fragment.entry;
    control.condition_exit = control.condition.fragment.exit;

    if (step.has_value()) {
        control.step = collect_expr_stmt(std::move(*step), control.loc,
                                         &step_boundary);
        control.step_entry = control.step.fragment.entry;
        control.step_exit = control.step.fragment.exit;
    }

    cir::BlockId continue_target =
        control.step.fragment.empty() ? control.condition_entry : control.step_entry;
    control_stack_.push_back(ControlTargets{
        ControlKind::Loop,
        continue_target,
        control.continuation_block});
}

StmtResult Session::finish_for(ForControl& control, const StmtResult& body_result) {
    if (!control_stack_.empty()) {
        control_stack_.pop_back();
    }

    cir::Fragment fragment = std::move(control.init.fragment);
    fragment = chain(std::move(fragment), std::move(control.condition.fragment), control.loc);

    builder_.cond_branch_from(control.condition_exit,
                              control.condition.value,
                              control.body_block,
                              control.continuation_block,
                              {},
                              control.loc);

    append_fragment_blocks(fragment, builder_.block_fragment(control.body_block));
    cir::BlockId loop_back_target =
        control.step.fragment.empty() ? control.condition_entry : control.step_entry;
    if (body_result.fragment.empty()) {
        builder_.branch_from(control.body_block, loop_back_target, {}, control.loc);
    } else {
        builder_.branch_from(control.body_block, body_result.fragment.entry, {}, control.loc);
        append_fragment_blocks(fragment, body_result.fragment);
        if (body_result.falls_through && !builder_.block_terminated(body_result.fragment.exit)) {
            builder_.branch_from(body_result.fragment.exit, loop_back_target, {}, control.loc);
        }
    }

    if (!control.step.fragment.empty()) {
        append_fragment_blocks(fragment, control.step.fragment);
        if (control.step.falls_through && !builder_.block_terminated(control.step.fragment.exit)) {
            builder_.branch_from(control.step.fragment.exit, control.condition_entry, {}, control.loc);
        }
    }

    append_fragment_blocks(fragment, builder_.block_fragment(control.continuation_block));
    fragment.exit = control.continuation_block;
    fragment.falls_through = true;
    StmtResult for_scope_cleanups = collect_scope_cleanups(control.loc);
    fragment = chain(std::move(fragment), std::move(for_scope_cleanups.fragment), control.loc);
    leave_scope();
    StmtResult result = make_stmt_result(std::move(fragment), false,
        control.init.has_error || control.condition.has_error ||
        control.step.has_error || body_result.has_error);
    result.contains_switch_label = body_result.contains_switch_label;
    return result;
}

DoWhileControl Session::begin_do_while(SrcLoc loc) {
    DoWhileControl control;
    control.body_block = builder_.create_detached_block("do.body");
    control.condition_block = builder_.create_detached_block("do.continue");
    control.continuation_block = builder_.create_detached_block("do.end");
    control.loc = loc;
    control_stack_.push_back(ControlTargets{
        ControlKind::Loop,
        control.condition_block,
        control.continuation_block});
    return control;
}

StmtResult Session::finish_do_while(DoWhileControl& control,
                                    ExprResult condition,
                                    const StmtResult& body_result,
                                    LifetimeBoundary condition_boundary) {
    if (!control_stack_.empty()) {
        control_stack_.pop_back();
    }

    ExprResult cond = require_value(std::move(condition), UseContext::Condition, control.loc);
    cond.fragment = chain(std::move(cond.fragment),
                          finish_lifetime_boundary(condition_boundary,
                                                   control.loc),
                          control.loc);
    cond.fragment = adopt_or_create_fragment_entry(std::move(cond.fragment), "do.cond");

    cir::Fragment fragment = builder_.block_fragment(control.body_block);
    if (body_result.fragment.empty()) {
        builder_.branch_from(control.body_block, control.condition_block, {}, control.loc);
    } else {
        builder_.branch_from(control.body_block, body_result.fragment.entry, {}, control.loc);
        append_fragment_blocks(fragment, body_result.fragment);
        if (body_result.falls_through && !builder_.block_terminated(body_result.fragment.exit)) {
            builder_.branch_from(body_result.fragment.exit, control.condition_block, {}, control.loc);
        }
    }

    append_fragment_blocks(fragment, builder_.block_fragment(control.condition_block));
    builder_.branch_from(control.condition_block, cond.fragment.entry, {}, control.loc);
    append_fragment_blocks(fragment, cond.fragment);
    builder_.cond_branch_from(cond.fragment.exit,
                              cond.value,
                              control.body_block,
                              control.continuation_block,
                              {},
                              control.loc);

    append_fragment_blocks(fragment, builder_.block_fragment(control.continuation_block));
    fragment.exit = control.continuation_block;
    fragment.falls_through = true;
    StmtResult result =
        make_stmt_result(std::move(fragment), false, cond.has_error || body_result.has_error);
    result.contains_switch_label = body_result.contains_switch_label;
    return result;
}

SwitchControl Session::begin_switch(ExprResult condition,
                                    SrcLoc loc,
                                    LifetimeBoundary condition_boundary) {
    bool dependent_pattern_condition =
        collecting_pattern_ && expr_is_value_dependent(condition);
    if (lang_opts_.is_cxx_mode()) {
        cir::TypeId source = file_.resolved_type(condition.type);
        if (file_.valid(source) &&
            file_.type(source).kind == cir::TypeKind::Record) {
            if (condition.category == ValueCategory::PrValue &&
                condition.value.valid()) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(condition),
                                               /*is_arrow=*/false,
                                               loc);
                condition = std::move(materialized.base_place);
            }
            cir::TypeId contextual_target;
            UserConversionSequence sequence =
                resolve_permitted_implicit_conversion(
                    condition,
                    PermittedImplicitTarget::IntegralOrEnum,
                    &contextual_target,
                    loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_error(
                    "switch condition has an ambiguous contextual "
                    "conversion to integral or enumeration type",
                    loc);
                condition.has_error = true;
            } else if (sequence.kind ==
                       UserConversionSequence::Kind::ConversionFunction) {
                condition = apply_user_conversion_sequence(
                    std::move(condition), contextual_target, sequence, loc);
            }
        }
    }
    ExprResult cond = require_value(std::move(condition), UseContext::RValue, loc);
    if (!is_integer_like_switch_type(file_, cond.type)) {
        if (!dependent_pattern_condition) {
            report_error("switch condition must have integer or enum type",
                         loc);
            cond.has_error = true;
        }
    } else {
        cir::TypeId promoted = integer_promotion_type(cond.type);
        cond = convert_to_arithmetic_type(std::move(cond), promoted, loc);
    }
    if (dependent_pattern_condition) {

        mark_pattern_unusable();
        bump_pattern_taint();
        if (!cond.value.valid()) {
            cir::TypeId placeholder_type = cond.type.valid()
                ? cond.type
                : file_.dependent_type("dependent-switch-condition");
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("switch.dependent.condition");
            cond.value = builder_.name_ref(
                "<dependent-switch-condition>", placeholder_type, loc);
            cond.fragment = chain(
                std::move(cond.fragment),
                finish_fragment_block(block, previous),
                loc);
            cond.type = placeholder_type;
            cond.category = ValueCategory::PrValue;
        }
    }
    cond.fragment = chain(std::move(cond.fragment),
                          finish_lifetime_boundary(condition_boundary, loc),
                          loc);
    cond.fragment = adopt_or_create_fragment_entry(std::move(cond.fragment), "switch.cond");

    SwitchContext context;
    context.condition = std::move(cond);
    context.dispatch_block = builder_.create_detached_block("switch.dispatch");
    context.continuation_block = builder_.create_detached_block("switch.end");
    context.default_target = context.continuation_block;
    context.loc = loc;
    context.control_flow_regions = control_flow_regions_;

    size_t index = switch_contexts_.size();
    switch_contexts_.push_back(std::move(context));
    switch_stack_.push_back(index);
    control_stack_.push_back(ControlTargets{
        ControlKind::Switch,
        {},
        switch_contexts_[index].continuation_block});

    switch_contexts_[index].control_depth_at_entry = control_stack_.size();
    return SwitchControl{index, loc};
}

StmtResult Session::collect_case_stmt(std::vector<SwitchLabelInput> labels,
                                      StmtResult child,
                                      SrcLoc loc) {
    bool has_error = child.has_error;
    if (switch_stack_.empty()) {
        report_error("case or default statement is not inside a switch", loc);
        has_error = true;
        child.has_error = true;
        return child;
    }

    SwitchContext& context = switch_contexts_[switch_stack_.back()];
    if (context.control_flow_regions != control_flow_regions_) {
        report_error(
            "case or default label crosses a control-flow-limited statement boundary",
            loc);
        has_error = true;
    }

    for (CleanupScope& scope : cleanup_scopes_) {
        if (scope.control_depth_at_entry >= context.control_depth_at_entry) {
            scope.suppress_lifetimes = true;
        }
    }
    bool default_only = !labels.empty();
    for (const SwitchLabelInput& label : labels) {
        if (label.kind != SwitchLabelKind::Default) {
            default_only = false;
            break;
        }
    }
    cir::BlockId label_block =
        builder_.create_detached_block(default_only ? "switch.default" : "switch.case");

    for (const SwitchLabelInput& label : labels) {
        if (label.kind == SwitchLabelKind::Default) {
            if (context.has_default) {
                report_error("multiple default labels in one switch", label.loc);
                has_error = true;
            } else {
                context.has_default = true;
                context.default_target = label_block;
            }
            continue;
        }

        bool dependent_label =
            in_template_definition() &&
            (expr_is_dependent(label.value) ||
             expr_is_value_dependent(label.value) ||
             (label.has_range &&
              (expr_is_dependent(label.range_end) ||
               expr_is_value_dependent(label.range_end))));
        if (dependent_label) {

            mark_pattern_unusable();
            bump_pattern_taint();
            continue;
        }

        int64_t low = 0;
        if (!eval_integer_constant(label.value,
                                   low,
                                   label.loc,
                                   "case expression is not an integer constant expression")) {
            has_error = true;
            continue;
        }
        int64_t high = low;
        if (label.has_range) {
            if (!eval_integer_constant(label.range_end,
                                       high,
                                       label.loc,
                                       "case range endpoint is not an integer constant expression")) {
                has_error = true;
                continue;
            }
            if (high < low) {
                report_error("empty range specified", label.loc);
                has_error = true;
                continue;
            }
        }

        low = convert_case_value_to_switch_type(file_, context.condition.type, low);
        high = convert_case_value_to_switch_type(file_, context.condition.type, high);
        if (high < low) {
            report_error("empty range specified", label.loc);
            has_error = true;
            continue;
        }

        bool overlaps_existing_case = false;
        for (const SwitchCaseTarget& existing : context.cases) {
            if (low <= existing.high && existing.low <= high) {
                report_error("duplicate case value", label.loc);
                has_error = true;
                overlaps_existing_case = true;
                break;
            }
        }
        if (!overlaps_existing_case) {
            context.cases.push_back(SwitchCaseTarget{low, high, label_block, label.loc});
        }
    }
    context.has_error = context.has_error || has_error;

    cir::Fragment fragment = builder_.block_fragment(label_block);
    if (child.fragment.empty()) {
        StmtResult result = make_stmt_result(std::move(fragment), child.always_returns, has_error);
        result.contains_switch_label = true;
        return result;
    }

    builder_.branch_from(label_block, child.fragment.entry, {}, loc);
    append_fragment_blocks(fragment, child.fragment);
    fragment.exit = child.fragment.exit;
    fragment.falls_through = child.falls_through;
    StmtResult result = make_stmt_result(std::move(fragment), child.always_returns, has_error);
    result.contains_switch_label = true;
    return result;
}

StmtResult Session::finish_switch(SwitchControl& control, const StmtResult& body_result) {
    if (!control_stack_.empty()) {
        control_stack_.pop_back();
    }
    if (!switch_stack_.empty()) {
        switch_stack_.pop_back();
    }
    if (control.context_index >= switch_contexts_.size()) {
        return body_result;
    }

    SwitchContext& context = switch_contexts_[control.context_index];
    cir::Fragment fragment = context.condition.fragment;
    builder_.branch_from(context.condition.fragment.exit,
                         context.dispatch_block,
                         {},
                         context.loc);

    cir::Fragment dispatch_fragment;
    dispatch_fragment.entry = context.dispatch_block;
    dispatch_fragment.exit = context.dispatch_block;
    dispatch_fragment.blocks.push_back(context.dispatch_block);
    dispatch_fragment.falls_through = false;

    cir::BlockId final_false_target = context.default_target.valid()
        ? context.default_target
        : context.continuation_block;
    std::vector<cir::SwitchCaseRange> cases;
    cases.reserve(context.cases.size());
    for (const SwitchCaseTarget& target : context.cases) {
        cases.push_back(cir::SwitchCaseRange{
            target.low,
            target.high,
            target.target,
            target.loc});
    }
    cir::TypeId condition_type_id = context.condition.type.valid()
        ? context.condition.type
        : (context.condition.value.valid()
               ? file_.inst(context.condition.value).result_type
               : builder_.int_type());
    if (!condition_type_id.valid()) {
        condition_type_id = builder_.int_type();
    }
    builder_.switch_branch_from(context.dispatch_block,
                                context.condition.value,
                                file_.type_ref(condition_type_id),
                                final_false_target,
                                std::move(cases),
                                context.loc);

    append_fragment_blocks(fragment, dispatch_fragment);
    append_fragment_blocks(fragment, body_result.fragment);
    if (body_result.falls_through &&
        !body_result.fragment.empty() &&
        !builder_.block_terminated(body_result.fragment.exit)) {
        builder_.branch_from(body_result.fragment.exit,
                             context.continuation_block,
                             {},
                             context.loc);
    }
    append_fragment_blocks(fragment, builder_.block_fragment(context.continuation_block));
    fragment.exit = context.continuation_block;
    fragment.falls_through = true;

    cir::SwitchFact fact;
    fact.condition = cir::ValueRef{context.condition.value};
    fact.condition_type = file_.type_ref(condition_type_id);
    fact.dispatch_block = context.dispatch_block;
    fact.default_block = final_false_target;
    fact.end_block = context.continuation_block;
    fact.loc = context.loc;
    for (const SwitchCaseTarget& target : context.cases) {
        fact.cases.push_back(cir::SwitchCaseRange{
            target.low,
            target.high,
            target.target,
            target.loc});
    }
    file_.add_switch_fact(std::move(fact));

    return make_stmt_result(std::move(fragment), false,
        context.condition.has_error || context.has_error || body_result.has_error);
}

} // namespace aburi::collect
