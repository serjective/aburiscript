#include <string>

#include "collect.h"
#include "../abi/endian.h"
#include "../abi/mangle_cir.h"

namespace aburi::collect {

namespace {

void append_fragment_blocks(cir::Fragment& target, const cir::Fragment& source) {
    if (source.empty()) {
        return;
    }
    if (target.empty()) {
        target.entry = source.entry;
    }
    target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                         source.blocks.end());
    target.exit = source.exit;
}

void write_u32(std::vector<uint8_t>& bytes, size_t offset, uint32_t value,
               EndiannessKind order) {
    abi::write_scalar_bits(bytes.data() + offset, 4, value, 0, order);
}

void write_i64(std::vector<uint8_t>& bytes, size_t offset, int64_t value,
               EndiannessKind order) {
    abi::write_scalar_bits(bytes.data() + offset, 8,
                           static_cast<uint64_t>(value), 0, order);
}

bool builtin_typeinfo_is_exported(cir::BuiltinTypeKind kind) {
    switch (kind) {
        case cir::BuiltinTypeKind::Void:
        case cir::BuiltinTypeKind::NullPtr:
        case cir::BuiltinTypeKind::Bool:
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
        case cir::BuiltinTypeKind::UChar:
        case cir::BuiltinTypeKind::Char8:
        case cir::BuiltinTypeKind::WChar:
        case cir::BuiltinTypeKind::Char16:
        case cir::BuiltinTypeKind::Char32:
        case cir::BuiltinTypeKind::Short:
        case cir::BuiltinTypeKind::UShort:
        case cir::BuiltinTypeKind::Int:
        case cir::BuiltinTypeKind::UInt:
        case cir::BuiltinTypeKind::Long:
        case cir::BuiltinTypeKind::ULong:
        case cir::BuiltinTypeKind::LongLong:
        case cir::BuiltinTypeKind::ULongLong:
        case cir::BuiltinTypeKind::Int128:
        case cir::BuiltinTypeKind::UInt128:
        case cir::BuiltinTypeKind::USize:
        case cir::BuiltinTypeKind::Float:
        case cir::BuiltinTypeKind::Double:
        case cir::BuiltinTypeKind::LongDouble:
            return true;
        default:
            return false;
    }
}

} // namespace

TryControl Session::begin_try(SrcLoc loc, TryRegionKind kind) {
    TryControl control;
    control.loc = loc;
    control.kind = kind;
    active_try_move_boundaries_.push_back(current_decl_context());
    control.move_boundary_pushed = true;
    control.saved_unwind_target = builder_.current_unwind_target();
    control.pads_snapshot = eh_pads_in_flight_.size();

    control.pad_block = builder_.create_detached_block("try.lpad");
    control.dispatch_block = builder_.create_detached_block("try.dispatch");
    cir::BlockId previous = builder_.current_block();
    builder_.switch_to_block(control.pad_block);

    control.landing_pad = builder_.eh_landing_pad(cir::EhLandingPadPayload{},
                                                  loc);
    control.selector = builder_.eh_selector(control.landing_pad, loc);
    builder_.branch(control.dispatch_block,
                    {control.landing_pad, control.selector}, loc);
    cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
    control.dispatch_exn = builder_.add_block_parameter(
        control.dispatch_block, void_ptr, "exn", loc);
    control.dispatch_sel = builder_.add_block_parameter(
        control.dispatch_block, builder_.int_type(), "sel", loc);
    builder_.switch_to_block(previous);

    eh_pads_in_flight_.push_back(control.landing_pad);
    track_speculative_rollback([this]() {
        if (!eh_pads_in_flight_.empty()) {
            eh_pads_in_flight_.pop_back();
        }
    });
    eh_code_targets_[control.pad_block.index] = control.dispatch_block;
    track_speculative_rollback([this, pad_index = control.pad_block.index]() {
        eh_code_targets_.erase(pad_index);
    });
    builder_.set_current_unwind_target(control.pad_block);
    return control;
}

void Session::finish_try_body(TryControl& control, StmtResult body) {
    builder_.set_current_unwind_target(control.saved_unwind_target);
    if (control.move_boundary_pushed &&
        !active_try_move_boundaries_.empty()) {
        active_try_move_boundaries_.pop_back();
        control.move_boundary_pushed = false;
    }
    control.has_error = control.has_error || body.has_error;
    control.body = std::move(body);
}

void Session::begin_catch_handler(TryControl& control,
                                  std::optional<cir::TypeRef> catch_type,
                                  std::string_view param_name,
                                  SrcLoc loc) {
    TryControl::Handler handler;
    handler.loc = loc;
    if (control.has_catch_all) {

        report_error("handler cannot follow the catch-all handler", loc);
        control.has_error = true;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId entry = begin_fragment_block("catch.body");
    cir::InstId adjusted = builder_.catch_begin(control.dispatch_exn, loc);

    handler.saved_unwind_target = builder_.current_unwind_target();
    handler.cleanup_pad = builder_.create_block("catch.cleanup.lpad");
    handler.cleanup_action = builder_.create_block("catch.cleanup.act");
    builder_.set_block_unwind_target(handler.cleanup_pad, {});
    builder_.set_block_unwind_target(handler.cleanup_action, {});
    builder_.switch_to_block(handler.cleanup_pad);
    cir::EhLandingPadPayload cleanup_payload;
    cleanup_payload.is_cleanup = true;
    cir::InstId cleanup_landing =
        builder_.eh_landing_pad(std::move(cleanup_payload), loc);
    handler.cleanup_landing_pad = cleanup_landing;
    cir::InstId cleanup_selector = builder_.eh_selector(cleanup_landing, loc);
    builder_.branch(handler.cleanup_action,
                    {cleanup_landing, cleanup_selector}, loc);
    cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
    cir::InstId cleanup_exn = builder_.add_block_parameter(
        handler.cleanup_action, void_ptr, "exn", loc);
    cir::InstId cleanup_sel = builder_.add_block_parameter(
        handler.cleanup_action, builder_.int_type(), "sel", loc);
    builder_.switch_to_block(handler.cleanup_action);
    builder_.catch_end(loc);
    emit_unwind_continue(handler.cleanup_action, cleanup_exn, cleanup_sel,
                         handler.saved_unwind_target, loc);
    builder_.switch_to_block(entry);
    builder_.set_current_unwind_target(handler.cleanup_pad);
    ++active_catch_handlers_;
    if (control.kind == TryRegionKind::ConstructorFunction) {
        ++active_constructor_function_try_handlers_;
    }

    control.handler_decl_fragment = cir::Fragment{};
    if (!catch_type.has_value()) {
        handler.is_catch_all = true;
        control.has_catch_all = true;
        control.handler_entry_fragment = finish_fragment_block(entry, previous);
        control.handlers.push_back(std::move(handler));
        return;
    }

    cir::TypeId declared = file_.resolved_type(catch_type->type);
    cir::TypeKind declared_kind =
        file_.valid(declared) ? file_.type(declared).kind : cir::TypeKind::Invalid;
    if (declared_kind == cir::TypeKind::Array) {
        declared = builder_.pointer_type(file_.array_element_ref(declared));
        declared_kind = cir::TypeKind::Pointer;
    } else if (declared_kind == cir::TypeKind::Function) {
        declared = builder_.pointer_type(declared);
        declared_kind = cir::TypeKind::Pointer;
    }
    if (declared_kind == cir::TypeKind::RValueReference) {
        report_error("catch parameter cannot be an rvalue reference", loc);
        control.has_error = true;
    }
    bool by_reference = declared_kind == cir::TypeKind::LValueReference;
    cir::TypeId object_type = declared;
    if (by_reference) {
        object_type =
            file_.resolved_type(file_.reference_referred_ref(declared).type);
    }
    cir::TypeKind object_kind = file_.valid(object_type)
        ? file_.type(object_type).kind
        : cir::TypeKind::Invalid;
    bool object_is_void =
        object_kind == cir::TypeKind::Builtin &&
        [&] {
            const auto* payload = std::get_if<cir::BuiltinTypePayload>(
                &file_.type_payload(object_type));
            return payload && payload->kind == cir::BuiltinTypeKind::Void;
        }();
    if (!file_.valid(object_type) || object_is_void) {
        report_error("cannot catch an object of void type", loc);
        control.has_error = true;
    }
    if (object_kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(object_type);
        if (!facts || facts->is_incomplete) {
            report_error("cannot catch an object of incomplete type", loc);
            control.has_error = true;
        } else if (facts->is_abstract) {
            report_error("cannot catch an object of abstract class type", loc);
            control.has_error = true;
        }
    }
    if (by_reference && object_kind == cir::TypeKind::Pointer) {

        report_error(
            "reference-to-pointer catch parameters are not supported yet",
            loc);
        control.has_error = true;
    }

    handler.typeinfo = control.has_error
        ? cir::EntityId{}
        : typeinfo_entity_for_type(file_.type_ref(object_type), loc);
    if (!control.has_error && !handler.typeinfo.valid()) {
        report_error("catching an object of type '" +
                         file_.format_type(object_type) +
                         "' is not supported yet",
                     loc);
        control.has_error = true;
    }

    ExprResult init;
    if (object_kind == cir::TypeKind::Pointer) {
        init.value = builder_.cast(object_type, adjusted, "value", loc);
        init.type = object_type;
        init.category = ValueCategory::PrValue;
    } else if (file_.valid(object_type)) {
        cir::InstId typed_ptr = builder_.cast(
            builder_.pointer_type(file_.type_ref(object_type)), adjusted,
            "value", loc);
        cir::InstId object_place = builder_.deref(typed_ptr, loc);
        init.value = object_place;
        init.place = object_place;
        init.type = object_type;
        init.category = ValueCategory::LValue;
    }
    control.handler_entry_fragment = finish_fragment_block(entry, previous);

    if (!param_name.empty() && !control.has_error && file_.valid(declared)) {
        DeclFlags flags;
        flags.type_qualifiers = catch_type->qualifiers;
        DeclResult param = declare_local_variable(
            param_name, catch_type->type, std::nullopt, loc, flags,
            /*assume_initializer=*/true);
        param = finish_variable_declaration(
            std::move(param), catch_type->type, std::move(init), loc, flags,
            param_name, ConstructorInitializationKind::Copy);
        if (param.entity.valid() && file_.valid(param.entity)) {
            file_.entity_mut(param.entity).is_exception_declaration = true;
        }
        control.has_error = control.has_error || param.has_error;
        control.handler_decl_fragment = std::move(param.fragment);
    }
    control.handlers.push_back(std::move(handler));
}

void Session::finish_catch_handler(TryControl& control,
                                   StmtResult body,
                                   SrcLoc loc) {
    if (control.handlers.empty()) {
        return;
    }
    TryControl::Handler& handler = control.handlers.back();
    builder_.set_current_unwind_target(handler.saved_unwind_target);
    if (active_catch_handlers_ > 0) {
        --active_catch_handlers_;
    }
    if (control.kind == TryRegionKind::ConstructorFunction &&
        active_constructor_function_try_handlers_ > 0) {
        --active_constructor_function_try_handlers_;
    }
    control.has_error = control.has_error || body.has_error;
    bool body_falls = body.falls_through;
    cir::Fragment fragment =
        chain(std::move(control.handler_entry_fragment),
              std::move(control.handler_decl_fragment), loc);
    fragment = chain(std::move(fragment), std::move(body.fragment), loc);
    if (body_falls) {

        cir::BlockId previous = builder_.current_block();
        cir::BlockId end_block = begin_fragment_block("catch.end");
        if (control.kind == TryRegionKind::ConstructorFunction) {

            builder_.rethrow_from(builder_.current_block(), loc);
        } else {
            builder_.catch_end(loc);
        }
        cir::Fragment end_fragment = finish_fragment_block(end_block, previous);
        fragment = chain(std::move(fragment), std::move(end_fragment), loc);
    }

    handler.fragment = std::move(fragment);
    handler.falls_through = body_falls &&
        control.kind != TryRegionKind::ConstructorFunction;
    handler.always_returns = body.always_returns;
}

StmtResult Session::finish_try(TryControl& control, SrcLoc loc) {

    std::vector<cir::EntityId> own_clauses;
    for (const TryControl::Handler& handler : control.handlers) {
        if (!handler.is_catch_all && handler.typeinfo.valid()) {
            own_clauses.push_back(handler.typeinfo);
        }
    }
    auto patch_landing_pad = [&](cir::InstId pad_inst) {
        if (!pad_inst.valid() || !file_.valid(pad_inst)) {
            return;
        }
        const auto* existing = std::get_if<cir::EhLandingPadPayload>(
            &file_.payload(file_.inst(pad_inst).payload_index));
        cir::EhLandingPadPayload patched =
            existing ? *existing : cir::EhLandingPadPayload{};
        for (cir::EntityId clause : own_clauses) {
            bool present = false;
            for (cir::EntityId prior : patched.clause_typeinfos) {
                present = present || prior == clause;
            }
            if (!present) {
                patched.clause_typeinfos.push_back(clause);
            }
        }
        patched.has_catch_all = patched.has_catch_all || control.has_catch_all;
        file_.inst_mut(pad_inst).payload_index =
            file_.add_payload(cir::InstPayload{std::move(patched)});
    };

    patch_landing_pad(control.landing_pad);
    for (size_t i = control.pads_snapshot; i < eh_pads_in_flight_.size();
         ++i) {
        if (eh_pads_in_flight_[i] != control.landing_pad) {
            patch_landing_pad(eh_pads_in_flight_[i]);
        }
    }

    for (const TryControl::Handler& handler : control.handlers) {
        if (!handler.cleanup_landing_pad.valid()) {
            continue;
        }
        eh_pads_in_flight_.push_back(handler.cleanup_landing_pad);
        track_speculative_rollback([this]() {
            if (!eh_pads_in_flight_.empty()) {
                eh_pads_in_flight_.pop_back();
            }
        });
    }

    bool body_falls = control.body.falls_through;
    bool body_returns = control.body.always_returns;
    cir::Fragment fragment = adopt_or_create_fragment_entry(
        std::move(control.body.fragment), "try.body");
    cir::BlockId continuation = builder_.create_detached_block("try.end");
    if (!builder_.block_terminated(fragment.exit)) {
        if (body_falls) {
            builder_.branch_from(fragment.exit, continuation, {}, loc);
        } else {

            builder_.unreachable_from(fragment.exit, loc);
        }
    }

    append_fragment_blocks(fragment, builder_.block_fragment(control.pad_block));
    append_fragment_blocks(fragment,
                           builder_.block_fragment(control.dispatch_block));
    cir::BlockId previous = builder_.current_block();
    builder_.switch_to_block(control.dispatch_block);
    cir::BlockId fallback{};
    for (const TryControl::Handler& handler : control.handlers) {
        if (handler.is_catch_all) {
            continue;
        }
        if (!handler.typeinfo.valid() || handler.fragment.empty()) {
            continue;
        }
        cir::InstId type_id = builder_.eh_typeid_for(handler.typeinfo, loc);
        cir::InstId matches = builder_.binary(cir::BinaryOpKind::Equal,
                                              builder_.bool_type(),
                                              control.dispatch_sel, type_id,
                                              loc);
        cir::BlockId next = builder_.create_detached_block("catch.dispatch");
        builder_.set_block_unwind_target(next, {});
        builder_.cond_branch(matches, handler.fragment.entry, next, {}, loc);
        append_fragment_blocks(fragment, builder_.block_fragment(next));
        builder_.switch_to_block(next);
    }
    for (const TryControl::Handler& handler : control.handlers) {
        if (handler.is_catch_all && !handler.fragment.empty()) {
            fallback = handler.fragment.entry;
        }
    }
    if (fallback.valid()) {
        builder_.branch(fallback, {}, loc);
    } else {
        emit_unwind_continue(builder_.current_block(), control.dispatch_exn,
                             control.dispatch_sel,
                             control.saved_unwind_target, loc);
    }
    builder_.switch_to_block(previous);

    bool any_handler_falls = false;
    bool all_handlers_return = true;
    for (TryControl::Handler& handler : control.handlers) {
        if (handler.fragment.empty()) {
            continue;
        }
        append_fragment_blocks(fragment, handler.fragment);
        if (!builder_.block_terminated(handler.fragment.exit)) {
            if (handler.falls_through) {
                builder_.branch_from(handler.fragment.exit, continuation, {},
                                     loc);
            } else {
                builder_.unreachable_from(handler.fragment.exit, loc);
            }
        }
        any_handler_falls = any_handler_falls || handler.falls_through;
        all_handlers_return = all_handlers_return && handler.always_returns;
    }

    append_fragment_blocks(fragment, builder_.block_fragment(continuation));
    fragment.exit = continuation;
    bool all_return = body_returns && all_handlers_return;
    fragment.falls_through = body_falls || any_handler_falls;
    return make_stmt_result(std::move(fragment), all_return,
                            control.has_error);
}

bool Session::expression_potentially_throws(const ExprResult& expr,
                                            bool* dependent) {

    if (dependent) {
        *dependent = expr_is_dependent(expr);
    }
    auto callable_potentially_throws = [&](cir::TypeId type) {
        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(type)));
        return !payload ||
               payload->exception_spec.kind !=
                   cir::FunctionExceptionSpecKind::NonThrowing;
    };
    for (cir::BlockId block_id : expr.fragment.blocks) {
        if (!file_.valid(block_id)) {
            continue;
        }
        const cir::Block& block = file_.block(block_id);
        switch (block.terminator.kind) {
            case cir::TerminatorKind::Throw:
            case cir::TerminatorKind::Rethrow:
                return true;
            default:
                break;
        }
        for (cir::InstId inst_id : block.instructions) {
            if (!file_.valid(inst_id)) {
                continue;
            }
            const cir::Inst& inst = file_.inst(inst_id);
            std::vector<cir::Operand> operands = file_.operands(inst.operands);
            switch (inst.kind) {
                case cir::InstKind::Call: {
                    if (operands.empty()) {
                        break;
                    }
                    if (const auto* entity =
                            std::get_if<cir::EntityId>(&operands[0].data)) {
                        if (callable_potentially_throws(
                                file_.entity(*entity).type)) {
                            return true;
                        }
                        break;
                    }
                    if (const auto* value =
                            std::get_if<cir::ValueRef>(&operands[0].data)) {
                        cir::TypeId callee_type =
                            file_.inst(value->inst).result_type;
                        if (callable_potentially_throws(
                                file_.pointer_pointee_type(callee_type))) {
                            return true;
                        }
                    }
                    break;
                }
                case cir::InstKind::ConstructInPlace:
                case cir::InstKind::Destroy: {
                    if (operands.size() > 1) {
                        if (const auto* entity = std::get_if<cir::EntityId>(
                                &operands[1].data);
                            entity && entity->valid() &&
                            callable_potentially_throws(
                                file_.entity(*entity).type)) {
                            return true;
                        }
                    }

                    if (inst.kind == cir::InstKind::ConstructInPlace &&
                        !operands.empty()) {
                        if (const auto* place_ref =
                                std::get_if<cir::ValueRef>(&operands[0].data);
                            place_ref && place_ref->valid() &&
                            file_.valid(place_ref->inst)) {
                            const cir::Inst& place =
                                file_.inst(place_ref->inst);
                            if (place.kind == cir::InstKind::LocalPlace) {
                                std::vector<cir::Operand> place_operands =
                                    file_.operands(place.operands);
                                const cir::EntityId* object =
                                    place_operands.empty()
                                        ? nullptr
                                        : std::get_if<cir::EntityId>(
                                              &place_operands.front().data);
                                if (object && object->valid() &&
                                    file_.valid(*object) &&
                                    file_.entity(*object).storage_duration ==
                                        cir::StorageDuration::Automatic) {
                                    cir::EntityId destructor =
                                        record_destructor(
                                            file_.entity(*object).type);
                                    if (destructor.valid() &&
                                        callable_potentially_throws(
                                            file_.entity(
                                                structor_complete_variant(
                                                    destructor))
                                                .type)) {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
                case cir::InstKind::DependentCall:
                case cir::InstKind::DependentRegion:
                    if (dependent) {
                        *dependent = true;
                    }
                    return true;
                default:
                    break;
            }
        }
    }

    auto lifetime_destructor_throws = [&](cir::TypeId type) {
        cir::TypeId leaf = array_class_element_leaf(type);
        cir::EntityId destructor =
            record_destructor(leaf.valid() ? leaf : type);
        if (destructor.valid() &&
            callable_potentially_throws(file_.entity(
                structor_complete_variant(destructor)).type)) {
            return true;
        }
        return false;
    };
    for (cir::LifetimeId lifetime : expr.materialized_lifetimes) {
        if (lifetime.valid() &&
            lifetime.index < lifetime_obligations_.size() &&
            lifetime_obligations_[lifetime.index].id == lifetime &&
            lifetime_destructor_throws(
                lifetime_obligations_[lifetime.index].type)) {
            return true;
        }
    }
    cir::EntityId temporary = temporary_entity_of_value(expr.value);
    if (temporary.valid() && file_.valid(temporary) &&
        lifetime_destructor_throws(file_.entity(temporary).type)) {
        return true;
    }
    return false;
}

ExprResult Session::collect_noexcept_expr(ExprResult operand,
                                          bool potentially_throwing,
                                          bool dependent,
                                          SrcLoc loc) {
    ExprResult result = make_boolean_literal(!potentially_throwing,
                                             potentially_throwing
                                                 ? "false"
                                                 : "true",
                                             loc);
    if (!dependent) {
        return result;
    }

    cir::TemplateValueExpression expression =
        std::move(operand.template_value_expr);

    expression.canonical_id = {};
    if (expression.definition_context.valid() &&
        !file_.valid(expression.definition_context)) {
        expression.definition_context = current_decl_context();
    }
    for (cir::TemplateValueExprNode& node : expression.nodes) {
        if (node.type.valid() && !file_.valid(node.type)) {
            node.type = {};
        }
        if (node.result_type.type.valid() &&
            !file_.valid(node.result_type.type)) {
            node.result_type = {};
        }
        if (node.qualifier_type.type.valid() &&
            !file_.valid(node.qualifier_type.type)) {
            node.qualifier_type = {};
        }
        if (node.entity.valid() && !file_.valid(node.entity)) {
            node.entity = {};
        }
        if (node.name.valid() && !file_.valid(node.name)) {
            node.name = {};
        }
    }
    if (!expression.valid()) {
        cir::TemplateValueExprNode operand_node;
        operand_node.kind = cir::TemplateValueExprKind::TypeOperand;
        operand_node.value = static_cast<int64_t>(operand.category);
        if (operand.type.valid() && file_.valid(operand.type)) {
            operand_node.result_type = file_.type_ref(operand.type);
        }
        operand_node.entity = operand.entity.valid() &&
                file_.valid(operand.entity)
            ? operand.entity
            : cir::EntityId{};
        operand_node.name = !operand.name.empty()
            ? file_.intern_name(operand.name)
            : (operand.dependent_value_name.valid() &&
                       file_.valid(operand.dependent_value_name)
                   ? operand.dependent_value_name
                   : cir::NameId{});
        if (operand.dependent_value_qualifier.type.valid() &&
            file_.valid(operand.dependent_value_qualifier.type)) {
            operand_node.qualifier_type = operand.dependent_value_qualifier;
        }
        operand_node.semantic_key = !operand.name.empty()
            ? operand.name
            : (operand.type.valid() && file_.valid(operand.type)
                   ? file_.format_type(operand.type)
                   : std::string("<dependent-operand>"));
        expression.nodes.push_back(operand_node);
        expression.root = 0;
        expression.loc = loc;
        expression.definition_context = current_decl_context();
        expression.definition_lookup_generation = lookup_generation_;
    }

    cir::TemplateValueExprNode noexcept_node;
    noexcept_node.kind = cir::TemplateValueExprKind::Noexcept;
    noexcept_node.lhs = expression.root;
    noexcept_node.result_type =
        file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::Bool));
    expression.nodes.push_back(noexcept_node);
    expression.root = static_cast<uint32_t>(expression.nodes.size() - 1);
    expression.canonical_id = {};

    result.value_dependent = true;
    result.references_template_value_parameter =
        operand.references_template_value_parameter;
    result.template_value_expr = std::move(expression);
    if (collecting_pattern()) {
        bump_pattern_taint();
    }
    return result;
}

void Session::begin_noexcept_body_region(cir::TypeId fn_type, SrcLoc loc) {

    if (!lang_opts_.is_cxx_mode() || !builder_.current_function().valid()) {
        return;
    }
    const auto* payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(file_.resolved_type(fn_type)));
    if (!payload ||
        payload->exception_spec.kind !=
            cir::FunctionExceptionSpecKind::NonThrowing) {
        return;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId pad = builder_.create_block("noexcept.lpad");
    cir::BlockId action = builder_.create_block("noexcept.terminate");
    builder_.set_block_unwind_target(pad, {});
    builder_.set_block_unwind_target(action, {});
    builder_.switch_to_block(pad);
    cir::EhLandingPadPayload clauses;
    clauses.has_catch_all = true;
    cir::InstId landing_pad =
        builder_.eh_landing_pad(std::move(clauses), loc);
    cir::InstId selector = builder_.eh_selector(landing_pad, loc);
    builder_.branch(action, {landing_pad, selector}, loc);
    cir::TypeId void_type = builder_.void_type();
    cir::InstId exn_param = builder_.add_block_parameter(
        action, builder_.pointer_type(void_type), "exn", loc);
    builder_.add_block_parameter(action, builder_.int_type(), "sel", loc);
    builder_.switch_to_block(action);
    builder_.catch_begin(exn_param, loc);
    cir::EntityId terminate_fn = runtime_function(
        file_.abi_policy().eh_runtime_hooks.terminate,
        function_type(file_.type_ref(void_type), {}, false, true), loc);
    file_.entity_mut(terminate_fn).attr_facts.is_noreturn = true;
    builder_.call(terminate_fn, void_type, {}, loc);
    builder_.unreachable(loc);
    builder_.switch_to_block(previous);

    eh_code_targets_[pad.index] = action;
    track_speculative_rollback([this, pad_index = pad.index]() {
        eh_code_targets_.erase(pad_index);
    });
    builder_.set_current_unwind_target(pad);
}

void Session::emit_unwind_continue(cir::BlockId from,
                                   cir::InstId exn,
                                   cir::InstId sel,
                                   cir::BlockId enclosing_pad,
                                   SrcLoc loc) {
    if (enclosing_pad.valid()) {
        auto found = eh_code_targets_.find(enclosing_pad.index);
        if (found != eh_code_targets_.end()) {
            builder_.branch_from(from, found->second, {exn, sel}, loc);
            return;
        }
    }
    builder_.resume_from(from, exn, sel, loc);
}

cir::EntityId Session::class_typeinfo_entity(cir::EntityId record_entity,
                                             const cir::RecordFacts& facts,
                                             SrcLoc loc) {
    if (facts.typeinfo_entity.valid()) {
        return facts.typeinfo_entity;
    }
    std::string zti_symbol =
        abi::itanium_record_data_symbol(file_, record_entity, "_ZTI");
    if (zti_symbol.empty()) {
        return {};
    }
    auto found = typeinfo_entities_.find(zti_symbol);
    if (found != typeinfo_entities_.end()) {
        return found->second;
    }

    std::string zts_symbol =
        abi::itanium_record_data_symbol(file_, record_entity, "_ZTS");
    std::string type_string = zts_symbol.substr(4);
    cir::TypeId zts_type =
        builder_.array_type(builder_.char_type(), type_string.size() + 1);
    cir::EntityId zts_entity =
        builder_.add_entity(cir::EntityKind::Variable, zts_symbol, zts_type,
                            {}, loc, cir::StorageDuration::Static);
    cir::Entity& zts_record = file_.entity_mut(zts_entity);
    zts_record.is_definition = true;
    zts_record.linkage = cir::LinkageKind::LinkOnceODR;
    zts_record.is_extern_c = true;
    mark_generated_abi_entity(zts_entity, record_entity,
                              cir::GeneratedSymbolRole::TypeName);
    zts_record.qualifiers = cir::QualConst;
    zts_record.has_static_initializer = true;
    zts_record.static_initializer_bytes.assign(type_string.begin(),
                                               type_string.end());
    zts_record.static_initializer_bytes.push_back(0);

    const std::vector<cir::RecordBaseFact>& bases = facts.bases;
    bool is_si = bases.size() == 1 && !bases.front().is_virtual &&
                 bases.front().declared_access ==
                     cir::RecordMemberAccess::Public &&
                 bases.front().has_non_virtual_offset &&
                 bases.front().non_virtual_offset == 0;
    const char* typeinfo_class_vtable =
        bases.empty() ? "_ZTVN10__cxxabiv117__class_type_infoE"
        : is_si       ? "_ZTVN10__cxxabiv120__si_class_type_infoE"
                      : "_ZTVN10__cxxabiv121__vmi_class_type_infoE";

    std::vector<cir::EntityId> base_typeinfos;
    if (!bases.empty()) {
        base_typeinfos.reserve(bases.size());
        for (const cir::RecordBaseFact& base : bases) {
            const cir::RecordFacts* base_facts = file_.record_facts_for_type(
                file_.resolved_type(base.type.type));
            cir::EntityId base_zti =
                base_facts
                    ? class_typeinfo_entity(base.record_entity, *base_facts,
                                            loc)
                    : cir::EntityId{};
            base_typeinfos.push_back(base_zti);
        }
    }

    const size_t ptr = std::max<size_t>(
        1, (file_.target_info().pointer_width + 7) / 8);
    size_t size_bytes = bases.empty() ? 2 * ptr
                        : is_si       ? 3 * ptr
                                      : 2 * ptr + 8 + 2 * ptr * bases.size();
    cir::TypeId zti_type = builder_.array_type(
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void)),
        (size_bytes + ptr - 1) / ptr);

    cir::EntityId typeinfo_vtable =
        extern_runtime_global(typeinfo_class_vtable, loc);
    cir::EntityId zti_entity =
        builder_.add_entity(cir::EntityKind::Variable, zti_symbol, zti_type,
                            {}, loc, cir::StorageDuration::Static);
    cir::Entity& zti_record = file_.entity_mut(zti_entity);
    zti_record.is_definition = true;
    zti_record.linkage = cir::LinkageKind::LinkOnceODR;
    zti_record.is_extern_c = true;
    mark_generated_abi_entity(zti_entity, record_entity,
                              cir::GeneratedSymbolRole::TypeInfo);
    zti_record.object_origin = cir::EntityObjectOrigin::TypeInfo;
    zti_record.has_static_initializer = true;
    zti_record.static_initializer_bytes.assign(size_bytes, 0);

    zti_record.static_initializer_relocations.push_back(
        cir::StaticInitializerRelocation{
            0, typeinfo_vtable,
            static_cast<int64_t>(2 * ptr)});
    zti_record.static_initializer_relocations.push_back(
        cir::StaticInitializerRelocation{ptr, zts_entity, 0});

    if (is_si) {
        if (base_typeinfos.front().valid()) {
            zti_record.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{2 * ptr,
                                                 base_typeinfos.front(), 0});
        }
    } else if (!bases.empty()) {

        write_u32(zti_record.static_initializer_bytes, 2 * ptr, 0,
                  file_.target_info().endianness);
        write_u32(zti_record.static_initializer_bytes, 2 * ptr + 4,
                  static_cast<uint32_t>(bases.size()),
                  file_.target_info().endianness);
        for (size_t i = 0; i < bases.size(); ++i) {
            const cir::RecordBaseFact& base = bases[i];
            size_t descriptor_offset = 2 * ptr + 8 + 2 * ptr * i;
            if (base_typeinfos[i].valid()) {
                zti_record.static_initializer_relocations.push_back(
                    cir::StaticInitializerRelocation{descriptor_offset,
                                                     base_typeinfos[i], 0});
            }

            int64_t offset = 0;
            if (base.is_virtual) {
                for (const cir::RecordFacts::VirtualBase& vbase :
                     facts.virtual_bases) {
                    if (vbase.record_entity == base.record_entity) {
                        offset = -static_cast<int64_t>(
                            3 * ptr + ptr * vbase.vtable_index);
                        break;
                    }
                }
            } else if (base.has_non_virtual_offset) {
                offset = static_cast<int64_t>(base.non_virtual_offset);
            }
            int64_t flags = (base.is_virtual ? 0x1 : 0) |
                            (base.declared_access ==
                                     cir::RecordMemberAccess::Public
                                 ? 0x2
                                 : 0);

            abi::write_scalar_bits(
                zti_record.static_initializer_bytes.data() +
                    descriptor_offset + ptr,
                ptr, static_cast<uint64_t>(offset * 256 + flags), 0,
                file_.target_info().endianness);
        }
    }

    typeinfo_entities_.emplace(zti_symbol, zti_entity);
    track_speculative_rollback([this, zti_symbol]() {
        typeinfo_entities_.erase(zti_symbol);
    });
    return zti_entity;
}

ExprResult Session::collect_throw_expr(std::optional<ExprResult> operand,
                                       SrcLoc loc) {
    ExprResult result;
    result.type = builder_.void_type();
    result.category = ValueCategory::PrValue;

    if (operand.has_value() && expr_is_dependent(*operand)) {
        return make_deferred_typed_expr(std::move(*operand),
                                        builder_.void_type(),
                                        ValueCategory::PrValue,
                                        loc);
    }

    if (!operand.has_value()) {

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.rethrow");
        builder_.rethrow_from(builder_.current_block(), loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        fragment.falls_through = false;
        result.fragment = std::move(fragment);
        return result;
    }

    ExprResult source = std::move(*operand);
    cir::TypeId source_resolved = file_.resolved_type(source.type);
    bool source_is_record = file_.valid(source_resolved) &&
        file_.type(source_resolved).kind == cir::TypeKind::Record;
    ExprResult value = source_is_record
        ? source
        : require_value(std::move(source), UseContext::RValue, loc);
    if (value.has_error) {
        result.fragment = std::move(value.fragment);
        result.has_error = true;
        return result;
    }
    cir::TypeId object_type = file_.resolved_type(value.type);
    if (!file_.valid(object_type)) {
        report_error("cannot determine the thrown expression's type", loc);
        result.has_error = true;
        return result;
    }
    const cir::Type& object_record = file_.type(object_type);
    const cir::RecordFacts* facts =
        object_record.kind == cir::TypeKind::Record
            ? file_.record_facts_for_type(object_type)
            : nullptr;
    if (object_record.kind == cir::TypeKind::Record &&
        (!facts || facts->is_incomplete)) {
        report_error("cannot throw an object of incomplete type", loc);
        result.has_error = true;
        return result;
    }
    if (facts && facts->is_abstract) {
        report_error("cannot throw an object of abstract class type", loc);
        result.has_error = true;
        return result;
    }
    if (object_record.kind == cir::TypeKind::Pointer) {
        cir::TypeRef pointee = file_.pointer_pointee_ref(object_type);
        cir::TypeId pointee_resolved = file_.resolved_type(pointee.type);
        if (file_.valid(pointee_resolved) &&
            file_.type(pointee_resolved).kind == cir::TypeKind::Record) {
            const cir::RecordFacts* pointee_facts =
                file_.record_facts_for_type(pointee_resolved);
            if (!pointee_facts || pointee_facts->is_incomplete) {
                report_error(
                    "cannot throw a pointer to an incomplete type", loc);
                result.has_error = true;
                return result;
            }
        }
    }

    cir::EntityId typeinfo =
        typeinfo_entity_for_type(file_.type_ref(object_type), loc);
    if (!typeinfo.valid()) {
        report_error("throwing an object of type '" +
                         file_.format_type(object_type) +
                         "' is not supported yet",
                     loc);
        result.has_error = true;
        return result;
    }

    cir::EntityId constructor{};
    ConstructorCallMaterialization materialized;
    bool use_constructor = source_is_record &&
        value.category != ValueCategory::PrValue;
    if (use_constructor) {
        ObjectTransferSelection selection =
            select_object_transfer_constructor(
                object_type, value, ImplicitMoveContext::Throw, loc);
        if (!selection.constructor.valid()) {
            report_error(selection.ambiguous
                             ? "exception object construction is ambiguous"
                             : "no matching constructor for exception object",
                         loc);
            result.has_error = true;
            return result;
        }
        constructor = selection.constructor;
        value.category = selection.selected_category;
        std::vector<ExprResult> arguments;
        arguments.push_back(std::move(value));
        materialized = materialize_selected_constructor_call(
            constructor, std::move(arguments), loc);
        if (materialized.has_error) {
            result.fragment = std::move(materialized.argument_fragment);
            result.has_error = true;
            return result;
        }
    } else if (source_is_record) {
        value = require_value(std::move(value), UseContext::RValue, loc);
    }

    cir::EntityId destructor = record_destructor(object_type);
    if (!validate_potentially_invoked_destructor(object_type, loc)) {
        result.has_error = true;
    }
    cir::BlockId allocation_previous = builder_.current_block();
    cir::BlockId allocation_block =
        begin_fragment_block("expr.throw.allocate");
    cir::InstId exception =
        builder_.eh_alloc_exception(file_.type_ref(object_type), loc);
    cir::Fragment allocation_fragment =
        finish_fragment_block(allocation_block, allocation_previous);

    bool adopted_exception_object = false;
    if (!use_constructor && source_is_record &&
        value.category == ValueCategory::PrValue) {
        adopted_exception_object =
            adopt_materialized_object_storage(value, exception);
        for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
            transfer_lifetime(lifetime, LifetimeOwnerKind::ExceptionObject);
        }
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.throw");
    if (use_constructor) {
        emit_construct_in_place(exception,
                                structor_complete_variant(constructor),
                                materialized.argument_values, loc);
    } else {
        cir::InstId store = builder_.store(exception, value.value, loc);
        if (adopted_exception_object) {
            file_.inst_mut(store).runtime_elided_object_operation = true;
        }
    }
    builder_.throw_from(builder_.current_block(), exception, typeinfo,
                        destructor.valid()
                            ? structor_complete_variant(destructor)
                            : cir::EntityId{},
                        loc);
    cir::Fragment throw_fragment = finish_fragment_block(block, previous);
    cir::Fragment operand_fragment =
        use_constructor ? std::move(materialized.argument_fragment)
                        : std::move(value.fragment);
    cir::Fragment fragment = chain(std::move(allocation_fragment),
                                   std::move(operand_fragment), loc);
    fragment = chain(std::move(fragment),
                     std::move(throw_fragment), loc);
    fragment.falls_through = false;
    result.fragment = std::move(fragment);
    return result;
}

cir::EntityId Session::typeinfo_entity_for_type(cir::TypeRef type, SrcLoc loc) {

    cir::TypeId resolved = file_.resolved_type(type.type);
    if (!file_.valid(resolved)) {
        return {};
    }
    if (file_.type(resolved).kind == cir::TypeKind::LValueReference ||
        file_.type(resolved).kind == cir::TypeKind::RValueReference) {
        type = file_.reference_referred_ref(resolved);
        resolved = file_.resolved_type(type.type);
    }
    type = cir::TypeRef{resolved, cir::QualNone, cir::MemorySpace::Default};
    if (!file_.valid(resolved)) {
        return {};
    }

    const cir::Type& semantic_type = file_.type(resolved);
    if (objc_.initialized &&
        semantic_type.kind == cir::TypeKind::Pointer) {

        cir::TypeId pointee =
            file_.resolved_type(file_.pointer_pointee_ref(resolved).type);
        cir::EntityId interface = objc_interface_for_object_type(pointee);
        if (interface.valid()) {
            return objc_ehtype_entity(interface, loc);
        }
        if (file_.valid(pointee) &&
            pointee == file_.resolved_type(objc_id_pointee_type())) {
            return extern_runtime_global("OBJC_EHTYPE_id", loc);
        }
    }
    if (semantic_type.kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(resolved);
        if (facts && !facts->is_incomplete) {
            return class_typeinfo_entity(facts->entity, *facts, loc);
        }

    } else if (semantic_type.kind == cir::TypeKind::Builtin) {
        const auto* payload = std::get_if<cir::BuiltinTypePayload>(
            &file_.type_payload(resolved));
        if (!payload || !builtin_typeinfo_is_exported(payload->kind)) {
            return {};
        }
        std::string symbol =
            abi::itanium_type_data_symbol(file_, type, "_ZTI");
        if (symbol.empty()) {
            return {};
        }
        cir::EntityId entity = extern_runtime_global(symbol, loc);
        file_.entity_mut(entity).object_origin =
            cir::EntityObjectOrigin::TypeInfo;
        return entity;
    }

    auto contains_incomplete_class = [&](auto&& self,
                                         cir::TypeRef candidate) -> bool {
        cir::TypeId candidate_type = file_.resolved_type(candidate.type);
        if (!file_.valid(candidate_type)) {
            return false;
        }
        switch (file_.type(candidate_type).kind) {
            case cir::TypeKind::Record: {
                const cir::RecordFacts* facts =
                    file_.record_facts_for_type(candidate_type);
                return !facts || facts->is_incomplete;
            }
            case cir::TypeKind::Pointer:
                return self(self, file_.pointer_pointee_ref(candidate_type));
            case cir::TypeKind::MemberPointer:
                return self(self,
                            file_.member_pointer_member_ref(candidate_type)) ||
                       self(self,
                            file_.member_pointer_class_ref(candidate_type));
            case cir::TypeKind::Array:
                return self(self, file_.array_element_ref(candidate_type));
            default:
                return false;
        }
    };

    auto descriptor_owner = [&]() -> cir::EntityId {
        if (semantic_type.kind == cir::TypeKind::Record) {
            return file_.record_entity(resolved);
        }
        if (semantic_type.kind == cir::TypeKind::Enum) {
            const auto* enumeration = std::get_if<cir::EnumTypePayload>(
                &file_.type_payload(resolved));
            return enumeration ? enumeration->entity : cir::EntityId{};
        }
        return {};
    };

    const char* runtime_vtable = nullptr;
    size_t descriptor_words = 2;
    uint32_t pbase_flags = 0;
    cir::TypeRef pointee_type{};
    cir::TypeRef context_type{};
    bool has_pointee = false;
    bool has_context = false;
    bool force_internal = false;

    switch (semantic_type.kind) {
        case cir::TypeKind::Record:
            runtime_vtable = "_ZTVN10__cxxabiv117__class_type_infoE";
            force_internal = true;
            break;
        case cir::TypeKind::Enum:
            runtime_vtable = "_ZTVN10__cxxabiv116__enum_type_infoE";
            break;
        case cir::TypeKind::Array:
            runtime_vtable = "_ZTVN10__cxxabiv117__array_type_infoE";
            break;
        case cir::TypeKind::Function:
            runtime_vtable = "_ZTVN10__cxxabiv120__function_type_infoE";
            break;
        case cir::TypeKind::Pointer: {
            pointee_type = file_.pointer_pointee_ref(resolved);
            cir::TypeId pointee_resolved =
                file_.resolved_type(pointee_type.type);

            if (file_.valid(pointee_resolved) &&
                file_.type(pointee_resolved).kind == cir::TypeKind::Builtin) {
                const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
                    &file_.type_payload(pointee_resolved));
                if (builtin && builtin_typeinfo_is_exported(builtin->kind) &&
                    (pointee_type.qualifiers & ~cir::QualConst) == 0) {
                    std::string symbol =
                        abi::itanium_type_data_symbol(file_, type, "_ZTI");
                    if (symbol.empty()) {
                        return {};
                    }
                    cir::EntityId entity =
                        extern_runtime_global(symbol, loc);
                    file_.entity_mut(entity).object_origin =
                        cir::EntityObjectOrigin::TypeInfo;
                    return entity;
                }
            }
            runtime_vtable = "_ZTVN10__cxxabiv119__pointer_type_infoE";
            descriptor_words = 4;
            has_pointee = true;
            break;
        }
        case cir::TypeKind::MemberPointer:
            runtime_vtable =
                "_ZTVN10__cxxabiv129__pointer_to_member_type_infoE";
            descriptor_words = 5;
            pointee_type = file_.member_pointer_member_ref(resolved);
            context_type = file_.member_pointer_class_ref(resolved);
            has_pointee = true;
            has_context = true;
            break;
        default:
            return {};
    }

    if (has_pointee) {
        if (pointee_type.qualifiers & cir::QualConst) {
            pbase_flags |= 0x1;
        }
        if (pointee_type.qualifiers & cir::QualVolatile) {
            pbase_flags |= 0x2;
        }
        if (pointee_type.qualifiers & cir::QualRestrict) {
            pbase_flags |= 0x4;
        }
        if (contains_incomplete_class(contains_incomplete_class,
                                      pointee_type)) {
            pbase_flags |= 0x8;
        }
        cir::TypeId pointee_resolved =
            file_.resolved_type(pointee_type.type);
        if (file_.valid(pointee_resolved) &&
            file_.type(pointee_resolved).kind == cir::TypeKind::Function) {
            const auto* function = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(pointee_resolved));
            if (function && function->exception_spec.kind ==
                                cir::FunctionExceptionSpecKind::NonThrowing) {
                pbase_flags |= 0x40;

                pointee_type.type = file_.function_type(
                    function->return_type,
                    function->parameters,
                    function->is_variadic,
                    function->has_prototype,
                    function->member_is_const,
                    {},
                    function->parameter_pack_flags,
                    function->member_ref_qualifier,
                    function->member_is_volatile);
            }
        }
    }
    if (has_context &&
        contains_incomplete_class(contains_incomplete_class, context_type)) {
        pbase_flags |= 0x10;
    }
    force_internal = force_internal || (pbase_flags & (0x8 | 0x10)) != 0;

    cir::EntityId pointee_typeinfo = has_pointee
        ? typeinfo_entity_for_type(pointee_type, loc)
        : cir::EntityId{};
    cir::EntityId context_typeinfo = has_context
        ? typeinfo_entity_for_type(context_type, loc)
        : cir::EntityId{};
    if ((has_pointee && !pointee_typeinfo.valid()) ||
        (has_context && !context_typeinfo.valid())) {
        return {};
    }

    std::string zti_symbol =
        abi::itanium_type_data_symbol(file_, type, "_ZTI");
    std::string zts_symbol =
        abi::itanium_type_data_symbol(file_, type, "_ZTS");
    if (zti_symbol.empty() || zts_symbol.size() < 4) {
        return {};
    }
    std::string cache_key =
        (force_internal ? "incomplete:" : "complete:") + zti_symbol;
    auto found = typeinfo_entities_.find(cache_key);
    if (found != typeinfo_entities_.end()) {
        return found->second;
    }

    std::string emitted_zti_symbol = zti_symbol;
    std::string emitted_zts_symbol = zts_symbol;
    if (force_internal) {
        std::string suffix = ".aburi.incomplete." +
            std::to_string(resolved.index);
        emitted_zti_symbol += suffix;
        emitted_zts_symbol += suffix;
    }
    std::string type_string = zts_symbol.substr(4);
    cir::TypeId zts_type =
        builder_.array_type(builder_.char_type(), type_string.size() + 1);
    cir::EntityId zts_entity = builder_.add_entity(
        cir::EntityKind::Variable,
        emitted_zts_symbol,
        zts_type,
        {},
        loc,
        cir::StorageDuration::Static);
    cir::Entity& zts_record = file_.entity_mut(zts_entity);
    zts_record.is_definition = true;
    zts_record.linkage = force_internal ? cir::LinkageKind::Internal
                                        : cir::LinkageKind::LinkOnceODR;
    zts_record.is_extern_c = true;
    zts_record.declared_with_extern = !force_internal;
    zts_record.qualifiers = cir::QualConst;
    mark_generated_abi_entity(zts_entity,
                              descriptor_owner(),
                              cir::GeneratedSymbolRole::TypeName);
    zts_record.has_static_initializer = true;
    zts_record.static_initializer_bytes.assign(type_string.begin(),
                                               type_string.end());
    zts_record.static_initializer_bytes.push_back(0);

    const size_t ptr = std::max<size_t>(
        1, (file_.target_info().pointer_width + 7) / 8);
    const size_t descriptor_bytes = descriptor_words * ptr;
    cir::TypeId descriptor_type = builder_.array_type(
        builder_.pointer_type(builder_.void_type()), descriptor_words);
    cir::EntityId vtable = extern_runtime_global(runtime_vtable, loc);
    cir::EntityId zti_entity = builder_.add_entity(
        cir::EntityKind::Variable,
        emitted_zti_symbol,
        descriptor_type,
        {},
        loc,
        cir::StorageDuration::Static);
    cir::Entity& zti_record = file_.entity_mut(zti_entity);
    zti_record.is_definition = true;
    zti_record.linkage = force_internal ? cir::LinkageKind::Internal
                                        : cir::LinkageKind::LinkOnceODR;
    zti_record.is_extern_c = true;
    zti_record.object_origin = cir::EntityObjectOrigin::TypeInfo;
    mark_generated_abi_entity(zti_entity,
                              descriptor_owner(),
                              cir::GeneratedSymbolRole::TypeInfo);
    zti_record.has_static_initializer = true;
    zti_record.static_initializer_bytes.assign(descriptor_bytes, 0);
    zti_record.static_initializer_relocations.push_back(
        cir::StaticInitializerRelocation{0, vtable,
                                         static_cast<int64_t>(2 * ptr)});
    zti_record.static_initializer_relocations.push_back(
        cir::StaticInitializerRelocation{ptr, zts_entity, 0});
    if (has_pointee) {
        write_u32(zti_record.static_initializer_bytes,
                  2 * ptr,
                  pbase_flags,
                  file_.target_info().endianness);
        zti_record.static_initializer_relocations.push_back(
            cir::StaticInitializerRelocation{3 * ptr,
                                             pointee_typeinfo,
                                             0});
    }
    if (has_context) {
        zti_record.static_initializer_relocations.push_back(
            cir::StaticInitializerRelocation{4 * ptr,
                                             context_typeinfo,
                                             0});
    }

    typeinfo_entities_.emplace(cache_key, zti_entity);
    track_speculative_rollback([this, cache_key]() {
        typeinfo_entities_.erase(cache_key);
    });
    return zti_entity;
}

} // namespace aburi::collect
