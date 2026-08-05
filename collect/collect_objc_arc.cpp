#include "collect.h"

namespace aburi::collect {

bool Session::arc_retainable_type(cir::TypeId type) const {
    if (!objc_.initialized) {
        return false;
    }
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Pointer) {
        return false;
    }
    cir::TypeId pointee =
        file_.resolved_type(file_.pointer_pointee_type(resolved));
    if (!file_.valid(pointee)) {
        return false;
    }
    if (pointee == file_.resolved_type(objc_.object_record_type)) {
        return true;
    }
    if (pointee == file_.resolved_type(objc_.class_record_type)) {

        return false;
    }
    return objc_interface_for_object_type(pointee).valid();
}

cir::ObjCOwnership Session::arc_ownership_of_ref(cir::TypeRef ref) const {
    cir::ObjCOwnership ownership = cir::ownership_of(ref.qualifiers);
    if (ownership != cir::ObjCOwnership::Unspecified) {
        return ownership;
    }
    cir::TypeId resolved = file_.resolved_type(ref.type);
    if (file_.valid(resolved) &&
        file_.type(resolved).kind == cir::TypeKind::Pointer) {
        if (const auto* pointer = std::get_if<cir::PointerTypePayload>(
                &file_.type_payload(resolved))) {
            ownership = cir::ownership_of(pointer->pointee.qualifiers);
            if (ownership != cir::ObjCOwnership::Unspecified) {
                return ownership;
            }
        }
    }
    if (arc_retainable_type(ref.type)) {
        return cir::ObjCOwnership::Strong;
    }
    return cir::ObjCOwnership::Unspecified;
}

cir::ObjCOwnership Session::arc_ownership_of(cir::EntityId entity) const {
    if (!file_.valid(entity)) {
        return cir::ObjCOwnership::Unspecified;
    }
    const cir::Entity& declared = file_.entity(entity);
    return arc_ownership_of_ref(
        cir::TypeRef{declared.type, declared.qualifiers, {}});
}

bool Session::expr_reads_objc_self(const ExprResult& expr) const {
    if (!expr.place.valid() || !file_.valid(expr.place)) {
        return false;
    }
    const cir::Inst& place_inst = file_.inst(expr.place);
    if (!place_inst.place_fact.valid() ||
        !file_.valid(place_inst.place_fact)) {
        return false;
    }
    cir::EntityId entity = file_.place_fact(place_inst.place_fact).entity;
    if (!entity.valid()) {
        return false;
    }
    const cir::Entity& declared = file_.entity(entity);
    return declared.storage_duration == cir::StorageDuration::Parameter &&
        declared.name.valid() && file_.name(declared.name) == "self";
}

cir::InstId Session::arc_null_object(SrcLoc loc) {
    cir::InstId zero = builder_.integer_literal(
        0, file_.builtin_type(cir::BuiltinTypeKind::ULong), "0", loc);
    return builder_.cast(objc_.id_type, zero, "arith", loc);
}

cir::EntityId Session::arc_strong_destroy_helper(SrcLoc loc) {
    if (objc_.strong_destroy_helper.valid()) {
        return objc_.strong_destroy_helper;
    }
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId slot_type = builder_.pointer_type(objc_.id_type);
    cir::TypeId helper_type =
        function_type(file_.type_ref(void_type),
                      {file_.type_ref(slot_type)}, false, true);
    std::vector<ParamInput> params;
    ParamInput param;
    param.name = ".slot";
    param.type = file_.type_ref(slot_type);
    param.loc = loc;
    param.arc_unretained = true;
    params.push_back(std::move(param));

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags flags;
    FunctionDeclStart helper = begin_function_type(
        "__aburi_arc_destroy_strong", helper_type,
        file_.type_ref(void_type), params, loc, flags);
    file_.entity_mut(helper.decl.entity).is_extern_c = true;
    file_.entity_mut(helper.decl.entity).linkage =
        cir::LinkageKind::LinkOnceODR;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId entry = begin_fragment_block("arc.destroy_strong");
    cir::InstId slot = helper.function.parameters.front().value.inst;
    (void)builder_.objc_arc_op(cir::ObjCArcOpKind::StoreStrong,
                               {slot, arc_null_object(loc)}, {}, loc);
    builder_.return_void(loc);
    cir::Fragment body = finish_fragment_block(entry, previous);
    builder_.switch_to_block(previous);
    finish_function(make_stmt_result(std::move(body), false, false), loc);
    restore_function_context(std::move(saved));

    objc_.strong_destroy_helper = helper.decl.entity;
    track_speculative_rollback([this]() {
        objc_.strong_destroy_helper = {};
    });
    return objc_.strong_destroy_helper;
}

cir::LifetimeId Session::register_arc_cleanup(cir::EntityId entity,
                                              cir::TypeId type,
                                              cir::EntityId cleanup_function,
                                              SrcLoc loc,
                                              bool full_expression_temporary) {
    if (cleanup_scopes_.empty() || !entity.valid() ||
        !cleanup_function.valid()) {
        return {};
    }
    const cir::Entity& declared = file_.entity(entity);
    if (declared.storage_duration != cir::StorageDuration::Automatic &&
        declared.storage_duration != cir::StorageDuration::Temporary &&
        declared.storage_duration != cir::StorageDuration::Parameter) {
        return {};
    }
    return register_cleanup_with_function(entity, type, loc,
                                          full_expression_temporary,
                                          cleanup_function, cleanup_function,
                                          /*call_with_address=*/true);
}

void Session::arc_finish_local_declaration(DeclResult& started,
                                           bool zero_initialize,
                                           SrcLoc loc) {
    if (!arc_enabled() || !started.entity.valid() || started.has_error) {
        return;
    }
    const cir::Entity& declared = file_.entity(started.entity);
    if (declared.storage_duration != cir::StorageDuration::Automatic ||
        is_reference_type(started.type) ||
        !arc_retainable_type(started.type)) {
        return;
    }
    cir::ObjCOwnership ownership = arc_ownership_of(started.entity);
    if (ownership != cir::ObjCOwnership::Strong &&
        ownership != cir::ObjCOwnership::Weak) {

        return;
    }
    if (zero_initialize) {

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("arc.local.nil");
        cir::InstId place =
            builder_.local_place(started.entity, started.type, loc);
        (void)builder_.store(place, arc_null_object(loc), loc);
        started.fragment = chain(std::move(started.fragment),
                                 finish_fragment_block(block, previous), loc);
    }
    (void)register_arc_cleanup(started.entity, started.type,
                               ownership == cir::ObjCOwnership::Weak
                                   ? arc_weak_destroy_function(loc)
                                   : arc_strong_destroy_helper(loc),
                               loc);
}

StmtResult Session::arc_finish_dealloc_body(StmtResult body,
                                            const FunctionDeclStart& start,
                                            SrcLoc loc) {
    if (!arc_enabled() ||
        objc_.current_method_family != cir::ObjCMethodFamily::Dealloc ||
        !body.falls_through || objc_.in_class_method ||
        start.function.parameters.empty()) {
        return body;
    }
    const cir::ObjCInterfaceFacts* facts =
        objc_.current_interface.valid()
            ? file_.objc_interface_facts(objc_.current_interface)
            : nullptr;
    if (!facts || !facts->super_class.valid()) {

        return body;
    }
    ObjCMessageSendInput send;
    ExprResult self_value;
    self_value.value = start.function.parameters.front().value.inst;
    self_value.type = file_.entity(start.function.parameters.front().entity)
                          .type;
    self_value.category = ValueCategory::PrValue;
    send.receiver = std::move(self_value);
    send.is_super = true;
    send.selector = "dealloc";
    send.internal = true;
    send.loc = loc;
    ExprResult chained = collect_objc_message_send(std::move(send));
    body.fragment = chain(std::move(body.fragment),
                          std::move(chained.fragment), loc);
    return body;
}

namespace {

bool is_plain_pointer_kind(cir::TypeKind kind) {
    return kind == cir::TypeKind::Pointer;
}

} // namespace

ExprResult Session::collect_objc_bridge_cast(ObjCBridgeKind kind,
                                             cir::TypeId target_type,
                                             ExprResult operand,
                                             SrcLoc loc) {
    ExprResult value = require_value(std::move(operand), UseContext::RValue,
                                     loc);
    bool source_retainable = arc_retainable_type(value.type);
    bool target_retainable = arc_retainable_type(target_type);
    if (kind == ObjCBridgeKind::BridgeRetained && !source_retainable) {
        report_error("__bridge_retained requires an Objective-C object "
                     "pointer operand", loc);
        value.has_error = true;
    }
    if (kind == ObjCBridgeKind::BridgeTransfer && !target_retainable) {
        report_error("__bridge_transfer requires an Objective-C object "
                     "pointer result type", loc);
        value.has_error = true;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.bridge");
    if (kind == ObjCBridgeKind::BridgeRetained && !value.has_error &&
        value.value.valid()) {
        if (value.arc_plus_one) {

            arc_claim_plus_one(value);
        } else {
            value.value = builder_.objc_arc_op(
                cir::ObjCArcOpKind::Retain, {value.value},
                file_.resolved_type(value.type), loc);
        }
        value.arc_plus_one = false;
        value.arc_pending_token = 0;
    }
    cir::InstId cast = builder_.cast(file_.resolved_type(target_type),
                                     value.value, "arith", loc);
    value.fragment = chain(std::move(value.fragment),
                           finish_fragment_block(block, previous), loc);
    value.value = cast;
    value.type = target_type;
    value.category = ValueCategory::PrValue;
    if (kind == ObjCBridgeKind::BridgeTransfer && !value.has_error) {

        value.arc_plus_one = true;
        value.arc_fresh_call = false;
        value.arc_pending_token = 0;
        arc_schedule_pending_release(value);
    }
    return value;
}

bool Session::arc_check_plain_cast(cir::TypeId target_type,
                                   cir::TypeId source_type,
                                   SrcLoc loc) {
    if (!arc_enabled()) {
        return false;
    }
    bool source_retainable = arc_retainable_type(source_type);
    bool target_retainable = arc_retainable_type(target_type);
    if (source_retainable == target_retainable) {
        return false;
    }

    cir::TypeId other = file_.resolved_type(source_retainable ? target_type
                                                              : source_type);
    if (!file_.valid(other) ||
        !is_plain_pointer_kind(file_.type(other).kind)) {
        return false;
    }
    cir::TypeId pointee = file_.resolved_type(file_.pointer_pointee_type(other));
    if (file_.valid(pointee) &&
        (pointee == file_.resolved_type(objc_.class_record_type) ||
         pointee == file_.resolved_type(objc_.selector_record_type))) {
        return false;
    }
    if (file_.valid(pointee) &&
        file_.type(pointee).kind == cir::TypeKind::Function) {
        return false;
    }
    if (source_retainable) {
        report_error("cast of Objective-C pointer type to C pointer type "
                     "requires a bridged cast (__bridge or "
                     "__bridge_retained)", loc);
    } else {
        report_error("cast of C pointer type to Objective-C pointer type "
                     "requires a bridged cast (__bridge or "
                     "__bridge_transfer)", loc);
    }
    return true;
}

bool Session::arc_prepare_writeback_argument(
    ExprResult& argument,
    std::vector<ArcWriteback>& writebacks,
    SrcLoc loc) {
    if (!arc_enabled() || !argument.value.valid() ||
        !file_.valid(argument.value)) {
        return false;
    }
    const cir::Inst& addr_inst = file_.inst(argument.value);
    if (addr_inst.kind != cir::InstKind::AddrOf) {
        return false;
    }
    std::vector<cir::ValueRef> operands =
        file_.value_operands(addr_inst.operands);
    if (operands.empty() || !file_.valid(operands.front().inst)) {
        return false;
    }
    const cir::Inst& place_inst = file_.inst(operands.front().inst);
    if (!place_inst.place_fact.valid() ||
        !file_.valid(place_inst.place_fact)) {
        return false;
    }
    cir::EntityId entity = file_.place_fact(place_inst.place_fact).entity;
    if (!entity.valid()) {
        return false;
    }
    const cir::Entity& declared = file_.entity(entity);
    if ((declared.storage_duration != cir::StorageDuration::Automatic &&
         declared.storage_duration != cir::StorageDuration::Parameter) ||
        !arc_retainable_type(declared.type) ||
        arc_ownership_of(entity) != cir::ObjCOwnership::Strong) {
        return false;
    }

    cir::TypeId object_type = declared.type;
    cir::EntityId temporary = builder_.add_entity(
        cir::EntityKind::Variable, "", object_type, {}, loc,
        cir::StorageDuration::Automatic);
    file_.entity_mut(temporary).is_definition = true;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("arc.writeback.in");
    cir::InstId original_place =
        builder_.local_place(entity, object_type, loc);
    cir::InstId temporary_place =
        builder_.local_place(temporary, object_type, loc);
    (void)builder_.store(temporary_place, builder_.load(original_place, loc),
                         loc);
    cir::InstId temporary_addr = builder_.addr_of(temporary_place, loc);
    cir::TypeId argument_type = file_.inst(argument.value).result_type;
    argument.value = builder_.cast(argument_type, temporary_addr, "arith",
                                   loc);
    argument.fragment = chain(std::move(argument.fragment),
                              finish_fragment_block(block, previous), loc);
    writebacks.push_back(
        ArcWriteback{entity, object_type, temporary, object_type});
    return true;
}

void Session::arc_emit_writebacks(const std::vector<ArcWriteback>& writebacks,
                                  SrcLoc loc) {
    for (const ArcWriteback& writeback : writebacks) {
        cir::InstId temporary_place = builder_.local_place(
            writeback.temporary, writeback.temporary_type, loc);
        cir::InstId written = builder_.load(temporary_place, loc);
        cir::InstId original_place = builder_.local_place(
            writeback.original, writeback.original_type, loc);
        cir::InstId slot = builder_.addr_of(original_place, loc);
        (void)builder_.objc_arc_op(cir::ObjCArcOpKind::StoreStrong,
                                   {slot, written}, {}, loc);
    }
}

cir::EntityId Session::arc_weak_destroy_function(SrcLoc loc) {
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    return extern_runtime_function(
        "objc_destroyWeak",
        file_.function_type(void_type,
                            {builder_.pointer_type(objc_.id_type)}),
        loc);
}

void Session::arc_schedule_pending_release(ExprResult& expr) {
    if (!arc_enabled() || !expr.arc_plus_one || !expr.value.valid() ||
        active_lifetime_boundaries_.empty()) {
        return;
    }
    ArcPendingRelease pending;
    pending.token = arc_pending_next_token_++;
    pending.boundary = active_lifetime_boundaries_.back();
    pending.value = expr.value;
    arc_pending_releases_.push_back(pending);
    expr.arc_pending_token = pending.token;
}

void Session::arc_claim_plus_one(const ExprResult& expr) {
    if (expr.arc_pending_token == 0) {
        return;
    }
    for (ArcPendingRelease& pending : arc_pending_releases_) {
        if (pending.token == expr.arc_pending_token) {
            pending.claimed = true;
            return;
        }
    }
}

cir::Fragment Session::arc_flush_boundary_releases(uint64_t boundary_id,
                                                   SrcLoc loc) {
    cir::Fragment fragment;
    bool any = false;
    for (const ArcPendingRelease& pending : arc_pending_releases_) {
        if (pending.boundary == boundary_id && !pending.claimed) {
            any = true;
            break;
        }
    }
    if (any) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("arc.expr.release");
        for (size_t i = arc_pending_releases_.size(); i-- > 0;) {
            const ArcPendingRelease& pending = arc_pending_releases_[i];
            if (pending.boundary == boundary_id && !pending.claimed) {
                (void)builder_.objc_arc_op(cir::ObjCArcOpKind::Release,
                                           {pending.value}, {}, loc);
            }
        }
        fragment = finish_fragment_block(block, previous);
    }
    arc_drop_boundary_releases(boundary_id);
    return fragment;
}

void Session::arc_drop_boundary_releases(uint64_t boundary_id) {
    arc_pending_releases_.erase(
        std::remove_if(arc_pending_releases_.begin(),
                       arc_pending_releases_.end(),
                       [boundary_id](const ArcPendingRelease& pending) {
                           return pending.boundary == boundary_id;
                       }),
        arc_pending_releases_.end());
}

ExprResult Session::arc_retain_value(ExprResult value, SrcLoc loc) {
    if (value.arc_plus_one || value.has_error || !value.value.valid() ||
        !arc_retainable_type(value.type)) {
        return value;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("arc.retain");
    cir::ObjCArcOpKind op = value.arc_fresh_call
        ? cir::ObjCArcOpKind::RetainAutoreleasedReturnValue
        : cir::ObjCArcOpKind::Retain;
    value.value = builder_.objc_arc_op(op, {value.value},
                                       file_.resolved_type(value.type), loc);
    value.fragment = chain(std::move(value.fragment),
                           finish_fragment_block(block, previous), loc);
    value.arc_plus_one = true;
    value.arc_fresh_call = false;
    return value;
}

ExprResult Session::arc_release_discarded(ExprResult value, SrcLoc loc) {
    if (!value.arc_plus_one || value.has_error || !value.value.valid()) {
        return value;
    }
    arc_claim_plus_one(value);
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("arc.release");
    (void)builder_.objc_arc_op(cir::ObjCArcOpKind::Release, {value.value},
                               {}, loc);
    value.fragment = chain(std::move(value.fragment),
                           finish_fragment_block(block, previous), loc);
    value.arc_plus_one = false;
    return value;
}

ExprResult Session::arc_adjust_return_value(ExprResult value, SrcLoc loc) {
    if (value.has_error || !value.value.valid() ||
        !arc_retainable_type(value.type)) {
        return value;
    }
    bool returns_retained =
        objc_.current_method_family == cir::ObjCMethodFamily::Alloc ||
        objc_.current_method_family == cir::ObjCMethodFamily::New ||
        objc_.current_method_family == cir::ObjCMethodFamily::Copy ||
        objc_.current_method_family == cir::ObjCMethodFamily::MutableCopy ||
        objc_.current_method_family == cir::ObjCMethodFamily::Init;
    if (value.arc_plus_one) {
        arc_claim_plus_one(value);
    }
    if (returns_retained && value.arc_plus_one) {

        return value;
    }
    value = arc_retain_value(std::move(value), loc);
    if (returns_retained) {
        return value;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("arc.autorelease_return");
    value.value = builder_.objc_arc_op(
        cir::ObjCArcOpKind::AutoreleaseReturnValue, {value.value},
        file_.resolved_type(value.type), loc);
    value.fragment = chain(std::move(value.fragment),
                           finish_fragment_block(block, previous), loc);
    value.arc_plus_one = false;
    return value;
}

} // namespace aburi::collect
