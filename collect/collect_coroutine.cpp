#include <string>
#include <utility>

#include "collect.h"

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

} // namespace

Session::CoroutinePromiseCallback Session::set_coroutine_promise_callback(
    CoroutinePromiseCallback callback) {
    CoroutinePromiseCallback previous = std::move(coroutine_promise_callback_);
    coroutine_promise_callback_ = std::move(callback);
    return previous;
}

void Session::diagnose_coroutine_codegen_gate(CoroutineState& coro,
                                              SrcLoc loc) {
    if (coro.codegen_gate_diagnosed) {
        return;
    }
    coro.codegen_gate_diagnosed = true;
    report_error("coroutine code generation is not implemented yet", loc);
}

Session::CoroutineState* Session::ensure_coroutine_context(
    std::string_view construct, SrcLoc loc) {
    if (coroutine_state_) {
        return coroutine_state_->discovery_failed ? nullptr
                                                  : coroutine_state_.get();
    }
    if (!current_function_.valid()) {
        report_error(std::string(construct) +
                         " is only allowed inside a function body",
                     loc);
        return nullptr;
    }

    coroutine_state_ = std::make_unique<CoroutineState>();
    CoroutineState* coro = coroutine_state_.get();
    coro->first_keyword_loc = loc;
    coro->discovery_failed = true;

    const cir::Function& fn = file_.function(current_function_);
    const cir::Entity& fn_entity = file_.entity(fn.entity);
    const auto* payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(file_.resolved_type(fn.type)));

    bool eligible = true;
    if (fn_entity.kind == cir::EntityKind::Constructor) {
        report_error("a constructor cannot be a coroutine", loc);
        eligible = false;
    } else if (fn_entity.kind == cir::EntityKind::Destructor) {
        report_error("a destructor cannot be a coroutine", loc);
        eligible = false;
    }
    if (fn_entity.decl_flags.is_consteval) {
        report_error("a consteval function cannot be a coroutine", loc);
        eligible = false;
    } else if (fn_entity.decl_flags.is_constexpr) {
        report_error("a constexpr function cannot be a coroutine", loc);
        eligible = false;
    }
    if (!fn_entity.is_record_member &&
        fn_entity.linkage == cir::LinkageKind::External &&
        file_.name(fn_entity.name) == "main") {
        report_error("'main' cannot be a coroutine", loc);
        eligible = false;
    }
    if (deduce_return_type_) {
        report_error(
            "a function with a deduced return type cannot be a coroutine",
            loc);
        eligible = false;
    }
    if (payload && payload->is_variadic) {
        report_error(
            "a coroutine cannot have a C-style variadic parameter list", loc);
        eligible = false;
    }
    if (has_plain_return_) {
        report_error(
            "a coroutine cannot contain a plain 'return' statement; use "
            "'co_return'",
            first_plain_return_loc_);
    }
    if (!eligible) {
        return nullptr;
    }
    bool dependent = collecting_pattern();
    if (!dependent && payload) {
        for (const cir::TypeRef& parameter : payload->parameters) {
            if (is_dependent_type(parameter.type)) {
                dependent = true;
                break;
            }
        }
    }
    if (!dependent && is_dependent_type(fn.result_type)) {
        dependent = true;
    }
    if (dependent) {
        report_error("coroutines in templates are not supported yet", loc);
        return nullptr;
    }

    std::vector<cir::TypeRef> traits_arguments;
    traits_arguments.push_back(type_ref(fn.result_type));
    if (fn_entity.kind == cir::EntityKind::Method &&
        fn_entity.is_record_member && !fn_entity.is_static_member_function) {
        cir::TypeRef object =
            type_ref(file_.entity(fn_entity.declaring_record).type);
        if (payload) {
            if (payload->member_is_const) {
                object.qualifiers |= cir::QualConst;
            }
            if (payload->member_is_volatile) {
                object.qualifiers |= cir::QualVolatile;
            }
        }
        bool rvalue = payload &&
            payload->member_ref_qualifier ==
                cir::FunctionRefQualifierKind::RValue;
        traits_arguments.push_back(type_ref(reference_type(
            object,
            rvalue ? cir::ReferenceKind::RValue
                   : cir::ReferenceKind::LValue)));
    }
    if (payload) {
        for (const cir::TypeRef& parameter : payload->parameters) {
            traits_arguments.push_back(parameter);
        }
    }

    if (!coroutine_promise_callback_) {
        report_error(
            "coroutine promise resolution is unavailable in this "
            "compilation mode",
            loc);
        return nullptr;
    }
    CoroutinePromiseResolution resolution =
        coroutine_promise_callback_(traits_arguments, loc);
    if (!resolution.traits_specialization.valid()) {
        report_error(
            "std::coroutine_traits is not declared; a coroutine requires a "
            "coroutine_traits declaration",
            loc);
        return nullptr;
    }
    if (!resolution.promise_type.valid()) {
        report_error(
            "std::coroutine_traits<...> does not define a usable "
            "'promise_type' for this coroutine",
            loc);
        return nullptr;
    }
    cir::TypeId promise = file_.resolved_type(resolution.promise_type);
    if (!file_.valid(promise) ||
        file_.type(promise).kind != cir::TypeKind::Record) {
        report_error("coroutine 'promise_type' must be a class type", loc);
        return nullptr;
    }
    if (!require_complete_class_type(promise, loc)) {
        report_error("coroutine 'promise_type' must be a complete class type",
                     loc);
        return nullptr;
    }

    coro->has_return_void =
        lookup_member_name(promise, "return_void").found_name;
    coro->has_return_value =
        lookup_member_name(promise, "return_value").found_name;
    if (coro->has_return_void && coro->has_return_value) {
        report_error(
            "coroutine promise type declares both 'return_void' and "
            "'return_value'",
            loc);
        return nullptr;
    }
    coro->has_await_transform =
        lookup_member_name(promise, "await_transform").found_name;
    coro->has_get_return_object_on_allocation_failure =
        lookup_member_name(promise, "get_return_object_on_allocation_failure")
            .found_name;

    coro->traits_specialization = resolution.traits_specialization;
    coro->promise_type = promise;
    coro->handle_type = file_.resolved_type(resolution.handle_type);
    coro->discovery_failed = false;

    if (lang_opts_.enable_coroutine_pre_split_cir) {
        emit_coroutine_preamble(*coro, loc);
    }
    return coro;
}

void Session::emit_coroutine_preamble(CoroutineState& coro, SrcLoc loc) {
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("coro.alloc");
    cir::InstId size = builder_.coro_frame_size(loc);
    cir::TypeId void_pointer = builder_.pointer_type(builder_.void_type());

    cir::TypeId promise_leaf = file_.resolved_type(coro.promise_type);
    MemberLookupResult promise_new =
        lookup_member_name(promise_leaf, "operatornew");
    if (promise_new.found_name) {
        cir::FunctionId function_id = builder_.current_function();
        bool has_parameters = function_id.valid() &&
            !file_.function(function_id).parameters.empty();
        if (has_parameters) {
            for (const MemberLookupDeclaration& declaration :
                 promise_new.declarations) {
                std::optional<cir::AllocationFunctionForm> form =
                    classify_allocation_function(declaration.entity,
                                                 /*is_array=*/false);
                if (form && form->is_placement) {
                    report_error(
                        "a coroutine allocation function taking the "
                        "coroutine's parameters is not supported yet",
                        loc);
                    coro.emission_failed = true;
                    break;
                }
            }
        }
    }
    AllocationSelection allocation_selection = select_allocation_function(
        coro.promise_type, /*is_array=*/false, /*force_global=*/false, {},
        loc, /*diagnose=*/false);
    cir::InstId allocation{};
    if (allocation_selection.valid()) {
        std::vector<cir::InstId> arguments{size};
        if (allocation_selection.form.is_aligned) {
            arguments.push_back(builder_.coro_frame_align(loc));
        }
        allocation = builder_.call(allocation_selection.entity, void_pointer,
                                   arguments, loc);
    } else {

        cir::EntityId allocator = implicit_allocation_operator(
            /*is_array=*/false, /*aligned=*/false, loc);
        allocation = builder_.call(allocator, void_pointer, {size}, loc);
    }

    // The [dcl.fct.def.coroutine] lifetime invariant requires allocation
    // failure to return without constructing a frame.
    cir::BlockId allocation_exit = block;
    if (coro.has_get_return_object_on_allocation_failure &&
        !coro.emission_failed) {
        if (!allocation_selection.valid() ||
            !allocation_selection.member_access_owner.valid()) {
            report_error(
                "get_return_object_on_allocation_failure requires an "
                "allocation function in the promise type's scope (the "
                "global nothrow form is not supported yet)",
                loc);
            coro.emission_failed = true;
        } else {
            cir::InstId null_value = builder_.cast(
                void_pointer, builder_.nullptr_literal("nullptr", loc),
                "nullptr", loc);
            cir::InstId is_null = builder_.binary(cir::BinaryOpKind::Equal,
                                                  builder_.bool_type(),
                                                  allocation, null_value,
                                                  loc);
            coro.alloc_failure_block =
                builder_.create_detached_block("coro.alloc.fail");
            cir::BlockId ok = builder_.create_detached_block("coro.alloc.ok");
            builder_.cond_branch(is_null, coro.alloc_failure_block, ok, {},
                                 loc);
            builder_.switch_to_block(ok);
            allocation_exit = ok;
        }
    }

    coro.frame_pointer = builder_.coro_begin(allocation, loc);
    coro.promise_place = builder_.coro_promise_place(
        coro.frame_pointer, coro.promise_type, loc);

    cir::Fragment fragment = builder_.block_fragment(block);
    if (allocation_exit != block) {
        fragment.blocks.push_back(allocation_exit);
        fragment.exit = allocation_exit;
        fragment.falls_through = true;
    }
    builder_.switch_to_block(previous);
    coro.preamble_fragment = std::move(fragment);
    coro.cleanup_block = builder_.create_detached_block("coro.cleanup");
}

ExprResult Session::collect_promise_member_call(CoroutineState& coro,
                                                std::string_view member,
                                                std::vector<ExprResult> args,
                                                SrcLoc loc) {
    ExprResult base;
    base.place = coro.promise_place;
    base.type = coro.promise_type;
    base.category = ValueCategory::LValue;
    ExprResult callee =
        collect_member_access_expr(std::move(base), member, false, loc);
    if (callee.has_error) {
        return callee;
    }
    return collect_call_expr(std::move(callee), std::move(args), loc);
}

ExprResult Session::emit_await(CoroutineState& coro,
                               ExprResult awaitable,
                               cir::CoroSaveKind kind,
                               SrcLoc loc,
                               std::vector<cir::BlockId>* resume_blocks_out) {
    ExprResult result;
    result.type = builder_.void_type();
    result.category = ValueCategory::PrValue;

    uint32_t index = kind == cir::CoroSaveKind::Initial ? 0u
        : kind == cir::CoroSaveKind::Final               ? 1u
        : coro.next_user_suspend_index++;

    if (awaitable.has_error) {
        result.fragment = std::move(awaitable.fragment);
        result.has_error = true;
        coro.emission_failed = true;
        return result;
    }

    if (lang_opts_.is_cxx_mode()) {
        bool rewritten = false;
        ExprResult converted = try_overloaded_unary(
            syntax::UnaryOperator::CoAwait, awaitable, &rewritten, loc);
        if (rewritten) {
            if (converted.has_error) {
                result.fragment = std::move(converted.fragment);
                result.has_error = true;
                coro.emission_failed = true;
                return result;
            }
            converted.fragment = chain(std::move(awaitable.fragment),
                                       std::move(converted.fragment), loc);
            awaitable = std::move(converted);
        }
    }

    cir::InstId awaiter_place = awaitable.place;
    cir::TypeId awaiter_type = awaitable.type;
    if (!awaiter_place.valid() &&
        awaitable.category == ValueCategory::PrValue &&
        awaitable.value.valid() && file_.valid(awaitable.type) &&
        file_.type(file_.resolved_type(awaitable.type)).kind ==
            cir::TypeKind::Record) {
        cir::EntityId temp = builder_.add_entity(
            cir::EntityKind::Variable,
            ".coro.awaiter." + std::to_string(index),
            awaitable.type, {}, loc, cir::StorageDuration::Temporary,
            cir::MemorySpace::Default, {});
        file_.entity_mut(temp).is_definition = true;
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("await.awaiter");
        awaiter_place = builder_.local_place(temp, awaitable.type, loc);
        builder_.store(awaiter_place, awaitable.value, loc);
        cir::Fragment materialization = finish_fragment_block(block, previous);
        awaitable.fragment = chain(std::move(awaitable.fragment),
                                   std::move(materialization), loc);
    }
    if (!awaiter_place.valid()) {
        report_error(
            "co_await operands without an object representation are not "
            "supported yet",
            loc);
        result.fragment = std::move(awaitable.fragment);
        result.has_error = true;
        coro.emission_failed = true;
        return result;
    }
    auto awaiter_base = [&]() {
        ExprResult base;
        base.place = awaiter_place;
        base.type = awaiter_type;
        base.category = ValueCategory::LValue;
        return base;
    };

    ExprResult ready_callee =
        collect_member_access_expr(awaiter_base(), "await_ready", false, loc);
    if (ready_callee.has_error) {
        result.fragment = std::move(awaitable.fragment);
        result.has_error = true;
        coro.emission_failed = true;
        return result;
    }
    ExprResult ready_call = collect_call_expr(std::move(ready_callee), {}, loc);
    ExprResult ready =
        require_value(std::move(ready_call), UseContext::Condition, loc);
    if (ready.has_error) {
        result.fragment = std::move(awaitable.fragment);
        result.has_error = true;
        coro.emission_failed = true;
        return result;
    }

    cir::Fragment fragment = chain(std::move(awaitable.fragment),
                                   std::move(ready.fragment), loc);
    fragment = adopt_or_create_fragment_entry(std::move(fragment),
                                              "await.check");

    cir::BlockId save_previous = builder_.current_block();
    cir::BlockId save_block = begin_fragment_block("await.save");
    builder_.coro_save(index, kind, loc);
    cir::Fragment save_fragment =
        finish_fragment_block(save_block, save_previous);

    ExprResult handle;
    handle.value = coro.frame_pointer;
    handle.type = builder_.pointer_type(builder_.void_type());
    handle.category = ValueCategory::PrValue;
    if (coro.handle_type.valid()) {
        cir::EntityId handle_record = file_.record_entity(coro.handle_type);
        cir::DeclContextId handle_context =
            handle_record.valid() && file_.valid(handle_record)
                ? file_.entity(handle_record).semantic_context
                : cir::DeclContextId{};
        ExprResult from_address = lookup_qualified_name(
            handle_context, "from_address", loc);
        std::vector<ExprResult> address_args;
        address_args.push_back(std::move(handle));
        handle = from_address.has_error
            ? std::move(from_address)
            : collect_call_expr(std::move(from_address),
                                std::move(address_args), loc);
        if (handle.has_error) {
            result.fragment = std::move(fragment);
            result.has_error = true;
            coro.emission_failed = true;
            return result;
        }
    }
    ExprResult suspend_callee = collect_member_access_expr(
        awaiter_base(), "await_suspend", false, loc);
    if (suspend_callee.has_error) {
        result.fragment = std::move(fragment);
        result.has_error = true;
        coro.emission_failed = true;
        return result;
    }
    std::vector<ExprResult> suspend_args;
    suspend_args.push_back(std::move(handle));
    ExprResult suspend_call = collect_call_expr(std::move(suspend_callee),
                                                std::move(suspend_args), loc);
    if (suspend_call.has_error) {
        result.fragment = std::move(fragment);
        result.has_error = true;
        coro.emission_failed = true;
        return result;
    }
    cir::TypeId suspend_type = file_.resolved_type(suspend_call.type);
    bool suspend_is_void = is_void_type(suspend_type);
    bool suspend_is_bool = !suspend_is_void && file_.valid(suspend_type) &&
        file_.type(suspend_type).kind == cir::TypeKind::Builtin &&
        suspend_type == builder_.bool_type();
    cir::InstId transfer_target{};
    if (!suspend_is_void && !suspend_is_bool) {

        if (file_.type(suspend_type).kind != cir::TypeKind::Record) {
            report_error(
                "await_suspend must return void, bool, or a coroutine "
                "handle",
                loc);
            result.fragment = std::move(fragment);
            result.has_error = true;
            coro.emission_failed = true;
            return result;
        }
        save_fragment = chain(std::move(save_fragment),
                              std::move(suspend_call.fragment), loc);
        suspend_call.fragment = {};
        cir::BlockId handle_previous = builder_.current_block();
        cir::BlockId handle_block = begin_fragment_block("await.transfer");
        cir::EntityId handle_entity = builder_.add_entity(
            cir::EntityKind::Variable, ".coro.transfer.handle", suspend_type,
            {}, loc, cir::StorageDuration::Temporary);
        cir::InstId handle_place =
            builder_.local_place(handle_entity, suspend_type, loc);
        builder_.store(handle_place,
                       suspend_call.value.valid()
                           ? suspend_call.value
                           : builder_.lvalue_to_rvalue(suspend_call.place,
                                                       loc),
                       loc);
        cir::Fragment handle_fragment =
            finish_fragment_block(handle_block, handle_previous);
        ExprResult handle_base;
        handle_base.place = handle_place;
        handle_base.type = suspend_type;
        handle_base.category = ValueCategory::LValue;
        ExprResult address_callee = collect_member_access_expr(
            std::move(handle_base), "address", false, loc);
        ExprResult address_call = address_callee.has_error
            ? std::move(address_callee)
            : collect_call_expr(std::move(address_callee), {}, loc);
        cir::TypeId address_type = file_.resolved_type(address_call.type);
        bool address_is_pointer = file_.valid(address_type) &&
            file_.type(address_type).kind == cir::TypeKind::Pointer &&
            is_void_type(
                file_.resolved_type(file_.pointer_pointee_type(address_type)));
        if (address_call.has_error || !address_is_pointer) {
            if (!address_call.has_error) {
                report_error(
                    "the awaiter's coroutine handle needs an address() "
                    "accessor returning void*",
                    loc);
            }
            result.fragment = std::move(fragment);
            result.has_error = true;
            coro.emission_failed = true;
            return result;
        }
        handle_fragment = chain(std::move(handle_fragment),
                                std::move(address_call.fragment), loc);
        save_fragment =
            chain(std::move(save_fragment), std::move(handle_fragment), loc);
        transfer_target = address_call.value;
    } else {
        save_fragment = chain(std::move(save_fragment),
                              std::move(suspend_call.fragment), loc);
    }

    cir::BlockId suspend_block = builder_.create_detached_block("await.suspend");
    cir::BlockId resume_entry{};
    cir::Fragment resume_fragment;
    cir::BlockId destroy_target = coro.cleanup_block;

    if (kind == cir::CoroSaveKind::Final) {
        // [dcl.fct.def.coroutine]: resuming a coroutine suspended at its
        // final suspend point is undefined; only destroy() may follow.
        resume_entry = builder_.create_detached_block("await.final.resumed");
        builder_.unreachable_from(resume_entry, loc);
        resume_fragment = builder_.block_fragment(resume_entry);
    } else {

        cir::BlockId resume_previous = builder_.current_block();
        cir::BlockId resume_block = begin_fragment_block("await.resume");
        cir::Fragment resume_head =
            finish_fragment_block(resume_block, resume_previous);
        ExprResult resume_callee = collect_member_access_expr(
            awaiter_base(), "await_resume", false, loc);
        if (resume_callee.has_error) {
            result.fragment = std::move(fragment);
            result.has_error = true;
            coro.emission_failed = true;
            return result;
        }
        ExprResult resume_call =
            collect_call_expr(std::move(resume_callee), {}, loc);
        result.value = resume_call.value;
        result.place = resume_call.place;
        result.type = resume_call.type;
        result.category = resume_call.category;
        result.entity = resume_call.entity;
        resume_fragment = chain(std::move(resume_head),
                                std::move(resume_call.fragment), loc);
        resume_entry = resume_fragment.entry;
    }

    cir::BlockId ready_target =
        kind == cir::CoroSaveKind::Final ? coro.cleanup_block : resume_entry;
    builder_.cond_branch_from(fragment.exit, ready.value, ready_target,
                              save_fragment.entry, {}, loc);

    if (suspend_is_bool) {
        cir::BlockId self_resume_target =
            kind == cir::CoroSaveKind::Final ? coro.cleanup_block
                                             : resume_entry;
        builder_.cond_branch_from(save_fragment.exit, suspend_call.value,
                                  suspend_block, self_resume_target, {}, loc);
    } else {
        builder_.branch_from(save_fragment.exit, suspend_block, {}, loc);
    }
    if (transfer_target.valid()) {
        cir::BlockId transfer_previous = builder_.current_block();
        builder_.switch_to_block(suspend_block);
        builder_.coro_transfer(transfer_target, loc);
        builder_.switch_to_block(transfer_previous);
    }
    builder_.coro_suspend_from(suspend_block, index, kind,
                               kind == cir::CoroSaveKind::Final
                                   ? resume_entry
                                   : resume_entry,
                               destroy_target, loc);

    if (resume_blocks_out) {
        *resume_blocks_out = resume_fragment.blocks;
    }
    append_fragment_blocks(fragment, save_fragment);
    append_fragment_blocks(fragment, builder_.block_fragment(suspend_block));
    append_fragment_blocks(fragment, resume_fragment);
    if (kind == cir::CoroSaveKind::Final) {
        fragment.falls_through = false;
    }
    result.fragment = std::move(fragment);
    return result;
}

void Session::emit_coroutine_parameter_copies(CoroutineState& coro,
                                              cir::Fragment& body_fragment,
                                              SrcLoc loc) {
    cir::FunctionId function_id = builder_.current_function();
    if (!function_id.valid()) {
        return;
    }
    const std::vector<cir::FunctionParameter> parameters =
        file_.function(function_id).parameters;
    if (parameters.empty()) {
        return;
    }

    std::unordered_map<uint32_t, cir::InstId> spill_places;
    for (cir::BlockId block_id : current_prologue_.blocks) {
        for (cir::InstId inst_id : file_.block(block_id).instructions) {
            const cir::Inst& inst = file_.inst(inst_id);
            if (inst.kind != cir::InstKind::LocalPlace) {
                continue;
            }
            std::vector<cir::Operand> operands = file_.operands(inst.operands);
            if (operands.empty()) {
                continue;
            }
            if (const auto* entity =
                    std::get_if<cir::EntityId>(&operands[0].data)) {
                spill_places.emplace(entity->index, inst_id);
            }
        }
    }

    const cir::Entity& fn_entity =
        file_.entity(file_.function(function_id).entity);
    bool has_object_parameter = fn_entity.kind == cir::EntityKind::Method &&
        fn_entity.is_record_member && !fn_entity.is_static_member_function;

    for (size_t index = 0; index < parameters.size(); ++index) {
        const cir::FunctionParameter& parameter = parameters[index];
        if (!parameter.entity.valid() || !file_.valid(parameter.entity)) {
            coro.promise_ctor_args_complete = false;
            continue;
        }
        cir::TypeId type =
            file_.resolved_type(file_.entity(parameter.entity).type);
        auto found = spill_places.find(parameter.entity.index);
        if (!file_.valid(type) || found == spill_places.end()) {
            coro.promise_ctor_args_complete = false;
            continue;
        }
        if (index == 0 && has_object_parameter) {
            coro.object_param_place = found->second;
            coro.object_param_type = file_.resolved_type(
                file_.entity(fn_entity.declaring_record).type);
            continue;
        }
        if (is_reference_type(type)) {
            coro.promise_ctor_args.push_back({found->second, type, true});
            continue;
        }
        const cir::RecordFacts* record = file_.record_facts_for_type(type);
        if (!record || !record->is_non_trivial_for_calls) {
            coro.promise_ctor_args.push_back({found->second, type, false});
            continue;
        }
        cir::InstId source_place = found->second;

        std::string name = ".coro.param.";
        if (file_.entity(parameter.entity).name.valid()) {
            name += file_.name(file_.entity(parameter.entity).name);
        }
        cir::EntityId copy_entity = builder_.add_entity(
            cir::EntityKind::Variable, name, type, {}, loc,
            cir::StorageDuration::Automatic);

        ExprResult source;
        source.place = source_place;
        source.type = type;
        source.category = ValueCategory::XValue;
        bool ambiguous = false;
        cir::EntityId constructor = select_constructor(
            type, {source}, &ambiguous, loc,
            ConstructorInitializationKind::Direct);
        if (!constructor.valid()) {
            report_error(
                "the coroutine parameter's frame copy has no viable "
                "constructor",
                loc);
            coro.emission_failed = true;
            return;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("coro.param.copy");
        cir::InstId copy_place = builder_.local_place(copy_entity, type, loc);
        emit_construct_in_place(copy_place,
                                structor_complete_variant(constructor),
                                {builder_.addr_of(source_place, loc)},
                                loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        current_prologue_ =
            chain(std::move(current_prologue_), std::move(fragment), loc);
        coro.parameter_copies.push_back({copy_place, type});
        coro.promise_ctor_args.push_back({copy_place, type, false});

        auto remap_range =
            [&](cir::OperandRange range) -> std::vector<cir::Operand> {
            std::vector<cir::Operand> operands = file_.operands(range);
            bool changed = false;
            for (cir::Operand& operand : operands) {
                auto* value = std::get_if<cir::ValueRef>(&operand.data);
                if (value && value->inst == source_place) {
                    *value = cir::ValueRef(copy_place);
                    changed = true;
                }
            }
            if (!changed) {
                operands.clear();
            }
            return operands;
        };
        for (cir::BlockId block_id : body_fragment.blocks) {
            for (cir::InstId inst_id : file_.block(block_id).instructions) {
                std::vector<cir::Operand> remapped =
                    remap_range(file_.inst(inst_id).operands);
                if (!remapped.empty()) {
                    file_.inst_mut(inst_id).operands =
                        file_.add_operands(remapped);
                }
            }
            std::vector<cir::Operand> remapped =
                remap_range(file_.block(block_id).terminator.operands);
            if (!remapped.empty()) {
                file_.block_mut(block_id).terminator.operands =
                    file_.add_operands(remapped);
            }
        }
    }
}

void Session::emit_coroutine_promise_init(CoroutineState& coro, SrcLoc loc) {

    if (coro.promise_ctor_args_complete &&
        (coro.object_param_place.valid() || !coro.promise_ctor_args.empty())) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("coro.promise.args");
        std::vector<ExprResult> q;
        if (coro.object_param_place.valid()) {
            cir::InstId pointer =
                builder_.lvalue_to_rvalue(coro.object_param_place, loc);
            cir::InstId object = builder_.deref(pointer, loc);
            ExprResult arg;
            arg.place = object;
            arg.type = coro.object_param_type;
            arg.category = ValueCategory::LValue;
            q.push_back(std::move(arg));
        }
        for (const CoroutineState::PromiseCtorArg& parameter :
             coro.promise_ctor_args) {
            ExprResult arg;
            arg.category = ValueCategory::LValue;
            if (parameter.is_reference) {
                cir::InstId pointer =
                    builder_.lvalue_to_rvalue(parameter.place, loc);
                arg.place = builder_.deref(pointer, loc);
                arg.type = file_.reference_referred_type(parameter.type);
            } else {
                arg.place = parameter.place;
                arg.type = parameter.type;
            }
            q.push_back(std::move(arg));
        }
        cir::Fragment head = finish_fragment_block(block, previous);

        bool ambiguous = false;
        cir::EntityId constructor = select_constructor(
            coro.promise_type, q, &ambiguous, loc,
            ConstructorInitializationKind::Direct);
        if (ambiguous) {
            report_error(
                "the promise constructor call assembled from the "
                "coroutine's parameters is ambiguous",
                loc);
            coro.emission_failed = true;
            current_prologue_ =
                chain(std::move(current_prologue_), std::move(head), loc);
            return;
        }
        if (constructor.valid()) {
            ConstructorCallMaterialization materialized =
                materialize_selected_constructor_call(constructor,
                                                      std::move(q), loc);
            if (materialized.has_error) {
                coro.emission_failed = true;
                current_prologue_ =
                    chain(std::move(current_prologue_), std::move(head), loc);
                return;
            }
            head = chain(std::move(head),
                         std::move(materialized.argument_fragment), loc);
            cir::BlockId call_previous = builder_.current_block();
            cir::BlockId call_block =
                begin_fragment_block("coro.promise.init");
            builder_.construct_in_place(coro.promise_place,
                                        structor_complete_variant(constructor),
                                        materialized.argument_values, loc);
            head = chain(std::move(head),
                         finish_fragment_block(call_block, call_previous),
                         loc);
            current_prologue_ =
                chain(std::move(current_prologue_), std::move(head), loc);
            return;
        }
        current_prologue_ =
            chain(std::move(current_prologue_), std::move(head), loc);
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("coro.promise.init");
    bool constructed = false;
    cir::EntityId promise_ctor = select_constructor(
        coro.promise_type, {}, nullptr, loc,
        ConstructorInitializationKind::Direct);
    if (promise_ctor.valid()) {
        const cir::RecordMethodFact* ctor_fact =
            file_.method_fact(promise_ctor);
        if (!ctor_fact || !ctor_fact->is_trivial) {
            builder_.construct_in_place(coro.promise_place, promise_ctor, {},
                                        loc);
            constructed = true;
        }
    }
    if (!constructed) {
        builder_.zero_object(coro.promise_place, loc);
    }
    current_prologue_ = chain(std::move(current_prologue_),
                              finish_fragment_block(block, previous), loc);
}

StmtResult Session::finish_coroutine_function(CoroutineState& coro,
                                              StmtResult body,
                                              SrcLoc loc) {
    current_prologue_ = chain(std::move(coro.preamble_fragment),
                              std::move(current_prologue_), loc);
    emit_coroutine_parameter_copies(coro, body.fragment, loc);

    emit_coroutine_promise_init(coro, loc);
    cir::Fragment replacement;
    ExprResult return_object =
        collect_promise_member_call(coro, "get_return_object", {}, loc);
    bool emission_ok = !coro.emission_failed && !return_object.has_error;
    replacement = chain(std::move(replacement),
                        std::move(return_object.fragment), loc);

    cir::BlockId handler_pad{};
    cir::BlockId handler_action{};
    cir::Fragment handler_fragment;
    if (emission_ok) {
        if (!coro.final_suspend_block.valid()) {
            coro.final_suspend_block =
                builder_.create_detached_block("coro.final");
        }
        cir::BlockId handler_previous = builder_.current_block();
        cir::BlockId pad = begin_fragment_block("coro.lpad");
        handler_pad = pad;
        cir::EhLandingPadPayload pad_payload;
        pad_payload.has_catch_all = true;
        cir::InstId exception =
            builder_.eh_landing_pad(std::move(pad_payload), loc);
        cir::InstId selector = builder_.eh_selector(exception, loc);
        cir::BlockId action =
            builder_.create_detached_block("coro.lpad.action");
        handler_action = action;
        cir::InstId exn_param = builder_.add_block_parameter(
            action, builder_.pointer_type(builder_.void_type()), "exn", loc);
        builder_.add_block_parameter(action, builder_.int_type(), "sel",
                                     loc);
        builder_.branch(action, {exception, selector}, loc);
        builder_.switch_to_block(action);
        builder_.catch_begin(exn_param, loc);
        builder_.coro_save(1, cir::CoroSaveKind::Final, loc);
        cir::Fragment handler_head = builder_.block_fragment(pad);
        handler_head.blocks.push_back(action);
        handler_head.exit = action;
        handler_head.falls_through = true;
        builder_.switch_to_block(handler_previous);
        ExprResult unhandled = collect_promise_member_call(
            coro, "unhandled_exception", {}, loc);
        emission_ok = !unhandled.has_error;
        handler_head = chain(std::move(handler_head),
                             std::move(unhandled.fragment), loc);
        cir::BlockId tail_previous = builder_.current_block();
        cir::BlockId tail = begin_fragment_block("coro.lpad.end");
        builder_.catch_end(loc);
        cir::Fragment tail_fragment =
            finish_fragment_block(tail, tail_previous);
        handler_head =
            chain(std::move(handler_head), std::move(tail_fragment), loc);
        if (!builder_.block_terminated(handler_head.exit)) {
            builder_.branch_from(handler_head.exit,
                                 coro.final_suspend_block, {}, loc);
        }
        handler_head.falls_through = false;
        handler_fragment = std::move(handler_head);
    }

    std::vector<cir::BlockId> initial_resume_blocks;
    if (emission_ok) {
        ExprResult initial =
            collect_promise_member_call(coro, "initial_suspend", {}, loc);
        ExprResult initial_await =
            emit_await(coro, std::move(initial), cir::CoroSaveKind::Initial,
                       loc, &initial_resume_blocks);
        emission_ok = !coro.emission_failed && !initial_await.has_error;
        replacement = chain(std::move(replacement),
                            std::move(initial_await.fragment), loc);
    }

    bool body_falls_through = body.falls_through;
    std::vector<cir::BlockId> covered_body_blocks = body.fragment.blocks;
    replacement = chain(std::move(replacement), std::move(body.fragment), loc);

    if (emission_ok && handler_pad.valid()) {
        auto stamp = [&](const std::vector<cir::BlockId>& blocks) {
            for (cir::BlockId block_id : blocks) {
                if (!block_id.valid()) {
                    continue;
                }
                if (file_.block(block_id).unwind_target.valid()) {
                    continue;
                }
                builder_.set_block_unwind_target(block_id, handler_pad);
            }
        };
        stamp(initial_resume_blocks);
        stamp(covered_body_blocks);
    }

    if (emission_ok && body_falls_through &&
        !builder_.block_terminated(replacement.exit)) {
        if (coro.has_return_void) {
            ExprResult falloff =
                collect_promise_member_call(coro, "return_void", {}, loc);
            emission_ok = !falloff.has_error;
            replacement =
                chain(std::move(replacement), std::move(falloff.fragment), loc);
            if (!coro.final_suspend_block.valid()) {
                coro.final_suspend_block =
                    builder_.create_detached_block("coro.final");
            }
            if (!builder_.block_terminated(replacement.exit)) {
                builder_.branch_from(replacement.exit,
                                     coro.final_suspend_block, {}, loc);
            }
        } else {
            builder_.unreachable_from(replacement.exit, loc);
        }
    }
    replacement.falls_through = false;
    if (emission_ok && !handler_fragment.empty()) {
        append_fragment_blocks(replacement, handler_fragment);
    }

    if (emission_ok && coro.final_suspend_block.valid()) {
        replacement.blocks.push_back(coro.final_suspend_block);
        ExprResult final_operand =
            collect_promise_member_call(coro, "final_suspend", {}, loc);
        ExprResult final_await = emit_await(coro, std::move(final_operand),
                                            cir::CoroSaveKind::Final, loc);
        emission_ok = !coro.emission_failed && !final_await.has_error;
        if (emission_ok && !final_await.fragment.empty()) {
            builder_.branch_from(coro.final_suspend_block,
                                 final_await.fragment.entry, {}, loc);
            append_fragment_blocks(replacement, final_await.fragment);
        } else if (!builder_.block_terminated(coro.final_suspend_block)) {
            builder_.unreachable_from(coro.final_suspend_block, loc);
        }
    }

    if (emission_ok) {
        cir::BlockId cleanup_previous = builder_.current_block();
        cir::BlockId cleanup_body = begin_fragment_block("coro.free");
        (void)validate_potentially_invoked_destructor(coro.promise_type, loc);
        builder_.destroy(coro.promise_place,
                         record_destructor(coro.promise_type), loc);
        for (size_t i = coro.parameter_copies.size(); i-- > 0;) {
            const CoroutineState::ParameterCopy& copy =
                coro.parameter_copies[i];
            (void)validate_potentially_invoked_destructor(copy.type, loc);
            builder_.destroy(copy.place, record_destructor(copy.type), loc);
        }

        DeallocationSelection deallocation = select_deallocation_function(
            coro.promise_type, /*is_array=*/false, /*force_global=*/false,
            /*placement_matching=*/false, nullptr, {}, loc,
            /*diagnose=*/false);
        if (deallocation.valid()) {
            std::vector<cir::InstId> arguments{coro.frame_pointer};
            if (deallocation.form.is_sized) {
                arguments.push_back(builder_.coro_frame_size(loc));
            }
            if (deallocation.form.is_aligned) {
                arguments.push_back(builder_.coro_frame_align(loc));
            }
            builder_.call(deallocation.entity, builder_.void_type(),
                          arguments, loc);
        } else {
            cir::EntityId deallocator = implicit_deallocation_operator(
                /*is_array=*/false, /*sized=*/false, /*aligned=*/false, loc);
            builder_.call(deallocator, builder_.void_type(),
                          {coro.frame_pointer}, loc);
        }
        cir::Fragment cleanup_fragment =
            finish_fragment_block(cleanup_body, cleanup_previous);
        builder_.coro_end_from(cleanup_fragment.exit, loc);
        replacement.blocks.push_back(coro.cleanup_block);
        builder_.branch_from(coro.cleanup_block, cleanup_fragment.entry, {},
                             loc);
        append_fragment_blocks(replacement, cleanup_fragment);
        replacement.exit = cleanup_fragment.exit;
        replacement.falls_through = false;
    }

    if (emission_ok && coro.alloc_failure_block.valid()) {
        cir::EntityId promise_record =
            file_.record_entity(file_.resolved_type(coro.promise_type));
        cir::DeclContextId promise_context =
            promise_record.valid() && file_.valid(promise_record)
                ? file_.entity(promise_record).semantic_context
                : cir::DeclContextId{};
        ExprResult callee = lookup_qualified_name(
            promise_context, "get_return_object_on_allocation_failure", loc);
        ExprResult failure_value =
            collect_call_expr(std::move(callee), {}, loc);
        cir::Fragment failure_fragment = std::move(failure_value.fragment);
        failure_value.fragment = {};
        std::unique_ptr<CoroutineState> failure_parked =
            std::move(coroutine_state_);
        StmtResult failure_return =
            collect_return_stmt(std::move(failure_value), loc);
        coroutine_state_ = std::move(failure_parked);
        emission_ok = !failure_return.has_error;
        failure_fragment = chain(std::move(failure_fragment),
                                 std::move(failure_return.fragment), loc);
        replacement.blocks.push_back(coro.alloc_failure_block);
        if (emission_ok && !failure_fragment.empty()) {
            builder_.branch_from(coro.alloc_failure_block,
                                 failure_fragment.entry, {}, loc);
            append_fragment_blocks(replacement, failure_fragment);
        } else if (!builder_.block_terminated(coro.alloc_failure_block)) {
            builder_.unreachable_from(coro.alloc_failure_block, loc);
        }
    }
    cir::BlockId ramp_return_block{};
    if (emission_ok) {
        ExprResult return_value;
        return_value.value = return_object.value;
        return_value.place = return_object.place;
        return_value.type = return_object.type;
        return_value.category = return_object.category;
        std::unique_ptr<CoroutineState> parked = std::move(coroutine_state_);
        StmtResult ramp_return =
            collect_return_stmt(std::move(return_value), loc);
        coroutine_state_ = std::move(parked);
        emission_ok = !ramp_return.has_error;
        if (emission_ok && !ramp_return.fragment.empty()) {
            ramp_return_block = ramp_return.fragment.exit.valid()
                ? ramp_return.fragment.exit
                : ramp_return.fragment.entry;
            append_fragment_blocks(replacement, ramp_return.fragment);
            replacement.falls_through = false;
        }
    }

    if (!emission_ok) {
        coro.emission_failed = true;
        StmtResult failed;
        failed.fragment = std::move(replacement);
        failed.fragment.falls_through = false;
        failed.falls_through = false;
        failed.has_error = true;
        return failed;
    }

    cir::CoroutineFact fact;
    fact.function = file_.function(current_function_).entity;
    fact.promise_type = coro.promise_type;
    fact.ramp_return_block = ramp_return_block;
    fact.alloc_failure_block = coro.alloc_failure_block;
    fact.eh_action_block = handler_action;
    fact.suspend_count = coro.next_user_suspend_index;
    file_.add_coroutine_fact(std::move(fact));

    StmtResult result;
    result.fragment = std::move(replacement);
    result.falls_through = false;
    result.always_returns = true;
    result.has_error = body.has_error;
    return result;
}

ExprResult Session::collect_coro_handle_builtin(BuiltinKind kind,
                                                std::vector<ExprResult> args,
                                                SrcLoc loc) {
    ExprResult result;
    result.category = ValueCategory::PrValue;
    result.type = builder_.void_type();
    if (args.empty()) {
        result.has_error = true;
        return result;
    }
    bool dependent = collecting_pattern();
    for (const ExprResult& arg : args) {
        dependent = dependent || expr_is_dependent(arg) ||
            expr_is_value_dependent(arg);
    }
    if (dependent) {
        ExprResult folded = std::move(args[0]);
        for (size_t i = 1; i < args.size(); ++i) {
            folded.fragment = chain(std::move(folded.fragment),
                                    std::move(args[i].fragment), loc);
        }
        return make_dependent_expr(std::move(folded), loc);
    }
    ExprResult frame =
        require_value(std::move(args[0]), UseContext::RValue, loc);
    if (frame.has_error || !frame.value.valid()) {
        result.fragment = std::move(frame.fragment);
        result.has_error = true;
        return result;
    }
    cir::TypeId void_pointer = builder_.pointer_type(builder_.void_type());
    cir::TypeId resume_pointer = builder_.pointer_type(
        builder_.function_type(builder_.void_type(), {void_pointer}));

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("coro.handle");

    auto header_slot = [&](int64_t index) {
        cir::InstId typed = builder_.cast(
            builder_.pointer_type(resume_pointer), frame.value, "value", loc);
        cir::InstId index_value = builder_.integer_literal(
            index, std::to_string(index), loc);
        cir::InstId slot =
            builder_.array_element_place(typed, index_value, loc);
        return builder_.load(slot, loc);
    };
    switch (kind) {
        case BuiltinKind::CORO_DONE: {
            cir::InstId resume_fn = header_slot(0);
            cir::InstId null_value = builder_.cast(
                resume_pointer, builder_.nullptr_literal("nullptr", loc),
                "nullptr", loc);
            result.value = builder_.binary(cir::BinaryOpKind::Equal,
                                           builder_.bool_type(), resume_fn,
                                           null_value, loc);
            result.type = builder_.bool_type();
            break;
        }
        case BuiltinKind::CORO_RESUME:
        case BuiltinKind::CORO_DESTROY: {
            cir::InstId callee =
                header_slot(kind == BuiltinKind::CORO_RESUME ? 0 : 1);
            builder_.call_indirect(callee, builder_.void_type(),
                                   {frame.value}, loc);
            break;
        }
        case BuiltinKind::CORO_PROMISE: {
            int64_t alignment = 0;
            int64_t from_promise = 0;
            if (args.size() < 3 ||
                !evaluate_integer_constant(
                    args[1], alignment, loc,
                    "__builtin_coro_promise alignment must be an integer "
                    "constant") ||
                !evaluate_integer_constant(
                    args[2], from_promise, loc,
                    "__builtin_coro_promise direction must be an integer "
                    "constant")) {
                result.has_error = true;
                break;
            }
            size_t pointer_bytes = (file_.target_info().pointer_width + 7) / 8;
            int64_t offset = static_cast<int64_t>(2 * pointer_bytes);
            if (alignment > 0) {
                int64_t align = alignment;
                offset = (offset + align - 1) / align * align;
            }
            if (from_promise != 0) {
                offset = -offset;
            }
            cir::TypeId byte_type =
                file_.builtin_type(cir::BuiltinTypeKind::Char);
            cir::InstId bytes = builder_.cast(
                builder_.pointer_type(byte_type), frame.value, "value", loc);
            cir::InstId offset_value = builder_.integer_literal(
                offset, std::to_string(offset), loc);
            cir::InstId element =
                builder_.array_element_place(bytes, offset_value, loc);
            cir::InstId address = builder_.addr_of(element, loc);
            result.value =
                builder_.cast(void_pointer, address, "value", loc);
            result.type = void_pointer;
            break;
        }
        default:
            result.has_error = true;
            break;
    }
    cir::Fragment fragment = finish_fragment_block(block, previous);
    result.fragment =
        chain(std::move(frame.fragment), std::move(fragment), loc);
    return result;
}

ExprResult Session::collect_await_expr(ExprResult operand, SrcLoc loc) {
    ExprResult result;
    result.type = builder_.void_type();
    result.category = ValueCategory::PrValue;
    if (active_catch_handlers_ > 0) {

        report_error("'co_await' cannot appear in the handler of a try block",
                     loc);
        result.fragment = std::move(operand.fragment);
        result.has_error = true;
        return result;
    }
    if (collecting_pattern()) {

        mark_pattern_unusable();
        bump_pattern_taint();
        return make_dependent_expr(std::move(operand), loc);
    }
    CoroutineState* coro = ensure_coroutine_context("'co_await'", loc);
    if (!coro) {
        result.fragment = std::move(operand.fragment);
        result.has_error = true;
        return result;
    }
    if (!lang_opts_.enable_coroutine_pre_split_cir) {
        diagnose_coroutine_codegen_gate(*coro, loc);
        result.fragment = std::move(operand.fragment);
        result.has_error = true;
        return result;
    }
    if (coro->has_await_transform) {

        std::vector<ExprResult> args;
        args.push_back(std::move(operand));
        operand = collect_promise_member_call(*coro, "await_transform",
                                              std::move(args), loc);
        if (operand.has_error) {
            result.fragment = std::move(operand.fragment);
            result.has_error = true;
            coro->emission_failed = true;
            return result;
        }
    }
    return emit_await(*coro, std::move(operand), cir::CoroSaveKind::User, loc);
}

ExprResult Session::collect_yield_expr(ExprResult operand, SrcLoc loc) {
    ExprResult result;
    result.type = builder_.void_type();
    result.category = ValueCategory::PrValue;
    if (active_catch_handlers_ > 0) {
        report_error("'co_yield' cannot appear in the handler of a try block",
                     loc);
        result.fragment = std::move(operand.fragment);
        result.has_error = true;
        return result;
    }
    if (collecting_pattern()) {
        mark_pattern_unusable();
        bump_pattern_taint();
        return make_dependent_expr(std::move(operand), loc);
    }
    CoroutineState* coro = ensure_coroutine_context("'co_yield'", loc);
    if (!coro) {
        result.fragment = std::move(operand.fragment);
        result.has_error = true;
        return result;
    }

    if (!lookup_member_name(coro->promise_type, "yield_value").found_name) {
        report_error("coroutine promise type has no member 'yield_value'",
                     loc);
        result.fragment = std::move(operand.fragment);
        result.has_error = true;
        return result;
    }
    if (!lang_opts_.enable_coroutine_pre_split_cir) {
        diagnose_coroutine_codegen_gate(*coro, loc);
        result.fragment = std::move(operand.fragment);
        result.has_error = true;
        return result;
    }
    std::vector<ExprResult> args;
    args.push_back(std::move(operand));
    ExprResult awaitable =
        collect_promise_member_call(*coro, "yield_value", std::move(args), loc);
    return emit_await(*coro, std::move(awaitable), cir::CoroSaveKind::User,
                      loc);
}

StmtResult Session::collect_co_return_stmt(std::optional<ExprResult> operand,
                                           SrcLoc loc,
                                           LifetimeBoundary boundary) {
    StmtResult result;
    result.has_error = true;
    if (collecting_pattern()) {
        discard_lifetime_boundary(boundary);
        mark_pattern_unusable();
        bump_pattern_taint();
        StmtResult deferred;
        if (operand.has_value()) {
            deferred.fragment = std::move(operand->fragment);
        }
        deferred.falls_through = false;
        deferred.always_returns = true;
        return deferred;
    }
    CoroutineState* coro = ensure_coroutine_context("'co_return'", loc);
    if (!coro) {
        discard_lifetime_boundary(boundary);
        if (operand.has_value()) {
            result.fragment = std::move(operand->fragment);
        }
        return result;
    }

    bool has_operand = operand.has_value();
    if (has_operand && !coro->has_return_value) {
        discard_lifetime_boundary(boundary);
        report_error("coroutine promise type has no member 'return_value'",
                     loc);
        result.fragment = std::move(operand->fragment);
        return result;
    }
    if (!has_operand && !coro->has_return_void) {
        discard_lifetime_boundary(boundary);
        report_error("coroutine promise type has no member 'return_void'",
                     loc);
        return result;
    }
    if (!lang_opts_.enable_coroutine_pre_split_cir) {
        discard_lifetime_boundary(boundary);
        diagnose_coroutine_codegen_gate(*coro, loc);
        if (operand.has_value()) {
            result.fragment = std::move(operand->fragment);
        }
        return result;
    }

    std::vector<ExprResult> args;
    if (has_operand) {
        args.push_back(std::move(*operand));
    }
    ExprResult call = collect_promise_member_call(
        *coro, has_operand ? "return_value" : "return_void", std::move(args),
        loc);
    cir::Fragment fragment = std::move(call.fragment);
    fragment = chain(std::move(fragment),
                     finish_lifetime_boundary(boundary, loc), loc);
    fragment = chain(std::move(fragment),
                     emit_cleanup_calls_from_depth(0, loc), loc);
    fragment = adopt_or_create_fragment_entry(std::move(fragment),
                                              "stmt.co_return");
    if (call.has_error) {
        coro->emission_failed = true;
        result.fragment = std::move(fragment);
        return result;
    }
    if (!coro->final_suspend_block.valid()) {
        coro->final_suspend_block =
            builder_.create_detached_block("coro.final");
    }
    if (!builder_.block_terminated(fragment.exit)) {
        builder_.branch_from(fragment.exit, coro->final_suspend_block, {},
                             loc);
    }
    fragment.falls_through = false;
    result.fragment = std::move(fragment);
    result.falls_through = false;
    result.always_returns = true;
    result.has_error = false;
    return result;
}

} // namespace aburi::collect
