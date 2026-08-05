#include "lowerer.h"

#include <algorithm>
#include <utility>
#include <variant>

#include "../abi/aarch64_call_classify.h"
#include "../builtin_registry.h"
#include "../cir/layout.h"

namespace aburi::cir2air {

namespace {

cir::EntityId entity_operand_at(const std::vector<cir::Operand>& operands,
                                size_t index) {
    if (index < operands.size()) {
        if (const auto* entity = std::get_if<cir::EntityId>(&operands[index].data)) {
            return *entity;
        }
    }
    return cir::EntityId{};
}

cir::ValueRef value_operand_at(const std::vector<cir::Operand>& operands,
                               size_t index) {
    if (index < operands.size()) {
        if (const auto* value = std::get_if<cir::ValueRef>(&operands[index].data)) {
            return *value;
        }
    }
    return cir::ValueRef{};
}

std::string builtin_runtime_name(std::string_view name) {
    constexpr std::string_view prefix = "__builtin_";
    if (name.rfind(prefix, 0) == 0) {
        name.remove_prefix(prefix.size());
    }
    return std::string(name);
}

uint64_t hfa_element_size(air::TypeId element) {
    return element == air::types::F32 ? 4 : 8;
}

cir::EntityId parameter_argument_object(const cir::File& file,
                                        cir::InstId value) {
    if (!file.valid(value) ||
        file.inst(value).kind != cir::InstKind::LValueToRValue) {
        return {};
    }
    std::vector<cir::Operand> value_operands =
        file.operands(file.inst(value).operands);
    cir::ValueRef place = value_operand_at(value_operands, 0);
    if (!file.valid(place.inst)) {
        return {};
    }
    const cir::Inst& place_inst = file.inst(place.inst);
    if (!place_inst.place_fact.valid()) {
        return {};
    }
    cir::EntityId entity = file.place_fact(place_inst.place_fact).entity;
    return file.valid(entity) && file.entity(entity).is_parameter_argument_object
        ? entity
        : cir::EntityId{};
}

} // namespace

bool Lowerer::marshal_argument(const abi::AggregateClass& cls,
                               cir::TypeRef param_type,
                               cir::ValueRef arg_ref,
                               std::vector<air::ValueId>& args,
                               std::vector<air::SigParam>& site_params,
                               SrcLoc loc) {
    air::Builder& b = *builder_;
    air::ValueId arg = value_for(arg_ref, loc);
    if (!arg.is_valid()) {
        return false;
    }
    cir::TypeId arg_type = file_.valid(arg_ref.inst)
        ? file_.inst(arg_ref.inst).result_type
        : cir::TypeId{};

    switch (cls.pass) {
        case abi::AggregatePass::UseSourceType:
            if (param_type.type.valid()) {
                arg = cast_value(arg, arg_type, param_type.type, loc);
                if (!arg.is_valid()) {
                    return false;
                }
            } else if (!mod_->types().is_scalar(air_func_->value_type(arg))) {
                error("not supported by the air backend yet: this argument kind",
                      loc);
                return false;
            }
            args.push_back(arg);
            site_params.push_back(
                {air_func_->value_type(arg), air::ParamRole::Normal});
            return true;
        case abi::AggregatePass::Ignore:

            return true;
        case abi::AggregatePass::CoerceIntSlots: {

            uint32_t slot_bytes = cls.slot_bytes;
            air::TypeId slot_type =
                slot_bytes == 4 ? air::types::I32 : air::types::I64;
            uint64_t padded = uint64_t{slot_bytes} * cls.int_slot_count;
            air::ValueId staging = create_entry_stack_alloc(padded, slot_bytes);
            b.memcpy_(staging, arg,
                      b.const_usize(static_cast<int64_t>(cls.byte_size)));
            for (uint8_t slot = 0; slot < cls.int_slot_count; ++slot) {
                air::ValueId slot_ptr = slot == 0
                    ? staging
                    : b.ptr_add(staging,
                                static_cast<int64_t>(slot_bytes * slot));
                args.push_back(b.load(slot_type, slot_ptr, slot_bytes));
                air::SigParam slot_param{slot_type, air::ParamRole::Normal};
                if (slot == 0 && cls.int_slot_count > 1) {
                    slot_param.coerce_group = cls.int_slot_count;
                }
                site_params.push_back(slot_param);
            }
            return true;
        }
        case abi::AggregatePass::CoerceHfa: {
            std::optional<air::TypeId> element =
                hfa_element_type(cls.hfa_element, loc);
            if (!element) {
                return false;
            }
            uint64_t element_size = hfa_element_size(*element);
            for (uint8_t lane = 0; lane < cls.hfa_count; ++lane) {
                air::ValueId lane_ptr = lane == 0
                    ? arg
                    : b.ptr_add(arg, static_cast<int64_t>(lane * element_size));
                args.push_back(b.load(*element, lane_ptr,
                                      static_cast<uint32_t>(element_size)));
                site_params.push_back({*element, air::ParamRole::Normal});
            }
            return true;
        }
        case abi::AggregatePass::CoerceClassedSlots: {

            uint64_t padded = 8ull * cls.int_slot_count;
            air::ValueId staging = create_entry_stack_alloc(padded, 8);
            b.memcpy_(staging, arg,
                      b.const_usize(static_cast<int64_t>(cls.byte_size)));
            for (uint8_t slot = 0; slot < cls.int_slot_count; ++slot) {
                air::ValueId slot_ptr = slot == 0
                    ? staging
                    : b.ptr_add(staging, static_cast<int64_t>(8 * slot));
                bool sse = (cls.sse_slot_mask >> slot) & 1;
                air::TypeId slot_type = sse ? air::types::F64 : air::types::I64;
                args.push_back(b.load(slot_type, slot_ptr, 8));
                air::SigParam slot_param{slot_type, air::ParamRole::Normal};
                if (slot == 0 && cls.int_slot_count > 1) {
                    slot_param.coerce_group = cls.int_slot_count;
                }
                site_params.push_back(slot_param);
            }
            return true;
        }
        case abi::AggregatePass::MemoryByval: {

            args.push_back(arg);
            air::SigParam byval;
            byval.type = air::types::PTR;
            byval.role = air::ParamRole::StackByval;
            byval.byval_size =
                static_cast<uint32_t>(std::max<uint64_t>(1, cls.byte_size));
            byval.byval_align = std::max<uint32_t>(1, cls.byte_align);
            site_params.push_back(byval);
            return true;
        }
        case abi::AggregatePass::Indirect: {

            if (parameter_argument_object(file_, arg_ref.inst).valid()) {
                args.push_back(arg);
                site_params.push_back(
                    {air::types::PTR, air::ParamRole::IndirectByval});
                return true;
            }
            auto size_align = param_type.type.valid()
                ? cir::size_align_of_type(file_, param_type.type)
                : cir::size_align_of_type(file_, arg_type);
            if (!size_align) {
                error("cannot pass an incomplete aggregate by value", loc);
                return false;
            }
            air::ValueId copy = create_entry_stack_alloc(
                std::max<uint64_t>(1, size_align->size_bytes),
                static_cast<uint32_t>(
                    std::max<size_t>(1, size_align->alignment_bytes)));
            b.memcpy_(copy, arg,
                      b.const_usize(static_cast<int64_t>(size_align->size_bytes)));
            args.push_back(copy);
            site_params.push_back({air::types::PTR, air::ParamRole::IndirectByval});
            return true;
        }
    }
    return false;
}

bool Lowerer::function_type_may_throw(cir::TypeId function_type) const {
    cir::TypeId resolved = file_.resolved_type(function_type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Function) {
        return true;
    }
    const auto& payload =
        std::get<cir::FunctionTypePayload>(file_.type_payload(resolved));
    return payload.exception_spec.kind !=
           cir::FunctionExceptionSpecKind::NonThrowing;
}

air::BlockId Lowerer::air_block_for(cir::BlockId target, SrcLoc loc) {
    auto found = block_ids_.find(id_key(target));
    if (found == block_ids_.end()) {
        error("branch target block was not lowered", loc);
        return air::BlockId{};
    }
    return found->second;
}

air::BlockId Lowerer::current_unwind_target(SrcLoc loc) {
    if (!file_.valid(current_cir_block_)) {
        return air::BlockId{};
    }
    const cir::Block& block = file_.block(current_cir_block_);
    if (!block.unwind_target.valid()) {
        return air::BlockId{};
    }
    return air_block_for(block.unwind_target, loc);
}

air::ValueId Lowerer::emit_call_or_invoke(air::FuncId callee,
                                          std::span<const air::ValueId> args,
                                          bool can_throw,
                                          SrcLoc loc) {
    air::Builder& b = *builder_;
    air::BlockId unwind = can_throw ? current_unwind_target(loc) : air::BlockId{};
    if (!unwind.is_valid()) {
        return b.call(callee, args);
    }
    air::BlockId normal = b.create_block();
    air::ValueId result = b.invoke(callee, args, normal, {}, unwind, {});
    b.set_insertion_point(normal);
    return result;
}

air::ValueId Lowerer::emit_call_indirect_or_invoke(
    air::SigId sig,
    air::ValueId callee,
    std::span<const air::ValueId> args,
    bool can_throw,
    SrcLoc loc) {
    air::Builder& b = *builder_;
    air::BlockId unwind = can_throw ? current_unwind_target(loc) : air::BlockId{};
    if (!unwind.is_valid()) {
        return b.call_indirect(sig, callee, args);
    }
    air::BlockId normal = b.create_block();
    air::ValueId result =
        b.invoke_indirect(sig, callee, args, normal, {}, unwind, {});
    b.set_insertion_point(normal);
    return result;
}

bool Lowerer::invoke_eh_runtime(const std::string& name,
                                std::span<const air::ValueId> args,
                                air::SigId sig,
                                SrcLoc loc) {
    air::BlockId unwind = current_unwind_target(loc);
    if (!unwind.is_valid()) {
        return false;
    }
    air::Builder& b = *builder_;
    air::FuncId helper = declare_runtime_helper(name, sig);
    air::BlockId normal = b.create_block();
    b.invoke(helper, args, normal, {}, unwind, {});
    b.set_insertion_point(normal);
    return true;
}

void Lowerer::lower_call(cir::InstId inst_id,
                         const cir::Inst& inst,
                         const std::vector<cir::Operand>& operands) {
    air::Builder& b = *builder_;
    if (operands.empty()) {
        error("call is missing a callee", inst.loc);
        return;
    }

    air::FuncId direct_callee{};
    air::ValueId indirect_callee{};
    SignatureInfo sig_info;

    if (const auto* entity = std::get_if<cir::EntityId>(&operands[0].data)) {
        if (file_.valid(*entity) &&
            file_.entity(*entity).decl_flags.is_consteval) {
            error("call to consteval function is not a constant expression",
                  inst.loc);
            return;
        }
        direct_callee = get_or_declare_function(*entity);
        if (!direct_callee.is_valid()) {
            return;
        }
        sig_info = signature_for_function_type(file_.entity(*entity).type, inst.loc);
    } else if (const auto* value = std::get_if<cir::ValueRef>(&operands[0].data)) {
        indirect_callee = value_for(*value, inst.loc);
        if (!indirect_callee.is_valid()) {
            return;
        }
        cir::TypeId callee_type = file_.inst(value->inst).result_type;
        cir::TypeId function_type = file_.pointer_pointee_type(callee_type);
        cir::TypeId resolved = file_.resolved_type(function_type);
        if (!file_.valid(resolved) ||
            file_.type(resolved).kind != cir::TypeKind::Function) {
            error("not supported by the air backend yet: calls through non-function pointers",
                  inst.loc);
            return;
        }
        sig_info = signature_for_function_type(function_type, inst.loc);
    } else {
        error("call callee operand has invalid kind", inst.loc);
        return;
    }
    if (!sig_info.ok) {
        return;
    }

    const abi::AggregateClass& ret_cls = sig_info.ret_class;
    auto ret_size_align = cir::size_align_of_type(file_, sig_info.return_type.type);
    auto aggregate_result_buffer = [&](uint64_t size, uint32_t align) {
        return create_entry_stack_alloc(std::max<uint64_t>(1, size),
                                        std::max<uint32_t>(1, align));
    };

    std::vector<air::ValueId> args;
    std::vector<air::SigParam> site_params;
    args.reserve(operands.size() + 1);
    site_params.reserve(operands.size() + 1);

    air::ValueId result_buffer{};
    if (ret_cls.pass == abi::AggregatePass::Indirect ||
        ret_cls.pass == abi::AggregatePass::MemoryByval) {
        if (!ret_size_align) {
            error("cannot return an incomplete aggregate by value", inst.loc);
            return;
        }
        result_buffer = inst.result_object_entity.valid()
            ? storage_for_entity(inst.result_object_entity, inst.loc)
            : aggregate_result_buffer(
                  ret_size_align->size_bytes,
                  static_cast<uint32_t>(ret_size_align->alignment_bytes));
        if (!result_buffer.is_valid()) {
            return;
        }
        args.push_back(result_buffer);
        site_params.push_back({air::types::PTR, air::ParamRole::Sret});
    }

    size_t source_args = operands.size() - 1;
    if (sig_info.has_prototype && !sig_info.is_variadic &&
        source_args != sig_info.param_classes.size()) {
        error("call argument count does not match callee type", inst.loc);
        return;
    }

    for (size_t i = 1; i < operands.size(); ++i) {
        cir::ValueRef arg_ref = value_operand_at(operands, i);
        size_t param_index = i - 1;
        if (param_index < sig_info.param_classes.size()) {
            if (!marshal_argument(sig_info.param_classes[param_index],
                                  sig_info.param_types[param_index],
                                  arg_ref, args, site_params, inst.loc)) {
                return;
            }
        } else if (sig_info.is_variadic || !sig_info.has_prototype) {

            cir::TypeId arg_type = file_.valid(arg_ref.inst)
                ? file_.inst(arg_ref.inst).result_type
                : cir::TypeId{};
            abi::AggregateClass vararg_class = abi::classify_vararg_native(
                file_, file_.type_ref(arg_type), options_.target.get());
            if (!marshal_argument(vararg_class, cir::TypeRef{}, arg_ref, args,
                                  site_params, inst.loc)) {
                return;
            }
        } else {
            error("call argument count does not match callee type", inst.loc);
            return;
        }
    }

    air::SigId call_sig = sig_info.sig;
    bool unprototyped_extras =
        !sig_info.has_prototype && source_args != sig_info.param_classes.size();
    const air::SigData& declared = mod_->types().signature(sig_info.sig);

    bool tail_byval = false;
    if (options_.target && (options_.target->arch == TargetArch::X86_64 ||
                            options_.target->arch == TargetArch::X86)) {
        for (size_t i = declared.params.size(); i < site_params.size(); ++i) {
            if (site_params[i].role == air::ParamRole::StackByval ||
                site_params[i].coerce_group > 1) {
                tail_byval = true;
                break;
            }
        }
    }
    if (unprototyped_extras || tail_byval) {
        if (unprototyped_extras &&
            ret_cls.pass != abi::AggregatePass::UseSourceType) {
            error("not supported by the air backend yet: unprototyped calls "
                  "returning aggregates",
                  inst.loc);
            return;
        }

        air::SigData site;
        site.ret_class = declared.ret_class;
        site.ret_type = declared.ret_type;
        site.ret_count = declared.ret_count;
        site.ret_sse_mask = declared.ret_sse_mask;
        site.params = site_params;
        if (tail_byval) {
            site.is_variadic = true;
            site.fixed_param_count = declared.fixed_param_count;
        } else {
            site.fixed_param_count = static_cast<uint32_t>(site.params.size());
        }
        call_sig = mod_->types().get_signature(std::move(site));
        if (direct_callee.is_valid()) {
            indirect_callee = b.func_addr(direct_callee);
            direct_callee = air::FuncId{};
        }
    }

    bool pair_return = (ret_cls.pass == abi::AggregatePass::CoerceIntSlots ||
                        ret_cls.pass == abi::AggregatePass::CoerceClassedSlots) &&
                       ret_cls.int_slot_count > 1;
    bool hfa_return = ret_cls.pass == abi::AggregatePass::CoerceHfa &&
                      ret_cls.hfa_count > 1;
    if (pair_return) {
        result_buffer = aggregate_result_buffer(
            uint64_t{ret_cls.slot_bytes} * ret_cls.int_slot_count,
            ret_cls.slot_bytes);
        args.push_back(result_buffer);
    } else if (hfa_return) {
        std::optional<air::TypeId> element =
            hfa_element_type(ret_cls.hfa_element, inst.loc);
        if (!element) {
            return;
        }
        uint64_t element_size = hfa_element_size(*element);
        result_buffer = aggregate_result_buffer(
            ret_cls.hfa_count * element_size,
            static_cast<uint32_t>(element_size));
        args.push_back(result_buffer);
    }

    const auto* call_payload =
        std::get_if<cir::CallPayload>(&file_.payload(inst.payload_index));
    if (call_payload && call_payload->must_tail &&
        indirect_callee.is_valid() &&
        mod_->types().signature(call_sig).ret_class == air::RetClass::Void &&
        mod_->target().arch == TargetArch::AARCH64) {

        air::Builder& b = *builder_;
        b.tail_call_indirect(call_sig, indirect_callee, args);
        b.set_insertion_point(b.create_block());
        return;
    }
    air::ValueId result = direct_callee.is_valid()
        ? emit_call_or_invoke(direct_callee, args, sig_info.may_throw, inst.loc)
        : emit_call_indirect_or_invoke(call_sig, indirect_callee, args,
                                       sig_info.may_throw, inst.loc);

    switch (ret_cls.pass) {
        case abi::AggregatePass::UseSourceType:
            if (result.is_valid()) {
                remember(inst_id, cast_value(result, sig_info.return_type.type,
                                             inst.result_type, inst.loc));
            }
            return;
        case abi::AggregatePass::Ignore:

            remember(inst_id, aggregate_result_buffer(
                                  ret_size_align ? ret_size_align->size_bytes : 1,
                                  ret_size_align
                                      ? static_cast<uint32_t>(
                                            ret_size_align->alignment_bytes)
                                      : 1));
            return;
        case abi::AggregatePass::CoerceIntSlots:
        case abi::AggregatePass::CoerceClassedSlots:
            if (ret_cls.int_slot_count <= 1) {
                result_buffer = aggregate_result_buffer(ret_cls.slot_bytes,
                                                        ret_cls.slot_bytes);
                b.store(result, result_buffer, ret_cls.slot_bytes);
            }
            remember(inst_id, result_buffer);
            return;
        case abi::AggregatePass::CoerceHfa:
            if (ret_cls.hfa_count <= 1) {
                std::optional<air::TypeId> element =
                    hfa_element_type(ret_cls.hfa_element, inst.loc);
                if (!element) {
                    return;
                }
                uint64_t element_size = hfa_element_size(*element);
                result_buffer = aggregate_result_buffer(
                    element_size, static_cast<uint32_t>(element_size));
                b.store(result, result_buffer,
                        static_cast<uint32_t>(element_size));
            }
            remember(inst_id, result_buffer);
            return;
        case abi::AggregatePass::Indirect:
        case abi::AggregatePass::MemoryByval:
            remember(inst_id, result_buffer);
            return;
    }
}

void Lowerer::lower_construct_in_place(const cir::Inst& inst,
                                       const std::vector<cir::Operand>& operands) {
    if (operands.size() < 2) {
        error("construct_in_place expects a place and a constructor", inst.loc);
        return;
    }
    air::ValueId place = value_for(value_operand_at(operands, 0), inst.loc);
    cir::EntityId constructor = entity_operand_at(operands, 1);
    if (!place.is_valid() || !file_.valid(constructor)) {
        error("construct_in_place has invalid operands", inst.loc);
        return;
    }
    if (file_.entity(constructor).decl_flags.is_consteval) {
        error("call to consteval constructor is not a constant expression",
              inst.loc);
        return;
    }
    air::FuncId callee = get_or_declare_function(constructor);
    if (!callee.is_valid()) {
        return;
    }
    SignatureInfo sig_info =
        signature_for_function_type(file_.entity(constructor).type, inst.loc);
    if (!sig_info.ok) {
        return;
    }

    std::vector<air::ValueId> args;
    std::vector<air::SigParam> site_params;
    args.reserve(operands.size() - 1);
    args.push_back(place);
    site_params.push_back({air::types::PTR, air::ParamRole::Normal});
    for (size_t i = 2; i < operands.size(); ++i) {
        cir::ValueRef arg_ref = value_operand_at(operands, i);
        size_t param_index = i - 1;
        if (param_index >= sig_info.param_classes.size() &&
            !sig_info.is_variadic) {
            error("constructor call arity does not match its signature", inst.loc);
            return;
        }
        abi::AggregateClass argument_class;
        cir::TypeRef parameter_type;
        if (param_index < sig_info.param_classes.size()) {
            argument_class = sig_info.param_classes[param_index];
            parameter_type = sig_info.param_types[param_index];
        } else {
            cir::TypeId argument_type = file_.valid(arg_ref.inst)
                ? file_.inst(arg_ref.inst).result_type
                : cir::TypeId{};
            argument_class = abi::classify_vararg_native(
                file_, file_.type_ref(argument_type), options_.target.get());
        }
        if (!marshal_argument(argument_class, parameter_type,
                              arg_ref, args, site_params, inst.loc)) {
            return;
        }
    }
    emit_call_or_invoke(callee, args, sig_info.may_throw, inst.loc);
}

void Lowerer::lower_destroy(const cir::Inst& inst,
                            const std::vector<cir::Operand>& operands) {
    if (operands.empty()) {
        error("destroy expects a place operand", inst.loc);
        return;
    }
    cir::EntityId destructor = entity_operand_at(operands, 1);
    if (!file_.valid(destructor)) {

        return;
    }
    air::ValueId place = value_for(value_operand_at(operands, 0), inst.loc);
    if (!place.is_valid()) {
        return;
    }
    air::FuncId callee = get_or_declare_function(destructor);
    if (!callee.is_valid()) {
        return;
    }
    air::ValueId args[] = {place};
    bool can_throw = function_type_may_throw(file_.entity(destructor).type);
    emit_call_or_invoke(callee, args, can_throw, inst.loc);
}

void Lowerer::lower_builtin_call(cir::InstId inst_id,
                                 const cir::Inst& inst,
                                 const cir::BuiltinCallPayload& payload,
                                 const std::vector<cir::ValueRef>& values) {
    air::Builder& b = *builder_;
    auto arg = [&](size_t index) -> air::ValueId {
        if (index >= values.size()) {
            error("builtin '" + payload.name + "' has too few operands", inst.loc);
            return air::ValueId{};
        }
        return value_for(values[index], inst.loc);
    };
    auto arg_type = [&](size_t index) -> cir::TypeId {
        return index < values.size() && file_.valid(values[index].inst)
            ? file_.inst(values[index].inst).result_type
            : cir::TypeId{};
    };

    switch (payload.kind) {
        case BuiltinKind::IS_CONSTANT_EVALUATED: {

            std::optional<air::TypeId> type = air_type(inst.result_type);
            remember(inst_id,
                     b.const_int(type.value_or(air::types::I8), 0));
            return;
        }
        case BuiltinKind::BIT_CAST: {
            air::ValueId source = arg(0);
            cir::TypeId source_type = arg_type(0);
            std::optional<cir::TypeSizeAlign> source_layout =
                cir::size_align_of_type(file_, source_type);
            std::optional<cir::TypeSizeAlign> target_layout =
                cir::size_align_of_type(file_, inst.result_type);
            if (!source.is_valid() || !source_layout || !target_layout ||
                source_layout->size_bytes != target_layout->size_bytes) {
                error("__builtin_bit_cast requires equally sized complete types",
                      inst.loc);
                return;
            }

            uint32_t source_align = static_cast<uint32_t>(
                std::max<size_t>(1, source_layout->alignment_bytes));
            uint32_t target_align = static_cast<uint32_t>(
                std::max<size_t>(1, target_layout->alignment_bytes));
            air::ValueId source_storage = source;
            if (!is_memory_only_type(source_type)) {
                source_storage = create_entry_stack_alloc(
                    std::max<uint64_t>(1, source_layout->size_bytes),
                    source_align);
                b.store(source, source_storage, source_align);
            }
            air::ValueId target_storage = create_entry_stack_alloc(
                std::max<uint64_t>(1, target_layout->size_bytes),
                target_align);
            b.memcpy_(target_storage,
                      source_storage,
                      b.const_usize(static_cast<int64_t>(
                          source_layout->size_bytes)));
            if (is_memory_only_type(inst.result_type)) {
                remember(inst_id, target_storage);
                return;
            }
            std::optional<air::TypeId> target_type = air_type(inst.result_type);
            if (!target_type || *target_type == air::types::VOID) {
                error("__builtin_bit_cast destination has no AIR value type",
                      inst.loc);
                return;
            }
            remember(inst_id,
                     b.load(*target_type, target_storage, target_align));
            return;
        }
        case BuiltinKind::EXPECT:
        case BuiltinKind::EXPECT_WITH_PROBABILITY: {

            air::ValueId value = arg(0);
            if (!value.is_valid()) {
                return;
            }
            remember(inst_id,
                     cast_value(value, arg_type(0), inst.result_type, inst.loc));
            return;
        }
        case BuiltinKind::LAUNDER: {
            air::ValueId pointer = arg(0);
            if (!pointer.is_valid()) {
                return;
            }
            remember(inst_id,
                     cast_value(pointer,
                                arg_type(0),
                                inst.result_type,
                                inst.loc));
            return;
        }
        case BuiltinKind::CONSTANT_P: {

            remember(inst_id, b.const_i32(0));
            return;
        }
        case BuiltinKind::UNREACHABLE: {
            b.unreachable_();

            air::BlockId continuation = b.create_block();
            b.set_insertion_point(continuation);
            return;
        }
        case BuiltinKind::TRAP:
            b.trap();
            return;
        case BuiltinKind::MEMCPY:
        case BuiltinKind::MEMMOVE: {
            air::ValueId dst = arg(0);
            air::ValueId src = arg(1);
            air::ValueId size = arg(2);
            if (!dst.is_valid() || !src.is_valid() || !size.is_valid()) {
                return;
            }
            size = int_resize(size, b.size_int_type(),
                              is_unsigned_domain(arg_type(2)), inst.loc);
            if (!size.is_valid()) {
                return;
            }
            if (payload.kind == BuiltinKind::MEMCPY) {
                b.memcpy_(dst, src, size);
            } else {
                b.memmove_(dst, src, size);
            }
            remember(inst_id, dst);
            return;
        }
        case BuiltinKind::MEMSET: {
            air::ValueId dst = arg(0);
            air::ValueId value = arg(1);
            air::ValueId size = arg(2);
            if (!dst.is_valid() || !value.is_valid() || !size.is_valid()) {
                return;
            }
            value = int_resize(value, air::types::I8, false, inst.loc);
            size = int_resize(size, b.size_int_type(),
                              is_unsigned_domain(arg_type(2)), inst.loc);
            if (!value.is_valid() || !size.is_valid()) {
                return;
            }
            b.memset_(dst, value, size);
            remember(inst_id, dst);
            return;
        }
        case BuiltinKind::CLZ:
        case BuiltinKind::CLZL:
        case BuiltinKind::CLZLL:
        case BuiltinKind::CTZ:
        case BuiltinKind::CTZL:
        case BuiltinKind::CTZLL:
        case BuiltinKind::POPCOUNT:
        case BuiltinKind::POPCOUNTL:
        case BuiltinKind::POPCOUNTLL: {
            air::ValueId value = arg(0);
            if (!value.is_valid()) {
                return;
            }
            if (!mod_->types().is_int(air_func_->value_type(value))) {
                error("bit builtin requires an integer operand", inst.loc);
                return;
            }
            air::ValueId lowered;
            switch (payload.kind) {
                case BuiltinKind::CLZ:
                case BuiltinKind::CLZL:
                case BuiltinKind::CLZLL:
                    lowered = b.clz(value);
                    break;
                case BuiltinKind::CTZ:
                case BuiltinKind::CTZL:
                case BuiltinKind::CTZLL:
                    lowered = b.ctz(value);
                    break;
                default:
                    lowered = b.popcnt(value);
                    break;
            }
            remember(inst_id,
                     cast_value(lowered, arg_type(0), inst.result_type, inst.loc));
            return;
        }
        case BuiltinKind::FFS:
        case BuiltinKind::FFSL:
        case BuiltinKind::FFSLL: {
            air::ValueId value = arg(0);
            if (!value.is_valid()) {
                return;
            }
            air::TypeId type = air_func_->value_type(value);
            if (!mod_->types().is_int(type)) {
                error("ffs builtin requires an integer operand", inst.loc);
                return;
            }
            air::ValueId one_based =
                b.iadd(b.ctz(value), b.const_int(type, 1));
            air::ValueId zero = b.const_int(type, 0);
            air::ValueId is_zero = b.icmp(air::IntCond::Eq, value, zero);
            air::ValueId selected = b.select(is_zero, zero, one_based);
            remember(inst_id,
                     cast_value(selected, arg_type(0), inst.result_type, inst.loc));
            return;
        }
        case BuiltinKind::BSWAP16:
        case BuiltinKind::BSWAP32:
        case BuiltinKind::BSWAP64: {
            air::ValueId value = arg(0);
            if (!value.is_valid()) {
                return;
            }
            uint16_t bits = payload.kind == BuiltinKind::BSWAP16
                ? 16
                : (payload.kind == BuiltinKind::BSWAP32 ? 32 : 64);
            air::TypeId swap_type = mod_->types().get_int(bits);
            value = int_resize(value, swap_type,
                               is_unsigned_domain(arg_type(0)), inst.loc);
            if (!value.is_valid()) {
                return;
            }
            remember(inst_id, cast_value(b.bswap(value), arg_type(0),
                                         inst.result_type, inst.loc));
            return;
        }
        case BuiltinKind::ABS:
        case BuiltinKind::LABS:
        case BuiltinKind::LLABS: {
            air::ValueId value = arg(0);
            if (!value.is_valid()) {
                return;
            }
            air::TypeId type = air_func_->value_type(value);
            if (!mod_->types().is_int(type)) {
                error("abs builtin requires an integer operand", inst.loc);
                return;
            }
            air::ValueId zero = b.const_int(type, 0);
            air::ValueId negated = b.isub(zero, value);
            air::ValueId is_negative =
                b.icmp(air::IntCond::Slt, value, zero);
            remember(inst_id,
                     cast_value(b.select(is_negative, negated, value),
                                arg_type(0), inst.result_type, inst.loc));
            return;
        }
        case BuiltinKind::FABS: case BuiltinKind::FABSF: case BuiltinKind::FABSL:
        case BuiltinKind::SQRT: case BuiltinKind::SQRTF: case BuiltinKind::SQRTL:
        case BuiltinKind::CBRT: case BuiltinKind::CBRTF: case BuiltinKind::CBRTL:
        case BuiltinKind::SIN: case BuiltinKind::SINF: case BuiltinKind::SINL:
        case BuiltinKind::COS: case BuiltinKind::COSF: case BuiltinKind::COSL:
        case BuiltinKind::EXP: case BuiltinKind::EXPF: case BuiltinKind::EXPL:
        case BuiltinKind::EXP2: case BuiltinKind::EXP2F: case BuiltinKind::EXP2L:
        case BuiltinKind::LOG: case BuiltinKind::LOGF: case BuiltinKind::LOGL:
        case BuiltinKind::LOG2: case BuiltinKind::LOG2F: case BuiltinKind::LOG2L:
        case BuiltinKind::LOG10: case BuiltinKind::LOG10F: case BuiltinKind::LOG10L:
        case BuiltinKind::FLOOR: case BuiltinKind::FLOORF: case BuiltinKind::FLOORL:
        case BuiltinKind::CEIL: case BuiltinKind::CEILF: case BuiltinKind::CEILL:
        case BuiltinKind::TRUNC: case BuiltinKind::TRUNCF: case BuiltinKind::TRUNCL:
        case BuiltinKind::RINT: case BuiltinKind::RINTF: case BuiltinKind::RINTL:
        case BuiltinKind::NEARBYINT: case BuiltinKind::NEARBYINTF:
        case BuiltinKind::NEARBYINTL:
        case BuiltinKind::ROUND: case BuiltinKind::ROUNDF:
        case BuiltinKind::ROUNDL: {

            air::ValueId value = arg(0);
            if (!value.is_valid()) {
                return;
            }
            air::TypeId type = air_func_->value_type(value);
            if (!mod_->types().is_float(type)) {
                error("float builtin requires a floating operand", inst.loc);
                return;
            }
            std::string name = builtin_runtime_name(payload.name);
            air::SigParam params[1] = {{type, air::ParamRole::Normal}};
            air::SigId sig = mod_->types().get_signature(
                air::RetClass::Scalar, type, 1, params);
            air::FuncId helper = declare_runtime_helper(name, sig);
            air::ValueId args[1] = {value};
            remember(inst_id, cast_value(b.call(helper, args), arg_type(0),
                                         inst.result_type, inst.loc));
            return;
        }
        case BuiltinKind::COPYSIGN:
        case BuiltinKind::COPYSIGNF:
        case BuiltinKind::COPYSIGNL: {

            air::ValueId magnitude = arg(0);
            air::ValueId sign = arg(1);
            if (!magnitude.is_valid() || !sign.is_valid()) {
                return;
            }
            air::TypeId type = air_func_->value_type(magnitude);
            if (!mod_->types().is_float(type) ||
                air_func_->value_type(sign) != type) {
                error("copysign builtin requires matching floating operands",
                      inst.loc);
                return;
            }
            air::SigParam params[2] = {
                {type, air::ParamRole::Normal},
                {type, air::ParamRole::Normal},
            };
            air::SigId sig = mod_->types().get_signature(
                air::RetClass::Scalar, type, 1, params);
            air::FuncId helper =
                declare_runtime_helper(builtin_runtime_name(payload.name),
                                       sig);
            air::ValueId args[2] = {magnitude, sign};
            remember(inst_id,
                     cast_value(b.call(helper, args),
                                arg_type(0),
                                inst.result_type,
                                inst.loc));
            return;
        }
        default:
            error("not supported by the air backend yet: builtin '" +
                      payload.name + "'",
                  inst.loc);
            return;
    }
}

void Lowerer::lower_terminator(const cir::Terminator& terminator) {
    air::Builder& b = *builder_;
    std::vector<cir::ValueRef> operands = file_.value_operands(terminator.operands);

    auto block_args_for = [&](cir::BlockId target, size_t first_arg,
                              std::vector<air::ValueId>& out) -> bool {
        if (!file_.valid(target)) {
            error("invalid branch target", terminator.loc);
            return false;
        }
        const cir::Block& target_block = file_.block(target);
        size_t arg_count = operands.size() > first_arg
            ? operands.size() - first_arg
            : 0;
        if (arg_count != target_block.parameters.size()) {
            error("branch target argument count does not match target parameters",
                  terminator.loc);
            return false;
        }
        out.clear();
        out.reserve(arg_count);
        for (size_t index = 0; index < arg_count; ++index) {
            air::ValueId incoming =
                value_for(operands[first_arg + index], terminator.loc);
            if (!incoming.is_valid()) {
                return false;
            }
            cir::TypeId source_type =
                file_.valid(operands[first_arg + index].inst)
                    ? file_.inst(operands[first_arg + index].inst).result_type
                    : cir::TypeId{};
            cir::TypeId param_type =
                file_.inst(target_block.parameters[index]).result_type;
            incoming = cast_value(incoming, source_type, param_type,
                                  terminator.loc);
            if (!incoming.is_valid()) {
                return false;
            }
            out.push_back(incoming);
        }
        return true;
    };
    auto air_block_for = [&](cir::BlockId target) -> air::BlockId {
        auto found = block_ids_.find(id_key(target));
        if (found == block_ids_.end()) {
            error("branch target block was not lowered", terminator.loc);
            return air::BlockId{};
        }
        return found->second;
    };

    switch (terminator.kind) {
        case cir::TerminatorKind::Return: {
            const abi::AggregateClass& ret_cls = current_sig_.ret_class;
            if (ret_cls.pass == abi::AggregatePass::UseSourceType) {
                const air::SigData& sig =
                    mod_->types().signature(air_func_->sig());
                if (sig.ret_class == air::RetClass::Void) {
                    b.ret();
                    return;
                }
                if (operands.empty()) {

                    b.ret(air_func_->undef(sig.ret_type));
                    return;
                }
                air::ValueId value = value_for(operands[0], terminator.loc);
                if (!value.is_valid()) {
                    return;
                }
                cir::TypeId source_type = file_.valid(operands[0].inst)
                    ? file_.inst(operands[0].inst).result_type
                    : cir::TypeId{};
                value = cast_value(value, source_type,
                                   current_sig_.return_type.type, terminator.loc);
                if (value.is_valid()) {
                    b.ret(value);
                }
                return;
            }
            if (ret_cls.pass == abi::AggregatePass::Ignore) {
                if (!operands.empty()) {
                    (void)value_for(operands[0], terminator.loc);
                }
                b.ret();
                return;
            }

            auto size_align =
                cir::size_align_of_type(file_, current_sig_.return_type.type);
            if (!size_align) {
                error("cannot return an incomplete aggregate by value",
                      terminator.loc);
                return;
            }
            air::ValueId source;
            if (operands.empty()) {

                source = create_entry_stack_alloc(
                    std::max<uint64_t>(1, size_align->size_bytes),
                    static_cast<uint32_t>(
                        std::max<size_t>(1, size_align->alignment_bytes)));
            } else {
                source = value_for(operands[0], terminator.loc);
                if (!source.is_valid()) {
                    return;
                }
            }
            switch (ret_cls.pass) {
                case abi::AggregatePass::Indirect:
                case abi::AggregatePass::MemoryByval:
                    if (!current_sret_.is_valid()) {
                        error("indirect return without an sret parameter",
                              terminator.loc);
                        return;
                    }
                    b.memcpy_(current_sret_, source,
                              b.const_usize(static_cast<int64_t>(
                                  size_align->size_bytes)));
                    b.ret();
                    return;
                case abi::AggregatePass::CoerceIntSlots:
                case abi::AggregatePass::CoerceClassedSlots: {

                    uint32_t slot_bytes = ret_cls.slot_bytes;
                    uint64_t padded =
                        uint64_t{slot_bytes} * ret_cls.int_slot_count;
                    air::ValueId staging =
                        create_entry_stack_alloc(padded, slot_bytes);
                    b.memcpy_(staging, source,
                              b.const_usize(static_cast<int64_t>(
                                  size_align->size_bytes)));
                    if (ret_cls.int_slot_count <= 1) {
                        bool sse = (ret_cls.sse_slot_mask & 1) != 0;
                        air::TypeId slot_type = sse ? air::types::F64
                            : slot_bytes == 4     ? air::types::I32
                                                  : air::types::I64;
                        b.ret(b.load(slot_type, staging, slot_bytes));
                    } else {
                        b.ret(staging);
                    }
                    return;
                }
                case abi::AggregatePass::CoerceHfa: {
                    std::optional<air::TypeId> element =
                        hfa_element_type(ret_cls.hfa_element, terminator.loc);
                    if (!element) {
                        return;
                    }
                    if (ret_cls.hfa_count <= 1) {
                        uint64_t element_size = hfa_element_size(*element);
                        b.ret(b.load(*element, source,
                                     static_cast<uint32_t>(element_size)));
                    } else {

                        b.ret(source);
                    }
                    return;
                }
                default:
                    return;
            }
        }
        case cir::TerminatorKind::Branch: {
            std::vector<air::ValueId> args;
            air::BlockId target = air_block_for(terminator.target);
            if (!target.is_valid() || !block_args_for(terminator.target, 0, args)) {
                return;
            }
            b.jump(target, args);
            return;
        }
        case cir::TerminatorKind::CondBranch: {
            if (operands.empty()) {
                error("conditional branch missing condition", terminator.loc);
                return;
            }
            air::ValueId condition =
                truth_value(value_for(operands[0], terminator.loc), terminator.loc);
            if (!condition.is_valid()) {
                return;
            }
            air::BlockId then_target = air_block_for(terminator.target);
            air::BlockId else_target = air_block_for(terminator.false_target);
            std::vector<air::ValueId> then_args;
            std::vector<air::ValueId> else_args;
            if (!then_target.is_valid() || !else_target.is_valid() ||
                !block_args_for(terminator.target, 1, then_args) ||
                !block_args_for(terminator.false_target, 1, else_args)) {
                return;
            }
            b.br_if(condition, then_target, then_args, else_target, else_args);
            return;
        }
        case cir::TerminatorKind::Switch: {
            if (operands.size() != 1) {
                error("switch terminator missing condition", terminator.loc);
                return;
            }
            air::ValueId condition = value_for(operands[0], terminator.loc);
            if (!condition.is_valid()) {
                return;
            }
            air::TypeId condition_type = air_func_->value_type(condition);
            if (!mod_->types().is_int(condition_type)) {
                error("switch condition must lower to an integer type",
                      terminator.loc);
                return;
            }
            const cir::InstPayload& payload = file_.payload(terminator.payload_index);
            const auto* switch_payload =
                std::get_if<cir::SwitchTerminatorPayload>(&payload);
            if (!switch_payload) {
                error("switch terminator payload is missing", terminator.loc);
                return;
            }
            air::BlockId default_target = air_block_for(terminator.target);
            if (!default_target.is_valid()) {
                return;
            }
            for (const cir::SwitchCaseRange& case_range : switch_payload->cases) {
                const cir::Block& case_block = file_.block(case_range.target);
                if (!case_block.parameters.empty()) {
                    error("switch targets with block parameters are not supported",
                          terminator.loc);
                    return;
                }
            }

            uint16_t width = mod_->types().int_width(condition_type);
            auto case_bits = [&](int64_t value) -> uint64_t {
                uint64_t bits = static_cast<uint64_t>(value);
                if (width < 64) {
                    bits &= (1ull << width) - 1;
                }
                return bits;
            };

            bool has_range = std::any_of(
                switch_payload->cases.begin(), switch_payload->cases.end(),
                [](const cir::SwitchCaseRange& case_range) {
                    return case_range.low != case_range.high;
                });
            if (!has_range) {
                std::vector<std::pair<uint64_t, air::BlockId>> cases;
                cases.reserve(switch_payload->cases.size());
                for (const cir::SwitchCaseRange& case_range : switch_payload->cases) {
                    air::BlockId target = air_block_for(case_range.target);
                    if (!target.is_valid()) {
                        return;
                    }
                    cases.push_back({case_bits(case_range.low), target});
                }
                b.switch_(condition, default_target, cases);
                return;
            }

            cir::IntegerTypeShape shape = cir::integer_shape_for_type(
                file_, switch_payload->condition_type.type);
            air::IntCond ge = shape.is_unsigned ? air::IntCond::Uge
                                                : air::IntCond::Sge;
            air::IntCond le = shape.is_unsigned ? air::IntCond::Ule
                                                : air::IntCond::Sle;
            size_t case_count = switch_payload->cases.size();
            for (size_t index = 0; index < case_count; ++index) {
                const cir::SwitchCaseRange& case_range = switch_payload->cases[index];
                air::BlockId target = air_block_for(case_range.target);
                if (!target.is_valid()) {
                    return;
                }
                air::ValueId matches;
                if (case_range.low == case_range.high) {
                    matches = b.icmp(air::IntCond::Eq, condition,
                                     b.const_int(condition_type,
                                                 case_bits(case_range.low)));
                } else {
                    air::ValueId above = b.icmp(
                        ge, condition,
                        b.const_int(condition_type, case_bits(case_range.low)));
                    air::ValueId below = b.icmp(
                        le, condition,
                        b.const_int(condition_type, case_bits(case_range.high)));
                    matches = b.iand(above, below);
                }
                if (index + 1 < case_count) {
                    air::BlockId next = b.create_block();
                    b.br_if(matches, target, next);
                    b.set_insertion_point(next);
                } else {
                    b.br_if(matches, target, default_target);
                }
            }
            if (case_count == 0) {
                b.jump(default_target);
            }
            return;
        }
        case cir::TerminatorKind::IndirectBranch: {
            if (operands.empty()) {
                error("indirect branch missing target", terminator.loc);
                return;
            }
            air::ValueId target = value_for(operands[0], terminator.loc);
            if (!target.is_valid()) {
                return;
            }

            std::vector<air::BlockId> plausible = label_target_blocks_;
            std::sort(plausible.begin(), plausible.end(),
                      [](air::BlockId a, air::BlockId c) {
                          return a.index < c.index;
                      });
            b.br_indirect(target, plausible);
            return;
        }
        case cir::TerminatorKind::AsmGoto: {
            const cir::InstPayload& term_payload =
                file_.payload(terminator.payload_index);
            const auto* asm_ref =
                std::get_if<cir::InlineAsmPayloadRef>(&term_payload);
            if (asm_ref == nullptr || !file_.valid(asm_ref->payload)) {
                error("asm goto terminator has no asm metadata",
                      terminator.loc);
                return;
            }
            const cir::InlineAsmPayload& asm_payload =
                file_.inline_asm_payload(asm_ref->payload);
            std::vector<cir::Operand> raw_operands =
                file_.operands(terminator.operands);
            std::vector<cir::ValueRef> values;
            values.reserve(raw_operands.size());
            for (size_t i = 0; i < raw_operands.size(); ++i) {
                values.push_back(value_operand_at(raw_operands, i));
            }

            air::AsmPayload air_payload;
            std::vector<air::ValueId> operands;
            if (!build_asm_payload(asm_payload, values, terminator.loc,
                                   air_payload, operands)) {
                return;
            }

            air::BlockId fallthrough = air_block_for(terminator.target);
            std::vector<air::BlockId> targets;
            targets.reserve(asm_payload.goto_targets.size());
            for (cir::BlockId target : asm_payload.goto_targets) {
                air::BlockId mapped = air_block_for(target);
                if (!mapped.is_valid()) {
                    error("asm goto label target is not reachable",
                          terminator.loc);
                    return;
                }
                targets.push_back(mapped);
            }
            if (!fallthrough.is_valid()) {
                error("asm goto fallthrough target is not reachable",
                      terminator.loc);
                return;
            }
            uint32_t payload_index =
                mod_->add_asm_payload(std::move(air_payload));
            b.asm_goto(payload_index, operands, fallthrough, targets);
            return;
        }
        case cir::TerminatorKind::Unreachable:
            b.unreachable_();
            return;
        case cir::TerminatorKind::Throw: {
            std::vector<cir::Operand> raw_operands =
                file_.operands(terminator.operands);
            air::ValueId exception =
                value_for(value_operand_at(raw_operands, 0), terminator.loc);
            cir::EntityId typeinfo = entity_operand_at(raw_operands, 1);
            air::GlobalId typeinfo_global = get_or_create_global(typeinfo);
            if (!exception.is_valid() || !typeinfo_global.is_valid()) {
                error("throw terminator has invalid operands", terminator.loc);
                return;
            }
            air::ValueId destructor;
            if (raw_operands.size() > 2) {
                cir::EntityId dtor = entity_operand_at(raw_operands, 2);
                if (file_.valid(dtor)) {
                    air::FuncId dtor_func = get_or_declare_function(dtor);
                    if (!dtor_func.is_valid()) {
                        return;
                    }
                    destructor = b.func_addr(dtor_func);
                }
            }

            if (current_unwind_target(terminator.loc).is_valid()) {
                if (!destructor.is_valid()) {
                    destructor = b.const_null();
                }
                const air::SigParam params[3] = {
                    {air::types::PTR, air::ParamRole::Normal},
                    {air::types::PTR, air::ParamRole::Normal},
                    {air::types::PTR, air::ParamRole::Normal},
                };
                air::SigId sig = mod_->types().get_signature(
                    air::RetClass::Void, air::TypeId{}, 0, params);
                const air::ValueId args[3] = {
                    exception, b.global_addr(typeinfo_global), destructor};
                if (invoke_eh_runtime("__cxa_throw", args, sig,
                                      terminator.loc)) {
                    b.unreachable_();
                    return;
                }
            }
            b.throw_(exception, b.global_addr(typeinfo_global), destructor);
            return;
        }
        case cir::TerminatorKind::Rethrow: {
            if (current_unwind_target(terminator.loc).is_valid()) {
                air::SigId sig = mod_->types().get_signature(
                    air::RetClass::Void, air::TypeId{}, 0, {});
                if (invoke_eh_runtime("__cxa_rethrow", {}, sig,
                                      terminator.loc)) {
                    b.unreachable_();
                    return;
                }
            }
            b.rethrow();
            return;
        }
        case cir::TerminatorKind::Resume:
            if (operands.size() != 2) {
                error("resume terminator must carry exception pointer and selector",
                      terminator.loc);
                return;
            }
            {
                air::ValueId exception = value_for(operands[0], terminator.loc);
                air::ValueId selector = value_for(operands[1], terminator.loc);
                if (exception.is_valid() && selector.is_valid()) {
                    b.resume(exception, selector);
                }
            }
            return;
        case cir::TerminatorKind::CoroSuspend:
        case cir::TerminatorKind::CoroEnd:
            error("pre-split coroutine CIR reached the air backend; the "
                  "coroutine split pass must run first",
                  terminator.loc);
            return;
        case cir::TerminatorKind::Invalid:
            error("invalid terminator reached lowering", terminator.loc);
            return;
    }
}

AirLoweringResult lower_cir_to_air(const cir::File& file, AirLoweringOptions options) {
    Lowerer lowerer(file, std::move(options));
    return lowerer.run();
}

} // namespace aburi::cir2air
