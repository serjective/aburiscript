#include "lowerer.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <utility>
#include <variant>

#include "../asm_constraints.h"

#include "../abi/aarch64_call_classify.h"
#include "../abi/call_classify.h"
#include "../cir/inst_schema.h"
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

cir::TypeRef type_operand_at(const std::vector<cir::Operand>& operands,
                             size_t index) {
    if (index < operands.size()) {
        if (const auto* type = std::get_if<cir::TypeRef>(&operands[index].data)) {
            return *type;
        }
    }
    return cir::TypeRef{};
}

uint64_t integer_from_bytes(const std::vector<uint8_t>& bytes) {
    uint64_t value = 0;
    for (size_t index = 0; index < bytes.size() && index < 8; ++index) {
        value = (value << 8) | bytes[index];
    }
    return value;
}

uint64_t all_ones_for_width(uint16_t width) {
    return width >= 64 ? ~0ull : ((1ull << width) - 1);
}

} // namespace

air::ValueId Lowerer::value_for(cir::ValueRef ref, SrcLoc loc) {
    auto found = inst_values_.find(id_key(ref.inst));
    if (found == inst_values_.end()) {
        error("missing lowered value for " + file_.format_inst(ref.inst), loc);
        return air::ValueId{};
    }
    return found->second;
}

air::ValueId Lowerer::storage_for_place(cir::InstId place_id, SrcLoc loc) {
    if (!place_id.valid() || !file_.valid(place_id)) {
        return {};
    }
    auto lowered = inst_values_.find(id_key(place_id));
    if (lowered != inst_values_.end()) {
        return lowered->second;
    }
    const cir::Inst& place = file_.inst(place_id);
    std::vector<cir::Operand> operands = file_.operands(place.operands);
    std::vector<cir::ValueRef> values = file_.value_operands(place.operands);
    switch (place.kind) {
        case cir::InstKind::LocalPlace:
        case cir::InstKind::GlobalPlace: {
            cir::EntityId entity = entity_operand_at(operands, 0);
            return entity.valid() ? storage_for_entity(entity, loc)
                                  : air::ValueId{};
        }
        case cir::InstKind::Deref:
        case cir::InstKind::AddrOf:
            return values.empty() ? air::ValueId{}
                                  : storage_for_place(values[0].inst, loc);
        case cir::InstKind::FieldAddr: {
            if (values.empty()) {
                return {};
            }
            air::ValueId base = storage_for_place(values[0].inst, loc);
            const cir::RecordFieldFact* field =
                file_.field_fact(entity_operand_at(operands, 1));
            return base.is_valid() && field
                ? builder_->ptr_add(base,
                                    static_cast<int64_t>(field->offset))
                : air::ValueId{};
        }
        case cir::InstKind::ArrayElementPlace: {
            if (values.size() != 2 || !file_.valid(values[1].inst)) {
                return {};
            }
            const cir::Inst& index_inst = file_.inst(values[1].inst);
            const auto* literal = index_inst.kind == cir::InstKind::IntegerLiteral
                ? std::get_if<cir::LiteralPayload>(
                      &file_.payload(index_inst.payload_index))
                : nullptr;
            const cir::IntegerValue* index_value = literal
                ? std::get_if<cir::IntegerValue>(&literal->value)
                : nullptr;
            std::optional<int64_t> index = index_value
                ? index_value->try_as_int64()
                : std::nullopt;
            std::optional<size_t> element_size = cir::size_of_type(
                file_, file_.place_object_type(place.result_type));
            air::ValueId base = storage_for_place(values[0].inst, loc);
            if (!base.is_valid() || !index.has_value() ||
                !element_size.has_value()) {
                return {};
            }
            return builder_->ptr_add(
                base, *index * static_cast<int64_t>(*element_size));
        }
        default:
            return {};
    }
}

air::ValueId Lowerer::storage_for_entity(cir::EntityId entity_id,
                                         SrcLoc loc) {
    if (!entity_id.valid() || !file_.valid(entity_id)) {
        error("invalid result-object entity", loc);
        return {};
    }
    auto found = local_places_.find(id_key(entity_id));
    if (found != local_places_.end()) {
        return found->second;
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if (entity.object_storage_alias.valid()) {
        air::ValueId aliased =
            storage_for_entity(entity.object_storage_alias, loc);
        if (aliased.is_valid()) {
            local_places_[id_key(entity_id)] = aliased;
        }
        return aliased;
    }
    if (entity.object_storage_alias_place.valid() &&
        file_.valid(entity.object_storage_alias_place)) {
        const cir::Inst& place =
            file_.inst(entity.object_storage_alias_place);
        if (place.kind == cir::InstKind::LocalPlace ||
            place.kind == cir::InstKind::GlobalPlace) {
            std::vector<cir::Operand> operands = file_.operands(place.operands);
            if (!operands.empty()) {
                if (const auto* target =
                        std::get_if<cir::EntityId>(&operands.front().data)) {
                    air::ValueId aliased = storage_for_entity(*target, loc);
                    if (aliased.is_valid()) {
                        local_places_[id_key(entity_id)] = aliased;
                    }
                    return aliased;
                }
            }
        }
        air::ValueId aliased =
            storage_for_place(entity.object_storage_alias_place, loc);

        return aliased;
    }
    if (entity.is_function_result_object) {
        if (!current_result_object_.is_valid()) {
            if (current_sret_.is_valid()) {
                current_result_object_ = current_sret_;
            } else if (auto size_align =
                           cir::size_align_of_type(file_, entity.type)) {
                current_result_object_ = create_entry_stack_alloc(
                    std::max<uint64_t>(1, size_align->size_bytes),
                    static_cast<uint32_t>(std::max<size_t>(
                        1, size_align->alignment_bytes)));
            }
        }
        if (current_result_object_.is_valid()) {
            local_places_[id_key(entity_id)] = current_result_object_;
        }
        return current_result_object_;
    }
    if (entity.storage_duration == cir::StorageDuration::Static ||
        entity.storage_duration == cir::StorageDuration::Thread) {
        air::GlobalId global = get_or_create_global(entity_id);
        return global.is_valid() ? builder_->global_addr(global)
                                 : air::ValueId{};
    }
    auto size_align = cir::size_align_of_type(file_, entity.type);
    if (!size_align) {
        error("cannot allocate result object with incomplete type", loc);
        return {};
    }
    size_t alignment = std::max<size_t>(
        {1, entity.attr_facts.requested_alignment,
         size_align->alignment_bytes});
    air::ValueId slot = create_entry_stack_alloc(
        std::max<uint64_t>(1, size_align->size_bytes),
        static_cast<uint32_t>(alignment));
    local_places_[id_key(entity_id)] = slot;
    return slot;
}

void Lowerer::remember(cir::InstId inst_id, air::ValueId value) {
    if (value.is_valid()) {
        inst_values_[id_key(inst_id)] = value;
    }
}

air::ValueId Lowerer::create_entry_stack_alloc(uint64_t size_bytes,
                                               uint32_t align_bytes) {
    air::BlockId entry = air_func_->entry_block();
    air::InstId first = air_func_->block(entry).first;
    air::Builder entry_builder(*mod_, *air_func_);
    if (first.is_valid()) {
        entry_builder.set_insertion_before(first);
    } else {
        entry_builder.set_insertion_point(entry);
    }
    return entry_builder.stack_alloc(size_bytes, align_bytes);
}

const cir::RecordFieldFact* Lowerer::field_fact_for_place(
    cir::InstId place_inst) const {
    if (!file_.valid(place_inst)) {
        return nullptr;
    }
    const cir::Inst& inst = file_.inst(place_inst);
    if (inst.kind != cir::InstKind::FieldAddr) {
        return nullptr;
    }
    std::vector<cir::Operand> operands = file_.operands(inst.operands);
    cir::EntityId field = entity_operand_at(operands, 1);
    return file_.valid(field) ? file_.field_fact(field) : nullptr;
}

air::ValueId Lowerer::truth_value(air::ValueId value, SrcLoc loc) {
    if (!value.is_valid()) {
        return value;
    }
    air::Builder& b = *builder_;
    air::TypeId type = air_func_->value_type(value);
    const air::TypeData& data = mod_->types().type(type);
    switch (data.kind) {
        case air::TypeKind::Int:
            return b.icmp(air::IntCond::Ne, value, b.const_int(type, 0));
        case air::TypeKind::Float:

            return b.fcmp(air::FloatCond::Une, value,
                          b.const_float_bits(type, 0));
        case air::TypeKind::Ptr:
            return b.icmp(air::IntCond::Ne, value,
                          air_func_->const_null(type));
        default:
            error("cannot convert value to condition", loc);
            return air::ValueId{};
    }
}

air::ValueId Lowerer::int_resize(air::ValueId value, air::TypeId to,
                                 bool source_unsigned, SrcLoc loc) {
    if (!value.is_valid()) {
        return value;
    }
    air::TypeId from = air_func_->value_type(value);
    if (from == to) {
        return value;
    }
    air::TypeTable& types = mod_->types();
    if (!types.is_int(from) || !types.is_int(to)) {
        error("internal integer resize on non-integer value", loc);
        return air::ValueId{};
    }
    uint16_t from_width = types.int_width(from);
    uint16_t to_width = types.int_width(to);
    if (to_width < from_width) {
        return builder_->trunc(to, value);
    }
    return source_unsigned ? builder_->zext(to, value)
                           : builder_->sext(to, value);
}

air::ValueId Lowerer::cast_value(air::ValueId value,
                                 cir::TypeId source_type,
                                 cir::TypeId target_type,
                                 SrcLoc loc) {
    if (!value.is_valid()) {
        return value;
    }
    auto int128_size = [&](cir::TypeId type_id) -> bool {
        if (!is_memory_only_type(type_id)) {
            return false;
        }
        cir::TypeId resolved = file_.resolved_type(type_id);
        if (!file_.valid(resolved)) {
            return false;
        }
        cir::TypeKind kind = file_.type(resolved).kind;
        return kind == cir::TypeKind::Builtin || kind == cir::TypeKind::BitInt;
    };
    std::optional<air::TypeId> target_air = air_type(target_type);
    if (!target_air) {
        if (is_memory_only_type(target_type)) {
            cir::TypeId target_resolved = file_.resolved_type(target_type);
            bool target_complex = file_.valid(target_resolved) &&
                file_.type(target_resolved).kind == cir::TypeKind::Complex;
            if (target_complex) {
                ComplexInfo to = complex_info(target_type, loc);
                if (!to.valid) {
                    return air::ValueId{};
                }
                air::Builder& b = *builder_;
                cir::TypeId source_resolved = file_.resolved_type(source_type);
                bool source_complex = file_.valid(source_resolved) &&
                    file_.type(source_resolved).kind == cir::TypeKind::Complex;
                air::ValueId re;
                air::ValueId im;
                if (source_complex) {
                    ComplexInfo from = complex_info(source_type, loc);
                    if (!from.valid) {
                        return air::ValueId{};
                    }
                    if (from.element == to.element) {
                        return value;
                    }
                    re = cast_value(b.load(from.element, value, from.align),
                                    from.element_cir, to.element_cir, loc);
                    im = cast_value(
                        b.load(from.element,
                               b.ptr_add(value,
                                         static_cast<int64_t>(from.element_size)),
                               from.align),
                        from.element_cir, to.element_cir, loc);
                } else {
                    re = cast_value(value, source_type, to.element_cir, loc);
                    im = to.is_float ? b.const_float_bits(to.element, 0)
                                     : b.const_int(to.element, 0);
                }
                if (!re.is_valid() || !im.is_valid()) {
                    return air::ValueId{};
                }
                air::ValueId buffer =
                    create_entry_stack_alloc(to.element_size * 2, to.align);
                b.store(re, buffer, to.align);
                b.store(im,
                        b.ptr_add(buffer, static_cast<int64_t>(to.element_size)),
                        to.align);
                return buffer;
            }
            if (int128_size(target_type) && !is_memory_only_type(source_type)) {

                air::TypeId from = air_func_->value_type(value);
                if (!mod_->types().is_int(from)) {
                    error("not supported by the air backend yet: "
                          "conversion to a 128-bit integer from this type",
                          loc);
                    return air::ValueId{};
                }
                air::Builder& b = *builder_;
                bool source_unsigned = is_unsigned_domain(source_type);
                air::ValueId low =
                    int_resize(value, air::types::I64, source_unsigned, loc);
                air::ValueId high = source_unsigned
                    ? b.const_i64(0)
                    : b.ashr(low, b.const_i64(63));
                air::ValueId buffer = create_entry_stack_alloc(16, 16);
                b.store(low, buffer, 8);
                b.store(high, b.ptr_add(buffer, 8), 8);
                return buffer;
            }

            return value;
        }
        error("not supported by the air backend yet: conversion target type",
              loc);
        return air::ValueId{};
    }
    if (*target_air == air::types::VOID) {

        return value;
    }
    if (is_memory_only_type(source_type)) {
        cir::TypeId source_resolved = file_.resolved_type(source_type);
        if (file_.valid(source_resolved) &&
            file_.type(source_resolved).kind == cir::TypeKind::Complex) {

            ComplexInfo from = complex_info(source_type, loc);
            if (!from.valid) {
                return air::ValueId{};
            }
            air::ValueId real = builder_->load(from.element, value, from.align);
            return cast_value(real, from.element_cir, target_type, loc);
        }
        if (int128_size(source_type) && mod_->types().is_int(*target_air)) {

            air::ValueId low = builder_->load(air::types::I64, value, 8);
            return int_resize(low, *target_air, true, loc);
        }
        error("not supported by the air backend yet: conversion source type",
              loc);
        return air::ValueId{};
    }
    if (*target_air == air::types::VOID) {
        return value;
    }
    if (is_nullptr_type(target_type)) {
        return air_func_->const_null(air_nullptr_carrier_type());
    }

    air::TypeTable& types = mod_->types();
    air::Builder& b = *builder_;
    air::TypeId from = air_func_->value_type(value);

    auto type_kind = [&](cir::TypeId type_id) -> std::optional<cir::TypeKind> {
        type_id = file_.resolved_type(type_id);
        if (!file_.valid(type_id)) {
            return std::nullopt;
        }
        return file_.type(type_id).kind;
    };
    if (is_nullptr_type(source_type)) {
        std::optional<cir::TypeKind> target_kind = type_kind(target_type);
        const air::TypeData& target_data = types.type(*target_air);
        if (target_kind &&
            (*target_kind == cir::TypeKind::Pointer ||
             *target_kind == cir::TypeKind::BlockPointer) &&
            target_data.kind == air::TypeKind::Ptr) {
            return air_func_->const_null(*target_air);
        }
        if (target_data.kind == air::TypeKind::Int) {
            return b.const_int(*target_air, 0);
        }
    }

    bool target_bool = file_.valid(target_type) &&
        file_.operator_value_domain(file_.type_ref(target_type)) ==
            cir::OperatorValueDomain::Bool;
    bool source_bool = file_.valid(source_type) &&
        file_.operator_value_domain(file_.type_ref(source_type)) ==
            cir::OperatorValueDomain::Bool;
    if (target_bool && !source_bool) {
        return truth_value(value, loc);
    }
    if (from == *target_air) {
        return value;
    }

    bool source_unsigned = is_unsigned_domain(source_type);
    bool target_unsigned = is_unsigned_domain(target_type);
    const air::TypeData& from_data = types.type(from);
    const air::TypeData& to_data = types.type(*target_air);

    if (from_data.kind == air::TypeKind::Int &&
        to_data.kind == air::TypeKind::Int) {
        return int_resize(value, *target_air, source_unsigned, loc);
    }
    if (from_data.kind == air::TypeKind::Int &&
        to_data.kind == air::TypeKind::Float) {
        return source_unsigned ? b.uitofp(*target_air, value)
                               : b.sitofp(*target_air, value);
    }
    if (from_data.kind == air::TypeKind::Float &&
        to_data.kind == air::TypeKind::Int) {
        return target_unsigned ? b.fptoui(*target_air, value)
                               : b.fptosi(*target_air, value);
    }
    if (from_data.kind == air::TypeKind::Float &&
        to_data.kind == air::TypeKind::Float) {
        auto float_bits = [](air::FloatKind kind) -> uint16_t {
            switch (kind) {
                case air::FloatKind::F32: return 32;
                case air::FloatKind::F64: return 64;
                case air::FloatKind::F128: return 128;
                case air::FloatKind::F80: return 80;
            }
            return 64;
        };
        uint16_t from_bits = float_bits(from_data.float_kind);
        uint16_t to_bits = float_bits(to_data.float_kind);
        return to_bits < from_bits ? b.fptrunc(*target_air, value)
                                   : b.fpext(*target_air, value);
    }
    if (from_data.kind == air::TypeKind::Ptr &&
        to_data.kind == air::TypeKind::Ptr) {
        return value;
    }
    if (from_data.kind == air::TypeKind::Ptr &&
        to_data.kind == air::TypeKind::Int) {
        return b.ptrtoint(*target_air, value);
    }
    if (from_data.kind == air::TypeKind::Int &&
        to_data.kind == air::TypeKind::Ptr) {
        return b.inttoptr(*target_air, value);
    }
    error("not supported by the air backend yet: this conversion", loc);
    return air::ValueId{};
}

void Lowerer::lower_function(cir::FunctionId function_id) {
    const cir::Function& function = file_.function(function_id);
    if (!file_.valid(function.entity)) {
        return;
    }
    const cir::Entity& entity = file_.entity(function.entity);

    size_t errors_at_entry = error_count();
    air::FuncId func = get_or_declare_function(function.entity);
    if (!func.is_valid()) {
        return;
    }

    if (entity.inline_definition_only &&
        (entity.symbol_policy.finalized
             ? entity.symbol_policy.emission
             : entity.linkage) != cir::LinkageKind::Internal) {
        return;
    }
    SignatureInfo sig_info = signature_for_function_type(function.type, function.loc);
    if (!sig_info.ok) {
        return;
    }
    current_sig_ = sig_info;

    air_func_ = &mod_->function(func);
    if (!air_func_->is_declaration()) {
        error("duplicate function body for " + air_func_->name(), function.loc);
        air_func_ = nullptr;
        return;
    }
    builder_ = std::make_unique<air::Builder>(*mod_, *air_func_);
    inst_values_.clear();
    local_places_.clear();
    block_ids_.clear();
    current_cir_block_ = {};

    const air::SigData& sig = mod_->types().signature(sig_info.sig);

    bool blocks_ok = true;
    for (size_t index = 0; index < function.blocks.size(); ++index) {
        cir::BlockId block_id = function.blocks[index];
        const cir::Block& block = file_.block(block_id);
        std::vector<air::TypeId> param_types;
        if (index == 0) {
            bool entry_params_match =
                block.parameters.size() == function.parameters.size();
            for (size_t p = 0; entry_params_match && p < block.parameters.size(); ++p) {
                entry_params_match =
                    block.parameters[p] == function.parameters[p].value.inst;
            }
            if (!entry_params_match) {
                error("entry block parameters do not mirror the function parameters",
                      function.loc);
                blocks_ok = false;
                break;
            }
            for (const air::SigParam& param : sig.params) {
                param_types.push_back(param.type);
            }
        } else {
            for (cir::InstId param_id : block.parameters) {
                std::optional<air::TypeId> type =
                    air_type(file_.inst(param_id).result_type);
                if (!type || *type == air::types::VOID) {
                    error("not supported by the air backend yet: block parameter type",
                          file_.inst(param_id).loc);
                    blocks_ok = false;
                    break;
                }
                param_types.push_back(*type);
            }
            if (!blocks_ok) {
                break;
            }
        }
        air::BlockId air_block = air_func_->create_block(param_types);
        block_ids_[id_key(block_id)] = air_block;
        if (index != 0) {
            std::span<const air::ValueId> params = air_func_->block_params(air_block);
            for (size_t p = 0; p < block.parameters.size(); ++p) {
                inst_values_[id_key(block.parameters[p])] = params[p];
            }
        }
    }
    if (!blocks_ok || function.blocks.empty()) {
        builder_.reset();
        air_func_ = nullptr;
        return;
    }

    label_target_blocks_.clear();
    for (cir::BlockId block_id : function.blocks) {
        for (cir::InstId label_inst : file_.block(block_id).instructions) {
            const cir::Inst& candidate = file_.inst(label_inst);
            if (candidate.kind != cir::InstKind::LabelAddress) {
                continue;
            }
            const auto* label = std::get_if<cir::LabelAddressPayload>(
                &file_.payload(candidate.payload_index));
            if (!label || !file_.valid(label->target)) {
                continue;
            }
            auto found = block_ids_.find(id_key(label->target));
            if (found == block_ids_.end()) {
                continue;
            }
            if (std::find(label_target_blocks_.begin(),
                          label_target_blocks_.end(),
                          found->second) == label_target_blocks_.end()) {
                label_target_blocks_.push_back(found->second);
            }
        }
    }

    for (cir::EntityId entity_id : file_.entity_ids()) {
        const cir::Entity& entity = file_.entity(entity_id);
        if (entity.kind != cir::EntityKind::Variable) {
            continue;
        }
        for (const cir::StaticInitializerRelocation& reloc :
             entity.static_initializer_relocations) {

            for (cir::BlockId target : {reloc.block, reloc.subtract_block}) {
                if (!target.valid()) {
                    continue;
                }
                auto found = block_ids_.find(id_key(target));
                if (found == block_ids_.end()) {
                    continue;
                }
                if (std::find(label_target_blocks_.begin(),
                              label_target_blocks_.end(),
                              found->second) == label_target_blocks_.end()) {
                    label_target_blocks_.push_back(found->second);
                }
            }
        }
    }

    std::span<const air::ValueId> entry_params =
        air_func_->block_params(air_func_->entry_block());
    size_t air_index = 0;
    current_sret_ = air::ValueId{};
    current_result_object_ = air::ValueId{};
    if (sig.ret_class == air::RetClass::IndirectSret) {
        if (entry_params.empty()) {
            error("indirect return without an sret parameter", function.loc);
            builder_.reset();
            air_func_ = nullptr;
            return;
        }
        current_sret_ = entry_params[air_index++];
    }
    bool params_ok =
        current_sig_.param_classes.size() == function.parameters.size();
    if (params_ok) {
        builder_->set_insertion_point(
            block_ids_[id_key(function.blocks.front())]);
        builder_->set_loc(function.loc);
    }
    for (size_t index = 0; params_ok && index < function.parameters.size();
         ++index) {
        const abi::AggregateClass& cls = current_sig_.param_classes[index];
        cir::InstId param_inst = function.parameters[index].value.inst;
        air::Builder& b = *builder_;
        switch (cls.pass) {
            case abi::AggregatePass::UseSourceType:
            case abi::AggregatePass::Indirect:
            case abi::AggregatePass::MemoryByval:

                if (air_index >= entry_params.size()) {
                    params_ok = false;
                    break;
                }
                inst_values_[id_key(param_inst)] = entry_params[air_index++];
                if (cls.pass == abi::AggregatePass::Indirect) {
                    cir::TypeId parameter_type = file_.resolved_type(
                        file_.entity(function.parameters[index].entity).type);
                    const cir::RecordFacts* record =
                        file_.record_facts_for_type(parameter_type);
                    if (record && record->is_non_trivial_for_calls) {
                        local_places_[id_key(
                            function.parameters[index].entity)] =
                            inst_values_[id_key(param_inst)];
                    }
                }
                break;
            case abi::AggregatePass::Ignore: {
                auto size_align = cir::size_align_of_type(
                    file_, current_sig_.param_types[index].type);
                inst_values_[id_key(param_inst)] = create_entry_stack_alloc(
                    size_align ? std::max<uint64_t>(1, size_align->size_bytes) : 1,
                    size_align ? static_cast<uint32_t>(std::max<size_t>(
                                     1, size_align->alignment_bytes))
                               : 1);
                break;
            }
            case abi::AggregatePass::CoerceIntSlots:
            case abi::AggregatePass::CoerceClassedSlots: {
                if (air_index + cls.int_slot_count > entry_params.size()) {
                    params_ok = false;
                    break;
                }
                uint32_t slot_bytes = cls.slot_bytes;
                air::ValueId buffer = create_entry_stack_alloc(
                    uint64_t{slot_bytes} * cls.int_slot_count, slot_bytes);
                for (uint8_t slot = 0; slot < cls.int_slot_count; ++slot) {
                    air::ValueId slot_ptr = slot == 0
                        ? buffer
                        : b.ptr_add(buffer,
                                    static_cast<int64_t>(slot_bytes * slot));
                    b.store(entry_params[air_index++], slot_ptr, slot_bytes);
                }
                inst_values_[id_key(param_inst)] = buffer;
                break;
            }
            case abi::AggregatePass::CoerceHfa: {
                std::optional<air::TypeId> element =
                    hfa_element_type(cls.hfa_element, function.loc);
                if (!element ||
                    air_index + cls.hfa_count > entry_params.size()) {
                    params_ok = false;
                    break;
                }
                uint32_t element_size =
                    *element == air::types::F32 ? 4 : 8;
                air::ValueId buffer = create_entry_stack_alloc(
                    static_cast<uint64_t>(cls.hfa_count) * element_size,
                    element_size);
                for (uint8_t lane = 0; lane < cls.hfa_count; ++lane) {
                    air::ValueId lane_ptr = lane == 0
                        ? buffer
                        : b.ptr_add(buffer,
                                    static_cast<int64_t>(lane * element_size));
                    b.store(entry_params[air_index++], lane_ptr, element_size);
                }
                inst_values_[id_key(param_inst)] = buffer;
                break;
            }
        }
    }
    if (!params_ok || air_index != entry_params.size()) {
        error("parameter count mismatch lowering " + air_func_->name(),
              function.loc);
        builder_.reset();
        air_func_ = nullptr;
        return;
    }

    for (cir::BlockId block_id : function.blocks) {
        for (cir::InstId inst_id : file_.block(block_id).instructions) {
            const cir::Inst& inst = file_.inst(inst_id);
            if (inst.kind != cir::InstKind::EhAllocException) {
                continue;
            }
            cir::TypeId object_type = file_.place_object_type(inst.result_type);
            auto size_align = cir::size_align_of_type(file_, object_type);
            if (!size_align) {
                error("cannot size the exception object type", inst.loc);
                builder_.reset();
                air_func_ = nullptr;
                return;
            }
            builder_->set_insertion_point(block_ids_[id_key(block_id)]);
            builder_->set_loc(inst.loc);
            remember(inst_id,
                     builder_->eh_alloc_exception(size_align->size_bytes));
        }
    }

    for (cir::BlockId block_id : function.blocks) {
        const cir::Block& block = file_.block(block_id);
        current_cir_block_ = block_id;
        builder_->set_insertion_point(block_ids_[id_key(block_id)]);
        for (cir::InstId inst_id : block.instructions) {
            if (file_.inst(inst_id).kind == cir::InstKind::Param) {
                continue;
            }
            builder_->set_loc(file_.inst(inst_id).loc);
            lower_inst(inst_id);
            if (error_count() > errors_at_entry) {
                builder_.reset();
                air_func_ = nullptr;
                return;
            }
        }
        builder_->set_loc(block.terminator.loc);
        lower_terminator(block.terminator);
        if (error_count() > errors_at_entry) {
            builder_.reset();
            air_func_ = nullptr;
            return;
        }
    }

    builder_.reset();
    air_func_ = nullptr;
    current_sret_ = air::ValueId{};
    current_result_object_ = air::ValueId{};
    current_cir_block_ = {};
}

void Lowerer::lower_inst(cir::InstId inst_id) {
    const cir::Inst& inst = file_.inst(inst_id);
    const cir::InstPayload& payload = file_.payload(inst.payload_index);
    std::vector<cir::Operand> operands = file_.operands(inst.operands);
    std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
    air::Builder& b = *builder_;

    auto unsupported = [&](std::string_view what) {
        error("not supported by the air backend yet: " + std::string(what),
              inst.loc);
    };

    switch (inst.kind) {
        case cir::InstKind::ReflectValue:
            error("'std::meta::info' values exist only during constant "
                  "evaluation and cannot be lowered to runtime code",
                  inst.loc);
            return;
        case cir::InstKind::CoroBegin:
        case cir::InstKind::CoroFrameSize:
        case cir::InstKind::CoroFrameAlign:
        case cir::InstKind::CoroPromisePlace:
        case cir::InstKind::CoroSave:
        case cir::InstKind::CoroTransfer:
            error("pre-split coroutine CIR reached the air backend; the "
                  "coroutine split pass must run first",
                  inst.loc);
            return;
        case cir::InstKind::ObjCMessageSend:
        case cir::InstKind::ObjCIvarAddr:
        case cir::InstKind::ObjCSelectorLiteral:
        case cir::InstKind::ObjCStringLiteral:
        case cir::InstKind::ObjCArcOp:
            error("Objective-C CIR reached the air backend; the Objective-C "
                  "lowering pass must expand it first",
                  inst.loc);
            return;
        case cir::InstKind::IntegerLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* value = literal
                ? std::get_if<cir::IntegerValue>(&literal->value)
                : nullptr;
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (type && mod_->types().is_ptr(*type)) {
                uint64_t raw = value ? value->low_bits : 0;
                remember(inst_id,
                         raw == 0
                             ? air_func_->const_null(*type)
                             : b.inttoptr(*type, b.const_i64(raw)));
                return;
            }
            if (!type || !mod_->types().is_int(*type)) {

                auto size_align = cir::size_align_of_type(file_, inst.result_type);
                if (is_memory_only_type(inst.result_type) && size_align &&
                    size_align->size_bytes == 16) {
                    uint64_t low = value ? value->low_bits : 0;
                    uint64_t high = value ? value->high_bits : 0;
                    air::ValueId buffer = create_entry_stack_alloc(16, 16);
                    if (file_.target_info().endianness ==
                        EndiannessKind::Big) {
                        b.store(b.const_i64(high), buffer, 8);
                        b.store(b.const_i64(low), b.ptr_add(buffer, 8), 8);
                    } else {
                        b.store(b.const_i64(low), buffer, 8);
                        b.store(b.const_i64(high), b.ptr_add(buffer, 8), 8);
                    }
                    remember(inst_id, buffer);
                    return;
                }
                unsupported("integer literal type");
                return;
            }
            uint64_t low = value ? value->low_bits : 0;
            uint64_t high = value ? value->high_bits : 0;
            remember(inst_id,
                     b.const_int(*type, low, high));
            return;
        }
        case cir::InstKind::BooleanLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* value = literal ? std::get_if<bool>(&literal->value) : nullptr;
            remember(inst_id, b.const_bool(value && *value));
            return;
        }
        case cir::InstKind::NullptrLiteral: {
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (!type) {
                unsupported("nullptr literal type");
                return;
            }
            const air::TypeData& type_data = mod_->types().type(*type);
            if (type_data.kind == air::TypeKind::Ptr) {
                remember(inst_id, air_func_->const_null(*type));
                return;
            }
            if (type_data.kind == air::TypeKind::Int) {
                remember(inst_id, b.const_int(*type, 0));
                return;
            }
            unsupported("nullptr literal type");
            return;
        }
        case cir::InstKind::FloatingLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* value =
                literal ? std::get_if<cir::FloatingValue>(&literal->value)
                        : nullptr;
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (!type || !mod_->types().is_float(*type)) {
                unsupported("floating literal type");
                return;
            }
            if (!value || !value->canonical()) {
                unsupported("floating literal payload");
                return;
            }
            remember(inst_id,
                     air_func_->const_float_bits(
                         *type, value->low_bits, value->high_bits));
            return;
        }
        case cir::InstKind::CharacterLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* bytes =
                literal ? std::get_if<cir::LiteralByteArray>(&literal->value) : nullptr;
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (!type || !mod_->types().is_int(*type)) {
                unsupported("character literal type");
                return;
            }
            remember(inst_id,
                     b.const_int(*type, bytes ? integer_from_bytes(*bytes) : 0));
            return;
        }
        case cir::InstKind::StringLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* bytes =
                literal ? std::get_if<cir::LiteralByteArray>(&literal->value) : nullptr;
            if (!bytes) {
                unsupported("string literal without byte payload");
                return;
            }

            cir::TypeId object_type = file_.place_object_type(inst.result_type);
            uint64_t element_size = 1;
            uint64_t object_size = bytes->size() + 1;
            cir::TypeId resolved = file_.resolved_type(object_type);
            if (file_.valid(resolved) &&
                file_.type(resolved).kind == cir::TypeKind::Array) {
                const auto& array = std::get<cir::ArrayTypePayload>(
                    file_.type_payload(resolved));
                if (auto elem = cir::size_align_of_type(file_, array.element_type.type)) {
                    element_size = elem->size_bytes;
                }
                if (auto whole = cir::size_align_of_type(file_, resolved)) {
                    object_size = whole->size_bytes;
                }
            }
            if (bytes->size() > object_size) {
                unsupported("string literal larger than its object type");
                return;
            }
            std::vector<uint8_t> image(*bytes);
            image.resize(object_size, 0);
            air::GlobalId global =
                intern_string_literal(image, element_size, inst.loc);
            remember(inst_id, b.global_addr(global));
            return;
        }
        case cir::InstKind::LocalPlace: {
            cir::EntityId entity_id = entity_operand_at(operands, 0);
            remember(inst_id, storage_for_entity(entity_id, inst.loc));
            return;
        }
        case cir::InstKind::GlobalPlace: {
            air::GlobalId global = get_or_create_global(entity_operand_at(operands, 0));
            if (!global.is_valid()) {
                return;
            }
            remember(inst_id, b.global_addr(global));
            return;
        }
        case cir::InstKind::FunctionToPointer: {
            air::FuncId callee = get_or_declare_function(entity_operand_at(operands, 0));
            if (!callee.is_valid()) {
                return;
            }
            remember(inst_id, b.func_addr(callee));
            return;
        }
        case cir::InstKind::MemberPointerValue:
            unsupported("member pointer values");
            return;
        case cir::InstKind::Load:
        case cir::InstKind::LValueToRValue: {
            if (file_.valid(values[0].inst) &&
                file_.inst(values[0].inst).kind == cir::InstKind::VectorElementPlace) {
                unsupported("vector element access");
                return;
            }
            if (const cir::RecordFieldFact* field = field_fact_for_place(values[0].inst);
                field && field->is_bitfield) {
                remember(inst_id, lower_bitfield_load(values[0].inst, *field,
                                                      inst.result_type, inst.loc));
                return;
            }
            air::ValueId place = value_for(values[0], inst.loc);
            if (!place.is_valid()) {
                return;
            }
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (!type || *type == air::types::VOID) {
                if (is_memory_only_type(inst.result_type)) {

                    remember(inst_id, place);
                    return;
                }
                unsupported("load of this type");
                return;
            }
            auto size_align = cir::size_align_of_type(file_, inst.result_type);
            uint32_t align = size_align
                ? static_cast<uint32_t>(std::max<size_t>(1, size_align->alignment_bytes))
                : 1;
            remember(inst_id, b.load(*type, place, align));
            return;
        }
        case cir::InstKind::Store: {
            if (inst.runtime_elided_object_operation) {
                return;
            }
            if (file_.valid(values[0].inst) &&
                file_.inst(values[0].inst).kind == cir::InstKind::VectorElementPlace) {
                unsupported("vector element access");
                return;
            }
            if (const cir::RecordFieldFact* field = field_fact_for_place(values[0].inst);
                field && field->is_bitfield) {
                air::ValueId value = value_for(values[1], inst.loc);
                if (value.is_valid()) {
                    cir::TypeId value_type = file_.valid(values[1].inst)
                        ? file_.inst(values[1].inst).result_type
                        : cir::TypeId{};
                    lower_bitfield_store(values[0].inst, value, value_type,
                                         *field, inst.loc);
                }
                return;
            }
            air::ValueId place = value_for(values[0], inst.loc);
            air::ValueId value = value_for(values[1], inst.loc);
            if (!place.is_valid() || !value.is_valid()) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            auto size_align = cir::size_align_of_type(file_, object_type);
            if (is_memory_only_type(object_type)) {
                if (!size_align) {
                    unsupported("aggregate store without layout");
                    return;
                }
                b.memcpy_(place, value, b.const_usize(static_cast<int64_t>(
                                            size_align->size_bytes)));
                return;
            }
            cir::TypeId source_type = file_.valid(values[1].inst)
                ? file_.inst(values[1].inst).result_type
                : cir::TypeId{};
            value = cast_value(value, source_type, object_type, inst.loc);
            if (!value.is_valid()) {
                return;
            }
            uint32_t align = size_align
                ? static_cast<uint32_t>(std::max<size_t>(1, size_align->alignment_bytes))
                : 1;
            b.store(value, place, align);
            return;
        }
        case cir::InstKind::ZeroObject: {
            air::ValueId place = value_for(values[0], inst.loc);
            if (!place.is_valid()) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            auto size_align = cir::size_align_of_type(file_, object_type);
            if (!size_align) {
                error("zero_object requires a complete object type", inst.loc);
                return;
            }
            b.memset_(place, b.const_int(air::types::I8, 0),
                      b.const_usize(static_cast<int64_t>(size_align->size_bytes)));
            return;
        }
        case cir::InstKind::AddrOf:
        case cir::InstKind::Deref:
            remember(inst_id, value_for(values[0], inst.loc));
            return;
        case cir::InstKind::FieldAddr: {
            air::ValueId base = value_for(values[0], inst.loc);
            if (!base.is_valid()) {
                return;
            }
            cir::EntityId field_entity = entity_operand_at(operands, 1);
            const cir::RecordFieldFact* field = file_.field_fact(field_entity);
            if (!field) {
                error("field_addr references a field without record layout facts",
                      inst.loc);
                return;
            }
            remember(inst_id,
                     b.ptr_add(base, static_cast<int64_t>(field->offset)));
            return;
        }
        case cir::InstKind::DataMemberPointerPlace:
            unsupported("data member pointer access");
            return;
        case cir::InstKind::MemberFunctionPointerCallee:
        case cir::InstKind::MemberFunctionPointerThis:
            unsupported("member function pointer calls");
            return;
        case cir::InstKind::ArrayElementPlace: {
            air::ValueId base = value_for(values[0], inst.loc);
            air::ValueId index = value_for(values[1], inst.loc);
            if (!base.is_valid() || !index.is_valid()) {
                return;
            }
            cir::TypeId element_type = file_.place_object_type(inst.result_type);
            auto size_align = cir::size_align_of_type(file_, element_type);
            if (!size_align) {
                unsupported("variable-length array element access");
                return;
            }
            cir::TypeId index_type = file_.valid(values[1].inst)
                ? file_.inst(values[1].inst).result_type
                : cir::TypeId{};

            air::TypeId offset_type = b.size_int_type();
            air::ValueId wide = int_resize(index, offset_type,
                                           is_unsigned_domain(index_type), inst.loc);
            if (!wide.is_valid()) {
                return;
            }
            air::ValueId offset = wide;
            if (size_align->size_bytes != 1) {
                offset = b.imul(wide, b.const_int(offset_type,
                                          size_align->size_bytes));
            }
            remember(inst_id, b.ptr_add(base, offset));
            return;
        }
        case cir::InstKind::SizeofType: {
            auto size_align =
                cir::size_align_of_type(file_, type_operand_at(operands, 0).type);
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (!type || !mod_->types().is_int(*type)) {
                unsupported("sizeof result type");
                return;
            }
            remember(inst_id,
                     b.const_int(*type,
                                 size_align ? static_cast<uint64_t>(
                                                  size_align->size_bytes)
                                            : 0));
            return;
        }
        case cir::InstKind::AlignofType: {
            auto size_align =
                cir::size_align_of_type(file_, type_operand_at(operands, 0).type);
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (!type || !mod_->types().is_int(*type)) {
                unsupported("alignof result type");
                return;
            }
            remember(inst_id,
                     b.const_int(*type,
                                 size_align ? static_cast<uint64_t>(
                                                  size_align->alignment_bytes)
                                            : 0));
            return;
        }
        case cir::InstKind::UnaryOp:
            if (const auto* descriptor = std::get_if<cir::UnaryOpDescriptor>(&payload)) {
                lower_unary(inst_id, inst, *descriptor, values);
            } else {
                error("unary instruction is missing a descriptor", inst.loc);
            }
            return;
        case cir::InstKind::BinaryOp:
            if (const auto* descriptor = std::get_if<cir::BinaryOpDescriptor>(&payload)) {
                lower_binary(inst_id, inst, *descriptor, values);
            } else {
                error("binary instruction is missing a descriptor", inst.loc);
            }
            return;
        case cir::InstKind::Cast: {
            cir::ValueRef source = value_operand_at(operands, 1);
            cir::TypeId source_type = file_.valid(source.inst)
                ? file_.inst(source.inst).result_type
                : cir::TypeId{};
            air::ValueId value = value_for(source, inst.loc);
            if (!value.is_valid()) {
                return;
            }
            remember(inst_id,
                     cast_value(value, source_type, inst.result_type, inst.loc));
            return;
        }
        case cir::InstKind::Call:
            if (inst.runtime_elided_object_operation) {
                return;
            }
            lower_call(inst_id, inst, operands);
            return;
        case cir::InstKind::ConstructInPlace:
            if (inst.runtime_elided_object_operation) {
                return;
            }
            lower_construct_in_place(inst, operands);
            return;
        case cir::InstKind::Destroy:
            lower_destroy(inst, operands);
            return;
        case cir::InstKind::BuiltinCall:
            if (const auto* builtin = std::get_if<cir::BuiltinCallPayload>(&payload)) {
                lower_builtin_call(inst_id, inst, *builtin, values);
            } else {
                error("builtin call instruction is missing builtin metadata",
                      inst.loc);
            }
            return;
        case cir::InstKind::Param:
            return;
        case cir::InstKind::LabelAddress: {
            const auto* label = std::get_if<cir::LabelAddressPayload>(&payload);
            if (!label || !file_.valid(label->target)) {
                error("label_address instruction is missing label metadata",
                      inst.loc);
                return;
            }
            auto found = block_ids_.find(id_key(label->target));
            if (found == block_ids_.end()) {
                error("label_address target block was not lowered", inst.loc);
                return;
            }
            remember(inst_id, b.label_addr(found->second));
            return;
        }
        case cir::InstKind::StackAlloc: {
            air::ValueId total = value_for(values[0], inst.loc);
            if (!total.is_valid()) {
                return;
            }
            cir::TypeId size_type = file_.valid(values[0].inst)
                ? file_.inst(values[0].inst).result_type
                : cir::TypeId{};
            air::ValueId wide = int_resize(total, b.size_int_type(),
                                           is_unsigned_domain(size_type), inst.loc);
            if (!wide.is_valid()) {
                return;
            }
            remember(inst_id, b.stack_alloc_dyn(wide, 16));
            return;
        }
        case cir::InstKind::StackSave:
            remember(inst_id, b.stack_save());
            return;
        case cir::InstKind::LifetimeStart:
        case cir::InstKind::LifetimeEnd:

            return;
        case cir::InstKind::StackRestore: {
            air::ValueId saved = value_for(values[0], inst.loc);
            if (saved.is_valid()) {
                b.stack_restore(saved);
            }
            return;
        }
        case cir::InstKind::AtomicLoad: {
            const auto* atomic = std::get_if<cir::AtomicPayload>(&payload);
            air::ValueId place = value_for(values[0], inst.loc);
            if (!atomic || !place.is_valid()) {
                return;
            }
            std::optional<air::TypeId> type = air_type(inst.result_type);
            if (!type ||
                (!mod_->types().is_int(*type) && *type != air::types::PTR)) {
                unsupported("atomic access of this type");
                return;
            }
            auto size_align = cir::size_align_of_type(file_, inst.result_type);
            uint32_t align = size_align
                ? static_cast<uint32_t>(std::max<size_t>(1, size_align->alignment_bytes))
                : 1;
            remember(inst_id, b.atomic_load(*type, place, align,
                                            atomic_order(atomic->order)));
            return;
        }
        case cir::InstKind::AtomicStore: {
            const auto* atomic = std::get_if<cir::AtomicPayload>(&payload);
            air::ValueId place = value_for(values[0], inst.loc);
            air::ValueId value = value_for(values[1], inst.loc);
            if (!atomic || !place.is_valid() || !value.is_valid()) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            std::optional<air::TypeId> type = air_type(object_type);
            if (!type ||
                (!mod_->types().is_int(*type) && *type != air::types::PTR)) {
                unsupported("atomic access of this type");
                return;
            }
            cir::TypeId source_type = file_.valid(values[1].inst)
                ? file_.inst(values[1].inst).result_type
                : cir::TypeId{};
            value = cast_value(value, source_type, object_type, inst.loc);
            if (!value.is_valid()) {
                return;
            }
            auto size_align = cir::size_align_of_type(file_, object_type);
            uint32_t align = size_align
                ? static_cast<uint32_t>(std::max<size_t>(1, size_align->alignment_bytes))
                : 1;
            b.atomic_store(value, place, align, atomic_order(atomic->order));
            return;
        }
        case cir::InstKind::AtomicRmw: {
            const auto* atomic = std::get_if<cir::AtomicPayload>(&payload);
            air::ValueId place = value_for(values[0], inst.loc);
            air::ValueId value = value_for(values[1], inst.loc);
            if (!atomic || !place.is_valid() || !value.is_valid()) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            std::optional<air::TypeId> type = air_type(object_type);
            if (!type || !mod_->types().is_int(*type)) {
                unsupported("atomic read-modify-write of this type");
                return;
            }
            cir::TypeId source_type = file_.valid(values[1].inst)
                ? file_.inst(values[1].inst).result_type
                : cir::TypeId{};
            value = cast_value(value, source_type, object_type, inst.loc);
            if (!value.is_valid()) {
                return;
            }
            air::RmwOp op = air::RmwOp::Xchg;
            switch (atomic->rmw_op) {
                case cir::AtomicRmwOp::Xchg: op = air::RmwOp::Xchg; break;
                case cir::AtomicRmwOp::Add: op = air::RmwOp::Add; break;
                case cir::AtomicRmwOp::Sub: op = air::RmwOp::Sub; break;
                case cir::AtomicRmwOp::And: op = air::RmwOp::And; break;
                case cir::AtomicRmwOp::Or: op = air::RmwOp::Or; break;
                case cir::AtomicRmwOp::Xor: op = air::RmwOp::Xor; break;
                case cir::AtomicRmwOp::Nand: op = air::RmwOp::Nand; break;
            }
            remember(inst_id,
                     b.atomic_rmw(op, place, value, atomic_order(atomic->order)));
            return;
        }
        case cir::InstKind::AtomicCmpXchg: {
            const auto* atomic = std::get_if<cir::AtomicPayload>(&payload);
            air::ValueId place = value_for(values[0], inst.loc);
            air::ValueId expected_place = value_for(values[1], inst.loc);
            air::ValueId desired = value_for(values[2], inst.loc);
            if (!atomic || !place.is_valid() || !expected_place.is_valid() ||
                !desired.is_valid()) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            std::optional<air::TypeId> type = air_type(object_type);
            if (!type || !mod_->types().is_int(*type)) {
                unsupported("atomic compare-exchange of this type");
                return;
            }
            cir::TypeId desired_type = file_.valid(values[2].inst)
                ? file_.inst(values[2].inst).result_type
                : cir::TypeId{};
            desired = cast_value(desired, desired_type, object_type, inst.loc);
            if (!desired.is_valid()) {
                return;
            }
            auto size_align = cir::size_align_of_type(file_, object_type);
            uint32_t align = size_align
                ? static_cast<uint32_t>(std::max<size_t>(1, size_align->alignment_bytes))
                : 1;
            air::ValueId expected = b.load(*type, expected_place, align);
            air::MemOrder failure = atomic_order(atomic->failure_order);
            if (failure == air::MemOrder::Release ||
                failure == air::MemOrder::AcqRel) {
                failure = air::MemOrder::SeqCst;
            }
            air::ValueId old_value = b.atomic_cas(place, expected, desired,
                                                  atomic_order(atomic->order),
                                                  failure);
            b.store(old_value, expected_place, align);
            remember(inst_id, b.icmp(air::IntCond::Eq, old_value, expected));
            return;
        }
        case cir::InstKind::AtomicFence: {
            const auto* atomic = std::get_if<cir::AtomicPayload>(&payload);
            if (atomic) {
                b.fence(atomic_order(atomic->order));
            }
            return;
        }
        case cir::InstKind::ComplexMake: {
            ComplexInfo info = complex_info(inst.result_type, inst.loc);
            if (!info.valid) {
                return;
            }
            air::ValueId real = value_for(values[0], inst.loc);
            air::ValueId imag = value_for(values[1], inst.loc);
            if (!real.is_valid() || !imag.is_valid()) {
                return;
            }
            real = cast_value(real,
                              file_.valid(values[0].inst)
                                  ? file_.inst(values[0].inst).result_type
                                  : cir::TypeId{},
                              info.element_cir, inst.loc);
            imag = cast_value(imag,
                              file_.valid(values[1].inst)
                                  ? file_.inst(values[1].inst).result_type
                                  : cir::TypeId{},
                              info.element_cir, inst.loc);
            if (!real.is_valid() || !imag.is_valid()) {
                return;
            }
            air::ValueId buffer =
                create_entry_stack_alloc(info.element_size * 2, info.align);
            b.store(real, buffer, info.align);
            b.store(imag,
                    b.ptr_add(buffer, static_cast<int64_t>(info.element_size)),
                    info.align);
            remember(inst_id, buffer);
            return;
        }
        case cir::InstKind::ComplexReal:
        case cir::InstKind::ComplexImag: {
            air::ValueId operand = value_for(values[0], inst.loc);
            if (!operand.is_valid()) {
                return;
            }
            cir::TypeId complex_type = file_.valid(values[0].inst)
                ? file_.inst(values[0].inst).result_type
                : cir::TypeId{};
            ComplexInfo info = complex_info(complex_type, inst.loc);
            if (!info.valid) {
                return;
            }
            air::ValueId source = inst.kind == cir::InstKind::ComplexImag
                ? b.ptr_add(operand, static_cast<int64_t>(info.element_size))
                : operand;
            remember(inst_id, b.load(info.element, source, info.align));
            return;
        }
        case cir::InstKind::ComplexRealPlace:
        case cir::InstKind::ComplexImagPlace: {
            air::ValueId place = value_for(values[0], inst.loc);
            if (!place.is_valid()) {
                return;
            }
            cir::TypeId base_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            ComplexInfo info = complex_info(base_type, inst.loc);
            if (!info.valid) {
                return;
            }
            remember(inst_id,
                     inst.kind == cir::InstKind::ComplexImagPlace
                         ? b.ptr_add(place, static_cast<int64_t>(info.element_size))
                         : place);
            return;
        }
        case cir::InstKind::VectorElementPlace:
        case cir::InstKind::VectorExtract:
            unsupported("vector types");
            return;
        case cir::InstKind::VaStart: {
            air::ValueId list = value_for(values[0], inst.loc);
            if (list.is_valid()) {
                b.va_start_(list);
            }
            return;
        }
        case cir::InstKind::VaArg:
            lower_va_arg(inst_id, inst, operands);
            return;
        case cir::InstKind::VaEnd:

            (void)value_for(values[0], inst.loc);
            return;
        case cir::InstKind::VaCopy: {
            air::ValueId dest = value_for(values[0], inst.loc);
            air::ValueId source = value_for(values[1], inst.loc);
            if (dest.is_valid() && source.is_valid()) {
                if (options_.target &&
                    options_.target->va_list_kind ==
                        VaListKind::AARCH64_VA_LIST) {

                    b.memcpy_(dest, source, b.const_i64(32));
                } else if (options_.target &&
                           options_.target->va_list_kind ==
                               VaListKind::X86_64_VA_LIST) {

                    b.memcpy_(dest, source, b.const_i64(24));
                } else {
                    b.store(b.load(air::types::PTR, source, 8), dest, 8);
                }
            }
            return;
        }
        case cir::InstKind::EhAllocException: {
            if (inst_values_.contains(id_key(inst_id))) {
                return;
            }
            cir::TypeId object_type = file_.place_object_type(inst.result_type);
            auto size_align = cir::size_align_of_type(file_, object_type);
            if (!size_align) {
                error("cannot size the exception object type", inst.loc);
                return;
            }
            remember(inst_id, b.eh_alloc_exception(size_align->size_bytes));
            return;
        }
        case cir::InstKind::EhLandingPad: {
            const auto* clauses =
                std::get_if<cir::EhLandingPadPayload>(&payload);
            if (!clauses) {
                error("landing pad instruction is missing clause metadata",
                      inst.loc);
                return;
            }
            air::EhLandingPadPayload out;
            out.is_cleanup = clauses->is_cleanup;
            out.has_catch_all = clauses->has_catch_all;
            out.clause_typeinfos.reserve(clauses->clause_typeinfos.size());
            for (cir::EntityId clause : clauses->clause_typeinfos) {
                air::GlobalId global = get_or_create_global(clause);
                if (!global.is_valid()) {
                    return;
                }
                out.clause_typeinfos.push_back(global);
            }
            uint32_t payload_index =
                mod_->add_eh_landing_pad_payload(std::move(out));
            remember(inst_id, b.eh_landing_pad(payload_index));
            return;
        }
        case cir::InstKind::EhSelector: {
            air::ValueId exception = value_for(values[0], inst.loc);
            if (exception.is_valid()) {
                remember(inst_id, b.eh_selector(exception));
            }
            return;
        }
        case cir::InstKind::EhTypeId: {
            cir::EntityId typeinfo = entity_operand_at(operands, 0);
            air::GlobalId global = get_or_create_global(typeinfo);
            if (!global.is_valid()) {
                return;
            }
            remember(inst_id, b.eh_typeid_for(b.global_addr(global)));
            return;
        }
        case cir::InstKind::CatchBegin: {
            air::ValueId exception = value_for(values[0], inst.loc);
            if (exception.is_valid()) {
                remember(inst_id, b.catch_begin(exception));
            }
            return;
        }
        case cir::InstKind::CatchEnd: {

            air::SigId sig = mod_->types().get_signature(
                air::RetClass::Void, air::TypeId{}, 0, {});
            if (invoke_eh_runtime("__cxa_end_catch", {}, sig, inst.loc)) {
                return;
            }
            b.catch_end();
            return;
        }
        case cir::InstKind::InlineAsm: {
            const auto* asm_ref = std::get_if<cir::InlineAsmPayloadRef>(&payload);
            if (!asm_ref || !file_.valid(asm_ref->payload)) {
                error("inline asm instruction is missing asm metadata", inst.loc);
                return;
            }
            lower_inline_asm(inst_id, inst,
                             file_.inline_asm_payload(asm_ref->payload), values);
            return;
        }
        case cir::InstKind::Invalid:
        case cir::InstKind::NameRef:
        case cir::InstKind::DependentCall:
        case cir::InstKind::DependentRegion:
        case cir::InstKind::Error:
            error("unsupported instruction reached lowering: " +
                      std::string(cir::inst_mnemonic(inst.kind)),
                  inst.loc);
            return;
    }
}

air::MemOrder Lowerer::atomic_order(cir::MemoryOrder order) const {
    switch (order) {
        case cir::MemoryOrder::Relaxed: return air::MemOrder::Relaxed;
        case cir::MemoryOrder::Consume:
        case cir::MemoryOrder::Acquire: return air::MemOrder::Acquire;
        case cir::MemoryOrder::Release: return air::MemOrder::Release;
        case cir::MemoryOrder::AcqRel: return air::MemOrder::AcqRel;
        case cir::MemoryOrder::SeqCst: return air::MemOrder::SeqCst;
    }
    return air::MemOrder::SeqCst;
}

air::ValueId Lowerer::lower_bitfield_load(cir::InstId place_inst,
                                          const cir::RecordFieldFact& field,
                                          cir::TypeId result_type,
                                          SrcLoc loc) {
    air::Builder& b = *builder_;
    cir::ValueRef place_ref;
    place_ref.inst = place_inst;
    air::ValueId place = value_for(place_ref, loc);
    if (!place.is_valid()) {
        return air::ValueId{};
    }
    uint32_t storage_bits = field.storage_size == 0 ? 32 : field.storage_size;
    if (storage_bits != 8 && storage_bits != 16 && storage_bits != 32 &&
        storage_bits != 64) {
        error("not supported by the air backend yet: bitfield storage width " +
                  std::to_string(storage_bits),
              loc);
        return air::ValueId{};
    }
    air::TypeId storage_type =
        mod_->types().get_int(static_cast<uint16_t>(storage_bits));
    uint32_t storage_align = storage_bits / 8;
    air::ValueId storage = b.load(storage_type, place, storage_align);
    if (field.bit_offset != 0) {
        storage = b.lshr(storage, b.const_int(storage_type, field.bit_offset));
    }
    uint32_t width = field.bit_width == 0
        ? storage_bits
        : cir::bitfield_value_width(file_, field);
    storage = b.iand(storage,
                     b.const_int(storage_type,
                                 all_ones_for_width(static_cast<uint16_t>(width))));
    bool is_signed = file_.operator_value_domain(field.type) ==
                     cir::OperatorValueDomain::SignedInteger;
    if (is_signed && width < storage_bits) {
        air::ValueId distance =
            b.const_int(storage_type, storage_bits - width);
        storage = b.ashr(b.shl(storage, distance), distance);
    }
    std::optional<air::TypeId> result_air = air_type(result_type);
    if (!result_air || !mod_->types().is_int(*result_air)) {
        error("not supported by the air backend yet: bitfield value type", loc);
        return air::ValueId{};
    }
    return int_resize(storage, *result_air, !is_signed, loc);
}

void Lowerer::lower_bitfield_store(cir::InstId place_inst,
                                   air::ValueId value,
                                   cir::TypeId value_type,
                                   const cir::RecordFieldFact& field,
                                   SrcLoc loc) {
    air::Builder& b = *builder_;
    cir::ValueRef place_ref;
    place_ref.inst = place_inst;
    air::ValueId place = value_for(place_ref, loc);
    if (!place.is_valid() || !value.is_valid()) {
        return;
    }
    uint32_t storage_bits = field.storage_size == 0 ? 32 : field.storage_size;
    if (storage_bits != 8 && storage_bits != 16 && storage_bits != 32 &&
        storage_bits != 64) {
        error("not supported by the air backend yet: bitfield storage width " +
                  std::to_string(storage_bits),
              loc);
        return;
    }
    uint32_t width = field.bit_width == 0
        ? storage_bits
        : cir::bitfield_value_width(file_, field);
    air::TypeId storage_type =
        mod_->types().get_int(static_cast<uint16_t>(storage_bits));
    uint32_t storage_align = storage_bits / 8;
    if (!mod_->types().is_int(air_func_->value_type(value))) {
        error("not supported by the air backend yet: bitfield value type", loc);
        return;
    }
    air::ValueId storage_value =
        int_resize(value, storage_type, is_unsigned_domain(value_type), loc);
    if (!storage_value.is_valid()) {
        return;
    }
    air::ValueId storage = b.load(storage_type, place, storage_align);
    uint64_t low_mask = all_ones_for_width(static_cast<uint16_t>(width));
    uint64_t shifted_mask = low_mask << field.bit_offset;
    uint64_t keep_mask = ~shifted_mask &
        all_ones_for_width(static_cast<uint16_t>(storage_bits));
    air::ValueId cleared = b.iand(storage, b.const_int(storage_type, keep_mask));
    air::ValueId clipped =
        b.iand(storage_value, b.const_int(storage_type, low_mask));
    if (field.bit_offset != 0) {
        clipped = b.shl(clipped, b.const_int(storage_type, field.bit_offset));
    }
    b.store(b.ior(cleared, clipped), place, storage_align);
}

Lowerer::ComplexInfo Lowerer::complex_info(cir::TypeId complex_type, SrcLoc loc) {
    ComplexInfo info;
    cir::TypeId resolved = file_.resolved_type(complex_type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Complex) {
        error("expected a complex type", loc);
        return info;
    }
    const auto& payload =
        std::get<cir::ComplexTypePayload>(file_.type_payload(resolved));
    std::optional<air::TypeId> element = air_type(payload.element_type.type);
    if (!element ||
        (!mod_->types().is_int(*element) && !mod_->types().is_float(*element))) {
        error("not supported by the air backend yet: complex element type", loc);
        return info;
    }
    auto elem_size = cir::size_align_of_type(file_, payload.element_type.type);
    if (!elem_size) {
        error("complex element type has no layout", loc);
        return info;
    }
    info.valid = true;
    info.element = *element;
    info.is_float = mod_->types().is_float(*element);
    info.element_size = elem_size->size_bytes;
    info.align = static_cast<uint32_t>(
        std::max<size_t>(1, elem_size->alignment_bytes));
    info.element_cir = payload.element_type.type;
    return info;
}

air::ValueId Lowerer::lower_complex_binary(const cir::Inst& inst,
                                           const cir::BinaryOpDescriptor& descriptor,
                                           air::ValueId lhs,
                                           cir::TypeId lhs_type,
                                           air::ValueId rhs,
                                           cir::TypeId rhs_type) {
    air::Builder& b = *builder_;
    ComplexInfo info = complex_info(descriptor.computation_type.type, inst.loc);
    if (!info.valid || !lhs.is_valid() || !rhs.is_valid()) {
        return air::ValueId{};
    }
    int64_t elem = static_cast<int64_t>(info.element_size);

    auto load_parts = [&](air::ValueId value, cir::TypeId type,
                          air::ValueId& re, air::ValueId& im) -> bool {
        cir::TypeId resolved = file_.resolved_type(type);
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Complex) {
            re = b.load(info.element, value, info.align);
            im = b.load(info.element, b.ptr_add(value, elem), info.align);
            return re.is_valid() && im.is_valid();
        }
        re = cast_value(value, type, info.element_cir, inst.loc);
        im = info.is_float ? b.const_float_bits(info.element, 0)
                           : b.const_int(info.element, 0);
        return re.is_valid();
    };
    air::ValueId lhs_re, lhs_im, rhs_re, rhs_im;
    if (!load_parts(lhs, lhs_type, lhs_re, lhs_im) ||
        !load_parts(rhs, rhs_type, rhs_re, rhs_im)) {
        return air::ValueId{};
    }

    auto add = [&](air::ValueId a, air::ValueId c) {
        return info.is_float ? b.fadd(a, c) : b.iadd(a, c);
    };
    auto sub = [&](air::ValueId a, air::ValueId c) {
        return info.is_float ? b.fsub(a, c) : b.isub(a, c);
    };
    auto mul = [&](air::ValueId a, air::ValueId c) {
        return info.is_float ? b.fmul(a, c) : b.imul(a, c);
    };
    auto divide = [&](air::ValueId a, air::ValueId c) {
        return info.is_float ? b.fdiv(a, c) : b.sdiv(a, c);
    };
    auto make = [&](air::ValueId re, air::ValueId im) -> air::ValueId {
        air::ValueId buffer =
            create_entry_stack_alloc(info.element_size * 2, info.align);
        b.store(re, buffer, info.align);
        b.store(im, b.ptr_add(buffer, elem), info.align);
        return buffer;
    };

    switch (descriptor.op) {
        case cir::BinaryOpKind::Add:
            return make(add(lhs_re, rhs_re), add(lhs_im, rhs_im));
        case cir::BinaryOpKind::Sub:
            return make(sub(lhs_re, rhs_re), sub(lhs_im, rhs_im));
        case cir::BinaryOpKind::Mul:
        case cir::BinaryOpKind::Div: {
            if (!info.is_float) {

                if (descriptor.op == cir::BinaryOpKind::Mul) {
                    return make(sub(mul(lhs_re, rhs_re), mul(lhs_im, rhs_im)),
                                add(mul(lhs_re, rhs_im), mul(lhs_im, rhs_re)));
                }
                air::ValueId denom =
                    add(mul(rhs_re, rhs_re), mul(rhs_im, rhs_im));
                return make(divide(add(mul(lhs_re, rhs_re), mul(lhs_im, rhs_im)),
                                   denom),
                            divide(sub(mul(lhs_im, rhs_re), mul(lhs_re, rhs_im)),
                                   denom));
            }
            if (info.element == air::types::F80) {
                error("not supported by the air backend yet: complex long "
                      "double multiply/divide", inst.loc);
                return air::ValueId{};
            }

            bool is_f32 = info.element == air::types::F32;
            const char* name = descriptor.op == cir::BinaryOpKind::Mul
                ? (is_f32 ? "__mulsc3" : "__muldc3")
                : (is_f32 ? "__divsc3" : "__divdc3");
            air::SigParam params[4] = {
                {info.element, air::ParamRole::Normal},
                {info.element, air::ParamRole::Normal},
                {info.element, air::ParamRole::Normal},
                {info.element, air::ParamRole::Normal},
            };
            const TargetInfo* target = options_.target.get();
            bool sysv_amd64 = target && target->arch == TargetArch::X86_64;
            air::ValueId buffer =
                create_entry_stack_alloc(info.element_size * 2, info.align);
            if (sysv_amd64 && is_f32) {
                air::SigId sig = mod_->types().get_signature(
                    air::RetClass::Scalar, air::types::F64, 1, params);
                air::FuncId helper = declare_runtime_helper(name, sig);
                air::ValueId args[4] = {lhs_re, lhs_im, rhs_re, rhs_im};
                air::ValueId packed = b.call(helper, args);
                b.store(packed, buffer, 8);
                return buffer;
            }
            air::SigId sig;
            if (target && target->arch == TargetArch::X86) {

                error("not supported by the air backend yet: complex "
                      "multiply/divide in 32-bit mode",
                      inst.loc);
                return buffer;
            }
            if (sysv_amd64) {
                air::SigData data;
                data.ret_class = air::RetClass::IntPair;
                data.ret_type = air::types::I64;
                data.ret_count = 2;
                data.ret_sse_mask = 0b11;
                data.params.assign(params, params + 4);
                sig = mod_->types().get_signature(std::move(data));
            } else {
                sig = mod_->types().get_signature(
                    air::RetClass::Hfa, info.element, 2, params);
            }
            air::FuncId helper = declare_runtime_helper(name, sig);
            air::ValueId args[5] = {lhs_re, lhs_im, rhs_re, rhs_im, buffer};
            b.call(helper, args);
            return buffer;
        }
        case cir::BinaryOpKind::Equal:
        case cir::BinaryOpKind::NotEqual: {
            bool equal = descriptor.op == cir::BinaryOpKind::Equal;
            air::ValueId re_cmp;
            air::ValueId im_cmp;
            if (info.is_float) {
                air::FloatCond cond =
                    equal ? air::FloatCond::Oeq : air::FloatCond::Une;
                re_cmp = b.fcmp(cond, lhs_re, rhs_re);
                im_cmp = b.fcmp(cond, lhs_im, rhs_im);
            } else {
                air::IntCond cond = equal ? air::IntCond::Eq : air::IntCond::Ne;
                re_cmp = b.icmp(cond, lhs_re, rhs_re);
                im_cmp = b.icmp(cond, lhs_im, rhs_im);
            }
            air::ValueId combined =
                equal ? b.iand(re_cmp, im_cmp) : b.ior(re_cmp, im_cmp);
            std::optional<air::TypeId> result_air = air_type(inst.result_type);
            if (result_air && mod_->types().is_int(*result_air)) {
                combined = int_resize(combined, *result_air, true, inst.loc);
            }
            return combined;
        }
        default:
            error("unsupported complex binary operator", inst.loc);
            return air::ValueId{};
    }
}

void Lowerer::lower_unary(cir::InstId inst_id,
                          const cir::Inst& inst,
                          const cir::UnaryOpDescriptor& descriptor,
                          const std::vector<cir::ValueRef>& values) {
    air::Builder& b = *builder_;
    air::ValueId operand = value_for(values[0], inst.loc);
    if (!operand.is_valid()) {
        return;
    }
    cir::TypeId operand_type = file_.valid(values[0].inst)
        ? file_.inst(values[0].inst).result_type
        : cir::TypeId{};
    cir::OperatorValueDomain domain =
        file_.operator_value_domain(descriptor.computation_type);

    switch (descriptor.op) {
        case cir::UnaryOpKind::Plus:
            remember(inst_id,
                     cast_value(operand, operand_type, inst.result_type, inst.loc));
            return;
        case cir::UnaryOpKind::Minus: {
            if (domain == cir::OperatorValueDomain::Complex) {
                ComplexInfo info =
                    complex_info(descriptor.computation_type.type, inst.loc);
                if (!info.valid) {
                    return;
                }
                int64_t elem = static_cast<int64_t>(info.element_size);
                air::ValueId re = b.load(info.element, operand, info.align);
                air::ValueId im = b.load(info.element,
                                         b.ptr_add(operand, elem), info.align);
                re = info.is_float ? b.fneg(re)
                                   : b.isub(b.const_int(info.element, 0), re);
                im = info.is_float ? b.fneg(im)
                                   : b.isub(b.const_int(info.element, 0), im);
                air::ValueId buffer =
                    create_entry_stack_alloc(info.element_size * 2, info.align);
                b.store(re, buffer, info.align);
                b.store(im, b.ptr_add(buffer, elem), info.align);
                remember(inst_id, buffer);
                return;
            }
            air::TypeId type = air_func_->value_type(operand);
            if (domain == cir::OperatorValueDomain::Floating ||
                mod_->types().is_float(type)) {
                remember(inst_id, b.fneg(operand));
                return;
            }
            remember(inst_id, b.isub(b.const_int(type, 0), operand));
            return;
        }
        case cir::UnaryOpKind::LogicalNot: {
            air::ValueId truth = truth_value(operand, inst.loc);
            if (!truth.is_valid()) {
                return;
            }
            air::ValueId inverted = b.ixor(truth, b.const_bool(true));
            std::optional<air::TypeId> result = air_type(inst.result_type);
            if (result && mod_->types().is_int(*result)) {
                inverted = int_resize(inverted, *result, true, inst.loc);
            }
            remember(inst_id, inverted);
            return;
        }
        case cir::UnaryOpKind::BitwiseNot: {
            if (domain == cir::OperatorValueDomain::Complex) {

                ComplexInfo info =
                    complex_info(descriptor.computation_type.type, inst.loc);
                if (!info.valid) {
                    return;
                }
                int64_t elem = static_cast<int64_t>(info.element_size);
                air::ValueId re = b.load(info.element, operand, info.align);
                air::ValueId im = b.load(info.element,
                                         b.ptr_add(operand, elem), info.align);
                im = info.is_float ? b.fneg(im)
                                   : b.isub(b.const_int(info.element, 0), im);
                air::ValueId buffer =
                    create_entry_stack_alloc(info.element_size * 2, info.align);
                b.store(re, buffer, info.align);
                b.store(im, b.ptr_add(buffer, elem), info.align);
                remember(inst_id, buffer);
                return;
            }
            air::TypeId type = air_func_->value_type(operand);
            if (!mod_->types().is_int(type)) {
                error("bitwise not requires an integer operand", inst.loc);
                return;
            }
            uint16_t width = mod_->types().int_width(type);
            remember(inst_id,
                     b.ixor(operand,
                            b.const_int(type, all_ones_for_width(width),
                                        width > 64 ? ~0ull : 0)));
            return;
        }
        case cir::UnaryOpKind::Invalid:
            break;
    }
    error("unsupported unary operator '" +
              std::string(cir::unary_op_spelling(descriptor.op)) + "'",
          inst.loc);
}

void Lowerer::lower_binary(cir::InstId inst_id,
                           const cir::Inst& inst,
                           const cir::BinaryOpDescriptor& descriptor,
                           const std::vector<cir::ValueRef>& values) {
    air::Builder& b = *builder_;
    air::ValueId lhs = value_for(values[0], inst.loc);
    air::ValueId rhs = value_for(values[1], inst.loc);
    if (!lhs.is_valid() || !rhs.is_valid()) {
        return;
    }
    cir::TypeId lhs_type = file_.valid(values[0].inst)
        ? file_.inst(values[0].inst).result_type
        : cir::TypeId{};
    cir::TypeId rhs_type = file_.valid(values[1].inst)
        ? file_.inst(values[1].inst).result_type
        : cir::TypeId{};

    auto finish_bool = [&](air::ValueId flag) {
        std::optional<air::TypeId> result = air_type(inst.result_type);
        if (flag.is_valid() && result && mod_->types().is_int(*result)) {
            flag = int_resize(flag, *result, true, inst.loc);
        }
        remember(inst_id, flag);
    };

    if (descriptor.op == cir::BinaryOpKind::Comma) {
        remember(inst_id, cast_value(rhs, rhs_type, inst.result_type, inst.loc));
        return;
    }
    {
        cir::TypeId computation = file_.resolved_type(descriptor.computation_type.type);
        if (file_.valid(computation) &&
            file_.type(computation).kind == cir::TypeKind::Complex) {
            remember(inst_id, lower_complex_binary(inst, descriptor,
                                                   lhs, lhs_type,
                                                   rhs, rhs_type));
            return;
        }
    }
    if (descriptor.op == cir::BinaryOpKind::LogicalAnd ||
        descriptor.op == cir::BinaryOpKind::LogicalOr) {
        air::ValueId lhs_truth = truth_value(lhs, inst.loc);
        air::ValueId rhs_truth = truth_value(rhs, inst.loc);
        if (!lhs_truth.is_valid() || !rhs_truth.is_valid()) {
            return;
        }
        finish_bool(descriptor.op == cir::BinaryOpKind::LogicalAnd
                        ? b.iand(lhs_truth, rhs_truth)
                        : b.ior(lhs_truth, rhs_truth));
        return;
    }

    auto resolved_kind = [&](cir::TypeId type) -> cir::TypeKind {
        type = file_.resolved_type(type);
        return file_.valid(type) ? file_.type(type).kind : cir::TypeKind::Invalid;
    };
    if (resolved_kind(lhs_type) == cir::TypeKind::Complex ||
        resolved_kind(rhs_type) == cir::TypeKind::Complex) {
        error("not supported by the air backend yet: complex numbers", inst.loc);
        return;
    }

    bool lhs_pointer = resolved_kind(lhs_type) == cir::TypeKind::Pointer;
    bool rhs_pointer = resolved_kind(rhs_type) == cir::TypeKind::Pointer;
    auto is_comparison = [&]() {
        switch (descriptor.op) {
            case cir::BinaryOpKind::Less:
            case cir::BinaryOpKind::LessEqual:
            case cir::BinaryOpKind::Greater:
            case cir::BinaryOpKind::GreaterEqual:
            case cir::BinaryOpKind::Equal:
            case cir::BinaryOpKind::NotEqual:
                return true;
            default:
                return false;
        }
    };
    auto element_size = [&](cir::TypeId pointer_type) -> uint64_t {
        cir::TypeRef pointee = file_.pointer_pointee_ref(
            file_.resolved_type(pointer_type));
        if (!pointee.valid()) {
            return 1;
        }
        cir::TypeId resolved = file_.resolved_type(pointee.type);
        if (file_.valid(resolved)) {
            cir::TypeKind kind = file_.type(resolved).kind;
            if (kind == cir::TypeKind::Function) {
                return 1;
            }
            if (kind == cir::TypeKind::Builtin &&
                std::get<cir::BuiltinTypePayload>(file_.type_payload(resolved)).kind ==
                    cir::BuiltinTypeKind::Void) {
                return 1;
            }
        }
        auto size = cir::size_align_of_type(file_, pointee.type);
        return size && size->size_bytes > 0 ? size->size_bytes : 1;
    };

    if (lhs_pointer && rhs_pointer && is_comparison()) {
        air::IntCond cond;
        switch (descriptor.op) {
            case cir::BinaryOpKind::Less: cond = air::IntCond::Ult; break;
            case cir::BinaryOpKind::LessEqual: cond = air::IntCond::Ule; break;
            case cir::BinaryOpKind::Greater: cond = air::IntCond::Ugt; break;
            case cir::BinaryOpKind::GreaterEqual: cond = air::IntCond::Uge; break;
            case cir::BinaryOpKind::Equal: cond = air::IntCond::Eq; break;
            default: cond = air::IntCond::Ne; break;
        }
        finish_bool(b.icmp(cond, lhs, rhs));
        return;
    }

    if ((descriptor.op == cir::BinaryOpKind::Add ||
         descriptor.op == cir::BinaryOpKind::Sub) &&
        (lhs_pointer || rhs_pointer)) {
        if (descriptor.op == cir::BinaryOpKind::Sub && lhs_pointer && rhs_pointer) {
            air::TypeId ptr_int = b.size_int_type();
            air::ValueId lhs_int = b.ptrtoint(ptr_int, lhs);
            air::ValueId rhs_int = b.ptrtoint(ptr_int, rhs);
            air::ValueId diff = b.isub(lhs_int, rhs_int);
            uint64_t scale = element_size(lhs_type);
            if (scale > 1) {
                diff = b.sdiv(diff, b.const_usize(static_cast<int64_t>(scale)));
            }
            std::optional<air::TypeId> result = air_type(inst.result_type);
            if (result && mod_->types().is_int(*result)) {
                diff = int_resize(diff, *result, false, inst.loc);
            }
            remember(inst_id, diff);
            return;
        }
        if (descriptor.op == cir::BinaryOpKind::Sub && !lhs_pointer) {
            error("pointer subtraction requires pointer lhs", inst.loc);
            return;
        }
        air::ValueId pointer = lhs_pointer ? lhs : rhs;
        air::ValueId index = lhs_pointer ? rhs : lhs;
        cir::TypeId pointer_type = lhs_pointer ? lhs_type : rhs_type;
        cir::TypeId index_type = lhs_pointer ? rhs_type : lhs_type;
        if (!mod_->types().is_int(air_func_->value_type(index))) {
            error("pointer arithmetic requires an integer index", inst.loc);
            return;
        }
        air::ValueId wide =
            int_resize(index, b.size_int_type(), is_unsigned_domain(index_type),
                       inst.loc);
        if (!wide.is_valid()) {
            return;
        }
        uint64_t scale = element_size(pointer_type);
        air::ValueId offset = scale == 1
            ? wide
            : b.imul(wide, b.const_usize(static_cast<int64_t>(scale)));
        if (descriptor.op == cir::BinaryOpKind::Sub) {
            offset = b.isub(b.const_usize(0), offset);
        }
        remember(inst_id, b.ptr_add(pointer, offset));
        return;
    }

    cir::TypeId computation = descriptor.computation_type.valid()
        ? descriptor.computation_type.type
        : lhs_type;
    lhs = cast_value(lhs, lhs_type, computation, inst.loc);
    rhs = cast_value(rhs, rhs_type, computation, inst.loc);
    if (!lhs.is_valid() || !rhs.is_valid()) {
        return;
    }

    cir::OperatorValueDomain domain =
        file_.operator_value_domain(file_.type_ref(computation));
    bool fp = domain == cir::OperatorValueDomain::Floating ||
              mod_->types().is_float(air_func_->value_type(lhs));
    bool use_unsigned = domain == cir::OperatorValueDomain::UnsignedInteger ||
                        domain == cir::OperatorValueDomain::Bool;

    air::ValueId out;
    switch (descriptor.op) {
        case cir::BinaryOpKind::Add:
            out = fp ? b.fadd(lhs, rhs) : b.iadd(lhs, rhs);
            break;
        case cir::BinaryOpKind::Sub:
            out = fp ? b.fsub(lhs, rhs) : b.isub(lhs, rhs);
            break;
        case cir::BinaryOpKind::Mul:
            out = fp ? b.fmul(lhs, rhs) : b.imul(lhs, rhs);
            break;
        case cir::BinaryOpKind::Div:
            out = fp ? b.fdiv(lhs, rhs)
                     : (use_unsigned ? b.udiv(lhs, rhs) : b.sdiv(lhs, rhs));
            break;
        case cir::BinaryOpKind::Mod:
            out = fp ? b.frem(lhs, rhs)
                     : (use_unsigned ? b.urem(lhs, rhs) : b.srem(lhs, rhs));
            break;
        case cir::BinaryOpKind::BitAnd:
            out = b.iand(lhs, rhs);
            break;
        case cir::BinaryOpKind::BitOr:
            out = b.ior(lhs, rhs);
            break;
        case cir::BinaryOpKind::BitXor:
            out = b.ixor(lhs, rhs);
            break;
        case cir::BinaryOpKind::Shl:
            out = b.shl(lhs, rhs);
            break;
        case cir::BinaryOpKind::Shr:
            out = use_unsigned ? b.lshr(lhs, rhs) : b.ashr(lhs, rhs);
            break;
        case cir::BinaryOpKind::Less:
        case cir::BinaryOpKind::LessEqual:
        case cir::BinaryOpKind::Greater:
        case cir::BinaryOpKind::GreaterEqual:
        case cir::BinaryOpKind::Equal:
        case cir::BinaryOpKind::NotEqual: {
            if (fp) {
                air::FloatCond cond;
                switch (descriptor.op) {
                    case cir::BinaryOpKind::Less: cond = air::FloatCond::Olt; break;
                    case cir::BinaryOpKind::LessEqual: cond = air::FloatCond::Ole; break;
                    case cir::BinaryOpKind::Greater: cond = air::FloatCond::Ogt; break;
                    case cir::BinaryOpKind::GreaterEqual: cond = air::FloatCond::Oge; break;
                    case cir::BinaryOpKind::Equal: cond = air::FloatCond::Oeq; break;

                    default: cond = air::FloatCond::Une; break;
                }
                finish_bool(b.fcmp(cond, lhs, rhs));
                return;
            }
            air::IntCond cond;
            switch (descriptor.op) {
                case cir::BinaryOpKind::Less:
                    cond = use_unsigned ? air::IntCond::Ult : air::IntCond::Slt;
                    break;
                case cir::BinaryOpKind::LessEqual:
                    cond = use_unsigned ? air::IntCond::Ule : air::IntCond::Sle;
                    break;
                case cir::BinaryOpKind::Greater:
                    cond = use_unsigned ? air::IntCond::Ugt : air::IntCond::Sgt;
                    break;
                case cir::BinaryOpKind::GreaterEqual:
                    cond = use_unsigned ? air::IntCond::Uge : air::IntCond::Sge;
                    break;
                case cir::BinaryOpKind::Equal:
                    cond = air::IntCond::Eq;
                    break;
                default:
                    cond = air::IntCond::Ne;
                    break;
            }
            finish_bool(b.icmp(cond, lhs, rhs));
            return;
        }
        case cir::BinaryOpKind::Invalid:
        case cir::BinaryOpKind::LogicalAnd:
        case cir::BinaryOpKind::LogicalOr:
        case cir::BinaryOpKind::Comma:
            break;
    }

    if (!out.is_valid()) {
        error("unsupported binary operator '" +
                  std::string(cir::binary_op_spelling(descriptor.op)) + "'",
              inst.loc);
        return;
    }
    remember(inst_id, cast_value(out, computation, inst.result_type, inst.loc));
}

bool Lowerer::build_asm_payload(const cir::InlineAsmPayload& payload,
                                const std::vector<cir::ValueRef>& values,
                                SrcLoc loc,
                                air::AsmPayload& air_payload,
                                std::vector<air::ValueId>& operands) {
    if (values.size() != payload.outputs.size() + payload.inputs.size()) {
        error("inline asm operand count does not match its metadata", loc);
        return false;
    }

    std::unordered_map<std::string, size_t> name_to_index;
    size_t position = 0;
    for (const cir::InlineAsmOperandPayload& out : payload.outputs) {
        if (out.symbolic_name.valid()) {
            name_to_index[std::string(file_.name(out.symbolic_name))] = position;
        }
        ++position;
    }
    for (const cir::InlineAsmOperandPayload& in : payload.inputs) {
        if (in.symbolic_name.valid()) {
            name_to_index[std::string(file_.name(in.symbolic_name))] = position;
        }
        ++position;
    }
    for (cir::NameId label : payload.goto_labels) {
        if (label.valid()) {
            name_to_index[std::string(file_.name(label))] = position;
        }
        ++position;
    }

    std::string text;
    text.reserve(payload.asm_string.size());
    for (size_t i = 0; i < payload.asm_string.size(); ++i) {
        char ch = payload.asm_string[i];
        if (ch == '%' && i + 1 < payload.asm_string.size()) {
            if (payload.asm_string[i + 1] == '%') {
                text += "%%";
                ++i;
                continue;
            }

            size_t modifier_end = i + 1;
            while (modifier_end < payload.asm_string.size() &&
                   std::isalpha(static_cast<unsigned char>(
                       payload.asm_string[modifier_end]))) {
                ++modifier_end;
            }
            if (modifier_end < payload.asm_string.size() &&
                payload.asm_string[modifier_end] == '[') {
                size_t close = payload.asm_string.find(']', modifier_end + 1);
                if (close == std::string::npos) {
                    error("malformed asm symbolic operand reference",
                          loc);
                    return false;
                }
                std::string name = payload.asm_string.substr(
                    modifier_end + 1, close - (modifier_end + 1));
                auto found = name_to_index.find(name);
                if (found == name_to_index.end()) {
                    error("asm references unknown operand '[" + name + "]'",
                          loc);
                    return false;
                }
                text += payload.asm_string.substr(i, modifier_end - i);
                text += std::to_string(found->second);
                i = close;
                continue;
            }
        }
        text += ch;
    }

    struct Norm {
        std::string spelling;
        bool immediate = false;
        bool memory_only = false;
        bool has_register = false;
    };
    TargetArch arch = mod_->target().arch;
    auto normalize = [&](const std::string& raw, bool is_output,
                         bool prefer_fp) -> Norm {
        Norm norm;
        std::string prefix;
        size_t p = 0;
        if (is_output) {
            prefix = (raw.empty() || raw[0] == '=') ? "=" : "+";
            if (!raw.empty() && (raw[0] == '=' || raw[0] == '+')) {
                p = 1;
            }
        }
        char specific = 0;
        char fp_letter = 0;
        bool generic = false;
        bool immediate = false;
        bool memory = false;
        for (; p < raw.size(); ++p) {
            char letter = raw[p];
            if (letter == '&' || letter == '%' || letter == '#' ||
                letter == '*' || letter == ' ') {
                continue;
            }
            switch (aburi::classify_asm_letter(arch, letter)) {
                case aburi::AsmLetterClass::GeneralReg:
                    generic = true;
                    break;
                case aburi::AsmLetterClass::SpecificReg:
                    specific = letter;
                    break;
                case aburi::AsmLetterClass::FpReg:
                    if (fp_letter == 0) {
                        fp_letter = letter;
                    }
                    break;
                case aburi::AsmLetterClass::Memory:
                    memory = true;
                    break;
                case aburi::AsmLetterClass::Immediate:
                    immediate = true;
                    break;
                case aburi::AsmLetterClass::Any:
                    generic = true;
                    immediate = true;
                    memory = true;
                    break;
                case aburi::AsmLetterClass::Unknown:
                    break;
            }
        }
        norm.has_register = specific != 0 || generic || fp_letter != 0;
        norm.memory_only = memory && !norm.has_register && !immediate;
        if (prefer_fp && fp_letter != 0) {
            norm.spelling = prefix + std::string(1, fp_letter);
        } else if (specific != 0) {
            norm.spelling = prefix + std::string(1, specific);
        } else if (generic) {
            norm.spelling = prefix + "r";
        } else if (fp_letter != 0) {
            norm.spelling = prefix + std::string(1, fp_letter);
        } else if (immediate) {
            norm.spelling = prefix + "i";
            norm.immediate = true;
        } else {
            norm.spelling = prefix + "m";
        }
        return norm;
    };

    air_payload.text = std::move(text);
    air_payload.clobbers = payload.clobbers;
    operands.reserve(values.size());

    std::vector<std::string> bindings;
    bool any_binding = false;
    auto record_binding = [&](const std::string& binding,
                              air::TypeId operand_type) {
        unsigned bits = mod_->types().int_width(operand_type);
        bindings.push_back(aburi::normalize_asm_register_name(
            mod_->target().arch, binding, bits != 0 ? bits : 64));
        any_binding = any_binding || !binding.empty();
    };

    for (size_t i = 0; i < payload.outputs.size(); ++i) {
        const cir::InlineAsmOperandPayload& out = payload.outputs[i];
        cir::TypeId place_type = file_.valid(values[i].inst)
            ? file_.inst(values[i].inst).result_type
            : cir::TypeId{};
        cir::TypeId object_type = file_.place_object_type(place_type);
        std::optional<air::TypeId> object_air = air_type(object_type);
        air::ValueId addr = value_for(values[i], loc);
        if (!addr.is_valid()) {
            error("not supported by the air backend yet: this asm output "
                  "operand", loc);
            return false;
        }
        bool scalar = object_air && mod_->types().is_scalar(*object_air);
        Norm norm = normalize(out.constraint, /*is_output=*/true,
                              /*prefer_fp=*/scalar &&
                                  mod_->types().is_float(*object_air));
        if (!scalar) {

            if (!norm.memory_only) {
                error("not supported by the air backend yet: this asm output "
                      "operand type", loc);
                return false;
            }
            object_air = air_func_->value_type(addr);
        }
        air_payload.constraints.push_back(norm.spelling);
        air_payload.operand_types.push_back(*object_air);
        record_binding(out.register_binding, *object_air);
        operands.push_back(addr);
    }

    for (size_t i = 0; i < payload.inputs.size(); ++i) {
        const cir::InlineAsmOperandPayload& in = payload.inputs[i];
        size_t value_index = payload.outputs.size() + i;

        bool tied = !in.constraint.empty() &&
                    in.constraint.find_first_not_of("0123456789") ==
                        std::string::npos;
        if (tied) {
            size_t tied_index =
                static_cast<size_t>(std::atoi(in.constraint.c_str()));
            if (tied_index >= payload.outputs.size()) {
                error("asm matching constraint '" + in.constraint +
                      "' references a nonexistent output operand", loc);
                return false;
            }
        }

        air::ValueId operand = value_for(values[value_index], loc);
        if (!operand.is_valid()) {
            return false;
        }
        air::TypeId operand_type = air_func_->value_type(operand);
        Norm norm = tied
            ? Norm{in.constraint, false, false, true}
            : normalize(in.constraint, /*is_output=*/false,
                        /*prefer_fp=*/mod_->types().is_float(operand_type));
        if (!norm.memory_only && !mod_->types().is_scalar(operand_type)) {
            error("not supported by the air backend yet: this asm input "
                  "operand type", loc);
            return false;
        }
        air_payload.constraints.push_back(norm.spelling);
        air_payload.operand_types.push_back(operand_type);
        record_binding(in.register_binding, operand_type);
        operands.push_back(operand);
    }

    if (any_binding) {
        air_payload.register_bindings = std::move(bindings);
    }
    return true;
}

void Lowerer::lower_inline_asm(cir::InstId inst_id,
                               const cir::Inst& inst,
                               const cir::InlineAsmPayload& payload,
                               const std::vector<cir::ValueRef>& values) {
    (void)inst_id;
    air::AsmPayload air_payload;
    std::vector<air::ValueId> operands;
    if (!build_asm_payload(payload, values, inst.loc, air_payload, operands)) {
        return;
    }
    uint32_t payload_index = mod_->add_asm_payload(std::move(air_payload));
    builder_->inline_asm(payload_index, operands);
}

void Lowerer::lower_va_arg(cir::InstId inst_id,
                           const cir::Inst& inst,
                           const std::vector<cir::Operand>& operands) {
    air::Builder& b = *builder_;
    cir::TypeRef target = type_operand_at(operands, 0);
    cir::ValueRef list_ref = value_operand_at(operands, 1);
    if (!target.type.valid()) {
        target = file_.type_ref(inst.result_type);
    }
    air::ValueId list = value_for(list_ref, inst.loc);
    if (!list.is_valid()) {
        return;
    }
    if (!options_.target) {
        error("not supported by the air backend yet: this va_list ABI", inst.loc);
        return;
    }
    if (options_.target->va_list_kind == VaListKind::AARCH64_VA_LIST) {
        lower_va_arg_aapcs64(inst_id, inst, target, list);
        return;
    }
    if (options_.target->va_list_kind == VaListKind::X86_64_VA_LIST) {
        lower_va_arg_sysv(inst_id, inst, target, list);
        return;
    }
    if (options_.target->va_list_kind != VaListKind::CHAR_PTR) {
        error("not supported by the air backend yet: this va_list ABI", inst.loc);
        return;
    }
    auto size_align = cir::size_align_of_type(file_, target.type);
    if (!size_align) {
        error("va_arg of an incomplete type", inst.loc);
        return;
    }
    uint64_t arg_size = size_align->size_bytes;
    uint64_t arg_align = std::max<size_t>(1, size_align->alignment_bytes);

    const uint64_t word = options_.target->pointer_width == 64 ? 8 : 4;
    const air::TypeId ptr_int = b.size_int_type();
    abi::AggregateClass cls =
        abi::classify_vararg_native(file_, target, options_.target.get());
    bool indirect = cls.pass == abi::AggregatePass::Indirect;

    uint64_t slot_align = (indirect || word == 4)
                              ? word
                              : std::max<uint64_t>(word, arg_align);
    uint64_t slot_size =
        indirect ? word : ((arg_size + word - 1) / word) * word;
    if (slot_size == 0) {
        slot_size = word;
    }

    air::ValueId current = b.load(air::types::PTR, list, static_cast<uint32_t>(word));
    air::ValueId current_int = b.ptrtoint(ptr_int, current);
    if (slot_align > word) {
        air::ValueId bumped = b.iadd(
            current_int, b.const_int(ptr_int, static_cast<uint64_t>(slot_align - 1)));
        current_int = b.iand(
            bumped, b.const_int(ptr_int, static_cast<uint64_t>(~(slot_align - 1))));
    }
    air::ValueId aligned = b.inttoptr(air::types::PTR, current_int);
    air::ValueId next_int =
        b.iadd(current_int, b.const_int(ptr_int, static_cast<uint64_t>(slot_size)));
    b.store(b.inttoptr(air::types::PTR, next_int), list,
            static_cast<uint32_t>(word));

    if (is_memory_only_type(target.type)) {
        air::ValueId source = indirect
            ? b.load(air::types::PTR, aligned, static_cast<uint32_t>(word))
            : aligned;
        air::ValueId copy = create_entry_stack_alloc(
            std::max<uint64_t>(1, arg_size), static_cast<uint32_t>(arg_align));
        b.memcpy_(copy, source, b.const_usize(static_cast<int64_t>(arg_size)));
        remember(inst_id, copy);
        return;
    }

    std::optional<air::TypeId> value_type = air_type(target.type);
    if (!value_type || *value_type == air::types::VOID) {
        error("not supported by the air backend yet: va_arg of this type",
              inst.loc);
        return;
    }
    remember(inst_id, b.load(*value_type, aligned,
                             static_cast<uint32_t>(std::min<uint64_t>(arg_align, word))));
}

void Lowerer::lower_va_arg_aapcs64(cir::InstId inst_id,
                                   const cir::Inst& inst,
                                   cir::TypeRef target,
                                   air::ValueId list) {
    air::Builder& b = *builder_;
    auto size_align = cir::size_align_of_type(file_, target.type);
    if (!size_align) {
        error("va_arg of an incomplete type", inst.loc);
        return;
    }
    uint64_t arg_size = size_align->size_bytes;
    uint64_t arg_align = std::max<size_t>(1, size_align->alignment_bytes);

    abi::AggregateClass cls = abi::classify_aarch64_vararg_native(
        file_, target, options_.target.get());

    bool use_vr = false;
    bool indirect = false;
    unsigned reg_count = 1;
    uint64_t elem_size = arg_size;
    switch (cls.pass) {
        case abi::AggregatePass::Ignore:
            error("va_arg of an empty record", inst.loc);
            return;
        case abi::AggregatePass::Indirect:
            indirect = true;
            break;
        case abi::AggregatePass::CoerceHfa:
            use_vr = true;
            reg_count = cls.hfa_count;
            elem_size =
                cls.hfa_element == cir::BuiltinTypeKind::Float16      ? 2
                : cls.hfa_element == cir::BuiltinTypeKind::Float      ? 4
                : cls.hfa_element == cir::BuiltinTypeKind::LongDouble ? 16
                                                                      : 8;
            break;
        case abi::AggregatePass::CoerceIntSlots:
        case abi::AggregatePass::CoerceClassedSlots:
        case abi::AggregatePass::MemoryByval:
            reg_count = cls.int_slot_count;
            break;
        case abi::AggregatePass::UseSourceType: {
            cir::TypeId resolved = file_.resolved_type(target.type);
            if (file_.valid(resolved) &&
                file_.type(resolved).kind == cir::TypeKind::Builtin) {
                cir::BuiltinTypeKind kind =
                    std::get<cir::BuiltinTypePayload>(file_.type_payload(resolved))
                        .kind;
                if (kind == cir::BuiltinTypeKind::Float ||
                    kind == cir::BuiltinTypeKind::Double ||
                    kind == cir::BuiltinTypeKind::LongDouble ||
                    kind == cir::BuiltinTypeKind::Float16) {
                    use_vr = true;
                    reg_count = 1;
                    break;
                }
            }
            reg_count =
                static_cast<unsigned>(std::max<uint64_t>(1, (arg_size + 7) / 8));
            break;
        }
    }

    const int64_t offs_offset = use_vr ? 28 : 24;
    const int64_t top_offset = use_vr ? 16 : 8;
    const int64_t reg_area_bytes =
        indirect ? 8
                 : static_cast<int64_t>(use_vr ? 16u * reg_count
                                               : 8u * reg_count);

    air::BlockId try_reg = b.create_block();
    air::BlockId in_reg = b.create_block();
    air::BlockId on_stack = b.create_block();
    const air::TypeId cont_params[] = {air::types::PTR};
    air::BlockId cont = b.create_block(cont_params);

    air::ValueId offs_ptr = b.ptr_add(list, offs_offset);
    air::ValueId offs = b.load(air::types::I32, offs_ptr, 4);
    air::ValueId regs_used =
        b.icmp(air::IntCond::Sge, offs, b.const_i32(0));
    b.br_if(regs_used, on_stack, try_reg);

    b.set_insertion_point(try_reg);
    air::ValueId aligned_offs = offs;
    if (!use_vr && !indirect && arg_align > 8) {

        air::ValueId bumped = b.iadd(aligned_offs, b.const_i32(15));
        aligned_offs = b.iand(bumped, b.const_i32(-16));
    }
    air::ValueId new_offs =
        b.iadd(aligned_offs, b.const_i32(static_cast<int32_t>(reg_area_bytes)));
    b.store(new_offs, offs_ptr, 4);
    air::ValueId fits = b.icmp(air::IntCond::Sle, new_offs, b.const_i32(0));
    b.br_if(fits, in_reg, on_stack);

    b.set_insertion_point(in_reg);
    air::ValueId reg_top =
        b.load(air::types::PTR, b.ptr_add(list, top_offset), 8);
    air::ValueId reg_base =
        b.ptr_add(reg_top, b.sext(air::types::I64, aligned_offs));
    air::ValueId in_reg_addr = reg_base;
    if (indirect) {
        in_reg_addr = b.load(air::types::PTR, reg_base, 8);
    } else if (use_vr && reg_count > 1 && elem_size < 16) {

        air::ValueId repacked = create_entry_stack_alloc(
            std::max<uint64_t>(1, arg_size), static_cast<uint32_t>(arg_align));
        air::TypeId elem_type =
            elem_size == 2 ? air::types::I16
            : elem_size == 4 ? air::types::F32
                             : air::types::F64;
        for (unsigned i = 0; i < reg_count; ++i) {
            air::ValueId element = b.load(
                elem_type, b.ptr_add(reg_base, static_cast<int64_t>(16u * i)),
                static_cast<uint32_t>(elem_size));
            b.store(element,
                    b.ptr_add(repacked, static_cast<int64_t>(elem_size * i)),
                    static_cast<uint32_t>(elem_size));
        }
        in_reg_addr = repacked;
    }
    {
        const air::ValueId args[] = {in_reg_addr};
        b.jump(cont, args);
    }

    b.set_insertion_point(on_stack);
    air::ValueId stack = b.load(air::types::PTR, list, 8);
    if (!indirect && arg_align > 8) {
        air::ValueId stack_int = b.ptrtoint(air::types::I64, stack);
        stack_int = b.iadd(stack_int, b.const_i64(15));
        stack_int = b.iand(stack_int, b.const_i64(-16));
        stack = b.inttoptr(air::types::PTR, stack_int);
    }
    const int64_t stack_slot_bytes =
        indirect ? 8
                 : static_cast<int64_t>(
                       std::max<uint64_t>(8, (arg_size + 7) & ~uint64_t{7}));
    b.store(b.ptr_add(stack, stack_slot_bytes), list, 8);
    air::ValueId on_stack_addr = stack;
    if (indirect) {
        on_stack_addr = b.load(air::types::PTR, stack, 8);
    }
    {
        const air::ValueId args[] = {on_stack_addr};
        b.jump(cont, args);
    }

    b.set_insertion_point(cont);
    air::ValueId addr = air_func_->block_params(cont)[0];

    if (is_memory_only_type(target.type)) {
        air::ValueId copy = create_entry_stack_alloc(
            std::max<uint64_t>(1, arg_size), static_cast<uint32_t>(arg_align));
        b.memcpy_(copy, addr, b.const_usize(static_cast<int64_t>(arg_size)));
        remember(inst_id, copy);
        return;
    }
    std::optional<air::TypeId> value_type = air_type(target.type);
    if (!value_type || *value_type == air::types::VOID) {
        error("not supported by the air backend yet: va_arg of this type",
              inst.loc);
        return;
    }
    remember(inst_id,
             b.load(*value_type, addr,
                    static_cast<uint32_t>(std::min<uint64_t>(arg_align, 8))));
}

void Lowerer::lower_va_arg_sysv(cir::InstId inst_id,
                                const cir::Inst& inst,
                                cir::TypeRef target,
                                air::ValueId list) {
    air::Builder& b = *builder_;
    auto size_align = cir::size_align_of_type(file_, target.type);
    if (!size_align) {
        error("va_arg of an incomplete type", inst.loc);
        return;
    }
    uint64_t arg_size = size_align->size_bytes;
    uint64_t arg_align = std::max<size_t>(1, size_align->alignment_bytes);

    abi::AggregateClass cls =
        abi::classify_vararg_native(file_, target, options_.target.get());

    bool memory = false;

    bool slot_sse[2] = {false, false};
    unsigned slot_count = 0;
    switch (cls.pass) {
        case abi::AggregatePass::Ignore:
            error("va_arg of an empty record", inst.loc);
            return;
        case abi::AggregatePass::MemoryByval:
            memory = true;
            break;
        case abi::AggregatePass::CoerceIntSlots:
            slot_count = cls.int_slot_count;
            break;
        case abi::AggregatePass::CoerceClassedSlots:
            slot_count = cls.int_slot_count;
            for (unsigned slot = 0; slot < slot_count && slot < 2; ++slot) {
                slot_sse[slot] = (cls.sse_slot_mask >> slot) & 1;
            }
            break;
        case abi::AggregatePass::CoerceHfa:
        case abi::AggregatePass::Indirect:

            memory = true;
            break;
        case abi::AggregatePass::UseSourceType: {
            cir::TypeId resolved = file_.resolved_type(target.type);
            if (file_.valid(resolved) &&
                file_.type(resolved).kind == cir::TypeKind::Builtin) {
                cir::BuiltinTypeKind kind =
                    std::get<cir::BuiltinTypePayload>(file_.type_payload(resolved))
                        .kind;
                if (kind == cir::BuiltinTypeKind::LongDouble) {
                    memory = true;
                    break;
                }
                if (kind == cir::BuiltinTypeKind::Float ||
                    kind == cir::BuiltinTypeKind::Double ||
                    kind == cir::BuiltinTypeKind::Float16) {
                    slot_count = 1;
                    slot_sse[0] = true;
                    break;
                }
            }
            slot_count =
                static_cast<unsigned>(std::max<uint64_t>(1, (arg_size + 7) / 8));
            break;
        }
    }

    unsigned n_int = 0;
    unsigned n_sse = 0;
    for (unsigned slot = 0; slot < slot_count && slot < 2; ++slot) {
        if (slot_sse[slot]) {
            ++n_sse;
        } else {
            ++n_int;
        }
    }

    auto take_overflow = [&]() -> air::ValueId {
        air::ValueId stack =
            b.load(air::types::PTR, b.ptr_add(list, 8), 8);
        if (arg_align > 8) {
            air::ValueId stack_int = b.ptrtoint(air::types::I64, stack);
            stack_int = b.iadd(stack_int,
                               b.const_i64(static_cast<int64_t>(arg_align - 1)));
            stack_int = b.iand(stack_int,
                               b.const_i64(static_cast<int64_t>(~(arg_align - 1))));
            stack = b.inttoptr(air::types::PTR, stack_int);
        }
        int64_t slot_bytes = static_cast<int64_t>(
            std::max<uint64_t>(8, (arg_size + 7) & ~uint64_t{7}));
        b.store(b.ptr_add(stack, slot_bytes), b.ptr_add(list, 8), 8);
        return stack;
    };

    air::ValueId addr;
    if (memory) {
        addr = take_overflow();
    } else {
        air::BlockId in_reg = b.create_block();
        air::BlockId on_stack = b.create_block();
        const air::TypeId cont_params[] = {air::types::PTR};
        air::BlockId cont = b.create_block(cont_params);

        air::ValueId gp_ptr = list;
        air::ValueId fp_ptr = b.ptr_add(list, 4);
        air::ValueId gp_offs = b.load(air::types::I32, gp_ptr, 4);
        air::ValueId fp_offs = b.load(air::types::I32, fp_ptr, 4);
        air::ValueId fits;
        if (n_int > 0 && n_sse > 0) {
            air::ValueId gp_fits = b.icmp(
                air::IntCond::Ule, gp_offs,
                b.const_i32(static_cast<int32_t>(48 - 8 * n_int)));
            air::ValueId fp_fits = b.icmp(
                air::IntCond::Ule, fp_offs,
                b.const_i32(static_cast<int32_t>(176 - 16 * n_sse)));
            fits = b.iand(gp_fits, fp_fits);
        } else if (n_sse > 0) {
            fits = b.icmp(air::IntCond::Ule, fp_offs,
                          b.const_i32(static_cast<int32_t>(176 - 16 * n_sse)));
        } else {
            fits = b.icmp(air::IntCond::Ule, gp_offs,
                          b.const_i32(static_cast<int32_t>(48 - 8 * n_int)));
        }
        b.br_if(fits, in_reg, on_stack);

        b.set_insertion_point(in_reg);
        air::ValueId reg_save =
            b.load(air::types::PTR, b.ptr_add(list, 16), 8);
        air::ValueId in_reg_addr;
        if (slot_count == 1) {
            air::ValueId offs = slot_sse[0] ? fp_offs : gp_offs;
            in_reg_addr = b.ptr_add(reg_save, b.zext(air::types::I64, offs));
        } else {

            air::ValueId gathered = create_entry_stack_alloc(
                8ull * slot_count, static_cast<uint32_t>(arg_align));
            air::ValueId gp_cursor = gp_offs;
            air::ValueId fp_cursor = fp_offs;
            for (unsigned slot = 0; slot < slot_count && slot < 2; ++slot) {
                air::ValueId offs = slot_sse[slot] ? fp_cursor : gp_cursor;
                air::ValueId lane_addr =
                    b.ptr_add(reg_save, b.zext(air::types::I64, offs));
                air::ValueId lane = b.load(air::types::I64, lane_addr, 8);
                b.store(lane,
                        slot == 0 ? gathered
                                  : b.ptr_add(gathered,
                                              static_cast<int64_t>(8 * slot)),
                        8);
                if (slot_sse[slot]) {
                    fp_cursor = b.iadd(fp_cursor, b.const_i32(16));
                } else {
                    gp_cursor = b.iadd(gp_cursor, b.const_i32(8));
                }
            }
            in_reg_addr = gathered;
        }
        if (n_int > 0) {
            b.store(b.iadd(gp_offs,
                           b.const_i32(static_cast<int32_t>(8 * n_int))),
                    gp_ptr, 4);
        }
        if (n_sse > 0) {
            b.store(b.iadd(fp_offs,
                           b.const_i32(static_cast<int32_t>(16 * n_sse))),
                    fp_ptr, 4);
        }
        {
            const air::ValueId args[] = {in_reg_addr};
            b.jump(cont, args);
        }

        b.set_insertion_point(on_stack);
        air::ValueId on_stack_addr = take_overflow();
        {
            const air::ValueId args[] = {on_stack_addr};
            b.jump(cont, args);
        }

        b.set_insertion_point(cont);
        addr = air_func_->block_params(cont)[0];
    }

    if (is_memory_only_type(target.type)) {
        air::ValueId copy = create_entry_stack_alloc(
            std::max<uint64_t>(1, arg_size), static_cast<uint32_t>(arg_align));
        b.memcpy_(copy, addr, b.const_usize(static_cast<int64_t>(arg_size)));
        remember(inst_id, copy);
        return;
    }
    std::optional<air::TypeId> value_type = air_type(target.type);
    if (!value_type || *value_type == air::types::VOID) {
        error("not supported by the air backend yet: va_arg of this type",
              inst.loc);
        return;
    }
    remember(inst_id,
             b.load(*value_type, addr,
                    static_cast<uint32_t>(std::min<uint64_t>(arg_align, 8))));
}

} // namespace aburi::cir2air
