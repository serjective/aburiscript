

#include "coro_split.h"

#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "../cir/builder.h"
#include "../cir/inst_schema.h"
#include "../cir/layout.h"

namespace aburi::cirpasses {

namespace {

using namespace aburi::cir;

constexpr uint32_t kInvalidIndex = 0xFFFFFFFFu;

size_t align_up(size_t value, size_t alignment) {
    if (alignment == 0) {
        return value;
    }
    return (value + alignment - 1) / alignment * alignment;
}

struct SuspendPoint {
    BlockId block{};
    CoroSuspendPayload payload;
    InstId transfer{};
};

struct FrameField {
    EntityId field{};
    TypeRef type{};
    size_t offset = 0;
};

struct CoroHarvest {
    InstId coro_begin{};
    InstId promise_place{};
    std::vector<InstId> frame_sizes;
    std::vector<InstId> frame_aligns;
    std::vector<SuspendPoint> suspends;
    std::vector<BlockId> end_blocks;
    std::vector<EntityId> promoted;
};

class CoroSplitter {
public:
    CoroSplitter(File& file, FunctionId function_id, const CoroutineFact& fact)
        : file_(file),
          builder_(file),
          function_id_(function_id),
          fact_(fact) {}

    bool run();

private:
    bool harvest();
    bool analyze_spills();
    bool build_frame();
    void rewrite_shared_body();
    void apply_spills();
    void rewrite_ramp();
    bool build_clone(bool is_destroy,
                     EntityId& entity_out,
                     FunctionId& function_out);
    void prune_unreachable(FunctionId function_id);
    bool validate_values(FunctionId function_id);

    void fail(const std::string& message, SrcLoc loc) {
        file_.add_error(message, loc);
        failed_ = true;
    }

    InstId make_field_addr(InstId frame_object_place,
                           const FrameField& field,
                           SrcLoc loc) {
        PlaceFact fact;
        fact.object_type = field.type;
        fact.storage_duration = StorageDuration::Unknown;
        fact.base = frame_object_place;
        fact.loc = loc;
        Inst inst;
        inst.kind = InstKind::FieldAddr;
        inst.result_type = file_.place_type(field.type);
        inst.place_fact = file_.add_place_fact(std::move(fact));
        inst.operands = file_.add_operands(
            {Operand::value(frame_object_place), Operand::entity(field.field)});
        inst.loc = loc;
        InstId id = file_.add_inst(inst);
        file_.place_fact_mut(inst.place_fact).source = id;
        return id;
    }
    InstId make_function_pointer(EntityId function, SrcLoc loc) {
        Inst inst;
        inst.kind = InstKind::FunctionToPointer;
        inst.result_type =
            builder_.pointer_type(file_.entity(function).type);
        inst.operands = file_.add_operands({Operand::entity(function)});
        inst.loc = loc;
        return file_.add_inst(inst);
    }

    InstId make_integer_literal(int64_t value, TypeId type, SrcLoc loc) {
        LiteralPayload literal;
        IntegerTypeShape shape = integer_shape_for_type(file_, type);
        literal.value = IntegerValue::from_signed(value, 64).cast(
            shape.bit_width, shape.is_unsigned);
        literal.spelling = std::to_string(value);
        Inst inst;
        inst.kind = InstKind::IntegerLiteral;
        inst.result_type = type;
        inst.payload_index = file_.add_payload(InstPayload{std::move(literal)});
        inst.loc = loc;
        return file_.add_inst(inst);
    }

    InstId make_store(InstId place, InstId value, SrcLoc loc) {
        Inst inst;
        inst.kind = InstKind::Store;
        inst.operands = file_.add_value_operands({place, value});
        inst.loc = loc;
        return file_.add_inst(inst);
    }

    InstId make_load(InstId place, TypeRef object_type, SrcLoc loc) {
        Inst inst;
        inst.kind = InstKind::Load;
        inst.result_type = object_type.type;
        inst.operands = file_.add_value_operands({place});
        inst.loc = loc;
        return file_.add_inst(inst);
    }
    InstId make_resume_slot_load(InstId target,
                                 std::vector<InstId>& out,
                                 SrcLoc loc) {
        TypeId slot_pointer = builder_.pointer_type(resume_pointer_type_);
        CastPayload cast_kind;
        cast_kind.kind = "value";
        Inst cast_inst;
        cast_inst.kind = InstKind::Cast;
        cast_inst.result_type = slot_pointer;
        cast_inst.payload_index =
            file_.add_payload(InstPayload{std::move(cast_kind)});
        cast_inst.operands = file_.add_operands(
            {Operand::type(file_.type_ref(slot_pointer)),
             Operand::value(target)});
        cast_inst.loc = loc;
        InstId typed = file_.add_inst(cast_inst);
        out.push_back(typed);

        PlaceFact fact;
        fact.object_type = file_.type_ref(resume_pointer_type_);
        fact.storage_duration = StorageDuration::Unknown;
        fact.base = typed;
        fact.loc = loc;
        Inst deref_inst;
        deref_inst.kind = InstKind::Deref;
        deref_inst.result_type =
            file_.place_type(file_.type_ref(resume_pointer_type_));
        deref_inst.place_fact = file_.add_place_fact(std::move(fact));
        deref_inst.operands =
            file_.add_operands({Operand::value(typed)});
        deref_inst.loc = loc;
        InstId place = file_.add_inst(deref_inst);
        file_.place_fact_mut(deref_inst.place_fact).source = place;
        out.push_back(place);

        InstId loaded =
            make_load(place, file_.type_ref(resume_pointer_type_), loc);
        out.push_back(loaded);
        return loaded;
    }

    InstId make_resume_call(InstId fn_value,
                            InstId target,
                            bool must_tail,
                            SrcLoc loc) {
        Inst call;
        call.kind = InstKind::Call;
        call.result_type = builder_.void_type();
        if (must_tail) {
            CallPayload payload;
            payload.must_tail = true;
            call.payload_index =
                file_.add_payload(InstPayload{std::move(payload)});
        }
        call.operands = file_.add_operands(
            {Operand::value(fn_value), Operand::value(target)});
        call.loc = loc;
        return file_.add_inst(call);
    }
    InstId make_frame_object_place(InstId frame_pointer,
                                   std::vector<InstId>& out,
                                   SrcLoc loc) {
        CastPayload cast_kind;
        cast_kind.kind = "value";
        Inst cast_inst;
        cast_inst.kind = InstKind::Cast;
        cast_inst.result_type = frame_pointer_type_;
        cast_inst.payload_index =
            file_.add_payload(InstPayload{std::move(cast_kind)});
        cast_inst.operands = file_.add_operands(
            {Operand::type(file_.type_ref(frame_pointer_type_)),
             Operand::value(frame_pointer)});
        cast_inst.loc = loc;
        InstId typed_pointer = file_.add_inst(cast_inst);
        out.push_back(typed_pointer);

        PlaceFact fact;
        fact.object_type = file_.type_ref(frame_type_);
        fact.storage_duration = StorageDuration::Unknown;
        fact.base = typed_pointer;
        fact.loc = loc;
        Inst deref_inst;
        deref_inst.kind = InstKind::Deref;
        deref_inst.result_type = file_.place_type(file_.type_ref(frame_type_));
        deref_inst.place_fact = file_.add_place_fact(std::move(fact));
        deref_inst.operands =
            file_.add_operands({Operand::value(typed_pointer)});
        deref_inst.loc = loc;
        InstId place = file_.add_inst(deref_inst);
        file_.place_fact_mut(deref_inst.place_fact).source = place;
        out.push_back(place);
        return place;
    }

    File& file_;
    Builder builder_;
    FunctionId function_id_;
    CoroutineFact fact_;
    CoroHarvest harvest_;
    bool failed_ = false;

    EntityId frame_record_{};
    TypeId frame_type_{};
    TypeId frame_pointer_type_{};
    size_t frame_size_ = 0;
    size_t frame_align_ = 0;
    FrameField resume_field_;
    FrameField destroy_field_;
    FrameField promise_field_;
    FrameField state_field_;
    std::unordered_map<uint32_t, FrameField> entity_fields_;
    std::vector<InstId> spilled_values_;
    std::unordered_map<uint32_t, FrameField> spill_fields_;
    std::unordered_map<uint32_t, FrameField> fields_by_entity_;
    InstId ramp_frame_place_{};
    TypeId state_type_{};
    TypeId void_pointer_type_{};
    TypeId resume_pointer_type_{};
    SrcLoc loc_{};
};

bool CoroSplitter::harvest() {
    const Function& fn = file_.function(function_id_);
    loc_ = fn.loc;
    std::unordered_set<uint32_t> promoted_set;
    std::unordered_set<uint32_t> excluded_set;

    for (const FunctionParameter& parameter : fn.parameters) {
        if (!parameter.entity.valid() || !file_.valid(parameter.entity)) {
            continue;
        }
        TypeId type =
            file_.resolved_type(file_.entity(parameter.entity).type);
        const RecordFacts* record = file_.record_facts_for_type(type);
        if (record && record->is_non_trivial_for_calls) {
            excluded_set.insert(parameter.entity.index);
        }
    }

    auto exclude_block_locals = [&](BlockId block_id) {
        for (InstId inst_id : file_.block(block_id).instructions) {
            if (!file_.valid(inst_id)) {
                continue;
            }
            const Inst& inst = file_.inst(inst_id);
            if (inst.kind != InstKind::LocalPlace) {
                continue;
            }
            std::vector<Operand> operands = file_.operands(inst.operands);
            if (!operands.empty()) {
                if (const auto* entity =
                        std::get_if<EntityId>(&operands[0].data)) {
                    excluded_set.insert(entity->index);
                }
            }
        }
    };
    if (file_.valid(fact_.ramp_return_block)) {
        exclude_block_locals(fact_.ramp_return_block);
    }
    if (file_.valid(fact_.alloc_failure_block)) {
        std::unordered_set<uint32_t> visited;
        std::vector<BlockId> worklist{fact_.alloc_failure_block};
        while (!worklist.empty()) {
            BlockId block_id = worklist.back();
            worklist.pop_back();
            if (!file_.valid(block_id) ||
                !visited.insert(block_id.index).second) {
                continue;
            }
            exclude_block_locals(block_id);
            const Terminator& terminator =
                file_.block(block_id).terminator;
            if (file_.valid(terminator.target)) {
                worklist.push_back(terminator.target);
            }
            if (file_.valid(terminator.false_target)) {
                worklist.push_back(terminator.false_target);
            }
        }
    }

    for (BlockId block_id : fn.blocks) {
        if (!file_.valid(block_id)) {
            continue;
        }
        const Block& block = file_.block(block_id);
        for (InstId inst_id : block.instructions) {
            if (!file_.valid(inst_id)) {
                continue;
            }
            const Inst& inst = file_.inst(inst_id);
            switch (inst.kind) {
                case InstKind::CoroBegin:
                    harvest_.coro_begin = inst_id;
                    break;
                case InstKind::CoroPromisePlace:
                    harvest_.promise_place = inst_id;
                    break;
                case InstKind::CoroFrameSize:
                    harvest_.frame_sizes.push_back(inst_id);
                    break;
                case InstKind::CoroFrameAlign:
                    harvest_.frame_aligns.push_back(inst_id);
                    break;
                case InstKind::LocalPlace: {
                    std::vector<Operand> operands =
                        file_.operands(inst.operands);
                    if (!operands.empty()) {
                        if (const auto* entity =
                                std::get_if<EntityId>(&operands[0].data)) {
                            if (!excluded_set.contains(entity->index) &&
                                promoted_set.insert(entity->index).second) {
                                harvest_.promoted.push_back(*entity);
                            }
                        }
                    }
                    break;
                }
                case InstKind::StackAlloc:
                    fail("a runtime-sized local in a coroutine is not "
                         "supported yet",
                         inst.loc);
                    break;
                default:
                    break;
            }
        }
        switch (block.terminator.kind) {
            case TerminatorKind::CoroSuspend: {
                SuspendPoint point;
                point.block = block_id;
                if (const auto* payload = std::get_if<CoroSuspendPayload>(
                        &file_.payload(block.terminator.payload_index))) {
                    point.payload = *payload;
                }
                for (InstId inst_id : block.instructions) {
                    if (file_.valid(inst_id) &&
                        file_.inst(inst_id).kind == InstKind::CoroTransfer) {
                        point.transfer = inst_id;
                    }
                }
                harvest_.suspends.push_back(point);
                break;
            }
            case TerminatorKind::CoroEnd:
                harvest_.end_blocks.push_back(block_id);
                break;
            default:
                break;
        }
    }
    if (!file_.valid(harvest_.coro_begin) ||
        !file_.valid(harvest_.promise_place)) {
        fail("coroutine function is missing its frame preamble", loc_);
    }
    return !failed_;
}

bool CoroSplitter::analyze_spills() {

    const Function& fn = file_.function(function_id_);
    std::unordered_map<uint32_t, size_t> block_index;
    for (BlockId block_id : fn.blocks) {
        block_index.emplace(block_id.index, block_index.size());
    }
    size_t count = fn.blocks.size();
    if (count == 0 || harvest_.suspends.empty()) {
        return !failed_;
    }
    size_t root = count;
    std::vector<std::vector<size_t>> predecessors(count + 1);
    auto add_edge = [&](size_t from, BlockId to) {
        if (!file_.valid(to)) {
            return;
        }
        auto found = block_index.find(to.index);
        if (found != block_index.end()) {
            predecessors[found->second].push_back(from);
        }
    };
    for (BlockId block_id : fn.blocks) {
        const Block& block = file_.block(block_id);
        size_t node = block_index.at(block_id.index);
        add_edge(node, block.unwind_target);
        add_edge(node, block.terminator.target);
        add_edge(node, block.terminator.false_target);
        if (block.terminator.kind == TerminatorKind::Switch) {
            if (const auto* payload = std::get_if<SwitchTerminatorPayload>(
                    &file_.payload(block.terminator.payload_index))) {
                for (const SwitchCaseRange& case_range : payload->cases) {
                    add_edge(node, case_range.target);
                }
            }
        }
    }
    for (const SuspendPoint& suspend : harvest_.suspends) {
        const Block& block = file_.block(suspend.block);
        add_edge(root, block.terminator.target);
        add_edge(root, block.terminator.false_target);
    }

    std::vector<bool> reachable(count + 1, false);
    {
        std::vector<size_t> successors_scratch;
        std::vector<std::vector<size_t>> successors(count + 1);
        for (size_t node = 0; node <= count; ++node) {
            for (size_t pred : predecessors[node]) {
                successors[pred].push_back(node);
            }
        }
        std::vector<size_t> worklist{root};
        reachable[root] = true;
        while (!worklist.empty()) {
            size_t node = worklist.back();
            worklist.pop_back();
            for (size_t next : successors[node]) {
                if (!reachable[next]) {
                    reachable[next] = true;
                    worklist.push_back(next);
                }
            }
        }
        (void)successors_scratch;
    }

    std::vector<std::vector<bool>> dominates(
        count + 1, std::vector<bool>(count + 1, true));
    dominates[root].assign(count + 1, false);
    dominates[root][root] = true;
    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t node = 0; node < count; ++node) {
            if (!reachable[node]) {
                continue;
            }
            std::vector<bool> merged(count + 1, true);
            bool has_predecessor = false;
            for (size_t pred : predecessors[node]) {
                if (!reachable[pred]) {
                    continue;
                }
                has_predecessor = true;
                for (size_t bit = 0; bit <= count; ++bit) {
                    merged[bit] = merged[bit] && dominates[pred][bit];
                }
            }
            if (!has_predecessor) {
                merged.assign(count + 1, false);
            }
            merged[node] = true;
            if (merged != dominates[node]) {
                dominates[node] = std::move(merged);
                changed = true;
            }
        }
    }

    std::unordered_map<uint32_t, size_t> def_block;
    for (BlockId block_id : fn.blocks) {
        size_t node = block_index.at(block_id.index);
        const Block& block = file_.block(block_id);
        for (InstId inst_id : block.parameters) {
            def_block.emplace(inst_id.index, node);
        }
        for (InstId inst_id : block.instructions) {
            def_block.emplace(inst_id.index, node);
        }
    }

    std::unordered_set<uint32_t> exempt;
    exempt.insert(harvest_.coro_begin.index);
    exempt.insert(harvest_.promise_place.index);
    std::unordered_set<uint32_t> promoted_entities;
    for (EntityId entity : harvest_.promoted) {
        promoted_entities.insert(entity.index);
    }
    auto is_promoted_local_place = [&](const Inst& inst) {
        if (inst.kind != InstKind::LocalPlace) {
            return false;
        }
        std::vector<Operand> operands = file_.operands(inst.operands);
        if (operands.empty()) {
            return false;
        }
        const auto* entity = std::get_if<EntityId>(&operands[0].data);
        return entity && promoted_entities.contains(entity->index);
    };

    std::unordered_set<uint32_t> spilled;
    for (BlockId block_id : fn.blocks) {
        const Block& block = file_.block(block_id);
        size_t node = block_index.at(block_id.index);
        auto consider = [&](OperandRange range) {
            for (const Operand& operand : file_.operands(range)) {
                const auto* value = std::get_if<ValueRef>(&operand.data);
                if (!value || !file_.valid(value->inst) ||
                    exempt.contains(value->inst.index)) {
                    continue;
                }
                auto def = def_block.find(value->inst.index);
                if (def == def_block.end() || def->second == node) {
                    continue;
                }
                if (!reachable[node] || dominates[node][def->second]) {
                    continue;
                }
                const Inst& def_inst = file_.inst(value->inst);
                if (is_promoted_local_place(def_inst)) {
                    continue;
                }
                if (!spilled.insert(value->inst.index).second) {
                    continue;
                }
                cir::TypeId type = def_inst.result_type;
                bool place_like = file_.valid(type) &&
                    file_.type(file_.resolved_type(type)).kind ==
                        TypeKind::Place;
                if (place_like || !file_.valid(type) ||
                    !size_align_of_type(file_, type).has_value()) {

                    fail("a value live across a coroutine suspension is "
                         "not supported yet (" +
                             std::string(inst_mnemonic(def_inst.kind)) + ")",
                         def_inst.loc);
                    continue;
                }
                spilled_values_.push_back(value->inst);
            }
        };
        for (InstId inst_id : block.instructions) {
            consider(file_.inst(inst_id).operands);
        }
        consider(block.terminator.operands);
    }
    return !failed_;
}

bool CoroSplitter::build_frame() {
    const Function& fn = file_.function(function_id_);
    const Entity& fn_entity = file_.entity(fn.entity);
    std::string base_name = std::string(file_.name(fn_entity.name));

    frame_record_ = builder_.add_entity(EntityKind::Record,
                                        base_name + ".coro.frame",
                                        TypeId{}, {}, loc_);
    file_.entity_mut(frame_record_).is_definition = true;
    file_.entity_mut(frame_record_).linkage = LinkageKind::Internal;
    frame_type_ = builder_.record_type(frame_record_, base_name + ".coro.frame");
    file_.entity_mut(frame_record_).type = frame_type_;
    frame_pointer_type_ = builder_.pointer_type(frame_type_);
    void_pointer_type_ = builder_.pointer_type(builder_.void_type());
    resume_pointer_type_ = builder_.pointer_type(
        builder_.function_type(builder_.void_type(), {void_pointer_type_}));
    state_type_ = file_.builtin_type(BuiltinTypeKind::UInt);

    size_t pointer_bytes =
        size_align_of_type(file_, void_pointer_type_)->size_bytes;

    RecordFacts facts;
    facts.entity = frame_record_;
    facts.type = file_.type_ref(frame_type_);
    facts.kind = RecordKind::Struct;
    facts.is_incomplete = false;

    size_t offset = 0;
    size_t max_align = pointer_bytes;
    auto add_field = [&](std::string name, TypeRef type, size_t size,
                         size_t align) -> FrameField {
        EntityId entity = builder_.add_entity(EntityKind::Field,
                                              std::move(name), type.type,
                                              frame_record_, loc_);
        offset = align_up(offset, align);
        RecordFieldFact fact;
        fact.name = file_.entity(entity).name;
        fact.entity = entity;
        fact.type = type;
        fact.offset = offset;
        facts.fields.push_back(fact);
        FrameField field{entity, type, offset};
        fields_by_entity_.emplace(entity.index, field);
        offset += size;
        max_align = std::max(max_align, align);
        return field;
    };

    TypeRef header_ref = file_.type_ref(resume_pointer_type_);
    resume_field_ = add_field("__coro_resume", header_ref, pointer_bytes,
                              pointer_bytes);
    destroy_field_ = add_field("__coro_destroy", header_ref, pointer_bytes,
                               pointer_bytes);
    auto promise_layout = size_align_of_type(file_, fact_.promise_type);
    if (!promise_layout.has_value()) {
        fail("coroutine promise type has no computable layout", loc_);
        return false;
    }
    promise_field_ = add_field("__coro_promise",
                               file_.type_ref(fact_.promise_type),
                               promise_layout->size_bytes,
                               promise_layout->alignment_bytes);
    auto state_layout = size_align_of_type(file_, state_type_);
    state_field_ = add_field("__coro_state", file_.type_ref(state_type_),
                             state_layout->size_bytes,
                             state_layout->alignment_bytes);

    for (EntityId entity : harvest_.promoted) {
        const Entity& record = file_.entity(entity);
        TypeId entity_type = record.type;
        auto layout = size_align_of_type(file_, entity_type);
        if (!layout.has_value()) {
            fail("a coroutine local has no computable layout; this shape is "
                 "not supported yet",
                 record.loc);
            return false;
        }
        TypeRef type = file_.type_ref(entity_type);
        type.qualifiers |= record.qualifiers;
        FrameField field = add_field(
            "__coro_local." + std::string(file_.name(record.name)) + "." +
                std::to_string(entity.index),
            type, layout->size_bytes, layout->alignment_bytes);
        entity_fields_.emplace(entity.index, field);
    }

    for (InstId value : spilled_values_) {
        const Inst& def_inst = file_.inst(value);
        auto layout = size_align_of_type(file_, def_inst.result_type);
        if (!layout.has_value()) {
            continue;
        }
        FrameField field = add_field(
            "__coro_spill." + std::to_string(value.index),
            file_.type_ref(def_inst.result_type), layout->size_bytes,
            layout->alignment_bytes);
        spill_fields_.emplace(value.index, field);
    }

    frame_align_ = max_align;
    frame_size_ = align_up(offset, max_align);
    facts.size_bits = frame_size_ * 8;
    facts.alignment = frame_align_;
    file_.set_record_facts(frame_record_, std::move(facts));
    return !failed_;
}

void CoroSplitter::rewrite_shared_body() {
    Function& fn = file_.function_mut(function_id_);

    BlockId begin_block{};
    for (BlockId block_id : fn.blocks) {
        const Block& block = file_.block(block_id);
        for (InstId inst_id : block.instructions) {
            if (file_.valid(inst_id) &&
                file_.inst(inst_id).kind == InstKind::CoroBegin) {
                begin_block = block_id;
                break;
            }
        }
        if (file_.valid(begin_block)) {
            break;
        }
    }

    std::vector<BlockId> rewrite_order;
    rewrite_order.reserve(fn.blocks.size());
    if (file_.valid(begin_block)) {
        rewrite_order.push_back(begin_block);
    }
    for (BlockId block_id : fn.blocks) {
        if (block_id != begin_block) {
            rewrite_order.push_back(block_id);
        }
    }
    for (BlockId block_id : rewrite_order) {
        Block& block = file_.block_mut(block_id);
        std::vector<InstId> rebuilt;
        rebuilt.reserve(block.instructions.size());
        for (InstId inst_id : block.instructions) {
            if (!file_.valid(inst_id)) {
                continue;
            }
            Inst& inst = file_.inst_mut(inst_id);
            SrcLoc loc = inst.loc;
            switch (inst.kind) {
                case InstKind::CoroBegin: {

                    std::vector<Operand> operands =
                        file_.operands(inst.operands);
                    CastPayload cast_kind;
                    cast_kind.kind = "value";
                    inst.kind = InstKind::Cast;
                    inst.payload_index =
                        file_.add_payload(InstPayload{std::move(cast_kind)});
                    std::vector<Operand> cast_operands;
                    cast_operands.push_back(
                        Operand::type(file_.type_ref(inst.result_type)));
                    if (!operands.empty()) {
                        cast_operands.push_back(operands[0]);
                    }
                    inst.operands = file_.add_operands(cast_operands);
                    rebuilt.push_back(inst_id);

                    std::vector<InstId> chain_ids;
                    ramp_frame_place_ =
                        make_frame_object_place(inst_id, chain_ids, loc);
                    for (InstId id : chain_ids) {
                        rebuilt.push_back(id);
                    }
                    break;
                }
                case InstKind::CoroPromisePlace: {
                    inst.kind = InstKind::FieldAddr;
                    inst.operands = file_.add_operands(
                        {Operand::value(ramp_frame_place_),
                         Operand::entity(promise_field_.field)});
                    rebuilt.push_back(inst_id);
                    break;
                }
                case InstKind::CoroFrameSize: {
                    LiteralPayload literal;
                    IntegerTypeShape shape =
                        integer_shape_for_type(file_, inst.result_type);
                    literal.value = IntegerValue::from_unsigned(
                        frame_size_, shape.bit_width).cast(
                            shape.bit_width, shape.is_unsigned);
                    literal.spelling = std::to_string(frame_size_);
                    inst.kind = InstKind::IntegerLiteral;
                    inst.operands = {};
                    inst.payload_index =
                        file_.add_payload(InstPayload{std::move(literal)});
                    rebuilt.push_back(inst_id);
                    break;
                }
                case InstKind::CoroFrameAlign: {
                    LiteralPayload literal;
                    IntegerTypeShape shape =
                        integer_shape_for_type(file_, inst.result_type);
                    literal.value = IntegerValue::from_unsigned(
                        frame_align_, shape.bit_width).cast(
                            shape.bit_width, shape.is_unsigned);
                    literal.spelling = std::to_string(frame_align_);
                    inst.kind = InstKind::IntegerLiteral;
                    inst.operands = {};
                    inst.payload_index =
                        file_.add_payload(InstPayload{std::move(literal)});
                    rebuilt.push_back(inst_id);
                    break;
                }
                case InstKind::CoroSave: {
                    const auto* payload = std::get_if<CoroSuspendPayload>(
                        &file_.payload(inst.payload_index));
                    uint32_t index = payload ? payload->index : kInvalidIndex;
                    bool is_final =
                        payload && payload->kind == CoroSaveKind::Final;
                    InstId index_value = make_integer_literal(
                        static_cast<int64_t>(index), state_type_, loc);
                    rebuilt.push_back(index_value);
                    InstId state_addr =
                        make_field_addr(ramp_frame_place_, state_field_, loc);
                    rebuilt.push_back(state_addr);

                    Inst& save = file_.inst_mut(inst_id);
                    save.kind = InstKind::Store;
                    save.payload_index = 0;
                    save.operands =
                        file_.add_value_operands({state_addr, index_value});
                    rebuilt.push_back(inst_id);
                    if (is_final) {

                        InstId null_pointer = make_integer_literal(
                            0, resume_pointer_type_, loc);
                        rebuilt.push_back(null_pointer);
                        InstId resume_addr = make_field_addr(
                            ramp_frame_place_, resume_field_, loc);
                        rebuilt.push_back(resume_addr);
                        rebuilt.push_back(
                            make_store(resume_addr, null_pointer, loc));
                    }
                    break;
                }
                case InstKind::LocalPlace: {
                    std::vector<Operand> operands =
                        file_.operands(inst.operands);
                    const auto* entity = operands.empty()
                        ? nullptr
                        : std::get_if<EntityId>(&operands[0].data);
                    auto found = entity
                        ? entity_fields_.find(entity->index)
                        : entity_fields_.end();
                    if (found != entity_fields_.end()) {
                        inst.kind = InstKind::FieldAddr;
                        inst.operands = file_.add_operands(
                            {Operand::value(ramp_frame_place_),
                             Operand::entity(found->second.field)});
                    }
                    rebuilt.push_back(inst_id);
                    break;
                }
                case InstKind::LifetimeStart:
                case InstKind::LifetimeEnd:

                    break;
                default:
                    rebuilt.push_back(inst_id);
                    break;
            }
        }
        block.instructions = std::move(rebuilt);
    }
    (void)begin_block;
}

void CoroSplitter::apply_spills() {

    if (spill_fields_.empty()) {
        return;
    }
    Function& fn = file_.function_mut(function_id_);
    std::unordered_map<uint32_t, uint32_t> def_block;
    for (BlockId block_id : fn.blocks) {
        const Block& block = file_.block(block_id);
        for (InstId inst_id : block.parameters) {
            def_block.emplace(inst_id.index, block_id.index);
        }
        for (InstId inst_id : block.instructions) {
            def_block.emplace(inst_id.index, block_id.index);
        }
    }

    for (BlockId block_id : fn.blocks) {
        std::vector<InstId> rebuilt;

        auto reload_for = [&](OperandRange range, SrcLoc loc)
            -> std::vector<Operand> {
            std::vector<Operand> operands = file_.operands(range);
            bool changed = false;
            for (Operand& operand : operands) {
                auto* value = std::get_if<ValueRef>(&operand.data);
                if (!value) {
                    continue;
                }
                auto field = spill_fields_.find(value->inst.index);
                if (field == spill_fields_.end()) {
                    continue;
                }
                auto def = def_block.find(value->inst.index);
                if (def != def_block.end() &&
                    def->second == block_id.index) {
                    continue;
                }
                InstId addr = make_field_addr(ramp_frame_place_,
                                              field->second, loc);
                rebuilt.push_back(addr);
                InstId reload = make_load(addr, field->second.type, loc);
                rebuilt.push_back(reload);
                *value = ValueRef(reload);
                changed = true;
            }
            if (!changed) {
                operands.clear();
            }
            return operands;
        };

        const std::vector<InstId> original =
            file_.block(block_id).instructions;
        for (InstId inst_id : original) {
            SrcLoc loc = file_.inst(inst_id).loc;
            std::vector<Operand> remapped =
                reload_for(file_.inst(inst_id).operands, loc);
            if (!remapped.empty()) {
                file_.inst_mut(inst_id).operands =
                    file_.add_operands(remapped);
            }
            rebuilt.push_back(inst_id);
            auto field = spill_fields_.find(inst_id.index);
            if (field != spill_fields_.end()) {
                InstId addr = make_field_addr(ramp_frame_place_,
                                              field->second, loc);
                rebuilt.push_back(addr);
                rebuilt.push_back(make_store(addr, inst_id, loc));
            }
        }
        {
            SrcLoc loc = file_.block(block_id).terminator.loc;
            std::vector<Operand> remapped = reload_for(
                file_.block(block_id).terminator.operands, loc);
            if (!remapped.empty()) {
                file_.block_mut(block_id).terminator.operands =
                    file_.add_operands(remapped);
            }
        }
        file_.block_mut(block_id).instructions = std::move(rebuilt);
    }
}

bool CoroSplitter::build_clone(bool is_destroy,
                               EntityId& entity_out,
                               FunctionId& function_out) {

    const Function fn = file_.function(function_id_);
    const Entity& fn_entity = file_.entity(fn.entity);

    std::string base = std::string(file_.name(fn_entity.name));
    for (char& c : base) {
        bool clean = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') || c == '_' || c == '$' || c == '.';
        if (!clean) {
            c = '_';
        }
    }
    std::string name =
        base + (is_destroy ? ".coro.destroy" : ".coro.resume");

    TypeId void_type = builder_.void_type();
    TypeId fn_type =
        builder_.function_type(void_type, {void_pointer_type_});
    EntityId clone_entity = builder_.add_entity(EntityKind::Function, name,
                                                fn_type, {}, loc_);
    file_.entity_mut(clone_entity).is_definition = true;
    file_.entity_mut(clone_entity).linkage = LinkageKind::Internal;
    EntityId param_entity = builder_.add_entity(
        EntityKind::Parameter, name + ".frame", void_pointer_type_,
        clone_entity, loc_, StorageDuration::Parameter);
    auto start = builder_.begin_function(
        clone_entity, void_type, {{param_entity, void_pointer_type_}}, loc_);
    entity_out = clone_entity;
    function_out = start.function;

    builder_.switch_to_block(start.entry);
    InstId frame_pointer = start.parameters.empty()
        ? InstId{}
        : start.parameters[0].value.inst;
    std::vector<InstId> entry_ids;
    InstId frame_place =
        make_frame_object_place(frame_pointer, entry_ids, loc_);
    InstId state_addr = make_field_addr(frame_place, state_field_, loc_);
    entry_ids.push_back(state_addr);
    Block& entry = file_.block_mut(start.entry);
    for (InstId id : entry_ids) {
        entry.instructions.push_back(id);
    }
    InstId state = builder_.load(state_addr, loc_);

    std::unordered_map<uint32_t, InstId> inst_map;
    std::unordered_map<uint32_t, BlockId> block_map;
    inst_map.emplace(harvest_.coro_begin.index, frame_pointer);
    inst_map.emplace(ramp_frame_place_.index, frame_place);

    std::unordered_map<uint32_t, InstId> entry_field_addrs;
    auto entry_addr_for_field = [&](EntityId field) -> InstId {
        auto known = fields_by_entity_.find(field.index);
        if (known == fields_by_entity_.end()) {
            return InstId{};
        }
        auto found = entry_field_addrs.find(field.index);
        if (found != entry_field_addrs.end()) {
            return found->second;
        }
        InstId addr = make_field_addr(frame_place, known->second, loc_);
        file_.block_mut(start.entry).instructions.push_back(addr);
        entry_field_addrs.emplace(field.index, addr);
        return addr;
    };
    for (BlockId block_id : fn.blocks) {
        for (InstId inst_id : file_.block(block_id).instructions) {
            if (!file_.valid(inst_id)) {
                continue;
            }
            const Inst& inst = file_.inst(inst_id);
            if (inst.kind != InstKind::FieldAddr) {
                continue;
            }
            std::vector<Operand> operands = file_.operands(inst.operands);
            if (operands.size() < 2) {
                continue;
            }
            const auto* base = std::get_if<ValueRef>(&operands[0].data);
            const auto* field = std::get_if<EntityId>(&operands[1].data);
            if (!base || !field || base->inst != ramp_frame_place_) {
                continue;
            }
            InstId entry_addr = entry_addr_for_field(*field);
            if (file_.valid(entry_addr)) {
                inst_map.emplace(inst_id.index, entry_addr);
            }
        }
    }

    Function& clone_fn = file_.function_mut(start.function);
    for (BlockId block_id : fn.blocks) {
        BlockId clone_block = builder_.create_detached_block(
            std::string(file_.name(file_.block(block_id).name)));
        block_map.emplace(block_id.index, clone_block);
        clone_fn.blocks.push_back(clone_block);

        for (InstId parameter : file_.block(block_id).parameters) {
            if (!file_.valid(parameter)) {
                continue;
            }
            InstId cloned = builder_.add_block_parameter(
                clone_block, file_.inst(parameter).result_type, {},
                file_.inst(parameter).loc);
            inst_map.emplace(parameter.index, cloned);
        }
    }

    auto map_value = [&](ValueRef ref) -> ValueRef {
        auto found = inst_map.find(ref.inst.index);
        return found != inst_map.end() ? ValueRef(found->second) : ref;
    };
    auto map_block = [&](BlockId id) -> BlockId {
        if (!file_.valid(id)) {
            return id;
        }
        auto found = block_map.find(id.index);
        return found != block_map.end() ? found->second : id;
    };

    for (BlockId block_id : fn.blocks) {
        const Block& source = file_.block(block_id);
        BlockId clone_id = block_map.at(block_id.index);

        std::vector<InstId> cloned_instructions;
        cloned_instructions.reserve(source.instructions.size());
        for (InstId inst_id : source.instructions) {
            if (!file_.valid(inst_id)) {
                continue;
            }
            if (file_.inst(inst_id).kind == InstKind::CoroTransfer) {

                continue;
            }
            Inst clone = file_.inst(inst_id);
            std::vector<Operand> operands = file_.operands(clone.operands);
            for (Operand& operand : operands) {
                if (auto* value = std::get_if<ValueRef>(&operand.data)) {
                    *value = map_value(*value);
                }
            }
            clone.operands = file_.add_operands(operands);
            if (clone.place_fact.valid()) {

                PlaceFact fact = file_.place_fact(clone.place_fact);
                if (fact.base.valid()) {
                    auto found = inst_map.find(fact.base.index);
                    if (found != inst_map.end()) {
                        fact.base = found->second;
                    }
                }
                clone.place_fact = file_.add_place_fact(std::move(fact));
            }
            InstId clone_inst = file_.add_inst(clone);
            if (clone.place_fact.valid()) {
                file_.place_fact_mut(clone.place_fact).source = clone_inst;
            }
            inst_map.emplace(inst_id.index, clone_inst);
            cloned_instructions.push_back(clone_inst);
        }

        Block& target = file_.block_mut(clone_id);
        target.instructions = std::move(cloned_instructions);
        target.unwind_target = map_block(source.unwind_target);

        Terminator terminator = source.terminator;
        std::vector<Operand> term_operands =
            file_.operands(terminator.operands);
        for (Operand& operand : term_operands) {
            if (auto* value = std::get_if<ValueRef>(&operand.data)) {
                *value = map_value(*value);
            }
        }
        terminator.operands = file_.add_operands(term_operands);
        terminator.target = map_block(terminator.target);
        terminator.false_target = map_block(terminator.false_target);
        if (terminator.kind == TerminatorKind::Switch) {
            if (const auto* payload = std::get_if<SwitchTerminatorPayload>(
                    &file_.payload(terminator.payload_index))) {
                SwitchTerminatorPayload remapped = *payload;
                for (SwitchCaseRange& case_range : remapped.cases) {
                    case_range.target = map_block(case_range.target);
                }
                terminator.payload_index =
                    file_.add_payload(InstPayload{std::move(remapped)});
            }
        }

        if (terminator.kind == TerminatorKind::CoroSuspend ||
            terminator.kind == TerminatorKind::CoroEnd) {
            const SuspendPoint* transfer_point = nullptr;
            if (terminator.kind == TerminatorKind::CoroSuspend) {
                for (const SuspendPoint& suspend : harvest_.suspends) {
                    if (suspend.block == block_id &&
                        file_.valid(suspend.transfer)) {
                        transfer_point = &suspend;
                        break;
                    }
                }
            }
            if (transfer_point) {
                std::vector<Operand> marker_operands = file_.operands(
                    file_.inst(transfer_point->transfer).operands);
                ValueRef target_ref{};
                if (!marker_operands.empty()) {
                    if (const auto* value =
                            std::get_if<ValueRef>(&marker_operands[0].data)) {
                        target_ref = map_value(*value);
                    }
                }
                SrcLoc transfer_loc = source.terminator.loc;
                std::vector<InstId> added;
                InstId fn_value = make_resume_slot_load(target_ref.inst,
                                                        added, transfer_loc);
                added.push_back(make_resume_call(fn_value, target_ref.inst,
                                                 /*must_tail=*/true,
                                                 transfer_loc));
                Block& clone_block = file_.block_mut(clone_id);
                for (InstId id : added) {
                    clone_block.instructions.push_back(id);
                }

                clone_block.unwind_target = {};
            }
            terminator = Terminator{};
            terminator.kind = TerminatorKind::Return;
            terminator.loc = source.terminator.loc;
        }
        file_.block_mut(clone_id).terminator = terminator;
    }

    std::vector<SwitchCaseRange> cases;
    for (const SuspendPoint& suspend : harvest_.suspends) {
        const Block& suspend_block = file_.block(suspend.block);
        BlockId successor = is_destroy
            ? suspend_block.terminator.false_target
            : suspend_block.terminator.target;
        if (!is_destroy && suspend.payload.kind == CoroSaveKind::Final) {

            continue;
        }
        SwitchCaseRange case_range;
        case_range.low = static_cast<int64_t>(suspend.payload.index);
        case_range.high = case_range.low;
        case_range.target = map_block(successor);
        case_range.loc = loc_;
        cases.push_back(case_range);
    }
    BlockId default_block = builder_.create_detached_block(
        is_destroy ? "coro.destroy.invalid" : "coro.resume.invalid");
    builder_.unreachable_from(default_block, loc_);
    clone_fn.blocks.push_back(default_block);
    builder_.switch_branch_from(start.entry, state,
                                file_.type_ref(state_type_), default_block,
                                std::move(cases), loc_);
    return !failed_;
}

void CoroSplitter::rewrite_ramp() {
    Function& fn = file_.function_mut(function_id_);
    for (BlockId block_id : fn.blocks) {
        if (file_.block(block_id).terminator.kind !=
                TerminatorKind::CoroSuspend &&
            file_.block(block_id).terminator.kind != TerminatorKind::CoroEnd) {
            continue;
        }
        const SuspendPoint* transfer_point = nullptr;
        for (const SuspendPoint& suspend : harvest_.suspends) {
            if (suspend.block == block_id && file_.valid(suspend.transfer)) {
                transfer_point = &suspend;
                break;
            }
        }
        SrcLoc loc = file_.block(block_id).terminator.loc;
        if (transfer_point) {

            std::vector<Operand> marker_operands = file_.operands(
                file_.inst(transfer_point->transfer).operands);
            InstId target{};
            if (!marker_operands.empty()) {
                if (const auto* value =
                        std::get_if<ValueRef>(&marker_operands[0].data)) {
                    target = value->inst;
                }
            }
            CastPayload cast_kind;
            cast_kind.kind = "value";
            Inst& marker = file_.inst_mut(transfer_point->transfer);
            marker.kind = InstKind::Cast;
            marker.result_type = void_pointer_type_;
            marker.payload_index =
                file_.add_payload(InstPayload{std::move(cast_kind)});
            marker.operands = file_.add_operands(
                {Operand::type(file_.type_ref(void_pointer_type_)),
                 Operand::value(target)});
            std::vector<InstId> added;
            InstId fn_value = make_resume_slot_load(target, added, loc);
            added.push_back(make_resume_call(fn_value, target,
                                             /*must_tail=*/false, loc));
            Block& transfer_block = file_.block_mut(block_id);
            for (InstId id : added) {
                transfer_block.instructions.push_back(id);
            }

            transfer_block.unwind_target = {};
        }

        Terminator terminator;
        terminator.kind = TerminatorKind::Branch;
        terminator.target = fact_.ramp_return_block;
        terminator.loc = loc;
        file_.block_mut(block_id).terminator = terminator;
    }
}

void CoroSplitter::prune_unreachable(FunctionId function_id) {

    Function& fn = file_.function_mut(function_id);
    auto successors_of = [&](BlockId id) {
        std::vector<BlockId> out;
        const Block& block = file_.block(id);
        auto add = [&](BlockId target) {
            if (file_.valid(target)) {
                out.push_back(target);
            }
        };
        add(block.terminator.target);
        add(block.terminator.false_target);
        if (block.terminator.kind == TerminatorKind::Switch) {
            if (const auto* payload = std::get_if<SwitchTerminatorPayload>(
                    &file_.payload(block.terminator.payload_index))) {
                for (const SwitchCaseRange& case_range : payload->cases) {
                    add(case_range.target);
                }
            }
        }
        add(block.unwind_target);
        return out;
    };
    struct WalkFrame {
        BlockId block;
        size_t next = 0;
        std::vector<BlockId> successors;
    };
    std::unordered_set<uint32_t> visited;
    std::vector<BlockId> postorder;
    postorder.reserve(fn.blocks.size());
    std::vector<WalkFrame> stack;
    if (file_.valid(fn.entry_block) &&
        visited.insert(fn.entry_block.index).second) {
        stack.push_back(
            {fn.entry_block, 0, successors_of(fn.entry_block)});
    }
    while (!stack.empty()) {
        WalkFrame& frame = stack.back();
        if (frame.next < frame.successors.size()) {
            BlockId next = frame.successors[frame.next++];
            if (visited.insert(next.index).second) {
                stack.push_back({next, 0, successors_of(next)});
            }
            continue;
        }
        postorder.push_back(frame.block);
        stack.pop_back();
    }
    fn.blocks.assign(postorder.rbegin(), postorder.rend());
}

bool CoroSplitter::validate_values(FunctionId function_id) {
    // The coroutine-frame ABI invariant requires SSA dominance within every
    // clone; values crossing suspension without frame storage must diagnose.
    const Function& fn = file_.function(function_id);
    std::unordered_map<uint32_t, size_t> block_index;
    for (BlockId block_id : fn.blocks) {
        block_index.emplace(block_id.index, block_index.size());
    }
    size_t count = fn.blocks.size();
    if (count == 0) {
        return !failed_;
    }

    std::vector<std::vector<size_t>> predecessors(count);
    auto add_edge = [&](BlockId from, BlockId to) {
        if (!file_.valid(to)) {
            return;
        }
        auto found = block_index.find(to.index);
        auto from_found = block_index.find(from.index);
        if (found != block_index.end() &&
            from_found != block_index.end()) {
            predecessors[found->second].push_back(from_found->second);
        }
    };
    for (BlockId block_id : fn.blocks) {
        const Block& block = file_.block(block_id);
        add_edge(block_id, block.unwind_target);
        add_edge(block_id, block.terminator.target);
        add_edge(block_id, block.terminator.false_target);
        if (block.terminator.kind == TerminatorKind::Switch) {
            if (const auto* payload = std::get_if<SwitchTerminatorPayload>(
                    &file_.payload(block.terminator.payload_index))) {
                for (const SwitchCaseRange& case_range : payload->cases) {
                    add_edge(block_id, case_range.target);
                }
            }
        }
    }
    size_t entry = block_index.count(fn.entry_block.index)
        ? block_index.at(fn.entry_block.index)
        : 0;
    std::vector<std::vector<bool>> dominates(
        count, std::vector<bool>(count, true));
    dominates[entry].assign(count, false);
    dominates[entry][entry] = true;
    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t node = 0; node < count; ++node) {
            if (node == entry) {
                continue;
            }
            std::vector<bool> merged(count, true);
            bool has_predecessor = false;
            for (size_t pred : predecessors[node]) {
                has_predecessor = true;
                for (size_t bit = 0; bit < count; ++bit) {
                    merged[bit] = merged[bit] && dominates[pred][bit];
                }
            }
            if (!has_predecessor) {
                merged.assign(count, false);
            }
            merged[node] = true;
            if (merged != dominates[node]) {
                dominates[node] = std::move(merged);
                changed = true;
            }
        }
    }

    std::unordered_map<uint32_t, std::pair<size_t, size_t>> defs;
    for (const FunctionParameter& parameter : fn.parameters) {
        if (file_.valid(parameter.value.inst)) {
            defs.emplace(parameter.value.inst.index,
                         std::make_pair(entry, size_t{0}));
        }
    }
    for (BlockId block_id : fn.blocks) {
        const Block& block = file_.block(block_id);
        size_t node = block_index.at(block_id.index);
        size_t position = 0;
        for (InstId inst_id : block.parameters) {
            defs.emplace(inst_id.index, std::make_pair(node, position));
        }
        for (InstId inst_id : block.instructions) {
            ++position;
            defs.emplace(inst_id.index, std::make_pair(node, position));
        }
    }

    for (BlockId block_id : fn.blocks) {
        const Block& block = file_.block(block_id);
        size_t node = block_index.at(block_id.index);
        size_t position = 0;
        auto check_operands = [&](OperandRange range, size_t use_position) {
            for (const Operand& operand : file_.operands(range)) {
                const auto* value = std::get_if<ValueRef>(&operand.data);
                if (!value || !file_.valid(value->inst)) {
                    continue;
                }
                auto def = defs.find(value->inst.index);
                bool ok = def != defs.end();
                if (ok) {
                    if (def->second.first == node) {
                        ok = def->second.second < use_position ||
                            def->second.second == 0;
                    } else {
                        ok = dominates[node][def->second.first];
                    }
                }
                if (!ok) {
                    fail("a value live across a coroutine suspension is not "
                         "supported yet (" +
                             std::string(inst_mnemonic(
                                 file_.inst(value->inst).kind)) +
                             ")",
                         file_.inst(value->inst).loc);
                    return false;
                }
            }
            return true;
        };
        for (InstId inst_id : block.instructions) {
            ++position;
            if (!check_operands(file_.inst(inst_id).operands, position)) {
                return false;
            }
        }
        if (!check_operands(block.terminator.operands, position + 1)) {
            return false;
        }
    }
    return !failed_;
}

bool CoroSplitter::run() {

    if (file_.valid(fact_.eh_action_block)) {
        Function& fn = file_.function_mut(function_id_);
        for (BlockId block_id : fn.blocks) {
            if (!file_.valid(block_id)) {
                continue;
            }

            for (InstId inst_id : file_.block(block_id).instructions) {
                if (!file_.valid(inst_id) ||
                    file_.inst(inst_id).kind != InstKind::EhLandingPad) {
                    continue;
                }
                const auto* payload = std::get_if<EhLandingPadPayload>(
                    &file_.payload(file_.inst(inst_id).payload_index));
                if (!payload || payload->has_catch_all) {
                    continue;
                }
                EhLandingPadPayload widened = *payload;
                widened.has_catch_all = true;
                file_.inst_mut(inst_id).payload_index =
                    file_.add_payload(InstPayload{std::move(widened)});
            }
            Block& block = file_.block_mut(block_id);
            if (block.terminator.kind != TerminatorKind::Resume) {
                continue;
            }
            block.terminator.kind = TerminatorKind::Branch;
            block.terminator.target = fact_.eh_action_block;
        }
    }
    if (!harvest() || !analyze_spills() || !build_frame()) {
        return false;
    }
    rewrite_shared_body();
    apply_spills();

    EntityId resume_entity{};
    EntityId destroy_entity{};
    FunctionId resume_function{};
    FunctionId destroy_function{};
    if (!build_clone(/*is_destroy=*/false, resume_entity, resume_function) ||
        !build_clone(/*is_destroy=*/true, destroy_entity, destroy_function)) {
        return false;
    }

    {
        Function& fn = file_.function_mut(function_id_);
        for (BlockId block_id : fn.blocks) {
            Block& block = file_.block_mut(block_id);
            for (size_t i = 0; i < block.instructions.size(); ++i) {
                if (block.instructions[i] != ramp_frame_place_) {
                    continue;
                }
                std::vector<InstId> stores;
                InstId resume_pointer =
                    make_function_pointer(resume_entity, loc_);
                InstId resume_addr =
                    make_field_addr(ramp_frame_place_, resume_field_, loc_);
                stores.push_back(resume_pointer);
                stores.push_back(resume_addr);
                stores.push_back(make_store(resume_addr, resume_pointer, loc_));
                InstId destroy_pointer =
                    make_function_pointer(destroy_entity, loc_);
                InstId destroy_addr =
                    make_field_addr(ramp_frame_place_, destroy_field_, loc_);
                stores.push_back(destroy_pointer);
                stores.push_back(destroy_addr);
                stores.push_back(
                    make_store(destroy_addr, destroy_pointer, loc_));
                block.instructions.insert(block.instructions.begin() + i + 1,
                                          stores.begin(), stores.end());
                break;
            }
        }
    }

    rewrite_ramp();
    prune_unreachable(function_id_);
    prune_unreachable(resume_function);
    prune_unreachable(destroy_function);
    if (!validate_values(function_id_) || !validate_values(resume_function) ||
        !validate_values(destroy_function)) {
        return false;
    }

    CoroutineFact* fact = file_.coroutine_fact_for_function_mut(
        file_.function(function_id_).entity);
    if (fact) {
        fact->frame_record = frame_record_;
        fact->resume_function = resume_entity;
        fact->destroy_function = destroy_entity;
    }
    return !failed_;
}

} // namespace

bool split_coroutines(cir::File& file) {
    bool ok = true;

    std::vector<CoroutineFact> facts = file.coroutine_facts();
    for (const CoroutineFact& fact : facts) {
        FunctionId target{};
        for (FunctionId function_id : file.function_ids()) {
            if (file.function(function_id).entity == fact.function) {
                target = function_id;
                break;
            }
        }
        if (!file.valid(target)) {
            continue;
        }
        if (file.entity(fact.function).is_template_pattern) {
            continue;
        }
        CoroSplitter splitter(file, target, fact);
        if (!splitter.run()) {
            ok = false;
        }
    }
    if (ok) {
        file.set_coroutines_lowered(true);
    }
    return ok;
}

} // namespace aburi::cirpasses
