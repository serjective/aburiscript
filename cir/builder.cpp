#include "builder.h"
#include "layout.h"

#include <algorithm>
#include <initializer_list>
#include <utility>

namespace aburi::cir {

namespace {

LiteralByteArray literal_bytes_from_string(std::string_view value) {
    LiteralByteArray bytes;
    bytes.reserve(value.size());
    for (unsigned char byte : value) {
        bytes.push_back(byte);
    }
    return bytes;
}

std::vector<Operand> operands_from_values(std::initializer_list<InstId> values) {
    std::vector<Operand> operands;
    operands.reserve(values.size());
    for (InstId value : values) {
        operands.push_back(Operand::value(value));
    }
    return operands;
}

std::vector<Operand> operands_from_values(const std::vector<InstId>& values) {
    std::vector<Operand> operands;
    operands.reserve(values.size());
    for (InstId value : values) {
        operands.push_back(Operand::value(value));
    }
    return operands;
}

void append_value_operands(std::vector<Operand>& operands, const std::vector<InstId>& values) {
    operands.reserve(operands.size() + values.size());
    for (InstId value : values) {
        operands.push_back(Operand::value(value));
    }
}

} // namespace

Builder::Builder(File& file) : file_(file) {}

Builder::Checkpoint Builder::checkpoint() const {
    return Checkpoint{current_function_, current_block_,
                      current_unwind_target_, block_name_counts_};
}

void Builder::rollback_to(const Checkpoint& checkpoint) {
    current_function_ = checkpoint.current_function;
    current_block_ = checkpoint.current_block;
    current_unwind_target_ = checkpoint.current_unwind_target;
    block_name_counts_ = checkpoint.block_name_counts;
}

NameId Builder::unique_block_name(std::string_view name) {
    std::string base(name);
    uint32_t& count = block_name_counts_[base];
    ++count;
    if (count == 1) {
        return file_.intern_name(base);
    }
    return file_.intern_name(base + "." + std::to_string(count));
}

TypeId Builder::void_type() {
    return file_.builtin_type(BuiltinTypeKind::Void);
}

TypeId Builder::bool_type() {
    return file_.builtin_type(BuiltinTypeKind::Bool);
}

TypeId Builder::char_type() {
    return file_.builtin_type(BuiltinTypeKind::Char);
}

TypeId Builder::int_type() {
    return file_.builtin_type(BuiltinTypeKind::Int);
}

TypeId Builder::float_type() {
    return file_.builtin_type(BuiltinTypeKind::Float);
}

TypeId Builder::double_type() {
    return file_.builtin_type(BuiltinTypeKind::Double);
}

TypeId Builder::long_double_type() {
    return file_.builtin_type(BuiltinTypeKind::LongDouble);
}

TypeId Builder::usize_type() {
    return file_.builtin_type(BuiltinTypeKind::USize);
}

TypeId Builder::unknown_type() {
    return file_.unknown_type();
}

TypeId Builder::dependent_type(std::string_view name) {
    return file_.dependent_type(std::string(name));
}

TypeId Builder::pointer_type(TypeId pointee) {
    return file_.pointer_type(pointee);
}

TypeId Builder::pointer_type(TypeRef pointee) {
    return file_.pointer_type(pointee);
}

TypeId Builder::array_type(TypeId element, std::optional<size_t> size) {
    return file_.array_type(element, size);
}

TypeId Builder::place_type(TypeId object_type) {
    return file_.place_type(object_type);
}

TypeId Builder::place_type(TypeRef object_type) {
    return file_.place_type(object_type);
}

TypeId Builder::record_type(EntityId entity, std::string_view name) {
    return file_.record_type(entity, std::string(name));
}

TypeId Builder::enum_type(EntityId entity,
                          std::string_view name,
                          TypeRef underlying_type,
                          bool is_scoped,
                          bool is_incomplete,
                          bool has_fixed_underlying_type) {
    return file_.enum_type(entity,
                           std::string(name),
                           underlying_type,
                           is_scoped,
                           is_incomplete,
                           has_fixed_underlying_type);
}

TypeId Builder::complex_type(TypeRef element_type) {
    return file_.complex_type(element_type);
}

TypeId Builder::type_param_type(EntityId entity,
                                std::string_view name,
                                uint32_t index,
                                uint32_t depth,
                                bool is_parameter_pack) {
    return file_.type_param_type(entity,
                                 std::string(name),
                                 index,
                                 depth,
                                 is_parameter_pack);
}

TypeId Builder::function_type(TypeId result, const std::vector<TypeId>& params) {
    return file_.function_type(result, params);
}

EntityId Builder::add_entity(EntityKind kind,
                             std::string_view name,
                             TypeId type,
                             EntityId parent,
                             SrcLoc loc,
                             StorageDuration storage_duration,
                             MemorySpace memory_space,
                             DeclSemanticFlags decl_flags) {
    Entity entity;
    entity.kind = kind;
    entity.name = file_.intern_name(name);
    entity.type = type;
    entity.parent = parent;
    entity.storage_duration = storage_duration;
    entity.memory_space = memory_space;
    entity.decl_flags = decl_flags;
    entity.is_template_pattern = mark_template_pattern_;
    entity.loc = loc;
    return file_.add_entity(std::move(entity));
}

FunctionStart Builder::begin_function(std::string_view name,
                                      TypeId result_type,
                                      const std::vector<std::pair<std::string, TypeId>>& params,
                                      SrcLoc loc,
                                      EntityKind kind,
                                      EntityId parent) {
    std::vector<TypeId> param_types;
    param_types.reserve(params.size());
    for (const auto& param : params) {
        param_types.push_back(param.second);
    }
    TypeId fn_type = file_.function_type(result_type, param_types);
    EntityId fn_entity = add_entity(kind, name, fn_type, parent, loc);

    std::vector<std::pair<EntityId, TypeId>> param_entities;
    param_entities.reserve(params.size());
    for (const auto& param : params) {
        EntityId entity = add_entity(EntityKind::Parameter,
                                     param.first,
                                     param.second,
                                     fn_entity,
                                     loc,
                                     StorageDuration::Parameter);
        param_entities.emplace_back(entity, param.second);
    }
    return begin_function(fn_entity, result_type, param_entities, loc);
}

FunctionStart Builder::begin_function(EntityId entity,
                                      TypeId result_type,
                                      const std::vector<std::pair<EntityId, TypeId>>& params,
                                      SrcLoc loc) {
    block_name_counts_.clear();

    std::vector<TypeId> param_types;
    param_types.reserve(params.size());
    for (const auto& param : params) {
        param_types.push_back(param.second);
    }
    TypeId fn_type = file_.entity(entity).type.valid()
        ? file_.entity(entity).type
        : file_.function_type(result_type, param_types);

    Block entry;
    entry.name = unique_block_name("entry");
    BlockId entry_id = file_.add_block(std::move(entry));

    Function fn;
    fn.entity = entity;
    fn.type = fn_type;
    fn.result_type = result_type;
    fn.entry_block = entry_id;
    fn.blocks.push_back(entry_id);
    fn.loc = loc;
    FunctionId fn_id = file_.add_function(std::move(fn));
    current_function_ = fn_id;
    current_block_ = entry_id;

    FunctionStart start;
    start.function = fn_id;
    start.entity = entity;
    start.entry = entry_id;

    for (const auto& param : params) {
        InstId p = this->param(param.first, param.second, loc);
        FunctionParameter function_param;
        function_param.entity = param.first;
        function_param.value = ValueRef{p};
        file_.block_mut(entry_id).parameters.push_back(p);
        file_.function_mut(fn_id).parameters.push_back(function_param);
        start.parameters.push_back(function_param);
    }
    return start;
}

void Builder::switch_to_block(BlockId block) {
    current_block_ = block;
}

BlockId Builder::create_block(std::string_view name) {
    Block block;
    block.name = unique_block_name(name);
    block.unwind_target = current_unwind_target_;
    BlockId id = file_.add_block(std::move(block));
    if (current_function_.valid()) {
        file_.function_mut(current_function_).blocks.push_back(id);
    }
    return id;
}

BlockId Builder::create_detached_block(std::string_view name) {
    Block block;
    block.name = unique_block_name(name);
    block.unwind_target = current_unwind_target_;
    return file_.add_block(std::move(block));
}

void Builder::set_block_unwind_target(BlockId block, BlockId target) {
    if (!file_.valid(block)) {
        return;
    }
    file_.block_mut(block).unwind_target = target;
}

InstId Builder::add_block_parameter(BlockId block,
                                    TypeId type,
                                    std::string_view name,
                                    SrcLoc loc) {
    if (!file_.valid(block)) {
        return {};
    }
    std::string param_name(name.empty() ? "block_param" : name);
    EntityId entity = add_entity(EntityKind::Parameter,
                                 param_name,
                                 type,
                                 {},
                                 loc,
                                 StorageDuration::Parameter);
    BlockId previous = current_block_;
    switch_to_block(block);
    InstId inst = param(entity, type, loc);
    switch_to_block(previous);
    file_.block_mut(block).parameters.push_back(inst);
    return inst;
}

void Builder::rename_block(BlockId block, std::string_view name) {
    if (!file_.valid(block)) {
        return;
    }
    file_.block_mut(block).name = unique_block_name(name);
}

Fragment Builder::block_fragment(BlockId block) const {
    if (!file_.valid(block)) {
        return {};
    }
    return Fragment{{block}, block, block, !block_terminated(block)};
}

Fragment Builder::concat(Fragment first, Fragment second, SrcLoc loc) {
    if (first.empty()) {
        return second;
    }
    if (second.empty()) {
        return first;
    }
    if (first.falls_through) {
        if (!block_terminated(first.exit)) {
            branch_from(first.exit, second.entry, {}, loc);
        }
        first.exit = second.exit;
        first.falls_through = second.falls_through;
    }
    first.blocks.insert(first.blocks.end(), second.blocks.begin(), second.blocks.end());
    return first;
}

void Builder::attach_fragment_to_function(FunctionId function, const Fragment& fragment) {
    if (!file_.valid(function)) {
        return;
    }
    std::vector<BlockId>& blocks = file_.function_mut(function).blocks;
    for (BlockId block : fragment.blocks) {
        if (!file_.valid(block)) {
            continue;
        }
        if (std::find(blocks.begin(), blocks.end(), block) == blocks.end()) {
            blocks.push_back(block);
        }
    }
}

bool Builder::block_terminated(BlockId block) const {
    return file_.valid(block) && file_.block(block).terminator.kind != TerminatorKind::Invalid;
}

bool Builder::current_block_terminated() const {
    return block_terminated(current_block_);
}

InstPayload Builder::payload_none() const {
    return {};
}

InstId Builder::append_inst(InstKind kind,
                            TypeId result_type,
                            const std::vector<Operand>& operands,
                            InstPayload payload,
                            SrcLoc loc,
                            PlaceFactId place_fact) {
    Inst inst;
    inst.kind = kind;
    inst.result_type = result_type;
    inst.place_fact = place_fact;
    inst.operands = file_.add_operands(operands);
    inst.payload_index = std::holds_alternative<std::monostate>(payload)
        ? 0
        : file_.add_payload(std::move(payload));
    inst.loc = loc;
    InstId id = file_.add_inst(std::move(inst));
    if (place_fact.valid() && file_.valid(place_fact)) {
        PlaceFact& fact = file_.place_fact_mut(place_fact);
        if (!fact.source.valid()) {
            fact.source = id;
        }
    }
    if (current_block_.valid()) {
        file_.append_to_block(current_block_, id);
    }
    return id;
}

InstId Builder::param(EntityId entity, TypeId type, SrcLoc loc) {
    return append_inst(InstKind::Param, type, {Operand::entity(entity)}, payload_none(), loc);
}

InstId Builder::integer_literal(int64_t value, std::string spelling, SrcLoc loc) {
    return integer_literal(value, int_type(), std::move(spelling), loc);
}

InstId Builder::integer_literal(int64_t value, TypeId type, std::string spelling, SrcLoc loc) {
    TypeId result_type = type.valid() ? type : int_type();
    IntegerTypeShape shape = integer_shape_for_type(file_, result_type);
    IntegerValue exact = IntegerValue::from_signed(value, 64).cast(
        shape.bit_width == 0 ? 64 : shape.bit_width,
        shape.is_unsigned);
    return integer_literal(exact, result_type, std::move(spelling), loc);
}

InstId Builder::integer_literal(IntegerValue value,
                                TypeId type,
                                std::string spelling,
                                SrcLoc loc) {
    LiteralPayload payload;
    payload.value = value;
    payload.spelling = std::move(spelling);
    return append_inst(InstKind::IntegerLiteral,
                       type.valid() ? type : int_type(),
                       {},
                       InstPayload{std::move(payload)},
                       loc);
}

InstId Builder::boolean_literal(bool value, std::string spelling, SrcLoc loc) {
    LiteralPayload payload;
    payload.value = value;
    payload.spelling = std::move(spelling);
    return append_inst(InstKind::BooleanLiteral, bool_type(), {}, InstPayload{std::move(payload)}, loc);
}

InstId Builder::nullptr_literal(std::string spelling, SrcLoc loc) {
    LiteralPayload payload;
    payload.value = std::monostate{};
    payload.spelling = std::move(spelling);
    return append_inst(InstKind::NullptrLiteral,
                       file_.builtin_type(BuiltinTypeKind::NullPtr),
                       {},
                       InstPayload{std::move(payload)},
                       loc);
}

InstId Builder::floating_literal(FloatingValue value,
                                 TypeId type,
                                 std::string spelling,
                                 SrcLoc loc) {
    LiteralPayload payload;
    payload.value = value;
    payload.spelling = std::move(spelling);
    return append_inst(InstKind::FloatingLiteral, type, {}, InstPayload{std::move(payload)}, loc);
}

InstId Builder::character_literal(TypeId type,
                                  std::string decoded,
                                  std::string spelling,
                                  SrcLoc loc) {
    LiteralPayload payload;
    payload.value = literal_bytes_from_string(decoded);
    payload.spelling = std::move(spelling);
    return append_inst(InstKind::CharacterLiteral, type, {}, InstPayload{std::move(payload)}, loc);
}

InstId Builder::string_literal(std::string value, std::string spelling, SrcLoc loc,
                               TypeRef element_type, size_t char_width) {
    LiteralPayload payload;
    LiteralByteArray narrow = literal_bytes_from_string(value);
    if (char_width < 1) {
        char_width = 1;
    }

    LiteralByteArray bytes;
    if (char_width == 1) {
        bytes = std::move(narrow);
    } else {
        bytes.assign(narrow.size() * char_width, 0);
        for (size_t index = 0; index < narrow.size(); ++index) {
            bytes[index * char_width] = narrow[index];
        }
    }

    size_t array_size = (bytes.size() / char_width) + 1;
    payload.value = std::move(bytes);
    payload.spelling = std::move(spelling);
    TypeRef element = element_type;
    if (!element.valid()) {
        element.type = char_type();
    }
    TypeRef object_ref = file_.type_ref(
        file_.array_type(element,
                         ArraySizeKind::Constant,
                         array_size));
    PlaceFactId fact = add_place_fact(object_ref,
                                      StorageDuration::Static,
                                      {},
                                      {},
                                      loc);
    if (file_.valid(fact)) {
        file_.place_fact_mut(fact).modifiable = false;
    }
    return append_inst(InstKind::StringLiteral,
                       place_type(object_ref),
                       {},
                       InstPayload{std::move(payload)},
                       loc,
                       fact);
}

InstId Builder::name_ref(std::string_view name, TypeId result_type, SrcLoc loc) {
    return append_inst(InstKind::NameRef,
                       result_type,
                       {Operand::name(file_.intern_name(name))},
                       payload_none(),
                       loc);
}

InstId Builder::local_place(EntityId entity, TypeId object_type, SrcLoc loc) {
    TypeRef object_ref = entity_object_ref(entity, object_type);
    PlaceFactId fact = add_place_fact(object_ref,
                                      file_.valid(entity)
                                          ? file_.entity(entity).storage_duration
                                          : StorageDuration::Automatic,
                                      entity,
                                      {},
                                      loc);
    return append_inst(InstKind::LocalPlace,
                       place_type(object_ref),
                       {Operand::entity(entity)},
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::global_place(EntityId entity, SrcLoc loc) {
    TypeRef object_ref = entity_object_ref(entity, file_.valid(entity) ? file_.entity(entity).type : unknown_type());
    PlaceFactId fact = add_place_fact(object_ref,
                                      file_.valid(entity)
                                          ? file_.entity(entity).storage_duration
                                          : StorageDuration::Static,
                                      entity,
                                      {},
                                      loc);
    return append_inst(InstKind::GlobalPlace,
                       place_type(object_ref),
                       {Operand::entity(entity)},
                       payload_none(),
                       loc,
                       fact);
}

TypeRef Builder::entity_object_ref(EntityId entity, TypeId fallback_type) {
    if (!file_.valid(entity)) {
        return file_.type_ref(fallback_type);
    }
    const Entity& entity_record = file_.entity(entity);
    TypeId object_type = file_.valid(entity_record.type) ? entity_record.type : fallback_type;
    return file_.type_ref(object_type, entity_record.qualifiers, entity_record.memory_space);
}

TypeRef Builder::object_ref_from_place(InstId place) {
    TypeId place_type_id = file_.inst(place).result_type;
    if (!file_.valid(place_type_id) || file_.type(place_type_id).kind != TypeKind::Place) {
        return file_.type_ref(unknown_type());
    }
    TypeRef object_type = file_.place_object_ref(place_type_id);
    return file_.valid(object_type.type) ? object_type : file_.type_ref(unknown_type());
}

TypeId Builder::object_type_from_place(InstId place) {
    return object_ref_from_place(place).type;
}

InstId Builder::load(InstId place, SrcLoc loc) {
    return append_inst(InstKind::Load,
                       object_type_from_place(place),
                       operands_from_values({place}),
                       payload_none(),
                       loc);
}

InstId Builder::lvalue_to_rvalue(InstId place, SrcLoc loc) {
    return append_inst(InstKind::LValueToRValue,
                       object_type_from_place(place),
                       operands_from_values({place}),
                       payload_none(),
                       loc);
}

InstId Builder::function_to_pointer(EntityId function, SrcLoc loc) {
    TypeId function_type = file_.valid(function) ? file_.entity(function).type : unknown_type();
    return append_inst(InstKind::FunctionToPointer,
                       pointer_type(function_type),
                       {Operand::entity(function)},
                       payload_none(),
                       loc);
}

InstId Builder::member_pointer_value(EntityId member,
                                     TypeId member_pointer_type,
                                     SrcLoc loc) {
    return append_inst(InstKind::MemberPointerValue,
                       member_pointer_type,
                       {Operand::entity(member)},
                       payload_none(),
                       loc);
}

InstId Builder::label_address(std::string_view name, BlockId target, SrcLoc loc) {
    LabelAddressPayload payload;
    payload.name = file_.intern_name(name);
    payload.target = target;
    return append_inst(InstKind::LabelAddress,
                       pointer_type(void_type()),
                       {},
                       InstPayload{std::move(payload)},
                       loc);
}

InstId Builder::store(InstId place, InstId value, SrcLoc loc) {
    return append_inst(InstKind::Store, {}, operands_from_values({place, value}), payload_none(), loc);
}

InstId Builder::stack_alloc(TypeRef object_type,
                            InstId total_bytes,
                            EntityId entity,
                            SrcLoc loc) {
    PlaceFactId fact = add_place_fact(object_type,
                                      StorageDuration::Automatic,
                                      entity,
                                      {},
                                      loc);
    return append_inst(InstKind::StackAlloc,
                       place_type(object_type),
                       {Operand::type(object_type), Operand::value(total_bytes)},
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::atomic_load(InstId place, MemoryOrder order, SrcLoc loc) {
    AtomicPayload payload;
    payload.order = order;
    return append_inst(InstKind::AtomicLoad,
                       object_type_from_place(place),
                       operands_from_values({place}),
                       InstPayload{payload},
                       loc);
}

InstId Builder::atomic_store(InstId place, InstId value, MemoryOrder order, SrcLoc loc) {
    AtomicPayload payload;
    payload.order = order;
    return append_inst(InstKind::AtomicStore,
                       {},
                       operands_from_values({place, value}),
                       InstPayload{payload},
                       loc);
}

InstId Builder::atomic_rmw(InstId place,
                           InstId value,
                           AtomicRmwOp op,
                           MemoryOrder order,
                           SrcLoc loc) {
    AtomicPayload payload;
    payload.order = order;
    payload.rmw_op = op;
    return append_inst(InstKind::AtomicRmw,
                       object_type_from_place(place),
                       operands_from_values({place, value}),
                       InstPayload{payload},
                       loc);
}

InstId Builder::atomic_cmpxchg(InstId place,
                               InstId expected_place,
                               InstId desired,
                               MemoryOrder success_order,
                               MemoryOrder failure_order,
                               bool is_weak,
                               SrcLoc loc) {
    AtomicPayload payload;
    payload.order = success_order;
    payload.failure_order = failure_order;
    payload.is_weak = is_weak;
    return append_inst(InstKind::AtomicCmpXchg,
                       bool_type(),
                       operands_from_values({place, expected_place, desired}),
                       InstPayload{payload},
                       loc);
}

InstId Builder::atomic_fence(MemoryOrder order, SrcLoc loc) {
    AtomicPayload payload;
    payload.order = order;
    return append_inst(InstKind::AtomicFence,
                       {},
                       {},
                       InstPayload{payload},
                       loc);
}

namespace {
TypeRef complex_element_ref(const File& file, TypeId complex_type) {
    TypeId resolved = file.resolved_type(complex_type);
    if (file.valid(resolved) && file.type(resolved).kind == TypeKind::Complex) {
        const auto* payload =
            std::get_if<ComplexTypePayload>(&file.type_payload(resolved));
        if (payload) {
            return payload->element_type;
        }
    }
    return {};
}
} // namespace

InstId Builder::complex_make(TypeId complex_type, InstId real, InstId imag, SrcLoc loc) {
    return append_inst(InstKind::ComplexMake,
                       complex_type,
                       operands_from_values({real, imag}),
                       payload_none(),
                       loc);
}

InstId Builder::complex_real(InstId value, SrcLoc loc) {
    TypeRef element =
        complex_element_ref(file_, file_.inst(value).result_type);
    return append_inst(InstKind::ComplexReal,
                       element.type,
                       operands_from_values({value}),
                       payload_none(),
                       loc);
}

InstId Builder::complex_imag(InstId value, SrcLoc loc) {
    TypeRef element =
        complex_element_ref(file_, file_.inst(value).result_type);
    return append_inst(InstKind::ComplexImag,
                       element.type,
                       operands_from_values({value}),
                       payload_none(),
                       loc);
}

InstId Builder::complex_real_place(InstId place, SrcLoc loc) {
    TypeRef base_ref = object_ref_from_place(place);
    TypeRef element = complex_element_ref(file_, base_ref.type);
    element.qualifiers |= base_ref.qualifiers;
    PlaceFactId fact = add_place_fact(element, StorageDuration::Unknown, {}, place, loc);
    return append_inst(InstKind::ComplexRealPlace,
                       place_type(element),
                       operands_from_values({place}),
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::complex_imag_place(InstId place, SrcLoc loc) {
    TypeRef base_ref = object_ref_from_place(place);
    TypeRef element = complex_element_ref(file_, base_ref.type);
    element.qualifiers |= base_ref.qualifiers;
    PlaceFactId fact = add_place_fact(element, StorageDuration::Unknown, {}, place, loc);
    return append_inst(InstKind::ComplexImagPlace,
                       place_type(element),
                       operands_from_values({place}),
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::stack_save(SrcLoc loc) {
    return append_inst(InstKind::StackSave,
                       pointer_type(file_.builtin_type(BuiltinTypeKind::Void)),
                       {},
                       payload_none(),
                       loc);
}

InstId Builder::stack_restore(InstId saved, SrcLoc loc) {
    return append_inst(InstKind::StackRestore,
                       {},
                       operands_from_values({saved}),
                       payload_none(),
                       loc);
}

InstId Builder::zero_object(InstId place, SrcLoc loc) {
    return append_inst(InstKind::ZeroObject,
                       {},
                       operands_from_values({place}),
                       payload_none(),
                       loc);
}

InstId Builder::lifetime_start(InstId place, SrcLoc loc) {
    return append_inst(InstKind::LifetimeStart,
                       {},
                       operands_from_values({place}),
                       payload_none(),
                       loc);
}

InstId Builder::lifetime_end(InstId place, SrcLoc loc) {
    return append_inst(InstKind::LifetimeEnd,
                       {},
                       operands_from_values({place}),
                       payload_none(),
                       loc);
}

InstId Builder::addr_of(InstId place, SrcLoc loc) {
    return append_inst(InstKind::AddrOf,
                       pointer_type(object_ref_from_place(place)),
                       operands_from_values({place}),
                       payload_none(),
                       loc);
}

InstId Builder::deref(InstId pointer, SrcLoc loc) {
    TypeId pointer_type_id =
        file_.resolved_type(file_.inst(pointer).result_type);
    TypeRef object_ref = file_.type_ref(unknown_type());
    if (file_.valid(pointer_type_id) && file_.type(pointer_type_id).kind == TypeKind::Pointer) {
        object_ref = file_.pointer_pointee_ref(pointer_type_id);
    } else if (file_.valid(pointer_type_id) &&
               (file_.type(pointer_type_id).kind == TypeKind::LValueReference ||
                file_.type(pointer_type_id).kind == TypeKind::RValueReference)) {

        object_ref = file_.reference_referred_ref(pointer_type_id);
    }
    PlaceFactId fact = add_place_fact(object_ref,
                                      StorageDuration::Unknown,
                                      {},
                                      pointer,
                                      loc);
    return append_inst(InstKind::Deref,
                       place_type(object_ref),
                       operands_from_values({pointer}),
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::field_addr(InstId base_place, EntityId field, TypeId field_type, SrcLoc loc) {
    TypeRef base_ref = object_ref_from_place(base_place);
    TypeRef field_ref = file_.type_ref(field_type);
    if (file_.valid(field)) {
        field_ref.qualifiers |= file_.entity(field).qualifiers;
    }

    uint8_t inherited = base_ref.qualifiers & (QualConst | QualVolatile);
    if (const RecordFieldFact* fact = file_.field_fact(field);
        fact && fact->is_mutable) {
        inherited &= ~QualConst;
    }
    field_ref.qualifiers |= inherited;
    field_ref = inherit_memory_if_default(field_ref, base_ref.memory_space);
    PlaceFactId fact = add_place_fact(field_ref,
                                      StorageDuration::Unknown,
                                      field,
                                      base_place,
                                      loc);
    return append_inst(InstKind::FieldAddr,
                       place_type(field_ref),
                       {Operand::value(base_place), Operand::entity(field)},
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::data_member_pointer_place(InstId base_place,
                                          InstId member_pointer,
                                          SrcLoc loc) {
    TypeRef base_ref = object_ref_from_place(base_place);
    TypeRef member_ref = file_.type_ref(unknown_type());
    if (file_.valid(member_pointer)) {
        TypeId pointer_type = file_.inst(member_pointer).result_type;
        if (file_.valid(pointer_type) &&
            file_.type(file_.resolved_type(pointer_type)).kind ==
                TypeKind::MemberPointer) {
            member_ref =
                file_.member_pointer_member_ref(file_.resolved_type(pointer_type));
        }
    }
    member_ref.qualifiers |= base_ref.qualifiers & (QualConst | QualVolatile);
    member_ref = inherit_memory_if_default(member_ref, base_ref.memory_space);
    PlaceFactId fact = add_place_fact(member_ref,
                                      StorageDuration::Unknown,
                                      {},
                                      base_place,
                                      loc);
    return append_inst(InstKind::DataMemberPointerPlace,
                       place_type(member_ref),
                       operands_from_values({base_place, member_pointer}),
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::member_function_pointer_callee(InstId adjusted_this,
                                               InstId member_pointer,
                                               TypeId function_pointer_type,
                                               SrcLoc loc) {
    return append_inst(InstKind::MemberFunctionPointerCallee,
                       function_pointer_type,
                       operands_from_values({adjusted_this, member_pointer}),
                       payload_none(),
                       loc);
}

InstId Builder::member_function_pointer_this(InstId object_pointer,
                                             InstId member_pointer,
                                             TypeId adjusted_pointer_type,
                                             SrcLoc loc) {
    return append_inst(InstKind::MemberFunctionPointerThis,
                       adjusted_pointer_type,
                       operands_from_values({object_pointer, member_pointer}),
                       payload_none(),
                       loc);
}

TypeRef Builder::inherit_memory_if_default(TypeRef ref, MemorySpace memory_space) const {
    if (ref.memory_space == MemorySpace::Default && memory_space != MemorySpace::Default) {
        ref.memory_space = memory_space;
    }
    return ref;
}

TypeRef Builder::element_ref_from_array_base(InstId base) {
    if (!file_.valid(base)) {
        return file_.type_ref(unknown_type());
    }
    TypeId base_type = file_.inst(base).result_type;
    if (!file_.valid(base_type)) {
        return file_.type_ref(unknown_type());
    }
    if (file_.type(base_type).kind == TypeKind::Pointer) {
        TypeRef pointee = file_.pointer_pointee_ref(base_type);
        return file_.valid(pointee.type) ? pointee : file_.type_ref(unknown_type());
    }
    if (file_.type(base_type).kind == TypeKind::Place) {
        TypeRef object_type = file_.place_object_ref(base_type);
        if (file_.valid(object_type.type) && file_.type(object_type.type).kind == TypeKind::Array) {
            TypeRef element_type = file_.array_element_ref(object_type.type);

            element_type = file_.type_ref(
                element_type.type,
                static_cast<uint8_t>(element_type.qualifiers | object_type.qualifiers),
                element_type.memory_space);
            element_type = inherit_memory_if_default(element_type, object_type.memory_space);
            return file_.valid(element_type.type) ? element_type : file_.type_ref(unknown_type());
        }
    }
    return file_.type_ref(unknown_type());
}

TypeRef Builder::element_ref_from_vector_base(InstId base) {
    if (!file_.valid(base)) {
        return file_.type_ref(unknown_type());
    }
    TypeId base_type = file_.inst(base).result_type;
    if (!file_.valid(base_type)) {
        return file_.type_ref(unknown_type());
    }
    if (file_.type(base_type).kind == TypeKind::Place) {
        TypeRef object_type = file_.place_object_ref(base_type);
        if (file_.valid(object_type.type) && file_.type(object_type.type).kind == TypeKind::Vector) {
            TypeRef element_type = file_.vector_element_ref(object_type.type);

            element_type = file_.type_ref(
                element_type.type,
                static_cast<uint8_t>(element_type.qualifiers | object_type.qualifiers),
                element_type.memory_space);
            element_type = inherit_memory_if_default(element_type, object_type.memory_space);
            return file_.valid(element_type.type) ? element_type : file_.type_ref(unknown_type());
        }
        return file_.type_ref(unknown_type());
    }
    if (file_.type(base_type).kind == TypeKind::Vector) {
        TypeRef element_type = file_.vector_element_ref(base_type);
        return file_.valid(element_type.type) ? element_type : file_.type_ref(unknown_type());
    }
    return file_.type_ref(unknown_type());
}

PlaceFactId Builder::add_place_fact(TypeRef object_type,
                                    StorageDuration storage_duration,
                                    EntityId entity,
                                    InstId base,
                                    SrcLoc loc) {
    PlaceFact fact;
    fact.object_type = object_type;
    fact.storage_duration = storage_duration;
    fact.entity = entity;
    fact.base = base;
    fact.loc = loc;
    return file_.add_place_fact(std::move(fact));
}

InstId Builder::array_element_place(InstId base, InstId index, SrcLoc loc) {
    TypeRef element_ref = element_ref_from_array_base(base);
    PlaceFactId fact = add_place_fact(element_ref,
                                      StorageDuration::Unknown,
                                      {},
                                      base,
                                      loc);
    return append_inst(InstKind::ArrayElementPlace,
                       place_type(element_ref),
                       operands_from_values({base, index}),
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::vector_element_place(InstId base_place, InstId index, SrcLoc loc) {
    TypeRef element_ref = element_ref_from_vector_base(base_place);
    PlaceFactId fact = add_place_fact(element_ref,
                                      StorageDuration::Unknown,
                                      {},
                                      base_place,
                                      loc);
    if (file_.valid(fact)) {
        file_.place_fact_mut(fact).addressable = false;
    }
    return append_inst(InstKind::VectorElementPlace,
                       place_type(element_ref),
                       operands_from_values({base_place, index}),
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::vector_extract(InstId vector, InstId index, SrcLoc loc) {
    return append_inst(InstKind::VectorExtract,
                       element_ref_from_vector_base(vector).type,
                       operands_from_values({vector, index}),
                       payload_none(),
                       loc);
}

InstId Builder::sizeof_type(TypeId queried_type, SrcLoc loc) {
    return append_inst(InstKind::SizeofType,
                       usize_type(),
                       {Operand::type(file_.type_ref(queried_type))},
                       payload_none(),
                       loc);
}

InstId Builder::reflect_type(TypeRef operand, SrcLoc loc) {
    ReflectPayload payload;
    payload.kind = MetaInfoKind::Type;
    return append_inst(InstKind::ReflectValue,
                       file_.builtin_type(BuiltinTypeKind::MetaInfo),
                       {Operand::type(operand)},
                       InstPayload{payload},
                       loc);
}

InstId Builder::reflect_entity(MetaInfoKind kind, EntityId entity, SrcLoc loc) {
    ReflectPayload payload;
    payload.kind = kind;
    return append_inst(InstKind::ReflectValue,
                       file_.builtin_type(BuiltinTypeKind::MetaInfo),
                       {Operand::entity(entity)},
                       InstPayload{payload},
                       loc);
}

InstId Builder::alignof_type(TypeId queried_type, SrcLoc loc) {
    return append_inst(InstKind::AlignofType,
                       usize_type(),
                       {Operand::type(file_.type_ref(queried_type))},
                       payload_none(),
                       loc);
}

InstId Builder::unary(UnaryOpKind op, TypeId result_type, InstId operand, SrcLoc loc) {
    TypeRef operand_type = file_.type_ref(file_.inst(operand).result_type);
    UnaryOpDescriptor descriptor;
    descriptor.op = op;
    descriptor.computation_type = operand_type;

    return append_inst(InstKind::UnaryOp,
                       result_type,
                       operands_from_values({operand}),
                       InstPayload{descriptor},
                       loc);
}

InstId Builder::binary(BinaryOpKind op, TypeId result_type, InstId lhs, InstId rhs, SrcLoc loc) {
    TypeRef lhs_type = file_.type_ref(file_.inst(lhs).result_type);
    TypeRef rhs_type = file_.type_ref(file_.inst(rhs).result_type);
    BinaryOpDescriptor descriptor;
    descriptor.op = op;
    descriptor.computation_type = lhs_type.valid() ? lhs_type : rhs_type;
    if (op == BinaryOpKind::Comma) {
        descriptor.computation_type = rhs_type;
    }

    return append_inst(InstKind::BinaryOp,
                       result_type,
                       operands_from_values({lhs, rhs}),
                       InstPayload{descriptor},
                       loc);
}

InstId Builder::cast(TypeId target_type, InstId value, std::string_view cast_kind, SrcLoc loc) {
    CastPayload payload;
    payload.kind = std::string(cast_kind);
    return append_inst(InstKind::Cast,
                       target_type,
                       {Operand::type(file_.type_ref(target_type)), Operand::value(value)},
                       InstPayload{std::move(payload)},
                       loc);
}

InstId Builder::call(EntityId callee, TypeId result_type, const std::vector<InstId>& args, SrcLoc loc) {
    std::vector<Operand> operands{Operand::entity(callee)};
    append_value_operands(operands, args);
    return append_inst(InstKind::Call, result_type, operands, payload_none(), loc);
}

InstId Builder::call_indirect(InstId callee, TypeId result_type, const std::vector<InstId>& args, SrcLoc loc) {
    std::vector<Operand> operands{Operand::value(callee)};
    append_value_operands(operands, args);
    return append_inst(InstKind::Call, result_type, operands, payload_none(), loc);
}

InstId Builder::call_virtual(InstId callee,
                             EntityId declaration,
                             TypeId result_type,
                             const std::vector<InstId>& args,
                             SrcLoc loc) {
    std::vector<Operand> operands{Operand::value(callee)};
    append_value_operands(operands, args);
    CallPayload payload;
    payload.virtual_declaration = declaration;
    return append_inst(InstKind::Call, result_type, operands,
                       InstPayload{payload}, loc);
}

InstId Builder::emit_va_start(InstId va_list_place, SrcLoc loc) {
    return append_inst(InstKind::VaStart,
                       void_type(),
                       operands_from_values({va_list_place}),
                       payload_none(),
                       loc);
}

InstId Builder::emit_va_arg(InstId va_list_place, TypeId result_type, SrcLoc loc) {
    return append_inst(InstKind::VaArg,
                       result_type,
                       {Operand::type(file_.type_ref(result_type)),
                        Operand::value(va_list_place)},
                       payload_none(),
                       loc);
}

InstId Builder::emit_va_end(InstId va_list_place, SrcLoc loc) {
    return append_inst(InstKind::VaEnd,
                       void_type(),
                       operands_from_values({va_list_place}),
                       payload_none(),
                       loc);
}

InstId Builder::emit_va_copy(InstId dest_place, InstId src_place, SrcLoc loc) {
    return append_inst(InstKind::VaCopy,
                       void_type(),
                       operands_from_values({dest_place, src_place}),
                       payload_none(),
                       loc);
}

InstId Builder::builtin_call(BuiltinKind kind,
                             std::string_view name,
                             TypeId result_type,
                             const std::vector<InstId>& args,
                             SrcLoc loc,
                             TypeRef type_operand,
                             std::vector<int64_t> integer_operands) {
    BuiltinCallPayload payload;
    payload.kind = kind;
    payload.name = std::string(name);
    payload.type_operand = type_operand;
    payload.integer_operands = std::move(integer_operands);
    return append_inst(InstKind::BuiltinCall,
                       result_type,
                       operands_from_values(args),
                       InstPayload{std::move(payload)},
                       loc);
}

InstId Builder::inline_asm(std::string asm_string,
                           std::string constraints,
                           const std::vector<InstId>& args,
                           bool has_side_effects,
                           bool align_stack,
                           bool intel_dialect,
                           SrcLoc loc) {
    InlineAsmPayload payload;
    payload.asm_string = std::move(asm_string);
    payload.constraints = std::move(constraints);
    payload.has_side_effects = has_side_effects;
    payload.align_stack = align_stack;
    payload.intel_dialect = intel_dialect;
    payload.is_goto = false;
    InlineAsmPayloadId payload_id = file_.add_inline_asm_payload(std::move(payload));
    return append_inst(InstKind::InlineAsm,
                       {},
                       operands_from_values(args),
                       InstPayload{InlineAsmPayloadRef{payload_id}},
                       loc);
}

InstId Builder::inline_asm(InlineAsmPayload payload,
                           const std::vector<InstId>& operands,
                           SrcLoc loc) {
    payload.is_goto = false;
    InlineAsmPayloadId payload_id = file_.add_inline_asm_payload(std::move(payload));
    return append_inst(InstKind::InlineAsm,
                       {},
                       operands_from_values(operands),
                       InstPayload{InlineAsmPayloadRef{payload_id}},
                       loc);
}

InstId Builder::construct_in_place(InstId place, EntityId constructor, const std::vector<InstId>& args, SrcLoc loc) {
    std::vector<Operand> operands{Operand::value(place), Operand::entity(constructor)};
    append_value_operands(operands, args);
    return append_inst(InstKind::ConstructInPlace, {}, operands, payload_none(), loc);
}

InstId Builder::destroy(InstId place, EntityId destructor, SrcLoc loc) {
    std::vector<Operand> operands{Operand::value(place)};
    if (destructor.valid()) {
        operands.push_back(Operand::entity(destructor));
    }
    return append_inst(InstKind::Destroy, {}, operands, payload_none(), loc);
}

InstId Builder::dependent_call(std::string_view name, TypeId result_type, const std::vector<InstId>& args, SrcLoc loc) {
    std::vector<Operand> operands{Operand::name(file_.intern_name(name))};
    append_value_operands(operands, args);
    return append_inst(InstKind::DependentCall, result_type, operands, payload_none(), loc);
}

InstId Builder::dependent_region(uint32_t hole, std::string display, InstId place, SrcLoc loc) {
    DependentRegionPayload payload;
    payload.hole = hole;
    payload.display = std::move(display);
    std::vector<Operand> operands;
    if (place.valid()) {
        operands.push_back(Operand::value(place));
    }
    return append_inst(InstKind::DependentRegion, {}, operands,
                       InstPayload{std::move(payload)}, loc);
}

InstId Builder::eh_alloc_exception(TypeRef object_type, SrcLoc loc) {
    PlaceFactId fact = add_place_fact(object_type,
                                      StorageDuration::Allocated,
                                      {},
                                      {},
                                      loc);
    return append_inst(InstKind::EhAllocException,
                       place_type(object_type),
                       {Operand::type(object_type)},
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::eh_landing_pad(EhLandingPadPayload payload, SrcLoc loc) {
    return append_inst(InstKind::EhLandingPad,
                       pointer_type(void_type()),
                       {},
                       InstPayload{std::move(payload)},
                       loc);
}

InstId Builder::eh_selector(InstId pad, SrcLoc loc) {
    return append_inst(InstKind::EhSelector,
                       int_type(),
                       operands_from_values({pad}),
                       payload_none(),
                       loc);
}

InstId Builder::eh_typeid_for(EntityId typeinfo, SrcLoc loc) {
    return append_inst(InstKind::EhTypeId,
                       int_type(),
                       {Operand::entity(typeinfo)},
                       payload_none(),
                       loc);
}

InstId Builder::catch_begin(InstId exception_ptr, SrcLoc loc) {
    return append_inst(InstKind::CatchBegin,
                       pointer_type(void_type()),
                       operands_from_values({exception_ptr}),
                       payload_none(),
                       loc);
}

InstId Builder::catch_end(SrcLoc loc) {
    return append_inst(InstKind::CatchEnd, {}, {}, payload_none(), loc);
}

InstId Builder::objc_message_send(const ObjCMessageSendPayload& payload,
                                  const std::vector<InstId>& receiver_and_args,
                                  TypeId result_type,
                                  SrcLoc loc) {
    return append_inst(InstKind::ObjCMessageSend,
                       result_type,
                       operands_from_values(receiver_and_args),
                       InstPayload{payload},
                       loc);
}

InstId Builder::objc_ivar_addr(InstId object_pointer,
                               EntityId ivar,
                               TypeId place_type,
                               SrcLoc loc) {
    std::vector<Operand> operands;
    operands.push_back(Operand::value(object_pointer));
    operands.push_back(Operand::entity(ivar));
    return append_inst(InstKind::ObjCIvarAddr,
                       place_type,
                       operands,
                       payload_none(),
                       loc);
}

InstId Builder::objc_selector_literal(SelectorId selector,
                                      TypeId sel_type,
                                      SrcLoc loc) {
    ObjCSelectorLiteralPayload payload;
    payload.selector = selector;
    return append_inst(InstKind::ObjCSelectorLiteral,
                       sel_type,
                       {},
                       InstPayload{payload},
                       loc);
}

InstId Builder::objc_arc_op(ObjCArcOpKind op,
                            const std::vector<InstId>& operands,
                            TypeId result_type,
                            SrcLoc loc) {
    ObjCArcOpPayload payload;
    payload.op = op;
    return append_inst(InstKind::ObjCArcOp,
                       result_type,
                       operands_from_values(operands),
                       InstPayload{payload},
                       loc);
}

InstId Builder::objc_string_literal(std::string bytes,
                                    std::string spelling,
                                    TypeId result_type,
                                    SrcLoc loc) {
    LiteralPayload payload;
    payload.value = literal_bytes_from_string(std::move(bytes));
    payload.spelling = std::move(spelling);
    return append_inst(InstKind::ObjCStringLiteral,
                       result_type,
                       {},
                       InstPayload{std::move(payload)},
                       loc);
}

InstId Builder::error(std::string message, SrcLoc loc) {
    ErrorPayload payload;
    payload.message = std::move(message);
    return append_inst(InstKind::Error, {}, {}, InstPayload{std::move(payload)}, loc);
}

void Builder::return_void(SrcLoc loc) {
    return_void_from(current_block_, loc);
}

void Builder::return_void_from(BlockId source, SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::Return;
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::return_value(InstId value, SrcLoc loc) {
    return_value_from(current_block_, value, loc);
}

void Builder::return_value_from(BlockId source, InstId value, SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::Return;
    term.operands = file_.add_value_operands({value});
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::branch(BlockId target, const std::vector<InstId>& args, SrcLoc loc) {
    branch_from(current_block_, target, args, loc);
}

void Builder::branch_from(BlockId source, BlockId target, const std::vector<InstId>& args, SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::Branch;
    term.target = target;
    term.operands = file_.add_value_operands(args);
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::cond_branch(InstId condition,
                          BlockId true_target,
                          BlockId false_target,
                          const std::vector<InstId>& args,
                          SrcLoc loc) {
    cond_branch_from(current_block_, condition, true_target, false_target, args, loc);
}

void Builder::cond_branch_from(BlockId source,
                               InstId condition,
                               BlockId true_target,
                               BlockId false_target,
                               const std::vector<InstId>& args,
                               SrcLoc loc) {
    std::vector<InstId> operands{condition};
    operands.insert(operands.end(), args.begin(), args.end());
    Terminator term;
    term.kind = TerminatorKind::CondBranch;
    term.target = true_target;
    term.false_target = false_target;
    term.operands = file_.add_value_operands(operands);
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::switch_branch(InstId condition,
                            TypeRef condition_type,
                            BlockId default_target,
                            std::vector<SwitchCaseRange> cases,
                            SrcLoc loc) {
    switch_branch_from(current_block_,
                       condition,
                       condition_type,
                       default_target,
                       std::move(cases),
                       loc);
}

void Builder::switch_branch_from(BlockId source,
                                 InstId condition,
                                 TypeRef condition_type,
                                 BlockId default_target,
                                 std::vector<SwitchCaseRange> cases,
                                 SrcLoc loc) {
    SwitchTerminatorPayload payload;
    payload.condition_type = condition_type;
    payload.cases = std::move(cases);

    Terminator term;
    term.kind = TerminatorKind::Switch;
    term.target = default_target;
    term.operands = file_.add_value_operands({condition});
    term.payload_index = file_.add_payload(InstPayload{std::move(payload)});
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::indirect_branch(InstId target, SrcLoc loc) {
    indirect_branch_from(current_block_, target, loc);
}

void Builder::indirect_branch_from(BlockId source, InstId target, SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::IndirectBranch;
    term.operands = file_.add_value_operands({target});
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::asm_goto_from(BlockId source,
                            InlineAsmPayload payload,
                            const std::vector<InstId>& operands,
                            BlockId fallthrough,
                            SrcLoc loc) {
    payload.is_goto = true;
    Terminator term;
    term.kind = TerminatorKind::AsmGoto;
    term.operands = file_.add_value_operands(operands);
    term.target = fallthrough;
    InlineAsmPayloadId payload_id = file_.add_inline_asm_payload(std::move(payload));
    term.payload_index = file_.add_payload(InstPayload{InlineAsmPayloadRef{payload_id}});
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::unreachable(SrcLoc loc) {
    unreachable_from(current_block_, loc);
}

void Builder::unreachable_from(BlockId source, SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::Unreachable;
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::throw_from(BlockId source,
                         InstId exception_place,
                         EntityId typeinfo,
                         EntityId destructor,
                         SrcLoc loc) {
    std::vector<Operand> operands{Operand::value(exception_place),
                                  Operand::entity(typeinfo)};
    if (destructor.valid()) {
        operands.push_back(Operand::entity(destructor));
    }
    Terminator term;
    term.kind = TerminatorKind::Throw;
    term.operands = file_.add_operands(operands);
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::rethrow_from(BlockId source, SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::Rethrow;
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::resume_from(BlockId source,
                          InstId exception_ptr,
                          InstId selector,
                          SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::Resume;
    term.operands = file_.add_value_operands({exception_ptr, selector});
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

InstId Builder::coro_begin(InstId allocation, SrcLoc loc) {
    return append_inst(InstKind::CoroBegin,
                       pointer_type(void_type()),
                       operands_from_values({allocation}),
                       payload_none(),
                       loc);
}

InstId Builder::coro_frame_size(SrcLoc loc) {
    return append_inst(InstKind::CoroFrameSize,
                       usize_type(),
                       {},
                       payload_none(),
                       loc);
}

InstId Builder::coro_frame_align(SrcLoc loc) {
    return append_inst(InstKind::CoroFrameAlign,
                       usize_type(),
                       {},
                       payload_none(),
                       loc);
}

InstId Builder::coro_promise_place(InstId frame,
                                   TypeId promise_type,
                                   SrcLoc loc) {
    TypeRef object_ref = file_.type_ref(promise_type);
    PlaceFactId fact = add_place_fact(object_ref,
                                      StorageDuration::Unknown,
                                      {},
                                      frame,
                                      loc);
    return append_inst(InstKind::CoroPromisePlace,
                       place_type(object_ref),
                       operands_from_values({frame}),
                       payload_none(),
                       loc,
                       fact);
}

InstId Builder::coro_save(uint32_t index, CoroSaveKind kind, SrcLoc loc) {
    CoroSuspendPayload payload;
    payload.index = index;
    payload.kind = kind;
    return append_inst(InstKind::CoroSave,
                       {},
                       {},
                       InstPayload{payload},
                       loc);
}

InstId Builder::coro_transfer(InstId frame, SrcLoc loc) {
    return append_inst(InstKind::CoroTransfer,
                       {},
                       operands_from_values({frame}),
                       payload_none(),
                       loc);
}

void Builder::coro_suspend_from(BlockId source,
                                uint32_t index,
                                CoroSaveKind kind,
                                BlockId resume_target,
                                BlockId destroy_target,
                                SrcLoc loc) {
    CoroSuspendPayload payload;
    payload.index = index;
    payload.kind = kind;
    Terminator term;
    term.kind = TerminatorKind::CoroSuspend;
    term.target = resume_target;
    term.false_target = destroy_target;
    term.payload_index = file_.add_payload(InstPayload{payload});
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

void Builder::coro_end_from(BlockId source, SrcLoc loc) {
    Terminator term;
    term.kind = TerminatorKind::CoroEnd;
    term.loc = loc;
    file_.set_terminator(source, std::move(term));
}

} // namespace aburi::cir
