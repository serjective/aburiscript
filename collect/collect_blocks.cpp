#include "collect.h"

#include "../abi/darwin_blocks.h"
#include "../cir/layout.h"

#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::collect {

namespace {

char scalar_encoding(const cir::File& file, cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return '?';
    }
    switch (file.type(resolved).kind) {
        case cir::TypeKind::Pointer:
            return '^';
        case cir::TypeKind::BlockPointer:
            return '@';
        default:
            break;
    }
    std::string spelling = file.format_type(resolved);
    if (spelling == "void") return 'v';
    if (spelling == "char") return 'c';
    if (spelling == "short") return 's';
    if (spelling == "int") return 'i';
    if (spelling == "long" || spelling == "long long") return 'q';
    if (spelling == "unsigned int") return 'I';
    if (spelling == "unsigned long" || spelling == "unsigned long long") return 'Q';
    if (spelling == "float") return 'f';
    if (spelling == "double" || spelling == "long double") return 'd';
    if (spelling == "_Bool" || spelling == "bool") return 'B';
    return '?';
}

std::string encode_signature(const cir::File& file,
                             cir::TypeId return_type,
                             const std::vector<cir::TypeId>& params) {

    size_t offset = 8;
    std::string tail;
    for (cir::TypeId param : params) {
        tail += scalar_encoding(file, param);
        tail += std::to_string(offset);
        offset += cir::size_of_type(file, param).value_or(8);
    }
    std::string out;
    out += scalar_encoding(file, return_type);
    out += std::to_string(offset);
    out += "@?0";
    out += tail;
    return out;
}

uint64_t entity_key(cir::EntityId id) {
    return (static_cast<uint64_t>(id.generation) << 32) | id.index;
}

const cir::RecordFieldFact* find_record_field(const cir::File& file,
                                              cir::TypeId record,
                                              std::string_view name) {
    const cir::RecordFacts* facts = file.record_facts_for_type(record);
    if (!facts) {
        return nullptr;
    }
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.name.valid() && file.name(field.name) == name) {
            return &field;
        }
    }
    return nullptr;
}

} // namespace

cir::EntityId Session::extern_runtime_global(std::string_view symbol, SrcLoc loc) {
    std::string key(symbol);
    auto found = runtime_globals_.find(key);
    if (found != runtime_globals_.end() && file_.valid(found->second)) {
        return found->second;
    }
    if (found != runtime_globals_.end()) {
        runtime_globals_.erase(found);
    }
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                               symbol,
                                               builder_.pointer_type(
                                                   file_.builtin_type(cir::BuiltinTypeKind::Void)),
                                               {},
                                               loc,
                                               cir::StorageDuration::Static,
                                               cir::MemorySpace::Default,
                                               {});
    file_.entity_mut(entity).is_definition = false;
    file_.entity_mut(entity).linkage = cir::LinkageKind::External;
    runtime_globals_.emplace(key, entity);
    track_speculative_rollback([this, key, entity] {
        auto current = runtime_globals_.find(key);
        if (current != runtime_globals_.end() && current->second == entity) {
            runtime_globals_.erase(current);
        }
    });
    return entity;
}

cir::EntityId Session::extern_runtime_function(std::string_view symbol,
                                               cir::TypeId function_type,
                                               SrcLoc loc) {
    std::string key(symbol);
    auto found = runtime_globals_.find(key);
    if (found != runtime_globals_.end() && file_.valid(found->second)) {
        return found->second;
    }
    if (found != runtime_globals_.end()) {
        runtime_globals_.erase(found);
    }
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Function,
                                               symbol,
                                               function_type,
                                               {},
                                               loc,
                                               cir::StorageDuration::Static,
                                               cir::MemorySpace::Default,
                                               {});
    file_.entity_mut(entity).is_definition = false;
    file_.entity_mut(entity).linkage = cir::LinkageKind::External;
    runtime_globals_.emplace(key, entity);
    track_speculative_rollback([this, key, entity] {
        auto current = runtime_globals_.find(key);
        if (current != runtime_globals_.end() && current->second == entity) {
            runtime_globals_.erase(current);
        }
    });
    return entity;
}

std::unique_ptr<Session::BlockContextState> Session::save_function_context(
    bool preserve_lambda_context) {
    auto saved = std::make_unique<BlockContextState>();
    saved->function = current_function_;
    saved->result_type = current_result_type_;
    saved->decltype_operand_depth = decltype_operand_depth_;
    saved->unevaluated_operand_depth = unevaluated_operand_depth_;
    saved->typeid_capture_discovery_depth =
        typeid_capture_discovery_depth_;
    saved->prologue = std::move(current_prologue_);
    saved->labels = std::move(function_labels_);
    saved->local_label_scopes = std::move(local_label_scopes_);
    saved->orphan_blocks = std::move(pending_orphan_label_blocks_);
    saved->vla_slot = vla_sp_slot_place_;
    saved->control_stack = std::move(control_stack_);
    saved->switch_contexts = std::move(switch_contexts_);
    saved->control_flow_regions = std::move(control_flow_regions_);
    saved->cleanup_scopes = std::move(cleanup_scopes_);
    saved->eh_cleanup_steps = std::move(eh_cleanup_steps_);
    saved->destructor_lifecycle_region =
        std::move(current_destructor_lifecycle_region_);
    saved->active_lifetime_boundaries =
        std::move(active_lifetime_boundaries_);
    saved->active_try_move_boundaries =
        std::move(active_try_move_boundaries_);
    saved->nrvo_return_candidates = std::move(nrvo_return_candidates_);
    saved->nrvo_has_incompatible_return = nrvo_has_incompatible_return_;
    saved->active_catch_handlers = active_catch_handlers_;
    saved->active_constructor_function_try_handlers =
        active_constructor_function_try_handlers_;
    saved->eh_code_targets = std::move(eh_code_targets_);
    saved->eh_pads_in_flight = std::move(eh_pads_in_flight_);
    saved->deduce_return = deduce_return_type_;
    saved->this_place = current_this_place_;
    saved->member_record = current_member_record_;
    saved->member_declarator_this_type = member_declarator_this_type_;
    saved->member_declarator_this_active = member_declarator_this_active_;
    saved->complete_class_object_place =
        current_complete_class_object_place_;
    saved->collecting_default_member_initializer =
        collecting_default_member_initializer_;
    saved->structor_flag = current_structor_flag_;
    saved->structor_vtt_place = current_structor_vtt_place_;
    saved->coroutine_state = std::move(coroutine_state_);
    saved->first_plain_return_loc = first_plain_return_loc_;
    saved->has_plain_return = has_plain_return_;
    if (!preserve_lambda_context) {
        saved->suspended_lambda_context = true;
        saved->lambda_frames = std::move(lambda_stack_);
        lambda_stack_.clear();
    }
    saved->builder_checkpoint = builder_.checkpoint();
    builder_.set_current_unwind_target({});
    control_stack_.clear();
    switch_contexts_.clear();
    control_flow_regions_.clear();
    cleanup_scopes_.clear();
    eh_cleanup_steps_.clear();
    current_destructor_lifecycle_region_ = {};
    active_lifetime_boundaries_.clear();
    active_try_move_boundaries_.clear();
    nrvo_return_candidates_.clear();
    nrvo_has_incompatible_return_ = false;
    active_catch_handlers_ = 0;
    active_constructor_function_try_handlers_ = 0;
    eh_code_targets_.clear();
    eh_pads_in_flight_.clear();
    function_labels_.clear();
    local_label_scopes_.clear();
    pending_orphan_label_blocks_.clear();
    vla_sp_slot_place_ = {};
    current_this_place_ = {};
    current_member_record_ = {};
    member_declarator_this_type_ = {};
    member_declarator_this_active_ = false;
    current_complete_class_object_place_ = {};
    collecting_default_member_initializer_ = false;
    current_structor_flag_ = {};
    current_structor_vtt_place_ = {};
    coroutine_state_.reset();
    first_plain_return_loc_ = {};
    has_plain_return_ = false;

    decltype_operand_depth_ = 0;
    unevaluated_operand_depth_ = 0;
    typeid_capture_discovery_depth_ = 0;
    return saved;
}

void Session::restore_function_context(
    std::unique_ptr<BlockContextState> saved) {
    current_function_ = saved->function;
    current_result_type_ = saved->result_type;
    decltype_operand_depth_ = saved->decltype_operand_depth;
    unevaluated_operand_depth_ = saved->unevaluated_operand_depth;
    typeid_capture_discovery_depth_ =
        saved->typeid_capture_discovery_depth;
    current_prologue_ = std::move(saved->prologue);
    function_labels_ = std::move(saved->labels);
    local_label_scopes_ = std::move(saved->local_label_scopes);
    pending_orphan_label_blocks_ = std::move(saved->orphan_blocks);
    vla_sp_slot_place_ = saved->vla_slot;
    control_stack_ = std::move(saved->control_stack);
    switch_contexts_ = std::move(saved->switch_contexts);
    control_flow_regions_ = std::move(saved->control_flow_regions);
    cleanup_scopes_ = std::move(saved->cleanup_scopes);
    eh_cleanup_steps_ = std::move(saved->eh_cleanup_steps);
    current_destructor_lifecycle_region_ =
        std::move(saved->destructor_lifecycle_region);
    active_lifetime_boundaries_ =
        std::move(saved->active_lifetime_boundaries);
    active_try_move_boundaries_ =
        std::move(saved->active_try_move_boundaries);
    nrvo_return_candidates_ = std::move(saved->nrvo_return_candidates);
    nrvo_has_incompatible_return_ = saved->nrvo_has_incompatible_return;
    active_catch_handlers_ = saved->active_catch_handlers;
    active_constructor_function_try_handlers_ =
        saved->active_constructor_function_try_handlers;
    eh_code_targets_ = std::move(saved->eh_code_targets);
    eh_pads_in_flight_ = std::move(saved->eh_pads_in_flight);
    deduce_return_type_ = saved->deduce_return;
    current_this_place_ = saved->this_place;
    current_member_record_ = saved->member_record;
    member_declarator_this_type_ = saved->member_declarator_this_type;
    member_declarator_this_active_ = saved->member_declarator_this_active;
    current_complete_class_object_place_ =
        saved->complete_class_object_place;
    collecting_default_member_initializer_ =
        saved->collecting_default_member_initializer;
    current_structor_flag_ = saved->structor_flag;
    current_structor_vtt_place_ = saved->structor_vtt_place;
    coroutine_state_ = std::move(saved->coroutine_state);
    first_plain_return_loc_ = saved->first_plain_return_loc;
    has_plain_return_ = saved->has_plain_return;
    if (saved->suspended_lambda_context) {
        lambda_stack_ = std::move(saved->lambda_frames);
    }
    builder_.rollback_to(saved->builder_checkpoint);
}

cir::EntityId Session::synthesize_block_helper(
    std::string_view name,
    bool has_destination,
    const std::function<void(cir::InstId destination, cir::InstId source)>&
        emit_body,
    SrcLoc loc) {
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId void_ptr = builder_.pointer_type(void_type);

    std::vector<ParamInput> params;
    if (has_destination) {
        ParamInput destination;
        destination.name = ".block.helper.dst";
        destination.type = file_.type_ref(void_ptr);
        destination.loc = loc;
        params.push_back(std::move(destination));
    }
    ParamInput source;
    source.name = ".block.helper.src";
    source.type = file_.type_ref(void_ptr);
    source.loc = loc;
    params.push_back(std::move(source));

    std::vector<cir::TypeRef> param_types;
    for (const ParamInput& param : params) {
        param_types.push_back(param.type);
    }
    cir::TypeId helper_type =
        function_type(file_.type_ref(void_type), param_types, false, true);

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags helper_flags;
    helper_flags.is_static = true;
    FunctionDeclStart fn = begin_function_type(name, helper_type,
                                               file_.type_ref(void_type),
                                               params, loc, helper_flags);
    cir::InstId destination_value{};
    cir::InstId source_value{};
    if (has_destination) {
        destination_value = fn.function.parameters[0].value.inst;
        source_value = fn.function.parameters[1].value.inst;
    } else {
        source_value = fn.function.parameters[0].value.inst;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("helper.body");
    emit_body(destination_value, source_value);
    cir::Fragment body_fragment = finish_fragment_block(block, previous);
    finish_function(make_stmt_result(std::move(body_fragment)), loc);
    restore_function_context(std::move(saved));
    return fn.decl.entity;
}

DeclResult Session::declare_block_byref_variable(
    std::string_view name,
    cir::TypeId type,
    std::optional<ExprResult> initializer,
    SrcLoc loc,
    DeclFlags flags) {
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId void_ptr = builder_.pointer_type(void_type);
    cir::TypeId int_type = builder_.int_type();
    uint32_t index = ++block_literal_counter_;

    cir::EntityId v_entity = builder_.add_entity(cir::EntityKind::Variable,
                                                 name,
                                                 type,
                                                 {},
                                                 loc,
                                                 cir::StorageDuration::Automatic,
                                                 cir::MemorySpace::Default,
                                                 flags.to_cir());
    file_.entity_mut(v_entity).is_definition = true;
    file_.entity_mut(v_entity).is_block_byref = true;
    file_.entity_mut(v_entity).qualifiers = flags.type_qualifiers;
    apply_attributes(v_entity, AttributeTarget::Variable, flags.attrs, loc);

    cir::TypeId resolved = file_.resolved_type(type);
    bool wants_helpers = file_.valid(resolved) &&
        file_.type(resolved).kind == cir::TypeKind::BlockPointer;

    std::string tag = ".block.byref." + std::to_string(index);
    std::vector<RecordFieldInput> fields;
    auto field = [&](std::string field_name, cir::TypeId field_type) {
        RecordFieldInput input;
        input.name = std::move(field_name);
        input.type = field_type;
        input.loc = loc;
        fields.push_back(std::move(input));
    };
    field("__isa", void_ptr);
    field("__forwarding", void_ptr);
    field("__flags", int_type);
    field("__size", int_type);
    if (wants_helpers) {
        field("__byref_keep", void_ptr);
        field("__byref_destroy", void_ptr);
    }
    field(std::string(name), type);
    cir::TypeId cell_record =
        define_record(cir::RecordKind::Struct, tag, std::move(fields), loc,
                      RecordLayoutOptions{.arc_managed_aggregate = true})
            .type;
    const cir::RecordFieldFact* value_field =
        find_record_field(file_, cell_record, name);

    cir::EntityId keep_entity{};
    cir::EntityId destroy_entity{};
    if (wants_helpers && value_field) {
        cir::TypeId assign_type = function_type(
            file_.type_ref(void_type),
            {file_.type_ref(void_ptr), file_.type_ref(void_ptr),
             file_.type_ref(int_type)},
            false, true);
        cir::TypeId dispose_type = function_type(
            file_.type_ref(void_type),
            {file_.type_ref(void_ptr), file_.type_ref(int_type)},
            false, true);
        cir::EntityId assign_fn =
            extern_runtime_function("_Block_object_assign", assign_type, loc);
        cir::EntityId dispose_fn =
            extern_runtime_function("_Block_object_dispose", dispose_type, loc);
        int64_t field_flags =
            static_cast<int64_t>(darwin_blocks::BLOCK_FIELD_IS_BLOCK |
                                 darwin_blocks::BLOCK_BYREF_CALLER);
        cir::TypeId cell_ptr = builder_.pointer_type(cell_record);
        keep_entity = synthesize_block_helper(
            "__block_byref_keep_" + std::to_string(index), true,
            [&](cir::InstId destination, cir::InstId source) {
                cir::InstId dst_place = builder_.deref(
                    builder_.cast(cell_ptr, destination, "arith", loc), loc);
                cir::InstId src_place = builder_.deref(
                    builder_.cast(cell_ptr, source, "arith", loc), loc);
                cir::InstId dst_field = builder_.field_addr(
                    dst_place, value_field->entity, value_field->type.type, loc);
                cir::InstId src_field = builder_.field_addr(
                    src_place, value_field->entity, value_field->type.type, loc);
                cir::InstId dst_addr = builder_.cast(
                    void_ptr, builder_.addr_of(dst_field, loc), "arith", loc);
                cir::InstId src_value = builder_.cast(
                    void_ptr, builder_.load(src_field, loc), "arith", loc);
                cir::InstId flag_value = builder_.integer_literal(
                    field_flags, "byref.flags", loc);
                builder_.call(assign_fn, void_type,
                              {dst_addr, src_value, flag_value}, loc);
            },
            loc);
        destroy_entity = synthesize_block_helper(
            "__block_byref_destroy_" + std::to_string(index), false,
            [&](cir::InstId, cir::InstId source) {
                cir::InstId src_place = builder_.deref(
                    builder_.cast(cell_ptr, source, "arith", loc), loc);
                cir::InstId src_field = builder_.field_addr(
                    src_place, value_field->entity, value_field->type.type, loc);
                cir::InstId src_value = builder_.cast(
                    void_ptr, builder_.load(src_field, loc), "arith", loc);
                cir::InstId flag_value = builder_.integer_literal(
                    field_flags, "byref.flags", loc);
                builder_.call(dispose_fn, void_type, {src_value, flag_value},
                              loc);
            },
            loc);
    }

    cir::EntityId cell_entity = builder_.add_entity(
        cir::EntityKind::Variable, ".block.byref.cell." + std::to_string(index),
        cell_record, {}, loc, cir::StorageDuration::Automatic,
        cir::MemorySpace::Default, {});
    file_.entity_mut(cell_entity).is_definition = true;

    size_t cell_size = cir::size_of_type(file_, cell_record).value_or(0);
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("byref.cell");
    cir::InstId cell_place = builder_.local_place(cell_entity, cell_record, loc);
    auto cell_field_place = [&](std::string_view field_name) -> cir::InstId {
        const cir::RecordFieldFact* fact =
            find_record_field(file_, cell_record, field_name);
        if (!fact) {
            return {};
        }
        return builder_.field_addr(cell_place, fact->entity, fact->type.type,
                                   loc);
    };
    cir::InstId null_ptr = builder_.cast(
        void_ptr, builder_.integer_literal(0, "0", loc), "arith", loc);
    builder_.store(cell_field_place("__isa"), null_ptr, loc);
    builder_.store(cell_field_place("__forwarding"),
                   builder_.cast(void_ptr, builder_.addr_of(cell_place, loc),
                                 "arith", loc),
                   loc);
    builder_.store(
        cell_field_place("__flags"),
        builder_.integer_literal(
            wants_helpers
                ? static_cast<int64_t>(darwin_blocks::BLOCK_HAS_COPY_DISPOSE)
                : 0,
            "byref.flags", loc),
        loc);
    builder_.store(cell_field_place("__size"),
                   builder_.integer_literal(static_cast<int64_t>(cell_size),
                                            "byref.size", loc),
                   loc);
    if (wants_helpers && keep_entity.valid() && destroy_entity.valid()) {
        builder_.store(cell_field_place("__byref_keep"),
                       builder_.cast(void_ptr,
                                     builder_.function_to_pointer(keep_entity,
                                                                  loc),
                                     "arith", loc),
                       loc);
        builder_.store(
            cell_field_place("__byref_destroy"),
            builder_.cast(void_ptr,
                          builder_.function_to_pointer(destroy_entity, loc),
                          "arith", loc),
            loc);
    }

    cir::InstId value_place{};
    if (value_field) {
        cir::InstId forwarding =
            builder_.load(cell_field_place("__forwarding"), loc);
        cir::InstId forwarded = builder_.deref(
            builder_.cast(builder_.pointer_type(cell_record), forwarding,
                          "arith", loc),
            loc);
        value_place = builder_.field_addr(forwarded, value_field->entity,
                                          value_field->type.type, loc);
    }
    cir::Fragment fragment = finish_fragment_block(block, previous);

    bind_entity(name,
                cir::LookupNamespace::Ordinary,
                v_entity,
                type,
                false,
                false,
                true,
                value_place,
                loc);
    block_byref_cells_[entity_key(v_entity)] =
        ByrefCellInfo{cell_entity, cell_record, cell_place, wants_helpers};

    bool has_error = false;
    if (initializer.has_value() && value_place.valid()) {
        if (initializer->category == ValueCategory::InitList ||
            is_aggregate_type(type)) {
            bool init_had_error = initializer->has_error;
            cir::Fragment init_fragment = emit_initializer_for_place(
                value_place, type, std::move(*initializer), loc);
            has_error = init_had_error;
            fragment = chain(std::move(fragment), std::move(init_fragment), loc);
        } else {
            ExprResult value =
                convert_to(std::move(*initializer), type, UseContext::Init, loc);
            has_error = value.has_error;
            fragment = chain(std::move(fragment), std::move(value.fragment), loc);
            cir::BlockId store_previous = builder_.current_block();
            cir::BlockId store_block = begin_fragment_block("byref.init");
            builder_.store(value_place, value.value, loc);
            fragment = chain(std::move(fragment),
                             finish_fragment_block(store_block, store_previous),
                             loc);
        }
    }

    DeclResult result;
    result.fragment = std::move(fragment);
    result.entity = v_entity;
    result.type = type;
    result.place = value_place;
    result.has_error = has_error;
    return result;
}

bool Session::make_block_byref_access(cir::EntityId entity,
                                      ExprResult& result,
                                      SrcLoc loc) {
    auto found = block_byref_cells_.find(entity_key(entity));
    if (found == block_byref_cells_.end()) {
        return false;
    }
    const ByrefCellInfo& info = found->second;
    const cir::RecordFieldFact* forwarding_field =
        find_record_field(file_, info.cell_record, "__forwarding");
    const cir::RecordFieldFact* value_field = find_record_field(
        file_, info.cell_record,
        file_.entity(entity).name.valid() ? file_.name(file_.entity(entity).name)
                                          : "");
    if (!forwarding_field || !value_field) {
        return false;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("byref.access");
    cir::InstId cell_place =
        builder_.local_place(info.cell_entity, info.cell_record, loc);
    cir::InstId forwarding = builder_.load(
        builder_.field_addr(cell_place, forwarding_field->entity,
                            forwarding_field->type.type, loc),
        loc);
    cir::InstId forwarded = builder_.deref(
        builder_.cast(builder_.pointer_type(info.cell_record), forwarding,
                      "arith", loc),
        loc);
    cir::InstId value_place = builder_.field_addr(
        forwarded, value_field->entity, value_field->type.type, loc);
    result.fragment = finish_fragment_block(block, previous);
    result.place = value_place;
    result.category = ValueCategory::LValue;
    return true;
}

cir::TypeId Session::block_header_record_type(SrcLoc loc) {
    if (block_header_record_.valid()) {
        return block_header_record_;
    }
    cir::TypeId void_ptr =
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
    std::vector<RecordFieldInput> fields;
    auto field = [&](const char* name, cir::TypeId type) {
        RecordFieldInput input;
        input.name = name;
        input.type = type;
        input.loc = loc;
        fields.push_back(std::move(input));
    };
    field("__isa", void_ptr);
    field("__flags", builder_.int_type());
    field("__reserved", builder_.int_type());
    field("__invoke", void_ptr);
    field("__descriptor", void_ptr);
    RecordDeclResult record = define_record(cir::RecordKind::Struct,
                                            ".block.header",
                                            std::move(fields),
                                            loc,
                                            {});
    block_header_record_ = record.type;
    return block_header_record_;
}

BlockLiteralStart Session::begin_block_literal(
    std::vector<ParamInput> params,
    const std::vector<std::string>& body_identifiers,
    SrcLoc loc) {
    BlockLiteralStart start;
    start.index = ++block_literal_counter_;
    start.loc = loc;
    start.params = params;

    std::vector<std::string> seen;
    for (const std::string& name : body_identifiers) {
        bool duplicate = false;
        for (const std::string& prior : seen) {
            if (prior == name) {
                duplicate = true;
                break;
            }
        }
        if (duplicate) {
            continue;
        }
        seen.push_back(name);
        bool is_param = false;
        for (const ParamInput& param : params) {
            if (param.name == name) {
                is_param = true;
                break;
            }
        }
        if (is_param) {
            continue;
        }
        const cir::Binding* binding = lookup_ordinary_binding(name);
        if (!binding || binding->is_type_name || binding->entities.empty()) {
            continue;
        }
        cir::EntityId entity = binding->entities.back();
        if (!file_.valid(entity)) {
            continue;
        }
        const cir::Entity& record = file_.entity(entity);
        if (record.kind != cir::EntityKind::Variable &&
            record.kind != cir::EntityKind::Parameter) {
            continue;
        }
        if (record.storage_duration != cir::StorageDuration::Automatic &&
            record.storage_duration != cir::StorageDuration::Parameter) {
            continue;
        }
        if (!binding->place.valid()) {
            continue;
        }
        BlockCapture capture;
        capture.name = name;
        capture.object_type = record.type;
        if (record.is_block_byref) {
            auto cell = block_byref_cells_.find(entity_key(entity));
            if (cell == block_byref_cells_.end()) {
                continue;
            }
            capture.is_byref = true;
            capture.byref_record = cell->second.cell_record;
            capture.source_place = cell->second.cell_place;
            capture.type = builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
        } else {
            capture.source_place = binding->place;
            capture.type = record.type;
        }
        start.captures.push_back(std::move(capture));
    }

    std::string tag = ".block.literal." + std::to_string(start.index);
    cir::TypeId void_ptr =
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
    std::vector<RecordFieldInput> fields;
    auto field = [&](const char* name, cir::TypeId type) {
        RecordFieldInput input;
        input.name = name;
        input.type = type;
        input.loc = loc;
        fields.push_back(std::move(input));
    };
    field("__isa", void_ptr);
    field("__flags", builder_.int_type());
    field("__reserved", builder_.int_type());
    field("__invoke", void_ptr);
    field("__descriptor", void_ptr);
    for (const BlockCapture& capture : start.captures) {
        field(capture.name.c_str(), capture.type);
    }
    RecordDeclResult record =
        define_record(cir::RecordKind::Struct, tag, std::move(fields), loc,
                      RecordLayoutOptions{.arc_managed_aggregate = true});
    start.literal_record = record.type;

    block_context_stack_.push_back(save_function_context());

    std::string invoke_name = "__block_invoke_" + std::to_string(start.index);
    std::vector<ParamInput> invoke_params;
    ParamInput literal_param;
    literal_param.name = ".block.literal";
    literal_param.type = file_.type_ref(void_ptr);
    literal_param.loc = loc;
    invoke_params.push_back(literal_param);
    for (const ParamInput& param : params) {
        invoke_params.push_back(param);
    }
    std::vector<cir::TypeRef> invoke_param_types;
    for (const ParamInput& param : invoke_params) {
        invoke_param_types.push_back(param.type);
    }

    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId invoke_type =
        function_type(file_.type_ref(void_type), invoke_param_types, false, true);
    DeclFlags invoke_flags;
    invoke_flags.is_static = true;
    FunctionDeclStart fn =
        begin_function_type(invoke_name, invoke_type, file_.type_ref(void_type),
                            invoke_params, loc, invoke_flags);
    start.invoke_entity = fn.decl.entity;
    start.invoke_function = fn.function.function;
    current_result_type_ = {};
    deduce_return_type_ = true;

    if (!start.captures.empty() && !fn.function.parameters.empty()) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(start.literal_record);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("block.captures");
        cir::InstId literal_value = fn.function.parameters[0].value.inst;
        cir::InstId literal_typed = builder_.cast(
            builder_.pointer_type(start.literal_record), literal_value, "arith", loc);
        cir::InstId literal_place = builder_.deref(literal_typed, loc);
        for (BlockCapture& capture : start.captures) {
            const cir::RecordFieldFact* field_fact = nullptr;
            if (facts) {
                for (const cir::RecordFieldFact& candidate : facts->fields) {
                    if (candidate.name.valid() &&
                        file_.name(candidate.name) == capture.name) {
                        field_fact = &candidate;
                        break;
                    }
                }
            }
            if (!field_fact) {
                continue;
            }
            cir::InstId capture_place = builder_.field_addr(
                literal_place, field_fact->entity, field_fact->type.type, loc);
            if (capture.is_byref) {

                cir::TypeId cell_ptr = builder_.pointer_type(capture.byref_record);
                cir::InstId cell_value = builder_.load(capture_place, loc);
                cir::InstId cell_place = builder_.deref(
                    builder_.cast(cell_ptr, cell_value, "arith", loc), loc);
                const cir::RecordFieldFact* forwarding_field =
                    find_record_field(file_, capture.byref_record, "__forwarding");
                const cir::RecordFieldFact* value_field =
                    find_record_field(file_, capture.byref_record, capture.name);
                if (forwarding_field && value_field) {
                    cir::InstId forwarding = builder_.load(
                        builder_.field_addr(cell_place, forwarding_field->entity,
                                            forwarding_field->type.type, loc),
                        loc);
                    cir::InstId forwarded = builder_.deref(
                        builder_.cast(cell_ptr, forwarding, "arith", loc), loc);
                    capture_place = builder_.field_addr(
                        forwarded, value_field->entity, value_field->type.type,
                        loc);
                }
            }
            bind_entity(capture.name,
                        cir::LookupNamespace::Ordinary,
                        field_fact->entity,
                        capture.is_byref ? capture.object_type : capture.type,
                        false,
                        false,
                        true,
                        capture_place,
                        loc);
        }
        cir::Fragment fragment = finish_fragment_block(block, previous);
        current_prologue_ = chain(std::move(current_prologue_), std::move(fragment), loc);
    }
    return start;
}

ExprResult Session::finish_block_literal(BlockLiteralStart start,
                                         StmtResult body,
                                         SrcLoc loc) {

    cir::TypeId return_type = current_result_type_.valid()
        ? current_result_type_
        : file_.builtin_type(cir::BuiltinTypeKind::Void);
    std::vector<cir::TypeRef> invoke_param_types;
    invoke_param_types.push_back(file_.type_ref(
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void))));
    std::vector<cir::TypeRef> block_param_types;
    for (const ParamInput& param : start.params) {
        invoke_param_types.push_back(param.type);
        block_param_types.push_back(param.type);
    }
    cir::TypeId invoke_type = function_type(file_.type_ref(return_type),
                                            invoke_param_types, false, true);
    file_.entity_mut(start.invoke_entity).type = invoke_type;
    if (file_.valid(start.invoke_function)) {
        cir::Function& fn = file_.function_mut(start.invoke_function);
        fn.type = invoke_type;
        fn.result_type = return_type;
    }
    current_result_type_ = return_type;
    finish_function(std::move(body), loc);

    if (!block_context_stack_.empty()) {
        std::unique_ptr<BlockContextState> saved =
            std::move(block_context_stack_.back());
        block_context_stack_.pop_back();
        restore_function_context(std::move(saved));
    }

    cir::TypeId block_fn_type = function_type(file_.type_ref(return_type),
                                              block_param_types, false, true);
    cir::TypeId block_ptr = block_pointer_type(file_.type_ref(block_fn_type));

    std::vector<cir::TypeId> signature_params;
    for (const ParamInput& param : start.params) {
        signature_params.push_back(param.type.type);
    }
    std::string signature =
        encode_signature(file_, return_type, signature_params);
    std::string sig_name = ".block.signature." + std::to_string(start.index);
    cir::TypeId char_type = builder_.char_type();
    cir::TypeId sig_array = file_.array_type(
        file_.type_ref(char_type), cir::ArraySizeKind::Constant,
        signature.size() + 1);
    cir::EntityId sig_entity = builder_.add_entity(cir::EntityKind::Variable,
                                                   sig_name,
                                                   sig_array,
                                                   {},
                                                   loc,
                                                   cir::StorageDuration::Static,
                                                   cir::MemorySpace::Default,
                                                   {});
    {
        cir::Entity& record = file_.entity_mut(sig_entity);
        record.is_definition = true;
        record.linkage = cir::LinkageKind::Internal;
        record.has_static_initializer = true;
        record.static_initializer_bytes.assign(signature.begin(), signature.end());
        record.static_initializer_bytes.push_back(0);
    }

    std::vector<std::pair<const BlockCapture*, uint32_t>> managed_captures;
    for (const BlockCapture& capture : start.captures) {
        if (capture.is_byref) {
            managed_captures.emplace_back(&capture,
                                          darwin_blocks::BLOCK_FIELD_IS_BYREF);
            continue;
        }
        cir::TypeId resolved_capture = file_.resolved_type(capture.type);
        if (file_.valid(resolved_capture) &&
            file_.type(resolved_capture).kind == cir::TypeKind::BlockPointer) {
            managed_captures.emplace_back(&capture,
                                          darwin_blocks::BLOCK_FIELD_IS_BLOCK);
            continue;
        }

        if (arc_enabled() && arc_retainable_type(capture.type)) {
            managed_captures.emplace_back(&capture,
                                          darwin_blocks::BLOCK_FIELD_IS_OBJECT);
        }
    }
    cir::EntityId copy_helper{};
    cir::EntityId dispose_helper{};
    if (!managed_captures.empty()) {
        cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
        cir::TypeId void_ptr = builder_.pointer_type(void_type);
        cir::TypeId int_type = builder_.int_type();
        cir::TypeId assign_type = function_type(
            file_.type_ref(void_type),
            {file_.type_ref(void_ptr), file_.type_ref(void_ptr),
             file_.type_ref(int_type)},
            false, true);
        cir::TypeId dispose_type = function_type(
            file_.type_ref(void_type),
            {file_.type_ref(void_ptr), file_.type_ref(int_type)},
            false, true);
        cir::EntityId assign_fn =
            extern_runtime_function("_Block_object_assign", assign_type, loc);
        cir::EntityId dispose_fn =
            extern_runtime_function("_Block_object_dispose", dispose_type, loc);
        cir::TypeId literal_ptr = builder_.pointer_type(start.literal_record);
        const cir::RecordFacts* literal_facts =
            file_.record_facts_for_type(start.literal_record);
        auto managed_field = [&](const BlockCapture& capture)
            -> const cir::RecordFieldFact* {
            if (!literal_facts) {
                return nullptr;
            }
            for (const cir::RecordFieldFact& candidate : literal_facts->fields) {
                if (candidate.name.valid() &&
                    file_.name(candidate.name) == capture.name) {
                    return &candidate;
                }
            }
            return nullptr;
        };
        copy_helper = synthesize_block_helper(
            "__block_copy_helper_" + std::to_string(start.index), true,
            [&](cir::InstId destination, cir::InstId source) {
                cir::InstId dst_place = builder_.deref(
                    builder_.cast(literal_ptr, destination, "arith", loc), loc);
                cir::InstId src_place = builder_.deref(
                    builder_.cast(literal_ptr, source, "arith", loc), loc);
                for (const auto& [capture, field_flags] : managed_captures) {
                    const cir::RecordFieldFact* fact = managed_field(*capture);
                    if (!fact) {
                        continue;
                    }
                    cir::InstId dst_addr = builder_.cast(
                        void_ptr,
                        builder_.addr_of(
                            builder_.field_addr(dst_place, fact->entity,
                                                fact->type.type, loc),
                            loc),
                        "arith", loc);
                    cir::InstId src_value = builder_.cast(
                        void_ptr,
                        builder_.load(builder_.field_addr(src_place, fact->entity,
                                                          fact->type.type, loc),
                                      loc),
                        "arith", loc);
                    builder_.call(
                        assign_fn, void_type,
                        {dst_addr, src_value,
                         builder_.integer_literal(
                             static_cast<int64_t>(field_flags), "field.flags",
                             loc)},
                        loc);
                }
            },
            loc);
        dispose_helper = synthesize_block_helper(
            "__block_dispose_helper_" + std::to_string(start.index), false,
            [&](cir::InstId, cir::InstId source) {
                cir::InstId src_place = builder_.deref(
                    builder_.cast(literal_ptr, source, "arith", loc), loc);
                for (const auto& [capture, field_flags] : managed_captures) {
                    const cir::RecordFieldFact* fact = managed_field(*capture);
                    if (!fact) {
                        continue;
                    }
                    cir::InstId src_value = builder_.cast(
                        void_ptr,
                        builder_.load(builder_.field_addr(src_place, fact->entity,
                                                          fact->type.type, loc),
                                      loc),
                        "arith", loc);
                    builder_.call(
                        dispose_fn, void_type,
                        {src_value,
                         builder_.integer_literal(
                             static_cast<int64_t>(field_flags), "field.flags",
                             loc)},
                        loc);
                }
            },
            loc);
    }

    size_t literal_size = cir::size_of_type(file_, start.literal_record).value_or(32);
    std::string descriptor_name = ".block.descriptor." + std::to_string(start.index);
    if (!block_descriptor_record_.valid()) {
        cir::TypeId void_ptr = builder_.pointer_type(
            file_.builtin_type(cir::BuiltinTypeKind::Void));
        std::vector<RecordFieldInput> descriptor_fields;
        auto descriptor_field = [&](const char* name, cir::TypeId type) {
            RecordFieldInput input;
            input.name = name;
            input.type = type;
            input.loc = loc;
            descriptor_fields.push_back(std::move(input));
        };
        descriptor_field("__reserved",
                         file_.builtin_type(cir::BuiltinTypeKind::ULong));
        descriptor_field("__size",
                         file_.builtin_type(cir::BuiltinTypeKind::ULong));
        descriptor_field("__signature", void_ptr);
        descriptor_field("__layout", void_ptr);
        block_descriptor_record_ = define_record(cir::RecordKind::Struct,
                                                 ".block.descriptor.shape",
                                                 std::move(descriptor_fields),
                                                 loc,
                                                 {})
                                       .type;
    }
    bool has_helpers = copy_helper.valid() && dispose_helper.valid();
    if (has_helpers && !block_descriptor_helpers_record_.valid()) {
        cir::TypeId void_ptr = builder_.pointer_type(
            file_.builtin_type(cir::BuiltinTypeKind::Void));
        std::vector<RecordFieldInput> descriptor_fields;
        auto descriptor_field = [&](const char* name, cir::TypeId type) {
            RecordFieldInput input;
            input.name = name;
            input.type = type;
            input.loc = loc;
            descriptor_fields.push_back(std::move(input));
        };
        descriptor_field("__reserved",
                         file_.builtin_type(cir::BuiltinTypeKind::ULong));
        descriptor_field("__size",
                         file_.builtin_type(cir::BuiltinTypeKind::ULong));
        descriptor_field("__copy", void_ptr);
        descriptor_field("__dispose", void_ptr);
        descriptor_field("__signature", void_ptr);
        descriptor_field("__layout", void_ptr);
        block_descriptor_helpers_record_ =
            define_record(cir::RecordKind::Struct,
                          ".block.descriptor.helpers.shape",
                          std::move(descriptor_fields),
                          loc,
                          {})
                .type;
    }
    cir::EntityId descriptor = builder_.add_entity(
        cir::EntityKind::Variable,
        descriptor_name,
        has_helpers ? block_descriptor_helpers_record_ : block_descriptor_record_,
        {},
        loc,
        cir::StorageDuration::Static,
        cir::MemorySpace::Default,
        {});
    {
        cir::Entity& record = file_.entity_mut(descriptor);
        record.is_definition = true;
        record.linkage = cir::LinkageKind::Internal;
        record.has_static_initializer = true;
        record.static_initializer_bytes.assign(has_helpers ? 48 : 32, 0);
        for (size_t i = 0; i < 8; ++i) {
            record.static_initializer_bytes[8 + i] =
                static_cast<uint8_t>((literal_size >> (i * 8)) & 0xff);
        }
        if (has_helpers) {
            record.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{16, copy_helper, 0});
            record.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{24, dispose_helper, 0});
            record.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{32, sig_entity, 0});
        } else {
            record.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{16, sig_entity, 0});
        }
    }

    if (start.captures.empty()) {

        cir::EntityId isa =
            extern_runtime_global("_NSConcreteGlobalBlock", loc);
        std::string literal_name = ".block.global." + std::to_string(start.index);
        cir::EntityId literal = builder_.add_entity(cir::EntityKind::Variable,
                                                    literal_name,
                                                    start.literal_record,
                                                    {},
                                                    loc,
                                                    cir::StorageDuration::Static,
                                                    cir::MemorySpace::Default,
                                                    {});
        cir::Entity& record = file_.entity_mut(literal);
        record.is_definition = true;
        record.linkage = cir::LinkageKind::Internal;
        record.has_static_initializer = true;
        record.static_initializer_bytes.assign(literal_size, 0);
        uint32_t flags = darwin_blocks::BLOCK_IS_GLOBAL |
                         darwin_blocks::BLOCK_HAS_SIGNATURE;
        for (size_t i = 0; i < 4; ++i) {
            record.static_initializer_bytes[8 + i] =
                static_cast<uint8_t>((flags >> (i * 8)) & 0xff);
        }
        record.static_initializer_relocations.push_back(
            cir::StaticInitializerRelocation{0, isa, 0});
        record.static_initializer_relocations.push_back(
            cir::StaticInitializerRelocation{16, start.invoke_entity, 0});
        record.static_initializer_relocations.push_back(
            cir::StaticInitializerRelocation{24, descriptor, 0});

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("block.global");
        cir::InstId place = builder_.global_place(literal, loc);
        cir::InstId address = builder_.addr_of(place, loc);
        cir::InstId typed = builder_.cast(block_ptr, address, "arith", loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = typed;
        result.type = block_ptr;
        result.category = ValueCategory::PrValue;
        return result;
    }

    const cir::RecordFacts* facts = file_.record_facts_for_type(start.literal_record);
    std::string temp_name = ".block.stack." + std::to_string(start.index);
    cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                             temp_name,
                                             start.literal_record,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(temp).is_definition = true;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("block.stack");
    cir::InstId literal_place = builder_.local_place(temp, start.literal_record, loc);
    auto field_place = [&](const char* name) -> cir::InstId {
        if (!facts) {
            return {};
        }
        for (const cir::RecordFieldFact& candidate : facts->fields) {
            if (candidate.name.valid() && file_.name(candidate.name) == name) {
                return builder_.field_addr(literal_place, candidate.entity,
                                           candidate.type.type, loc);
            }
        }
        return {};
    };
    cir::TypeId void_ptr =
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
    cir::EntityId isa = extern_runtime_global("_NSConcreteStackBlock", loc);
    cir::InstId isa_place_value = builder_.global_place(isa, loc);
    cir::InstId isa_address = builder_.cast(
        void_ptr, builder_.addr_of(isa_place_value, loc), "arith", loc);
    builder_.store(field_place("__isa"), isa_address, loc);
    uint32_t literal_flags = darwin_blocks::BLOCK_HAS_SIGNATURE;
    if (has_helpers) {
        literal_flags |= darwin_blocks::BLOCK_HAS_COPY_DISPOSE;
    }
    builder_.store(field_place("__flags"),
                   builder_.integer_literal(
                       static_cast<int64_t>(literal_flags), "flags", loc),
                   loc);
    builder_.store(field_place("__reserved"), builder_.integer_literal(0, "0", loc), loc);
    cir::InstId invoke_pointer = builder_.cast(
        void_ptr, builder_.function_to_pointer(start.invoke_entity, loc), "arith", loc);
    builder_.store(field_place("__invoke"), invoke_pointer, loc);
    cir::InstId descriptor_place = builder_.global_place(descriptor, loc);
    cir::InstId descriptor_address = builder_.cast(
        void_ptr, builder_.addr_of(descriptor_place, loc), "arith", loc);
    builder_.store(field_place("__descriptor"), descriptor_address, loc);
    for (const BlockCapture& capture : start.captures) {
        cir::InstId value;
        if (capture.is_byref) {
            value = builder_.cast(void_ptr,
                                  builder_.addr_of(capture.source_place, loc),
                                  "arith", loc);
        } else {
            value = builder_.lvalue_to_rvalue(capture.source_place, loc);
        }
        builder_.store(field_place(capture.name.c_str()), value, loc);
    }
    cir::InstId address = builder_.addr_of(literal_place, loc);
    cir::InstId typed = builder_.cast(block_ptr, address, "arith", loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = typed;
    result.type = block_ptr;
    result.category = ValueCategory::PrValue;
    result.name = ".block.stack.literal";
    return result;
}

} // namespace aburi::collect
