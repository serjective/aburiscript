#include "collect.h"
#include "collect_template_state.h"

#include <algorithm>
#include <limits>
#include <string>
#include <unordered_set>
#include <utility>

namespace aburi::collect {

StructuredBindingStart Session::begin_structured_binding(
    std::vector<StructuredBindingNameInput> names,
    SrcLoc loc) {
    StructuredBindingStart start;
    start.loc = loc;
    start.names = std::move(names);
    start.backing_name = ".structured.binding." +
        std::to_string(file_.entity_ids().size());

    std::vector<std::string> introduced;
    introduced.reserve(start.names.size());
    for (const StructuredBindingNameInput& input : start.names) {
        if (input.name.empty()) {
            report_error("structured binding name cannot be empty", input.loc);
            start.has_error = true;
            continue;
        }
        if (std::find(introduced.begin(), introduced.end(), input.name) !=
            introduced.end()) {
            report_error("redefinition of structured binding '" +
                             input.name + "'",
                         input.loc);
            start.has_error = true;
        }
        introduced.push_back(input.name);

        cir::EntityId entity = builder_.add_entity(
            cir::EntityKind::StructuredBinding,
            input.name,
            builder_.unknown_type(),
            {},
            input.loc,
            cir::StorageDuration::Unknown,
            cir::MemorySpace::Default,
            {});
        file_.entity_mut(entity).is_definition = true;
        file_.entity_mut(entity).owning_function = current_function_entity();
        apply_attributes(entity, AttributeTarget::Variable,
                         input.attrs, input.loc);
        cir::BindingId binding = bind_entity(
            input.name,
            cir::LookupNamespace::Ordinary,
            entity,
            builder_.unknown_type(),
            false,
            false,
            true,
            {},
            input.loc);
        start.entities.push_back(entity);
        start.bindings.push_back(binding);
    }
    return start;
}

void Session::register_structured_binding_pack(
    std::string_view name,
    cir::EntityId declaration,
    const std::vector<cir::EntityId>& elements) {
    std::string key(name);
    tstate().function_parameter_pack_names_.insert(key);
    uint64_t declaration_index =
        static_cast<uint64_t>(declaration.index);
    journal_speculative_set_entry(
        "structured binding pack declaration identity",
        tstate().function_parameter_pack_params_,
        declaration_index);
    tstate().function_parameter_pack_params_.insert(
        declaration_index);
    std::vector<FunctionParameterPackElement>& projected =
        tstate().function_parameter_pack_elements_[key];
    projected.clear();
    projected.reserve(elements.size());
    for (cir::EntityId entity : elements) {
        if (!entity.valid() || !file_.valid(entity)) {
            continue;
        }
        uint64_t entity_index = static_cast<uint64_t>(entity.index);
        journal_speculative_set_entry(
            "structured binding pack element identity",
            tstate().function_parameter_pack_params_,
            entity_index);
        tstate().function_parameter_pack_params_.insert(
            entity_index);
        FunctionParameterPackElement element;
        element.entity = entity;
        element.type = file_.entity(entity).type;
        element.loc = file_.entity(entity).loc;
        projected.push_back(element);
    }
    if (current_scope_ != InvalidScopeId && current_scope_ < scopes_.size()) {
        scopes_[current_scope_].structured_binding_packs.emplace_back(
            std::move(key), declaration);
    }
}

DeclResult Session::finish_structured_binding(StructuredBindingStart start,
                                              DeclResult backing,
                                              SrcLoc loc,
                                              bool is_condition,
                                              StructuredBindingTupleInput tuple) {
    backing.has_error = backing.has_error || start.has_error;
    if (!backing.entity.valid() || !file_.valid(backing.entity)) {
        backing.has_error = true;
        return backing;
    }

    cir::Entity& backing_entity = file_.entity_mut(backing.entity);
    backing_entity.object_origin =
        cir::EntityObjectOrigin::StructuredBindingBacking;
    if (!backing_entity.semantic_context.valid()) {
        backing_entity.semantic_context = current_decl_context();
        backing_entity.lexical_context = current_decl_context();
    }
    cir::EntityId enclosing_function = current_function_entity();
    if (enclosing_function.valid() &&
        !backing_entity.owning_function.valid()) {
        backing_entity.owning_function = enclosing_function;
    }
    if (enclosing_function.valid()) {
        uint32_t ordinal = 0;
        for (cir::EntityId prior : file_.entity_ids()) {
            if (prior == backing.entity) {
                break;
            }
            const cir::Entity& candidate = file_.entity(prior);
            if (candidate.object_origin ==
                    cir::EntityObjectOrigin::StructuredBindingBacking &&
                candidate.owning_function == enclosing_function) {
                ++ordinal;
            }
        }
        backing_entity.local_name_ordinal = ordinal;
    }

    cir::TypeRef decomposed = type_ref(backing.type);
    cir::TypeId resolved_backing = file_.resolved_type(backing.type);
    if (file_.valid(resolved_backing) &&
        (file_.type(resolved_backing).kind == cir::TypeKind::LValueReference ||
         file_.type(resolved_backing).kind == cir::TypeKind::RValueReference)) {
        decomposed = file_.reference_referred_ref(resolved_backing);
    } else {
        decomposed.qualifiers = static_cast<uint8_t>(
            decomposed.qualifiers | backing_entity.qualifiers);
    }

    cir::StructuredBindingFact fact;
    fact.backing = backing.entity;
    fact.decomposed_type = decomposed;
    fact.is_condition = is_condition;
    fact.loc = loc;
    for (const StructuredBindingNameInput& input : start.names) {
        fact.source_names.push_back(file_.intern_name(input.name));
    }

    size_t pack_source_index = std::numeric_limits<size_t>::max();
    for (size_t i = 0; i < start.names.size(); ++i) {
        if (start.names[i].is_pack) {
            pack_source_index = i;
            break;
        }
    }
    bool has_pack = pack_source_index != std::numeric_limits<size_t>::max();
    fact.has_pack = has_pack;
    fact.pack_position = has_pack
        ? static_cast<uint32_t>(pack_source_index)
        : std::numeric_limits<uint32_t>::max();
    auto arity_matches = [&](size_t element_count) {
        return has_pack
            ? element_count + 1 >= start.entities.size()
            : element_count == start.entities.size();
    };
    auto source_index_for_projection = [&](size_t projection_index,
                                           size_t element_count) {
        if (!has_pack) {
            return projection_index;
        }
        size_t fixed_count = start.entities.size() - 1;
        size_t pack_count = element_count >= fixed_count
            ? element_count - fixed_count
            : 0;
        if (projection_index < pack_source_index) {
            return projection_index;
        }
        if (projection_index < pack_source_index + pack_count) {
            return pack_source_index;
        }
        return projection_index - pack_count + 1;
    };
    auto projection_loc = [&](size_t projection_index,
                              size_t element_count) {
        size_t source = source_index_for_projection(projection_index,
                                                    element_count);
        return source < start.names.size() ? start.names[source].loc : loc;
    };

    std::vector<cir::StructuredBindingProjectionFact> projections;
    cir::TypeId resolved = file_.resolved_type(decomposed.type);
    if (is_dependent_type(resolved)) {
        fact.strategy = cir::StructuredBindingStrategy::Dependent;
        fact.is_dependent = true;
        projections.resize(start.entities.size());
        for (size_t i = 0; i < projections.size(); ++i) {
            projections[i].binding = start.entities[i];
            projections[i].type = type_ref(resolved);
            projections[i].referenced_type = type_ref(resolved);
            projections[i].index = static_cast<uint32_t>(i);
            projections[i].is_dependent = true;
            projections[i].loc = start.names[i].loc;
        }
        if (collecting_pattern_) {
            bump_pattern_taint();
            mark_pattern_unusable();
        }
    } else if (file_.valid(resolved) &&
               file_.type(resolved).kind == cir::TypeKind::Array) {
        fact.strategy = cir::StructuredBindingStrategy::Array;
        const auto& array = std::get<cir::ArrayTypePayload>(
            file_.type_payload(resolved));
        if (!array.size.has_value()) {
            report_error("cannot decompose an array of unknown bound", loc);
            backing.has_error = true;
        }
        size_t size = array.size.value_or(0);
        if (!arity_matches(size)) {
            report_error("structured binding declares " +
                             std::to_string(start.entities.size()) +
                             (has_pack
                                  ? " entries including a pack, but the array decomposes into "
                                  : " names, but the array decomposes into ") +
                             std::to_string(size) + " elements",
                         loc);
            backing.has_error = true;
        }
        cir::TypeRef element = array.element_type;
        element.qualifiers = static_cast<uint8_t>(
            element.qualifiers | decomposed.qualifiers);
        projections.resize(has_pack && arity_matches(size)
                               ? size
                               : start.entities.size());
        for (size_t i = 0; i < projections.size(); ++i) {
            size_t source = source_index_for_projection(i, projections.size());
            projections[i].binding = source < start.entities.size()
                ? start.entities[source]
                : cir::EntityId{};
            projections[i].type = element;
            projections[i].referenced_type = element;
            projections[i].index = static_cast<uint32_t>(i);
            projections[i].loc = projection_loc(i, projections.size());
            projections[i].is_pack_element = has_pack &&
                source == pack_source_index;
        }
    } else if (tuple.selected) {
        fact.strategy = cir::StructuredBindingStrategy::Tuple;
        backing.has_error = backing.has_error || tuple.has_error;
        size_t tuple_count = tuple.elements.size();
        projections.resize(has_pack && arity_matches(tuple_count)
                               ? tuple_count
                               : start.entities.size());
        for (size_t i = 0; i < projections.size(); ++i) {
            size_t source = source_index_for_projection(i, projections.size());
            projections[i].binding = source < start.entities.size()
                ? start.entities[source]
                : cir::EntityId{};
            projections[i].index = static_cast<uint32_t>(i);
            projections[i].loc = projection_loc(i, projections.size());
            projections[i].is_pack_element = has_pack &&
                source == pack_source_index;
            if (i >= tuple.elements.size()) {
                projections[i].type = type_ref(builder_.unknown_type());
                projections[i].referenced_type = projections[i].type;
                continue;
            }

            StructuredBindingTupleElementInput& element = tuple.elements[i];
            projections[i].type = element.element_type;
            cir::ReferenceKind reference_kind =
                element.initializer.category == ValueCategory::LValue
                    ? cir::ReferenceKind::LValue
                    : cir::ReferenceKind::RValue;
            cir::TypeId holder_type = reference_type(
                element.element_type, reference_kind);
            projections[i].referenced_type = type_ref(holder_type);

            DeclFlags holder_flags;
            holder_flags.suppress_name_binding = true;
            holder_flags.is_thread_local =
                backing_entity.storage_duration == cir::StorageDuration::Thread;
            std::string holder_name = start.backing_name + ".element." +
                std::to_string(i);
            bool local = current_function_entity().valid();
            holder_flags.is_static = local &&
                backing_entity.storage_duration == cir::StorageDuration::Static;
            DeclResult holder = local
                ? declare_local_variable(holder_name,
                                         holder_type,
                                         std::move(element.initializer),
                                         projections[i].loc,
                                         holder_flags,
                                         true)
                : declare_global_variable(holder_name,
                                          holder_type,
                                          std::move(element.initializer),
                                          projections[i].loc,
                                          holder_flags,
                                          true);
            backing.fragment = chain(std::move(backing.fragment),
                                     std::move(holder.fragment),
                                     projections[i].loc);
            backing.has_error = backing.has_error || holder.has_error;
            projections[i].holder = holder.entity;
            if (holder.entity.valid() && local) {
                file_.entity_mut(holder.entity).owning_function =
                    enclosing_function;
            }
        }
    } else if (file_.valid(resolved) &&
               file_.type(resolved).kind == cir::TypeKind::Record) {
        fact.strategy = cir::StructuredBindingStrategy::Member;
        cir::EntityId record = file_.record_entity(resolved);
        (void)require_complete_class_type(
            resolved, loc, cir::InstantiationDemandKind::BaseMemberList);
        const cir::RecordFacts* record_facts = file_.record_facts(record);

        struct MemberOwner {
            cir::TypeId type{};
            const cir::RecordFacts* facts = nullptr;
            std::vector<const cir::RecordFieldFact*> fields;
        };
        std::vector<MemberOwner> owners;
        std::unordered_set<uint32_t> visited_records;
        auto gather_member_owners = [&](auto&& self, cir::TypeId type) -> void {
            type = file_.resolved_type(type);
            cir::EntityId owner = file_.record_entity(type);
            if (!owner.valid() ||
                !visited_records.insert(owner.index).second) {
                return;
            }
            (void)require_complete_class_type(
                type, loc, cir::InstantiationDemandKind::BaseMemberList);
            const cir::RecordFacts* facts = file_.record_facts(owner);
            if (!facts) {
                return;
            }
            MemberOwner candidate;
            candidate.type = type;
            candidate.facts = facts;
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_base_subobject || field.is_virtual_base_storage ||
                    (field.name.valid() && file_.name(field.name) == ".vptr") ||
                    (!field.name.valid() && field.is_bitfield)) {
                    continue;
                }
                candidate.fields.push_back(&field);
            }
            if (!candidate.fields.empty()) {
                owners.push_back(std::move(candidate));
            }
            for (const cir::RecordBaseFact& base : facts->bases) {
                self(self, base.type.type);
            }
        };
        gather_member_owners(gather_member_owners, resolved);

        const MemberOwner* selected_owner = nullptr;
        std::vector<cir::EntityId> selected_base_path;
        if (owners.size() == 1) {
            selected_owner = &owners.front();
            if (file_.resolved_type(selected_owner->type) != resolved) {
                DerivedToBasePathResult path = analyze_derived_to_base_path(
                    resolved, selected_owner->type);
                if (path.kind != DerivedToBasePathKind::Unique) {
                    report_error(
                        "structured binding member base is ambiguous in the initializer type",
                        loc);
                    backing.has_error = true;
                } else {
                    selected_base_path = std::move(path.path);
                    if (!check_base_path_access_in_context(
                            selected_base_path,
                            resolved,
                            selected_owner->type,
                            current_access_context(),
                            loc)) {
                        backing.has_error = true;
                    }
                }
            }
        } else if (owners.size() > 1) {
            report_error(
                "cannot decompose a class whose data members are declared in more than one class in its base hierarchy",
                loc);
            backing.has_error = true;
        }

        std::vector<const cir::RecordFieldFact*> fields;
        if (selected_owner) {
            fields = selected_owner->fields;
            for (const cir::RecordFieldFact* field : fields) {
                if (field->is_anonymous_union_object) {
                    report_error("cannot decompose a class with an anonymous union member",
                                 loc);
                    backing.has_error = true;
                }
            }
        }
        if (!record_facts) {
            report_error("cannot decompose an incomplete class type", loc);
            backing.has_error = true;
        } else if (record_facts->kind == cir::RecordKind::Union) {
            report_error("cannot decompose a union type", loc);
            backing.has_error = true;
        }
        if (!arity_matches(fields.size())) {
            report_error("structured binding declares " +
                             std::to_string(start.entities.size()) +
                             (has_pack
                                  ? " entries including a pack, but the class decomposes into "
                                  : " names, but the class decomposes into ") +
                             std::to_string(fields.size()) + " elements",
                         loc);
            backing.has_error = true;
        }
        projections.resize(has_pack && arity_matches(fields.size())
                               ? fields.size()
                               : start.entities.size());
        for (size_t i = 0; i < projections.size(); ++i) {
            size_t source = source_index_for_projection(i, projections.size());
            projections[i].binding = source < start.entities.size()
                ? start.entities[source]
                : cir::EntityId{};
            projections[i].index = static_cast<uint32_t>(i);
            projections[i].loc = projection_loc(i, projections.size());
            projections[i].is_pack_element = has_pack &&
                source == pack_source_index;
            if (i >= fields.size()) {
                projections[i].type = type_ref(builder_.unknown_type());
                projections[i].referenced_type = projections[i].type;
                continue;
            }
            const cir::RecordFieldFact& field = *fields[i];
            check_member_access(field.entity, field.declared_access,
                                projections[i].loc);
            projections[i].member = field.entity;
            projections[i].base_path = selected_base_path;
            projections[i].type = field.type;
            projections[i].type.qualifiers = static_cast<uint8_t>(
                projections[i].type.qualifiers | decomposed.qualifiers);
            if (field.is_mutable) {
                projections[i].type.qualifiers = static_cast<uint8_t>(
                    projections[i].type.qualifiers & ~cir::QualConst);
            }
            projections[i].referenced_type =
                is_reference_type(field.type.type) ? field.type
                                                   : projections[i].type;
            projections[i].is_bitfield = field.is_bitfield;
        }
    } else {
        fact.strategy = cir::StructuredBindingStrategy::Invalid;
        report_error("structured binding initializer must have array or non-union class type",
                     loc);
        backing.has_error = true;
        projections.resize(start.entities.size());
        for (size_t i = 0; i < projections.size(); ++i) {
            projections[i].binding = start.entities[i];
            projections[i].type = type_ref(builder_.unknown_type());
            projections[i].referenced_type = projections[i].type;
            projections[i].index = static_cast<uint32_t>(i);
            projections[i].loc = start.names[i].loc;
        }
    }

    auto projection_for_source = [&](size_t source_index)
        -> std::optional<size_t> {
        if (!has_pack) {
            return source_index < projections.size()
                ? std::optional<size_t>(source_index)
                : std::nullopt;
        }
        if (source_index == pack_source_index) {
            return std::nullopt;
        }
        if (source_index < pack_source_index) {
            return source_index < projections.size()
                ? std::optional<size_t>(source_index)
                : std::nullopt;
        }
        size_t suffix_count = start.entities.size() - source_index;
        return projections.size() >= suffix_count
            ? std::optional<size_t>(projections.size() - suffix_count)
            : std::nullopt;
    };

    std::vector<cir::EntityId> pack_elements;
    if (has_pack && pack_source_index < start.entities.size()) {
        const StructuredBindingNameInput& pack_name =
            start.names[pack_source_index];
        for (size_t i = 0; i < projections.size(); ++i) {
            if (!projections[i].is_pack_element) {
                continue;
            }
            cir::EntityId element = builder_.add_entity(
                cir::EntityKind::StructuredBinding,
                pack_name.name,
                projections[i].type.type,
                {},
                pack_name.loc,
                backing_entity.storage_duration,
                cir::MemorySpace::Default,
                {});
            cir::Entity& element_entity = file_.entity_mut(element);
            element_entity.is_definition = true;
            element_entity.qualifiers = projections[i].type.qualifiers;
            element_entity.owning_function = backing_entity.owning_function;
            element_entity.structured_binding_backing = backing.entity;
            element_entity.structured_binding_index =
                static_cast<uint32_t>(i);
            apply_attributes(element,
                             AttributeTarget::Variable,
                             pack_name.attrs,
                             pack_name.loc);
            projections[i].binding = element;
            pack_elements.push_back(element);
        }
    }

    fact.projections = projections;
    file_.set_structured_binding_fact(backing.entity, fact);

    for (size_t i = 0; i < start.entities.size(); ++i) {
        cir::Entity& binding_entity = file_.entity_mut(start.entities[i]);
        std::optional<size_t> projection_index = projection_for_source(i);
        const cir::TypeRef projected = projection_index.has_value()
            ? projections[*projection_index].type
            : type_ref(builder_.unknown_type());
        binding_entity.type = projected.type;
        binding_entity.qualifiers = projected.qualifiers;
        binding_entity.storage_duration = backing_entity.storage_duration;
        binding_entity.owning_function = backing_entity.owning_function;
        binding_entity.structured_binding_backing = backing.entity;
        binding_entity.structured_binding_index = projection_index.has_value()
            ? static_cast<uint32_t>(*projection_index)
            : std::numeric_limits<uint32_t>::max();
        if (i < start.bindings.size()) {
            if (cir::Binding* binding = file_.binding_mut(start.bindings[i])) {
                binding->type = projected;
                binding->place = {};
            }
        }
    }
    if (has_pack && pack_source_index < start.entities.size()) {
        register_structured_binding_pack(
            start.names[pack_source_index].name,
            start.entities[pack_source_index],
            pack_elements);
    }
    return backing;
}

cir::InstId Session::structured_binding_projection_place(cir::EntityId binding,
                                                          SrcLoc loc) {
    if (!binding.valid() || !file_.valid(binding)) {
        return {};
    }
    const cir::Entity& binding_entity = file_.entity(binding);
    const cir::StructuredBindingFact* fact =
        file_.structured_binding_fact(binding);
    if (!fact || !binding_entity.structured_binding_backing.valid()) {
        return {};
    }
    uint32_t index = binding_entity.structured_binding_index;
    if (index >= fact->projections.size()) {
        return {};
    }
    const cir::StructuredBindingProjectionFact& projection =
        fact->projections[index];
    cir::EntityId storage = projection.holder.valid()
        ? projection.holder
        : fact->backing;
    if (!storage.valid() || !file_.valid(storage)) {
        return {};
    }
    const cir::Entity& storage_entity = file_.entity(storage);
    cir::InstId place =
        storage_entity.storage_duration == cir::StorageDuration::Automatic ||
                storage_entity.storage_duration == cir::StorageDuration::Temporary
            ? builder_.local_place(storage, storage_entity.type, loc)
            : builder_.global_place(storage, loc);
    if (is_reference_type(storage_entity.type)) {
        cir::InstId reference = builder_.lvalue_to_rvalue(place, loc);
        place = builder_.deref(reference, loc);
    }
    if (fact->strategy == cir::StructuredBindingStrategy::Array) {
        cir::InstId offset = builder_.integer_literal(
            projection.index, builder_.usize_type(),
            std::to_string(projection.index), loc);
        place = builder_.array_element_place(place, offset, loc);
    } else if (fact->strategy == cir::StructuredBindingStrategy::Member &&
               projection.member.valid()) {
        for (cir::EntityId base : projection.base_path) {
            place = builder_.field_addr(
                place, base, file_.entity(base).type, loc);
        }
        place = builder_.field_addr(
            place, projection.member, projection.type.type, loc);
    }
    if (is_reference_type(projection.type.type)) {
        cir::InstId reference = builder_.lvalue_to_rvalue(place, loc);
        place = builder_.deref(reference, loc);
    }
    return place;
}

ExprResult Session::structured_binding_expr_result(cir::EntityId binding,
                                                   std::string_view name,
                                                   SrcLoc loc) {
    ExprResult result;
    result.entity = binding;
    result.name = std::string(name);
    result.potential_results.push_back(binding);
    if (!binding.valid() || !file_.valid(binding)) {
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    const cir::Entity& binding_entity = file_.entity(binding);
    const cir::StructuredBindingFact* fact =
        file_.structured_binding_fact(binding);
    if (!fact || !binding_entity.structured_binding_backing.valid()) {
        report_error("structured binding '" + std::string(name) +
                         "' cannot be used in its own initializer",
                     loc);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    uint32_t index = binding_entity.structured_binding_index;
    if (index >= fact->projections.size()) {
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    const cir::StructuredBindingProjectionFact& projection =
        fact->projections[index];
    result.type = projection.type.type;
    result.value_dependent = projection.is_dependent;
    if (fact->is_dependent || projection.is_dependent) {
        result.category = ValueCategory::Dependent;
        if (collecting_pattern_) {
            bump_pattern_taint();
        }
        return make_dependent_expr(std::move(result), loc);
    }

    if (is_cross_function_local(binding) || is_default_argument_local(binding)) {
        result.category = ValueCategory::LValue;
        result.deferred_entity_place = true;
        if (!note_potential_lambda_capture(binding, loc)) {
            result.has_error = true;
        }
        return result;
    }

    cir::EntityId storage = projection.holder.valid()
        ? projection.holder
        : fact->backing;
    cir::Fragment ensure;
    if (storage.valid() && file_.valid(storage) &&
        file_.entity(storage).storage_duration == cir::StorageDuration::Thread) {
        ensure = ensure_thread_initialized(storage, loc);
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.structured_binding");
    cir::InstId place = structured_binding_projection_place(binding, loc);
    cir::Fragment projection_fragment = finish_fragment_block(block, previous);
    result.fragment = chain(std::move(ensure),
                            std::move(projection_fragment), loc);
    result.place = place;
    result.category = ValueCategory::LValue;
    result.designates_bitfield = projection.is_bitfield;
    if (is_reference_type(result.type)) {
        result.type = file_.reference_referred_type(
            file_.resolved_type(result.type));
    }
    result.has_error = !place.valid();
    return result;
}

} // namespace aburi::collect
