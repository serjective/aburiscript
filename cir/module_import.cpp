

#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

#include "file.h"

namespace aburi::cir {

struct ModuleGraphImporter {
    File& target;
    const File& source;
    uint32_t srcloc_delta = 0;
    uint64_t binding_generation = 0;
    std::string refusal;
    std::vector<NameId> name_map;
    std::vector<TypeId> type_map;
    std::vector<char> type_in_progress;
    std::vector<EntityId> entity_map;
    std::vector<DeclContextId> context_map;
    std::vector<BindingId> binding_map;
    std::vector<FunctionId> function_map;
    std::vector<BlockId> block_map;
    std::vector<InstId> inst_map;
    std::vector<uint32_t> payload_map;
    std::vector<PlaceFactId> place_fact_map;
    std::vector<ConstantStateId> constant_state_map;
    std::vector<InlineAsmPayloadId> inline_asm_map;
    std::vector<PlaceholderResultFactId> placeholder_map;
    std::vector<GenericId> generic_map;
    std::vector<SpecificId> specific_map;
    std::vector<ClosureIdentityId> closure_identity_map;
    ModuleAttachmentId unit_map{};
    File::PreludeMark prelude;
    std::vector<char> covered_entities;
    std::vector<char> covered_contexts;
    std::vector<char> covered_bindings;
    std::vector<char> covered_functions;
    std::vector<char> covered_blocks;
    std::vector<char> covered_insts;
    std::vector<char> covered_generics;
    std::vector<char> covered_specifics;
    std::vector<char> covered_constant_states;
    std::vector<char> covered_closure_identities;
    std::vector<char> covered_place_facts;
    std::vector<char> covered_inline_asm;
    std::vector<char> covered_placeholders;
    std::vector<ModuleAttachmentId> unit_attachment_map;
    bool allow_templates = false;

    ModuleGraphImporter(File& target_file, const File& source_file,
                        uint32_t delta, uint64_t generation,
                        bool templates_allowed)
        : target(target_file),
          source(source_file),
          srcloc_delta(delta),
          binding_generation(generation),
          allow_templates(templates_allowed) {}

    SrcLoc loc(SrcLoc value) const {
        return value.isInvalid() ? value : SrcLoc(value.offset + srcloc_delta);
    }

    NameId name(NameId id) const {
        return id.valid() && id.index < name_map.size() ? name_map[id.index]
                                                        : NameId{};
    }
    EntityId entity(EntityId id) const {
        return id.valid() && id.index < entity_map.size()
            ? entity_map[id.index]
            : EntityId{};
    }
    DeclContextId context(DeclContextId id) const {
        return id.valid() && id.index < context_map.size()
            ? context_map[id.index]
            : DeclContextId{};
    }
    BindingId binding(BindingId id) const {
        return id.valid() && id.index < binding_map.size()
            ? binding_map[id.index]
            : BindingId{};
    }
    FunctionId function(FunctionId id) const {
        return id.valid() && id.index < function_map.size()
            ? function_map[id.index]
            : FunctionId{};
    }
    BlockId block(BlockId id) const {
        return id.valid() && id.index < block_map.size()
            ? block_map[id.index]
            : BlockId{};
    }
    InstId inst(InstId id) const {
        return id.valid() && id.index < inst_map.size() ? inst_map[id.index]
                                                        : InstId{};
    }
    ValueRef value(ValueRef ref) const { return ValueRef(inst(ref.inst)); }
    PlaceFactId place_fact(PlaceFactId id) const {
        return id.valid() && id.index < place_fact_map.size()
            ? place_fact_map[id.index]
            : PlaceFactId{};
    }
    ConstantStateId constant_state(ConstantStateId id) const {
        return id.valid() && id.index < constant_state_map.size()
            ? constant_state_map[id.index]
            : ConstantStateId{};
    }
    ClosureIdentityId closure_identity(ClosureIdentityId id) const {
        return id.valid() && id.index < closure_identity_map.size()
            ? closure_identity_map[id.index]
            : ClosureIdentityId{};
    }
    ModuleAttachmentId unit(ModuleAttachmentId id) const {
        if (!id.valid()) {
            return {};
        }
        if (id.index < unit_attachment_map.size() &&
            unit_attachment_map[id.index].valid()) {
            return unit_attachment_map[id.index];
        }
        return unit_map;
    }

    TypeId type(TypeId id) {
        if (!id.valid() || id.index >= source.types_.size()) {
            return TypeId{};
        }
        if (type_map[id.index].valid()) {
            return type_map[id.index];
        }
        if (type_in_progress[id.index]) {

            refuse("cyclic type graph");
            return TypeId{};
        }
        type_in_progress[id.index] = 1;
        const Type& record = source.types_[id.index];
        TypeSpec spec;
        spec.kind = record.kind;
        spec.payload = remap_type_payload(
            source.type_payloads_[record.payload_index]);
        spec.debug_name = name(record.debug_name);
        spec.canonical = record.canonical == id ? TypeId{}
                                                : type(record.canonical);
        spec.desugared = type(record.desugared);
        spec.resolved = record.resolved == id ? TypeId{}
                                              : type(record.resolved);
        if (record.resolved == id) {

        }
        spec.dependency = record.dependency;
        spec.loc = loc(record.loc);
        TypeId imported = target.intern_type(std::move(spec));
        type_in_progress[id.index] = 0;
        type_map[id.index] = imported;
        return imported;
    }

    TypeRef type_ref(TypeRef ref) {
        TypeRef result = ref;
        result.type = type(ref.type);
        return result;
    }

    void refuse(std::string reason) {
        if (refusal.empty()) {
            refusal = std::move(reason);
        }
    }

    static std::string unit_key(const File& file, const ModuleUnitFact& fact) {
        std::string key;
        if (fact.module_name.valid()) {
            key = file.name(fact.module_name);
        }
        if (fact.partition_name.valid()) {
            key += ':';
            key += file.name(fact.partition_name);
        }
        return key;
    }

    template <typename IdT>
    static void seed_table(const std::vector<IdT>& source_remap,
                           const std::vector<IdT>& target_remap,
                           std::vector<IdT>& map,
                           std::vector<char>& covered) {
        size_t limit = source_remap.size() < target_remap.size()
            ? source_remap.size()
            : target_remap.size();
        for (size_t origin_index = 1; origin_index < limit; ++origin_index) {
            IdT in_source = source_remap[origin_index];
            if (!in_source.valid() || in_source.index >= map.size()) {
                continue;
            }
            map[in_source.index] = target_remap[origin_index];
            covered[in_source.index] = 1;
        }
    }

    void seed_provenance() {
        for (size_t index = 2; index < source.module_units_.size(); ++index) {
            std::string key = unit_key(source, source.module_units_[index]);
            const File::ModuleGraphRemap& from =
                source.module_import_provenance_.at(key);
            const File::ModuleGraphRemap& onto =
                target.module_import_provenance_.at(key);
            unit_attachment_map[index] = onto.unit;
            seed_table(from.entities, onto.entities, entity_map,
                       covered_entities);
            seed_table(from.contexts, onto.contexts, context_map,
                       covered_contexts);
            seed_table(from.bindings, onto.bindings, binding_map,
                       covered_bindings);
            seed_table(from.functions, onto.functions, function_map,
                       covered_functions);
            seed_table(from.blocks, onto.blocks, block_map, covered_blocks);
            seed_table(from.insts, onto.insts, inst_map, covered_insts);
            seed_table(from.generics, onto.generics, generic_map,
                       covered_generics);
            seed_table(from.specifics, onto.specifics, specific_map,
                       covered_specifics);
            seed_table(from.constant_states, onto.constant_states,
                       constant_state_map, covered_constant_states);
            seed_table(from.closure_identities, onto.closure_identities,
                       closure_identity_map, covered_closure_identities);
            seed_table(from.place_facts, onto.place_facts, place_fact_map,
                       covered_place_facts);
            seed_table(from.inline_asm_payloads, onto.inline_asm_payloads,
                       inline_asm_map, covered_inline_asm);
            seed_table(from.placeholder_facts, onto.placeholder_facts,
                       placeholder_map, covered_placeholders);
        }
    }

    TemplateValueExpression value_expression(
        const TemplateValueExpression& expression) {
        TemplateValueExpression result = expression;
        for (TemplateValueExprNode& node : result.nodes) {
            node.type = type(node.type);
            node.result_type = type_ref(node.result_type);
            node.entity = entity(node.entity);
            node.name = name(node.name);
            node.qualifier_type = type_ref(node.qualifier_type);
            for (TemplateValuePackReference& reference :
                 node.pack_references) {
                reference.declaration = entity(reference.declaration);
                reference.owner = entity(reference.owner);
                reference.parameter_type = type(reference.parameter_type);
                reference.name = name(reference.name);
            }
            for (TemplateArgument& argument_value :
                 node.template_arguments.values()) {
                argument_value = argument(argument_value);
            }
        }

        result.canonical_id = ValueExprId{};
        result.loc = loc(result.loc);
        result.definition_context = context(result.definition_context);
        result.definition_lookup_generation = binding_generation;
        target.canonicalize_template_value_expression(result);
        return result;
    }

    TemplateArgument argument(const TemplateArgument& source_argument) {
        TemplateArgument result = source_argument;
        result.type = type_ref(result.type);
        result.value_type = type_ref(result.value_type);
        result.value_entity = entity(result.value_entity);
        result.closure_identity = closure_identity(result.closure_identity);
        for (TemplateArgument& element : result.value_elements) {
            element = argument(element);
        }
        result.dependent_value_expr =
            value_expression(result.dependent_value_expr);
        result.generated_pack_count_type =
            type_ref(result.generated_pack_count_type);
        result.generated_pack_count_expr =
            value_expression(result.generated_pack_count_expr);
        result.dependent_value_qualifier =
            type_ref(result.dependent_value_qualifier);
        result.dependent_value_name = name(result.dependent_value_name);
        result.template_entity = entity(result.template_entity);
        result.dependent_template_qualifier =
            type_ref(result.dependent_template_qualifier);
        result.template_name = name(result.template_name);
        if (result.unconverted_value_alternative) {
            result.unconverted_value_alternative =
                std::make_shared<TemplateArgument>(
                    argument(*result.unconverted_value_alternative));
        }
        result.constant_state = constant_state(result.constant_state);
        return result;
    }

    TypePayload remap_type_payload(const TypePayload& payload) {
        TypePayload result = payload;
        if (auto* pointer = std::get_if<PointerTypePayload>(&result)) {
            pointer->pointee = type_ref(pointer->pointee);
        } else if (auto* block_pointer =
                       std::get_if<BlockPointerTypePayload>(&result)) {
            block_pointer->pointee = type_ref(block_pointer->pointee);
        } else if (auto* member = std::get_if<MemberPointerTypePayload>(&result)) {
            member->class_type = type_ref(member->class_type);
            member->member_type = type_ref(member->member_type);
        } else if (auto* reference =
                       std::get_if<ReferenceTypePayload>(&result)) {
            reference->referred_type = type_ref(reference->referred_type);
        } else if (auto* array = std::get_if<ArrayTypePayload>(&result)) {
            array->element_type = type_ref(array->element_type);
            array->size_expr = inst(array->size_expr);
            array->dependent_size_expr =
                value_expression(array->dependent_size_expr);
        } else if (auto* function = std::get_if<FunctionTypePayload>(&result)) {
            function->return_type = type_ref(function->return_type);
            for (TypeRef& parameter : function->parameters) {
                parameter = type_ref(parameter);
            }
            function->exception_spec.predicate =
                value_expression(function->exception_spec.predicate);
        } else if (auto* record = std::get_if<RecordTypePayload>(&result)) {
            record->entity = entity(record->entity);
            record->name = name(record->name);
        } else if (auto* enumeration = std::get_if<EnumTypePayload>(&result)) {
            enumeration->entity = entity(enumeration->entity);
            enumeration->name = name(enumeration->name);
            enumeration->underlying_type =
                type_ref(enumeration->underlying_type);
        } else if (auto* vector_type = std::get_if<VectorTypePayload>(&result)) {
            vector_type->element_type = type_ref(vector_type->element_type);
        } else if (auto* complex_type =
                       std::get_if<ComplexTypePayload>(&result)) {
            complex_type->element_type = type_ref(complex_type->element_type);
        } else if (auto* typedef_type =
                       std::get_if<TypedefTypePayload>(&result)) {
            typedef_type->entity = entity(typedef_type->entity);
            typedef_type->name = name(typedef_type->name);
            typedef_type->underlying_type =
                type_ref(typedef_type->underlying_type);
        } else if (auto* type_param =
                       std::get_if<TypeParamTypePayload>(&result)) {
            type_param->entity = entity(type_param->entity);
            type_param->name = name(type_param->name);
        } else if (auto* specialization =
                       std::get_if<TemplateSpecializationTypePayload>(
                           &result)) {
            specialization->template_name = name(specialization->template_name);
            specialization->primary_template =
                entity(specialization->primary_template);
            for (TemplateArgument& element : specialization->arguments) {
                element = argument(element);
            }
            specialization->splice_operand =
                value_expression(specialization->splice_operand);
        } else if (auto* specialization =
                       std::get_if<AliasSpecializationTypePayload>(
                           &result)) {
            specialization->template_name =
                name(specialization->template_name);
            specialization->alias_template =
                entity(specialization->alias_template);
            for (TemplateArgument& element : specialization->arguments) {
                element = argument(element);
            }
            specialization->associated_type =
                type_ref(specialization->associated_type);
        } else if (auto* dependent_name =
                       std::get_if<DependentNameTypePayload>(&result)) {
            dependent_name->qualifier_type =
                type_ref(dependent_name->qualifier_type);
            dependent_name->member_name = name(dependent_name->member_name);
            for (TemplateArgument& element :
                 dependent_name->template_arguments) {
                element = argument(element);
            }
        } else if (auto* dependent =
                       std::get_if<DependentTypePayload>(&result)) {
            dependent->debug_name = name(dependent->debug_name);
        } else if (std::holds_alternative<AutoTypePayload>(result)) {
        } else if (auto* typeof_expr =
                       std::get_if<TypeofExprTypePayload>(&result)) {
            typeof_expr->expr = inst(typeof_expr->expr);
        } else if (auto* decltype_expr =
                       std::get_if<DecltypeExprTypePayload>(&result)) {
            decltype_expr->expr = inst(decltype_expr->expr);
            decltype_expr->operand_type =
                type_ref(decltype_expr->operand_type);
            decltype_expr->dependent_value_qualifier =
                type_ref(decltype_expr->dependent_value_qualifier);
            decltype_expr->dependent_value_name =
                name(decltype_expr->dependent_value_name);
            decltype_expr->operand_expression =
                value_expression(decltype_expr->operand_expression);
        } else if (auto* transform =
                       std::get_if<BuiltinTypeTransformTypePayload>(
                           &result)) {
            transform->operand_type = type_ref(transform->operand_type);
        } else if (auto* pack_element =
                       std::get_if<BuiltinPackElementTypePayload>(&result)) {
            for (TemplateArgument& element : pack_element->arguments) {
                element = argument(element);
            }
        } else if (auto* pack_index =
                       std::get_if<PackIndexTypePayload>(&result)) {
            pack_index->pack_type = type_ref(pack_index->pack_type);
            pack_index->index_expression =
                value_expression(pack_index->index_expression);
            for (TypeRef& expansion : pack_index->expansions) {
                expansion = type_ref(expansion);
            }
        } else if (auto* place = std::get_if<PlaceTypePayload>(&result)) {
            place->object_type = type_ref(place->object_type);
        }
        return result;
    }

    bool preflight() {
        auto reject = [this](bool condition, const char* reason) {
            if (condition) {
                refuse(reason);
            }
            return condition;
        };
        for (size_t index = 2; index < source.module_units_.size(); ++index) {
            std::string key = unit_key(source, source.module_units_[index]);
            if (reject(source.module_import_provenance_.find(key) ==
                           source.module_import_provenance_.end(),
                       "an imported unit lacks graph provenance") ||
                reject(target.module_import_provenance_.find(key) ==
                           target.module_import_provenance_.end(),
                       "an imported unit is not graph-imported here")) {
                return false;
            }
        }
        if (reject(source.module_units_.size() < 2,
                   "source declares no module unit") ||
            reject(!allow_templates &&
                       (source.generics_.size() > 1 ||
                        source.specifics_.size() > 1 ||
                        !source.template_specializations_.empty()),
                   "interface declares templates") ||
            false) {
            return false;
        }

        if (!allow_templates) {
            for (size_t index = 1; index < source.entities_.size(); ++index) {
                if (reject(source.entities_[index].is_template_pattern,
                           "interface contains template patterns")) {
                    return false;
                }
            }
        }
        for (const auto& [key, facts] : source.record_facts_) {

            uint32_t owner_index = static_cast<uint32_t>(key);
            bool pattern_owned = allow_templates &&
                owner_index < source.entities_.size() &&
                source.entities_[owner_index].is_template_pattern;
            if (pattern_owned) {
                continue;
            }
            if (reject(!facts.dependent_bases.empty(),
                       "interface record has dependent bases")) {
                return false;
            }
        }
        return true;
    }
    bool verify_prelude() {
        prelude = source.prelude_mark();
        const File::PreludeMark& target_prelude = target.prelude_mark();
        if (prelude.entities != target_prelude.entities ||
            prelude.decl_contexts != target_prelude.decl_contexts ||
            prelude.bindings != target_prelude.bindings) {
            refuse("prelude shape mismatch");
            return false;
        }
        if (prelude.entities > source.entities_.size() ||
            prelude.decl_contexts > source.decl_contexts_.size() ||
            prelude.bindings > source.bindings_.size()) {
            refuse("prelude mark exceeds source tables");
            return false;
        }
        for (size_t index = 1; index < prelude.entities; ++index) {
            const Entity& seed = source.entities_[index];
            const Entity& twin = target.entities_[index];
            if (seed.kind != twin.kind ||
                source.name(seed.name) != target.name(twin.name)) {
                refuse("prelude entity mismatch");
                return false;
            }
        }
        for (size_t index = 1; index < prelude.decl_contexts; ++index) {
            if (source.decl_contexts_[index].kind !=
                target.decl_contexts_[index].kind) {
                refuse("prelude context mismatch");
                return false;
            }
        }
        for (size_t index = 1; index < prelude.bindings; ++index) {
            const Binding& seed = source.bindings_[index];
            const Binding& twin = target.bindings_[index];
            if (seed.lookup_namespace != twin.lookup_namespace ||
                source.name(seed.name) != target.name(twin.name)) {
                refuse("prelude binding mismatch");
                return false;
            }
        }
        if (prelude.decl_contexts < 2 ||
            source.decl_contexts_[1].kind !=
                DeclContextKind::TranslationUnit) {
            refuse("translation-unit context is not the first context");
            return false;
        }
        return true;
    }

    File::ModuleGraphImportResult run() {
        File::ModuleGraphImportResult result;
        if (!preflight() || !verify_prelude()) {
            result.refusal = refusal;
            return result;
        }
        result.first_imported_entity_index = target.entities_.size();

        name_map.assign(source.names_.size(), NameId{});
        for (size_t index = 1; index < source.names_.size(); ++index) {
            name_map[index] = target.intern_name(source.names_[index]);
        }

        entity_map.assign(source.entities_.size(), EntityId{});
        covered_entities.assign(source.entities_.size(), 0);
        context_map.assign(source.decl_contexts_.size(), DeclContextId{});
        covered_contexts.assign(source.decl_contexts_.size(), 0);
        binding_map.assign(source.bindings_.size(), BindingId{});
        covered_bindings.assign(source.bindings_.size(), 0);
        function_map.assign(source.functions_.size(), FunctionId{});
        covered_functions.assign(source.functions_.size(), 0);
        block_map.assign(source.blocks_.size(), BlockId{});
        covered_blocks.assign(source.blocks_.size(), 0);
        inst_map.assign(source.insts_.size(), InstId{});
        covered_insts.assign(source.insts_.size(), 0);
        generic_map.assign(source.generics_.size(), GenericId{});
        covered_generics.assign(source.generics_.size(), 0);
        specific_map.assign(source.specifics_.size(), SpecificId{});
        covered_specifics.assign(source.specifics_.size(), 0);
        constant_state_map.assign(source.constant_states_.size(),
                                  ConstantStateId{});
        covered_constant_states.assign(source.constant_states_.size(), 0);
        closure_identity_map.assign(source.closure_identities_.size(),
                                    ClosureIdentityId{});
        covered_closure_identities.assign(source.closure_identities_.size(),
                                          0);
        place_fact_map.assign(source.place_facts_.size(), PlaceFactId{});
        covered_place_facts.assign(source.place_facts_.size(), 0);
        inline_asm_map.assign(source.inline_asm_payloads_.size(),
                              InlineAsmPayloadId{});
        covered_inline_asm.assign(source.inline_asm_payloads_.size(), 0);
        placeholder_map.assign(source.placeholder_result_facts_.size(),
                               PlaceholderResultFactId{});
        covered_placeholders.assign(source.placeholder_result_facts_.size(),
                                    0);
        unit_attachment_map.assign(source.module_units_.size(),
                                   ModuleAttachmentId{});
        seed_provenance();

        for (size_t index = 1; index < source.entities_.size(); ++index) {
            if (covered_entities[index]) {
                continue;
            }
            if (index < prelude.entities) {
                entity_map[index] =
                    EntityId{static_cast<uint32_t>(index),
                             target.entity_generations_[index]};
                continue;
            }
            entity_map[index] = target.add_record<Entity, EntityId>(
                target.entities_, target.entity_generations_, Entity{});
        }
        for (size_t index = 1; index < source.decl_contexts_.size(); ++index) {
            if (covered_contexts[index]) {
                continue;
            }
            if (index < prelude.decl_contexts) {
                context_map[index] =
                    DeclContextId{static_cast<uint32_t>(index),
                                  target.decl_context_generations_[index]};
                continue;
            }
            context_map[index] =
                target.add_record<DeclContext, DeclContextId>(
                    target.decl_contexts_,
                    target.decl_context_generations_,
                    DeclContext{});
        }
        for (size_t index = 1; index < source.functions_.size(); ++index) {
            if (covered_functions[index]) {
                continue;
            }
            function_map[index] = target.add_record<Function, FunctionId>(
                target.functions_, target.function_generations_, Function{});
        }
        for (size_t index = 1; index < source.blocks_.size(); ++index) {
            if (covered_blocks[index]) {
                continue;
            }
            block_map[index] = target.add_record<Block, BlockId>(
                target.blocks_, target.block_generations_, Block{});
        }
        for (size_t index = 1; index < source.insts_.size(); ++index) {
            if (covered_insts[index]) {
                continue;
            }
            inst_map[index] = target.add_record<Inst, InstId>(
                target.insts_, target.inst_generations_, Inst{});
        }

        type_map.assign(source.types_.size(), TypeId{});
        type_in_progress.assign(source.types_.size(), 0);

        {
            ModuleUnitFact fact = source.module_units_[1];
            fact.module_name = name(fact.module_name);
            fact.partition_name = name(fact.partition_name);
            auto remap_edges = [this](std::vector<ModuleAttachmentId>& edges) {
                std::vector<ModuleAttachmentId> remapped;
                remapped.reserve(edges.size());
                for (ModuleAttachmentId edge : edges) {
                    ModuleAttachmentId mapped =
                        edge.valid() && edge.index < unit_attachment_map.size()
                        ? unit_attachment_map[edge.index]
                        : ModuleAttachmentId{};
                    if (mapped.valid()) {
                        remapped.push_back(mapped);
                    }
                }
                edges = std::move(remapped);
            };
            remap_edges(fact.direct_imports);
            remap_edges(fact.exported_imports);
            fact.loc = loc(fact.loc);
            unit_map = target.add_module_unit(std::move(fact));
            if (unit_attachment_map.size() > 1) {
                unit_attachment_map[1] = unit_map;
            }
        }

        import_place_facts();
        import_constant_states();
        import_closure_identities();
        import_inline_asm_payloads();
        import_entities();
        if (!refusal.empty()) {
            return {ModuleAttachmentId{}, refusal,
                    result.first_imported_entity_index};
        }
        import_bodies();
        import_contexts_and_bindings();
        import_record_facts();
        import_placeholder_facts();
        import_structured_bindings();
        import_defaulted_comparisons();
        if (allow_templates) {
            import_template_tables();
        }
        if (!refusal.empty()) {
            return {ModuleAttachmentId{}, refusal,
                    result.first_imported_entity_index};
        }
        target.note_imported_definitions_since(
            result.first_imported_entity_index);
        result.unit = unit_map;
        return result;
    }

    void import_place_facts() {
        for (size_t index = 1; index < source.place_facts_.size(); ++index) {
            if (covered_place_facts[index]) {
                continue;
            }
            PlaceFact fact = source.place_facts_[index];
            fact.object_type = type_ref(fact.object_type);
            fact.entity = entity(fact.entity);
            fact.base = inst(fact.base);
            fact.source = inst(fact.source);
            fact.loc = loc(fact.loc);
            place_fact_map[index] = target.add_record<PlaceFact, PlaceFactId>(
                target.place_facts_, target.place_fact_generations_,
                std::move(fact));
        }
    }

    void import_constant_states();
    void import_closure_identities();
    void import_inline_asm_payloads();
    void import_entities();
    void import_bodies();
    void import_contexts_and_bindings();
    void import_record_facts();
    void import_placeholder_facts();
    void import_template_tables();
    void import_structured_bindings();
    void import_defaulted_comparisons();
    void merge_top_level_bindings();
    uint32_t payload(uint32_t payload_index);
    OperandRange operands(OperandRange range);
};

File::ModuleGraphImportResult File::import_module_graph(
    const File& source, std::string_view module_key, uint32_t srcloc_delta,
    uint64_t binding_generation, bool allow_templates) {

    TransactionId transaction = begin_transaction();
    ModuleGraphImporter importer(*this, source, srcloc_delta,
                                 binding_generation, allow_templates);
    ModuleGraphImportResult result = importer.run();
    if (result.unit.valid()) {
        commit_transaction(transaction);
        result.remap.srcloc_delta = srcloc_delta;
        result.remap.unit = result.unit;
        result.remap.names = std::move(importer.name_map);
        result.remap.types = std::move(importer.type_map);
        result.remap.entities = std::move(importer.entity_map);
        result.remap.contexts = std::move(importer.context_map);
        result.remap.bindings = std::move(importer.binding_map);
        result.remap.functions = std::move(importer.function_map);
        result.remap.blocks = std::move(importer.block_map);
        result.remap.insts = std::move(importer.inst_map);
        result.remap.generics = std::move(importer.generic_map);
        result.remap.specifics = std::move(importer.specific_map);
        result.remap.constant_states = std::move(importer.constant_state_map);
        result.remap.closure_identities =
            std::move(importer.closure_identity_map);
        result.remap.place_facts = std::move(importer.place_fact_map);
        result.remap.inline_asm_payloads = std::move(importer.inline_asm_map);
        result.remap.placeholder_facts = std::move(importer.placeholder_map);
        result.remap.units = std::move(importer.unit_attachment_map);

        record_module_import_provenance_mutation(module_key);
        module_import_provenance_[std::string(module_key)] = result.remap;
    } else {
        rollback_transaction(transaction);
    }
    return result;
}

void ModuleGraphImporter::import_constant_states() {
    for (size_t index = 1; index < source.constant_states_.size(); ++index) {
        if (covered_constant_states[index]) {
            continue;
        }
        ConstantStateFact fact = source.constant_states_[index];
        fact.type = type_ref(fact.type);
        fact.address_entity = entity(fact.address_entity);
        fact.member_entity = entity(fact.member_entity);
        fact.subobject_entity = entity(fact.subobject_entity);
        fact.active_union_member = entity(fact.active_union_member);
        constant_state_map[index] =
            target.add_record<ConstantStateFact, ConstantStateId>(
                target.constant_states_,
                target.constant_state_generations_,
                std::move(fact));
    }
}

void ModuleGraphImporter::import_closure_identities() {
    for (size_t index = 1; index < source.closure_identities_.size();
         ++index) {
        if (covered_closure_identities[index]) {
            continue;
        }
        ClosureIdentityFact fact = source.closure_identities_[index];
        fact.source_loc = loc(fact.source_loc);
        fact.key_loc = loc(fact.key_loc);
        fact.lexical_owner = entity(fact.lexical_owner);
        fact.abi_context_name = name(fact.abi_context_name);
        fact.abi_context_decl = context(fact.abi_context_decl);
        fact.record = entity(fact.record);
        fact.type = type_ref(fact.type);
        fact.call_operator = entity(fact.call_operator);
        fact.invoker = entity(fact.invoker);
        closure_identity_map[index] =
            target.add_closure_identity(std::move(fact));
    }
}

void ModuleGraphImporter::import_inline_asm_payloads() {
    for (size_t index = 1; index < source.inline_asm_payloads_.size();
         ++index) {
        if (covered_inline_asm[index]) {
            continue;
        }
        InlineAsmPayload payload_record = source.inline_asm_payloads_[index];
        for (InlineAsmOperandPayload& operand : payload_record.outputs) {
            operand.symbolic_name = name(operand.symbolic_name);
        }
        for (InlineAsmOperandPayload& operand : payload_record.inputs) {
            operand.symbolic_name = name(operand.symbolic_name);
        }
        for (NameId& label : payload_record.goto_labels) {
            label = name(label);
        }
        for (BlockId& target_block : payload_record.goto_targets) {
            target_block = block(target_block);
        }
        inline_asm_map[index] =
            target.add_record<InlineAsmPayload, InlineAsmPayloadId>(
                target.inline_asm_payloads_,
                target.inline_asm_payload_generations_,
                std::move(payload_record));
    }
}

void ModuleGraphImporter::import_entities() {
    for (size_t index = prelude.entities; index < source.entities_.size();
         ++index) {
        if (covered_entities[index]) {
            continue;
        }
        Entity record = source.entities_[index];
        record.name = name(record.name);
        record.unnamed_type_linkage_name =
            name(record.unnamed_type_linkage_name);
        record.type = type(record.type);
        record.parent = entity(record.parent);
        record.operator_function.literal_suffix =
            name(record.operator_function.literal_suffix);
        record.declaring_record = entity(record.declaring_record);
        record.lexical_context = context(record.lexical_context);
        record.semantic_context = context(record.semantic_context);
        record.namespace_alias_target = entity(record.namespace_alias_target);
        record.owning_function = entity(record.owning_function);
        record.structured_binding_backing =
            entity(record.structured_binding_backing);
        record.local_source_name = name(record.local_source_name);
        record.local_enclosing_function =
            entity(record.local_enclosing_function);
        record.module_attachment = unit(record.module_attachment);
        record.origin_unit = unit(record.origin_unit);
        record.linkage_predecessor = entity(record.linkage_predecessor);
        record.placeholder_result = PlaceholderResultFactId{};
        record.abi_owner = entity(record.abi_owner);
        record.object_storage_alias = entity(record.object_storage_alias);
        record.object_storage_alias_place =
            inst(record.object_storage_alias_place);
        for (StaticInitializerRelocation& relocation :
             record.static_initializer_relocations) {
            relocation.entity = entity(relocation.entity);
        }
        record.constant_entity = entity(record.constant_entity);
        record.constant_closure_identity =
            closure_identity(record.constant_closure_identity);
        record.constant_meta_type = type_ref(record.constant_meta_type);
        for (TemplateArgument& element : record.constant_value_elements) {
            element = argument(element);
        }
        record.constant_state = constant_state(record.constant_state);
        record.template_parameter_object =
            entity(record.template_parameter_object);
        record.loc = loc(record.loc);

        record.symbol_policy = SymbolPolicy{};
        target.entities_[entity_map[index].index] = std::move(record);
    }
}

uint32_t ModuleGraphImporter::payload(uint32_t payload_index) {
    if (payload_index == 0 || payload_index >= source.payloads_.size()) {
        return 0;
    }
    InstPayload payload_record = source.payloads_[payload_index];
    if (auto* unary = std::get_if<UnaryOpDescriptor>(&payload_record)) {
        unary->computation_type = type_ref(unary->computation_type);
    } else if (auto* binary =
                   std::get_if<BinaryOpDescriptor>(&payload_record)) {
        binary->computation_type = type_ref(binary->computation_type);
    } else if (auto* call = std::get_if<CallPayload>(&payload_record)) {
        call->virtual_declaration = entity(call->virtual_declaration);
    } else if (auto* builtin =
                   std::get_if<BuiltinCallPayload>(&payload_record)) {
        builtin->type_operand = type_ref(builtin->type_operand);
    } else if (auto* label =
                   std::get_if<LabelAddressPayload>(&payload_record)) {
        label->name = name(label->name);
        label->target = block(label->target);
    } else if (auto* switch_payload =
                   std::get_if<SwitchTerminatorPayload>(&payload_record)) {
        switch_payload->condition_type =
            type_ref(switch_payload->condition_type);
        for (SwitchCaseRange& case_range : switch_payload->cases) {
            case_range.target = block(case_range.target);
            case_range.loc = loc(case_range.loc);
        }
    } else if (auto* asm_ref =
                   std::get_if<InlineAsmPayloadRef>(&payload_record)) {
        asm_ref->payload = asm_ref->payload.valid() &&
                asm_ref->payload.index < inline_asm_map.size()
            ? inline_asm_map[asm_ref->payload.index]
            : InlineAsmPayloadId{};
    } else if (auto* pad = std::get_if<EhLandingPadPayload>(&payload_record)) {
        for (EntityId& clause : pad->clause_typeinfos) {
            clause = entity(clause);
        }
    } else if (std::holds_alternative<DependentRegionPayload>(
                   payload_record)) {

        if (!allow_templates) {
            refuse("dependent region outside a template pattern");
            return 0;
        }
    }
    return target.add_payload(std::move(payload_record));
}

OperandRange ModuleGraphImporter::operands(OperandRange range) {
    std::vector<Operand> remapped = source.operands(range);
    for (Operand& operand : remapped) {
        if (auto* value_ref = std::get_if<ValueRef>(&operand.data)) {
            operand.data = value(*value_ref);
        } else if (auto* ref = std::get_if<TypeRef>(&operand.data)) {
            operand.data = type_ref(*ref);
        } else if (auto* entity_id = std::get_if<EntityId>(&operand.data)) {
            operand.data = entity(*entity_id);
        } else if (auto* name_id = std::get_if<NameId>(&operand.data)) {
            operand.data = name(*name_id);
        } else if (auto* specific_id = std::get_if<SpecificId>(&operand.data)) {
            if (!allow_templates) {
                refuse("template specific outside a template pattern");
            } else {
                operand.data = specific_id->valid() &&
                        specific_id->index < specific_map.size()
                    ? specific_map[specific_id->index]
                    : SpecificId{};
            }
        }
    }
    return target.add_operands(remapped);
}

void ModuleGraphImporter::import_bodies() {
    for (size_t index = 1; index < source.insts_.size(); ++index) {
        if (covered_insts[index]) {
            continue;
        }
        Inst record = source.insts_[index];
        record.result_type = type(record.result_type);
        record.place_fact = place_fact(record.place_fact);
        record.operands = operands(record.operands);
        record.payload_index = payload(record.payload_index);
        record.result_object_entity = entity(record.result_object_entity);
        record.loc = loc(record.loc);
        target.insts_[inst_map[index].index] = std::move(record);
    }
    for (size_t index = 1; index < source.blocks_.size(); ++index) {
        if (covered_blocks[index]) {
            continue;
        }
        Block record = source.blocks_[index];
        record.name = name(record.name);
        for (InstId& parameter : record.parameters) {
            parameter = inst(parameter);
        }
        for (InstId& instruction : record.instructions) {
            instruction = inst(instruction);
        }
        record.terminator.operands = operands(record.terminator.operands);
        record.terminator.target = block(record.terminator.target);
        record.terminator.false_target = block(record.terminator.false_target);
        record.terminator.payload_index =
            payload(record.terminator.payload_index);
        record.terminator.loc = loc(record.terminator.loc);
        record.unwind_target = block(record.unwind_target);
        target.blocks_[block_map[index].index] = std::move(record);
    }
    for (size_t index = 1; index < source.functions_.size(); ++index) {
        if (covered_functions[index]) {
            continue;
        }
        Function record = source.functions_[index];
        record.entity = entity(record.entity);
        record.type = type(record.type);
        record.result_type = type(record.result_type);
        for (FunctionParameter& parameter : record.parameters) {
            parameter.entity = entity(parameter.entity);
            parameter.value = value(parameter.value);
        }
        for (BlockId& body_block : record.blocks) {
            body_block = block(body_block);
        }
        record.entry_block = block(record.entry_block);
        record.loc = loc(record.loc);
        target.functions_[function_map[index].index] = std::move(record);
    }
}

void ModuleGraphImporter::import_contexts_and_bindings() {
    for (size_t index = 1;
         index < source.bindings_.size() && index < prelude.bindings;
         ++index) {
        if (covered_bindings[index]) {
            continue;
        }
        binding_map[index] = BindingId{static_cast<uint32_t>(index),
                                       target.binding_generations_[index]};
    }
    for (size_t index = prelude.bindings; index < source.bindings_.size();
         ++index) {
        if (covered_bindings[index]) {
            continue;
        }
        Binding record = source.bindings_[index];
        record.name = name(record.name);
        record.context = context(record.context);
        for (EntityId& bound : record.entities) {
            bound = entity(bound);
        }
        for (uint64_t& generation : record.entity_generations) {
            generation = binding_generation;
        }
        for (MemberUsingOrigin& origin : record.member_using_origins) {
            origin.entity = entity(origin.entity);
            origin.importing_record = entity(origin.importing_record);
            origin.nominated_record = entity(origin.nominated_record);
            origin.loc = loc(origin.loc);
        }
        record.type = type_ref(record.type);
        record.place = inst(record.place);
        record.generation = binding_generation;
        record.loc = loc(record.loc);
        binding_map[index] = target.add_record<Binding, BindingId>(
            target.bindings_, target.binding_generations_, std::move(record));
    }
    for (size_t index = prelude.decl_contexts;
         index < source.decl_contexts_.size(); ++index) {
        if (covered_contexts[index]) {
            continue;
        }
        DeclContext record = source.decl_contexts_[index];
        record.owner = entity(record.owner);
        record.parent = context(record.parent);
        for (DeclContextId& child : record.children) {
            child = context(child);
        }
        for (BindingId& bound : record.bindings) {
            bound = binding(bound);
        }
        auto remap_binding_map =
            [this](std::unordered_map<uint64_t, BindingId>& map) {
                std::unordered_map<uint64_t, BindingId> remapped;
                remapped.reserve(map.size());
                for (const auto& [key, id] : map) {
                    NameId remapped_name =
                        name(NameId{static_cast<uint32_t>(key), 0});
                    if (remapped_name.valid()) {
                        remapped.emplace(
                            (static_cast<uint64_t>(remapped_name.generation)
                             << 32) |
                                remapped_name.index,
                            binding(id));
                    }
                }
                map = std::move(remapped);
            };
        remap_binding_map(record.ordinary_latest_bindings);
        remap_binding_map(record.ordinary_value_bindings);
        remap_binding_map(record.ordinary_callable_bindings);
        remap_binding_map(record.ordinary_type_name_bindings);
        remap_binding_map(record.ordinary_template_name_bindings);
        remap_binding_map(record.ordinary_namespace_bindings);
        remap_binding_map(record.tag_bindings);
        remap_binding_map(record.label_bindings);
        for (DeclContextId& nominated : record.using_directives) {
            nominated = context(nominated);
        }
        record.using_directive_origins.resize(
            record.using_directives.size());
        for (ModuleAttachmentId& origin : record.using_directive_origins) {
            origin = unit(origin);
        }
        record.loc = loc(record.loc);
        target.decl_contexts_[context_map[index].index] = std::move(record);
    }
    merge_top_level_bindings();
}

void ModuleGraphImporter::import_record_facts() {
    for (const auto& [key, source_facts] : source.record_facts_) {
        uint32_t source_index = static_cast<uint32_t>(key);
        if (source_index < prelude.entities ||
            (source_index < covered_entities.size() &&
             covered_entities[source_index])) {

            continue;
        }
        EntityId owner = entity(EntityId{source_index, 0});
        if (!owner.valid()) {
            continue;
        }
        RecordFacts facts = source_facts;
        facts.entity = entity(facts.entity);
        facts.type = type_ref(facts.type);
        facts.closure_identity = closure_identity(facts.closure_identity);
        for (RecordBaseFact& base : facts.bases) {
            base.name = name(base.name);
            base.type = type_ref(base.type);
            base.record_entity = entity(base.record_entity);
        }
        for (RecordFieldFact& field : facts.fields) {
            field.name = name(field.name);
            field.entity = entity(field.entity);
            field.type = type_ref(field.type);
            field.lambda_capture_source =
                entity(field.lambda_capture_source);
            field.bit_width_expression =
                value_expression(field.bit_width_expression);
            field.default_member_initializer_context =
                context(field.default_member_initializer_context);
            field.default_member_initializer_loc =
                loc(field.default_member_initializer_loc);
        }
        facts.anonymous_union_object = entity(facts.anonymous_union_object);
        facts.anonymous_union_parent_context =
            context(facts.anonymous_union_parent_context);
        for (AnonymousUnionPromotionFact& promotion :
             facts.anonymous_union_promotions) {
            promotion.name = name(promotion.name);
            promotion.member = entity(promotion.member);
            for (EntityId& step : promotion.path) {
                step = entity(step);
            }
        }
        for (VariantMemberFact& variant_member : facts.variant_members) {
            variant_member.member = entity(variant_member.member);
            variant_member.owning_union = entity(variant_member.owning_union);
            for (EntityId& step : variant_member.path) {
                step = entity(step);
            }
        }
        for (RecordMethodFact& method : facts.methods) {
            method.name = name(method.name);
            method.type = type_ref(method.type);
            method.entity = entity(method.entity);
            method.operator_function.literal_suffix =
                name(method.operator_function.literal_suffix);
            method.noexcept_declaration_context =
                context(method.noexcept_declaration_context);
            method.noexcept_lookup_generation = binding_generation;
            method.noexcept_operand_loc = loc(method.noexcept_operand_loc);
            for (FunctionParameterScopeFact& parameter :
                 method.declarator_parameters) {
                parameter.name = name(parameter.name);
                parameter.type = type_ref(parameter.type);
                parameter.loc = loc(parameter.loc);
                parameter.source_parameter_pack_name =
                    name(parameter.source_parameter_pack_name);
            }
            method.implicit_equality_origin =
                entity(method.implicit_equality_origin);
            for (PotentiallyConstructedSubobjectFact& subobject :
                 method.potentially_constructed_subobjects) {
                subobject.entity = entity(subobject.entity);
                subobject.type = type_ref(subobject.type);
            }
            method.explicit_value_expression =
                value_expression(method.explicit_value_expression);
            method.explicit_declaration_context =
                context(method.explicit_declaration_context);
            method.explicit_lookup_generation = binding_generation;
            method.first_required_loc = loc(method.first_required_loc);
            method.first_required_lookup_generation = binding_generation;
            method.deleting_destructor_deallocation.entity =
                entity(method.deleting_destructor_deallocation.entity);
            if (method.inherited_constructor) {
                method.inherited_constructor->origin_constructor =
                    entity(method.inherited_constructor->origin_constructor);
                method.inherited_constructor->origin_record =
                    entity(method.inherited_constructor->origin_record);
                for (InheritedConstructorRouteFact& route :
                     method.inherited_constructor->routes) {
                    route.nominated_direct_base =
                        entity(route.nominated_direct_base);
                    route.using_loc = loc(route.using_loc);
                }
            }
            if (method.constructor_delegation) {
                method.constructor_delegation->target_constructor =
                    entity(method.constructor_delegation->target_constructor);
                method.constructor_delegation->initializer_loc =
                    loc(method.constructor_delegation->initializer_loc);
            }
        }
        for (RecordStaticDataMemberFact& member : facts.static_data_members) {
            member.name = name(member.name);
            member.type = type_ref(member.type);
            member.entity = entity(member.entity);
            member.initializer_loc = loc(member.initializer_loc);
            member.initializer_context = context(member.initializer_context);
            member.initializer_lookup_generation = binding_generation;
            member.initializer_value_expression =
                value_expression(member.initializer_value_expression);
            target.canonicalize_template_value_expression(
                member.initializer_value_expression);
        }
        for (RecordUsingDeclarationFact& using_declaration :
             facts.using_declarations) {
            using_declaration.terminal_name =
                name(using_declaration.terminal_name);
            using_declaration.nominated_entity =
                entity(using_declaration.nominated_entity);
            using_declaration.dependent_qualifier =
                type_ref(using_declaration.dependent_qualifier);
            for (RecordUsingDeclarationEntry& entry :
                 using_declaration.entries) {
                entry.entity = entity(entry.entity);
                entry.hidden_by = entity(entry.hidden_by);
            }
            using_declaration.loc = loc(using_declaration.loc);
        }
        for (RecordInheritedConstructorNominationFact& nomination :
             facts.inherited_constructor_nominations) {
            nomination.nominated_record = entity(nomination.nominated_record);
            nomination.dependent_qualifier =
                type_ref(nomination.dependent_qualifier);
            nomination.loc = loc(nomination.loc);
        }
        for (VirtualSubobjectFact& subobject : facts.virtual_subobjects) {
            subobject.record_entity = entity(subobject.record_entity);
            subobject.type = type_ref(subobject.type);
            for (EntityId& step : subobject.storage_path) {
                step = entity(step);
            }
        }
        for (VirtualOverrideEdgeFact& edge : facts.virtual_override_edges) {
            edge.overriding = entity(edge.overriding);
            edge.overridden = entity(edge.overridden);
            for (EntityId& step : edge.covariance_path) {
                step = entity(step);
            }
        }
        for (VirtualFinalOverriderFact& overrider :
             facts.virtual_final_overriders) {
            overrider.virtual_declaration =
                entity(overrider.virtual_declaration);
            overrider.final_overrider = entity(overrider.final_overrider);
            for (EntityId& candidate : overrider.conflict_candidates) {
                candidate = entity(candidate);
            }
        }
        for (RecordClassFriendGrant& grant : facts.class_friends) {
            grant.entity = entity(grant.entity);
            grant.type_pattern = type_ref(grant.type_pattern);
            grant.member_name = name(grant.member_name);
        }
        for (RecordFunctionFriendGrant& grant : facts.function_friends) {
            grant.entity = entity(grant.entity);
            grant.context = context(grant.context);
            grant.module_attachment = unit(grant.module_attachment);
            grant.signature_owner = entity(grant.signature_owner);
            grant.name = name(grant.name);
            grant.type_pattern = type_ref(grant.type_pattern);
            grant.qualifier_pattern = type_ref(grant.qualifier_pattern);
            grant.member_name = name(grant.member_name);
        }
        for (EntityId& slot : facts.vtable_slots) {
            slot = entity(slot);
        }
        auto remap_slot_fact = [this](VirtualTableSlotFact& slot) {
            slot.declaration = entity(slot.declaration);
            slot.final_overrider = entity(slot.final_overrider);
            for (EntityId& step : slot.this_adjustment.path) {
                step = entity(step);
            }
            for (EntityId& step : slot.result_adjustment.path) {
                step = entity(step);
            }
        };
        for (VirtualTableSlotFact& slot : facts.primary_vtable_slot_facts) {
            remap_slot_fact(slot);
        }
        facts.vtable_entity = entity(facts.vtable_entity);
        facts.typeinfo_entity = entity(facts.typeinfo_entity);
        facts.vtt_entity = entity(facts.vtt_entity);
        for (RecordFacts::SecondaryVtable& secondary :
             facts.secondary_vtables) {
            secondary.base_field = entity(secondary.base_field);
            for (EntityId& step : secondary.storage_path) {
                step = entity(step);
            }
            secondary.base_type = type_ref(secondary.base_type);
            for (EntityId& slot : secondary.slots) {
                slot = entity(slot);
            }
            for (VirtualTableSlotFact& slot : secondary.slot_facts) {
                remap_slot_fact(slot);
            }
        }
        for (RecordFacts::VirtualBase& virtual_base : facts.virtual_bases) {
            virtual_base.record_entity = entity(virtual_base.record_entity);
            virtual_base.type = type_ref(virtual_base.type);
            virtual_base.storage_field = entity(virtual_base.storage_field);
        }
        uint64_t target_key =
            (static_cast<uint64_t>(owner.generation) << 32) | owner.index;
        target.record_record_facts_mutation(target_key);
        target.record_facts_.emplace(target_key, std::move(facts));
    }
}

void ModuleGraphImporter::import_placeholder_facts() {
    for (size_t index = 1; index < source.placeholder_result_facts_.size();
         ++index) {
        if (covered_placeholders[index]) {
            continue;
        }
        PlaceholderResultFact fact = source.placeholder_result_facts_[index];
        fact.declared_function_type = type(fact.declared_function_type);
        fact.declared_return_pattern = type_ref(fact.declared_return_pattern);
        fact.candidate = type_ref(fact.candidate);
        fact.result = type_ref(fact.result);
        fact.defining_entity = entity(fact.defining_entity);
        fact.declaration_loc = loc(fact.declaration_loc);
        fact.first_return_loc = loc(fact.first_return_loc);
        placeholder_map[index] =
            target.add_record<PlaceholderResultFact, PlaceholderResultFactId>(
                target.placeholder_result_facts_,
                target.placeholder_result_fact_generations_,
                std::move(fact));
    }

    for (size_t index = prelude.entities; index < source.entities_.size();
         ++index) {
        if (covered_entities[index]) {
            continue;
        }
        PlaceholderResultFactId original =
            source.entities_[index].placeholder_result;
        if (original.valid() && original.index < placeholder_map.size()) {
            target.entities_[entity_map[index].index].placeholder_result =
                placeholder_map[original.index];
        }
    }
}

void ModuleGraphImporter::import_template_tables() {
    for (size_t index = 1; index < source.generics_.size(); ++index) {
        if (covered_generics[index]) {
            continue;
        }
        Generic record = source.generics_[index];
        record.entity = entity(record.entity);
        record.loc = loc(record.loc);
        for (EntityId& parameter : record.parameters) {
            parameter = entity(parameter);
        }
        record.pattern_function = function(record.pattern_function);
        generic_map[index] = target.add_generic(std::move(record));
    }
    for (size_t index = 1; index < source.specifics_.size(); ++index) {
        if (covered_specifics[index]) {
            continue;
        }
        Specific record = source.specifics_[index];
        record.generic = record.generic.valid() &&
                record.generic.index < generic_map.size()
            ? generic_map[record.generic.index]
            : GenericId{};
        record.function = function(record.function);
        record.entity = entity(record.entity);
        record.loc = loc(record.loc);
        specific_map[index] = target.add_specific(std::move(record));
    }
    for (const auto& [key, source_fact] : source.template_specializations_) {
        uint32_t source_index = static_cast<uint32_t>(key);
        if (source_index < covered_entities.size() &&
            covered_entities[source_index]) {
            continue;
        }
        EntityId owner = entity(EntityId{source_index, 0});
        if (!owner.valid()) {
            continue;
        }
        TemplateSpecializationFact fact = source_fact;
        fact.template_entity = entity(fact.template_entity);
        fact.selected_template_entity = entity(fact.selected_template_entity);
        for (TemplateArgumentBinding& binding : fact.argument_bindings) {
            for (TemplateArgument& element : binding.arguments) {
                element = argument(element);
            }
        }
        for (TemplateArgumentBinding& binding :
             fact.selected_argument_bindings) {
            for (TemplateArgument& element : binding.arguments) {
                element = argument(element);
            }
        }
        for (TemplateArgument& element : fact.dependent_arguments) {
            element = argument(element);
        }
        for (TemplateArgument& element :
             fact.selected_dependent_arguments) {
            element = argument(element);
        }
        fact.pattern_type = type(fact.pattern_type);
        fact.point_of_instantiation = loc(fact.point_of_instantiation);
        fact.point_lookup_generation = binding_generation;
        for (InstantiationDemandFact& demand : fact.instantiation_demands) {
            demand.subject = entity(demand.subject);
            demand.first_requirement = loc(demand.first_requirement);
            demand.point_lookup_generation = binding_generation;
        }
        target.set_template_specialization(owner, std::move(fact));
    }

    for (size_t index = 1; index < source.types_.size(); ++index) {
        if (!type_map[index].valid()) {
            (void)type(TypeId{static_cast<uint32_t>(index),
                              source.type_generations_[index]});
            if (!refusal.empty()) {
                return;
            }
        }
    }
}

void ModuleGraphImporter::import_structured_bindings() {
    for (const auto& [key, source_fact] : source.structured_binding_facts_) {
        uint32_t source_index = static_cast<uint32_t>(key);
        if (source_index < covered_entities.size() &&
            covered_entities[source_index]) {
            continue;
        }
        EntityId backing = entity(EntityId{source_index, 0});
        if (!backing.valid()) {
            continue;
        }
        StructuredBindingFact fact = source_fact;
        fact.backing = backing;
        fact.decomposed_type = type_ref(fact.decomposed_type);
        for (NameId& source_name : fact.source_names) {
            source_name = name(source_name);
        }
        for (StructuredBindingProjectionFact& projection :
             fact.projections) {
            projection.binding = entity(projection.binding);
            projection.holder = entity(projection.holder);
            projection.member = entity(projection.member);
            for (EntityId& step : projection.base_path) {
                step = entity(step);
            }
            projection.type = type_ref(projection.type);
            projection.referenced_type = type_ref(projection.referenced_type);
        }
        fact.loc = loc(fact.loc);
        target.set_structured_binding_fact(backing, std::move(fact));
    }
}

void ModuleGraphImporter::import_defaulted_comparisons() {
    for (const auto& [key, source_fact] :
         source.defaulted_comparison_facts_) {
        uint32_t source_index = static_cast<uint32_t>(key);
        if (source_index < covered_entities.size() &&
            covered_entities[source_index]) {
            continue;
        }
        EntityId function = entity(EntityId{source_index, 0});
        if (!function.valid()) {
            continue;
        }
        DefaultedComparisonFact fact = source_fact;
        fact.function = function;
        fact.owner_record = entity(fact.owner_record);
        fact.result_type = type_ref(fact.result_type);
        fact.implicit_equality_origin = entity(fact.implicit_equality_origin);
        for (ComparisonSubobjectFact& subobject : fact.subobjects) {
            subobject.entity = entity(subobject.entity);
            subobject.type = type_ref(subobject.type);
            subobject.array_leaf_type = type_ref(subobject.array_leaf_type);
        }
        target.set_defaulted_comparison_fact(function, std::move(fact));
    }
}

void ModuleGraphImporter::merge_top_level_bindings() {

    const DeclContext& source_tu = source.decl_contexts_[1];
    DeclContextId target_tu = context_map[1];
    target.record_decl_context_mutation(target_tu);
    DeclContext& tu = target.decl_contexts_[target_tu.index];

    for (BindingId source_binding : source_tu.bindings) {
        if (source_binding.index < prelude.bindings ||
            (source_binding.index < covered_bindings.size() &&
             covered_bindings[source_binding.index])) {
            continue;
        }
        BindingId mapped = binding(source_binding);
        if (!mapped.valid()) {
            continue;
        }
        const Binding& record = target.bindings_[mapped.index];
        uint64_t key =
            (static_cast<uint64_t>(record.name.generation) << 32) |
            record.name.index;
        const std::unordered_map<uint64_t, BindingId>* slot = nullptr;
        switch (record.lookup_namespace) {
            case LookupNamespace::Ordinary:
                slot = &tu.ordinary_latest_bindings;
                break;
            case LookupNamespace::Tag:
                slot = &tu.tag_bindings;
                break;
            case LookupNamespace::Label:
                slot = &tu.label_bindings;
                break;
            case LookupNamespace::None:
                break;
        }
        if (slot != nullptr && slot->count(key) != 0) {
            refuse("top-level name '" + target.name(record.name) +
                   "' is already bound in the importer");
            return;
        }
    }
    for (BindingId source_binding : source_tu.bindings) {
        if (source_binding.index < prelude.bindings ||
            (source_binding.index < covered_bindings.size() &&
             covered_bindings[source_binding.index])) {
            continue;
        }
        BindingId mapped = binding(source_binding);
        if (!mapped.valid()) {
            continue;
        }
        tu.bindings.push_back(mapped);
        target.index_binding_in_decl_context(target_tu, mapped);
    }
    for (DeclContextId source_child : source_tu.children) {
        if (source_child.index < prelude.decl_contexts ||
            (source_child.index < covered_contexts.size() &&
             covered_contexts[source_child.index])) {
            continue;
        }
        DeclContextId mapped = context(source_child);
        if (mapped.valid()) {
            tu.children.push_back(mapped);
        }
    }

    for (size_t directive_index = 0;
         directive_index < source_tu.using_directives.size();
         ++directive_index) {
        DeclContextId mapped =
            context(source_tu.using_directives[directive_index]);
        if (!mapped.valid()) {
            continue;
        }
        ModuleAttachmentId origin =
            directive_index < source_tu.using_directive_origins.size()
            ? unit(source_tu.using_directive_origins[directive_index])
            : unit_map;
        if (!origin.valid()) {
            origin = unit_map;
        }
        bool already = false;
        for (size_t existing = 0; existing < tu.using_directives.size();
             ++existing) {
            if (tu.using_directives[existing] == mapped) {
                already = true;
                break;
            }
        }
        if (already) {
            continue;
        }
        tu.using_directives.push_back(mapped);
        tu.using_directive_origins.resize(tu.using_directives.size());
        tu.using_directive_origins.back() = origin;
    }
}

TemplateValueExpression File::ModuleGraphRemap::value_expression(
    const TemplateValueExpression& expression,
    uint64_t definition_lookup_generation) const {
    TemplateValueExpression result = expression;
    for (TemplateValueExprNode& node : result.nodes) {
        node.type = type(node.type);
        node.result_type = type_ref(node.result_type);
        node.entity = entity(node.entity);
        node.name = name(node.name);
        node.qualifier_type = type_ref(node.qualifier_type);
        for (TemplateValuePackReference& reference :
             node.pack_references) {
            reference.declaration = entity(reference.declaration);
            reference.owner = entity(reference.owner);
            reference.parameter_type = type(reference.parameter_type);
            reference.name = name(reference.name);
        }
        for (TemplateArgument& argument_value :
             node.template_arguments.values()) {
            argument_value = argument(argument_value);
        }
    }
    result.canonical_id = ValueExprId{};
    result.loc = loc(result.loc);
    result.definition_context = context(result.definition_context);
    result.definition_lookup_generation = definition_lookup_generation;
    return result;
}

TemplateArgument File::ModuleGraphRemap::argument(
    const TemplateArgument& value) const {
    TemplateArgument result = value;
    result.type = type_ref(result.type);
    result.value_type = type_ref(result.value_type);
    result.value_entity = entity(result.value_entity);
    result.closure_identity = closure(result.closure_identity);
    for (TemplateArgument& element : result.value_elements) {
        element = argument(element);
    }
    result.dependent_value_expr =
        value_expression(result.dependent_value_expr, 0);
    result.generated_pack_count_type =
        type_ref(result.generated_pack_count_type);
    result.generated_pack_count_expr =
        value_expression(result.generated_pack_count_expr, 0);
    result.dependent_value_qualifier =
        type_ref(result.dependent_value_qualifier);
    result.dependent_value_name = name(result.dependent_value_name);
    result.template_entity = entity(result.template_entity);
    result.dependent_template_qualifier =
        type_ref(result.dependent_template_qualifier);
    result.template_name = name(result.template_name);
    if (result.unconverted_value_alternative) {
        result.unconverted_value_alternative =
            std::make_shared<TemplateArgument>(
                argument(*result.unconverted_value_alternative));
    }
    result.constant_state = constant_state(result.constant_state);
    return result;
}

} // namespace aburi::cir
