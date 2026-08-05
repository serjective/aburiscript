#include "collect.h"
#include "collect_template_state.h"
#include "../abi/mangle_cir.h"

#include <functional>
#include <string>
#include <unordered_set>
#include <utility>

namespace aburi::collect {

namespace {

constexpr std::string_view anonymous_namespace_name = "(anonymous namespace)";

bool is_itanium_class_data_role(cir::GeneratedSymbolRole role) {
    switch (role) {
        case cir::GeneratedSymbolRole::VTable:
        case cir::GeneratedSymbolRole::VTT:
        case cir::GeneratedSymbolRole::ConstructionVTable:
        case cir::GeneratedSymbolRole::TypeInfo:
        case cir::GeneratedSymbolRole::TypeName:
            return true;
        default:
            return false;
    }
}

bool is_itanium_class_data_support_role(cir::GeneratedSymbolRole role) {
    return role == cir::GeneratedSymbolRole::Thunk ||
           role == cir::GeneratedSymbolRole::DeletingDestructor;
}

bool is_callable_entity_kind(cir::EntityKind kind) {
    return kind == cir::EntityKind::Function ||
           kind == cir::EntityKind::Method ||
           kind == cir::EntityKind::Constructor ||
           kind == cir::EntityKind::Destructor;
}

} // namespace

bool Session::namespace_lookup_reaches_context(
    cir::DeclContextId nominated,
    cir::DeclContextId target) const {
    if (!nominated.valid() || !target.valid()) {
        return false;
    }
    std::vector<cir::DeclContextId> pending{nominated};
    std::unordered_set<uint32_t> visited;
    while (!pending.empty()) {
        cir::DeclContextId context = pending.back();
        pending.pop_back();
        if (context == target) {
            return true;
        }
        if (!file_.valid(context) ||
            !visited.insert(context.index).second) {
            continue;
        }
        const cir::DeclContext& declaration = file_.decl_context(context);
        pending.insert(pending.end(),
                       declaration.using_directives.begin(),
                       declaration.using_directives.end());
    }
    return false;
}

Session::NamespaceEnterResult Session::enter_named_namespace(std::string_view name,
                                                             SrcLoc loc,
                                                             bool is_inline) {
    NamespaceEnterResult result;
    cir::DeclContextId parent_context = current_decl_context();
    if (!parent_context.valid()) {
        result.has_error = true;
        return result;
    }

    const cir::Binding* conflicting = file_.lookup_ordinary_binding(
        parent_context, name, /*include_parents=*/false);
    const cir::Binding* existing = file_.lookup_namespace_name_binding(
        parent_context, name, /*include_parents=*/false);
    if (conflicting && !existing) {
        report_error("redefinition of '" + std::string(name) +
                         "' as a namespace",
                     loc);
        result.has_error = true;
    }

    cir::DeclContextId namespace_context;
    if (existing && !existing->entities.empty()) {
        result.entity = existing->entities.back();
        namespace_context = file_.entity(result.entity).semantic_context;
        if (is_inline && namespace_context.valid() &&
            !file_.decl_context(namespace_context).is_inline_namespace) {
            report_error("cannot add 'inline' to a previously declared namespace '" +
                             std::string(name) + "'",
                         loc);
            result.has_error = true;
        }
    }
    if (!namespace_context.valid()) {
        result.entity =
            builder_.add_entity(cir::EntityKind::Namespace, name, {}, {}, loc);
        namespace_context =
            file_.create_decl_context(cir::DeclContextKind::Namespace,
                                      parent_context,
                                      result.entity,
                                      loc);
        file_.entity_mut(result.entity).semantic_context = namespace_context;
        file_.decl_context_mut(namespace_context).is_inline_namespace = is_inline;
        bind_entity(name,
                    cir::LookupNamespace::Ordinary,
                    result.entity,
                    {},
                    false,
                    false,
                    true,
                    {},
                    loc);
    }

    if (is_inline && !result.has_error) {
        file_.add_using_directive(parent_context, namespace_context);
    }

    cleanup_scopes_.push_back(CleanupScope{control_stack_.size(), {}});
    ScopeFrame frame;
    frame.parent = current_scope_;
    frame.flags = ScopeFlags::NamespaceScope | ScopeFlags::FileScope;
    frame.context = namespace_context;
    scopes_.push_back(frame);
    current_scope_ = static_cast<ScopeId>(scopes_.size() - 1);
    return result;
}

Session::NamespaceEnterResult Session::enter_anonymous_namespace(SrcLoc loc) {
    NamespaceEnterResult result = enter_named_namespace(anonymous_namespace_name, loc);

    if (!result.has_error) {
        cir::DeclContextId namespace_context = current_decl_context();
        ScopeId parent_scope = scopes_[current_scope_].parent;
        if (parent_scope != InvalidScopeId && namespace_context.valid()) {
            file_.add_using_directive(scopes_[parent_scope].context,
                                      namespace_context);
        }
    }
    return result;
}

void Session::leave_namespace() {
    leave_scope();
}

bool Session::collect_namespace_alias(std::string_view alias,
                                      cir::DeclContextId target,
                                      SrcLoc loc) {
    if (!target.valid()) {
        return false;
    }
    cir::EntityId target_entity = file_.decl_context(target).owner;
    if (!target_entity.valid() ||
        file_.entity(target_entity).kind != cir::EntityKind::Namespace) {
        report_error("namespace alias target is not a namespace", loc);
        return false;
    }
    cir::EntityId alias_entity = builder_.add_entity(
        cir::EntityKind::NamespaceAlias, alias, {}, {}, loc);
    cir::Entity& alias_record = file_.entity_mut(alias_entity);
    alias_record.namespace_alias_target = target_entity;
    alias_record.semantic_context = target;
    bind_entity(alias,
                cir::LookupNamespace::Ordinary,
                alias_entity,
                {},
                false,
                false,
                false,
                {},
                loc);
    return true;
}

bool Session::collect_dependent_namespace_alias(std::string_view alias,
                                                SrcLoc loc) {
    cir::EntityId alias_entity = builder_.add_entity(
        cir::EntityKind::NamespaceAlias, alias, {}, {}, loc);
    file_.entity_mut(alias_entity).namespace_alias_is_dependent = true;
    bind_entity(alias,
                cir::LookupNamespace::Ordinary,
                alias_entity,
                {},
                false,
                false,
                true,
                {},
                loc);
    return true;
}

bool Session::collect_using_directive(cir::DeclContextId nominated, SrcLoc loc) {
    if (!nominated.valid()) {
        return false;
    }
    cir::EntityId owner = file_.decl_context(nominated).owner;
    if (!owner.valid() ||
        file_.entity(owner).kind != cir::EntityKind::Namespace) {
        report_error("using-directive target is not a namespace", loc);
        return false;
    }
    file_.add_using_directive(current_decl_context(), nominated);
    bump_lookup_generation();
    return true;
}

bool Session::collect_using_declaration(cir::DeclContextId source_context,
                                        std::string_view name,
                                        SrcLoc loc,
                                        bool uses_typename,
                                        cir::TypeRef dependent_qualifier) {
    cir::DeclContextId context = current_decl_context();
    cir::EntityId importing_record =
        context.valid() && file_.valid(context) &&
                file_.decl_context(context).kind ==
                    cir::DeclContextKind::Record
            ? file_.decl_context(context).owner
            : cir::EntityId{};
    cir::RecordMemberAccess import_access = cir::RecordMemberAccess::Public;
    auto active_access = record_member_access_by_context_.find(
        static_cast<uint64_t>(context.index));
    if (active_access != record_member_access_by_context_.end()) {
        import_access = active_access->second;
    }

    auto append_record_fact = [&](cir::RecordUsingDeclarationFact fact) {
        cir::RecordFacts updated;
        if (const cir::RecordFacts* existing =
                file_.record_facts(importing_record)) {
            updated = *existing;
        } else {
            updated.entity = importing_record;
            updated.type = type_ref(file_.entity(importing_record).type);
        }
        uint32_t index = static_cast<uint32_t>(
            updated.using_declarations.size());
        updated.using_declarations.push_back(std::move(fact));
        file_.set_record_facts(importing_record, std::move(updated));
        return index;
    };

    if (!source_context.valid() && dependent_qualifier.type.valid() &&
        importing_record.valid()) {
        const cir::RecordFacts* existing =
            file_.record_facts(importing_record);
        if (existing && std::any_of(
                existing->using_declarations.begin(),
                existing->using_declarations.end(),
                [&](const cir::RecordUsingDeclarationFact& fact) {
                    return fact.terminal_name.valid() &&
                        file_.name(fact.terminal_name) == name &&
                        fact.dependent_qualifier == dependent_qualifier;
                })) {
            report_error("declaration named by using-declaration is already "
                         "named in this class scope", loc);
            return false;
        }
        cir::RecordUsingDeclarationFact fact;
        fact.terminal_name = file_.intern_name(name);
        fact.dependent_qualifier = dependent_qualifier;
        fact.declared_access = import_access;
        fact.uses_typename = uses_typename;
        fact.base_validation_deferred = true;
        fact.loc = loc;
        (void)append_record_fact(std::move(fact));

        cir::Binding binding;
        binding.name = file_.intern_name(name);
        binding.context = context;
        binding.lookup_namespace = cir::LookupNamespace::Ordinary;
        binding.type = type_ref(file_.dependent_name_type(
            dependent_qualifier, name));
        binding.is_type_name = uses_typename;
        binding.dependent_member_using = true;
        binding.loc = loc;
        file_.add_binding(std::move(binding));
        bump_lookup_generation();
        return true;
    }
    if (!source_context.valid() || !file_.valid(source_context)) {
        return false;
    }

    cir::EntityId nominated_entity =
        file_.decl_context(source_context).owner;
    cir::EntityKind nominated_kind =
        nominated_entity.valid() && file_.valid(nominated_entity)
            ? file_.entity(nominated_entity).kind
            : cir::EntityKind::Invalid;
    cir::EntityId nominated_record =
        nominated_kind == cir::EntityKind::Record
            ? nominated_entity
            : cir::EntityId{};

    std::vector<MemberLookupDeclaration> selected_declarations;
    const cir::Binding* ordinary = nullptr;
    const cir::Binding* tag = nullptr;
    if (nominated_record.valid()) {
        MemberLookupResult lookup = lookup_member_name(
            file_.entity(nominated_record).type, name);
        if (lookup.ambiguous) {
            report_error("member '" + std::string(name) +
                             "' is ambiguous in the nominated class",
                         loc);
            return false;
        }
        if (!lookup.found_name || lookup.declarations.empty()) {
            report_error("no member named '" + std::string(name) +
                             "' in the nominated scope",
                         loc);
            return false;
        }
        selected_declarations = std::move(lookup.declarations);
    } else {
        ordinary = file_.lookup_ordinary_binding(
            source_context, name, /*include_parents=*/false);
        tag = file_.lookup_tag_binding(
            source_context, name, /*include_parents=*/false);
        if (!ordinary && !tag) {
            report_error("no member named '" + std::string(name) +
                             "' in the nominated scope",
                         loc);
            return false;
        }
    }

    std::vector<cir::EntityId> selected_entities;
    auto append_entity = [&](cir::EntityId entity) {
        if (entity.valid() && file_.valid(entity) &&
            std::find(selected_entities.begin(), selected_entities.end(),
                      entity) == selected_entities.end()) {
            selected_entities.push_back(entity);
        }
    };
    for (const MemberLookupDeclaration& declaration :
         selected_declarations) {
        append_entity(declaration.entity);
    }
    auto append_binding_entities = [&](const cir::Binding* binding) {
        if (!binding) {
            return;
        }
        for (cir::EntityId entity : binding->entities) {
            append_entity(entity);
        }
    };
    if (!nominated_record.valid()) {
        append_binding_entities(ordinary);
        append_binding_entities(tag);
    }
    if (selected_entities.empty()) {
        report_error("no declaration named '" + std::string(name) +
                         "' in the nominated scope",
                     loc);
        return false;
    }

    bool names_only_enumerators = std::all_of(
        selected_entities.begin(), selected_entities.end(),
        [&](cir::EntityId entity) {
            return file_.entity(entity).kind == cir::EntityKind::Enumerator;
        });
    if (importing_record.valid()) {
        if (!names_only_enumerators) {
            if (!nominated_record.valid()) {
                report_error("class-scope using-declaration does not name "
                             "an enumerator or a base-class member", loc);
                return false;
            }
            bool is_base = false;
            bool has_dependent_base = false;
            for (ScopeId scope = current_scope_;
                 scope != InvalidScopeId && scope < scopes_.size();
                 scope = scopes_[scope].parent) {
                if (scopes_[scope].context != context) {
                    continue;
                }
                for (const RecordBaseInput& base :
                     scopes_[scope].pending_bases) {
                    if (base.is_dependent ||
                        (in_template_definition() &&
                         is_dependent_type(base.type))) {
                        has_dependent_base = true;
                        continue;
                    }
                    cir::TypeId base_type = file_.resolved_type(base.type);
                    cir::TypeId nominated_type = file_.resolved_type(
                        file_.entity(nominated_record).type);
                    if (base_type == nominated_type ||
                        derived_to_base_path(base_type, nominated_type,
                                             nullptr)) {
                        is_base = true;
                    }
                }
                break;
            }
            if (!is_base && !has_dependent_base) {
                report_error("using-declaration nominates '" +
                                 file_.format_type(
                                     file_.entity(nominated_record).type) +
                                 "', which is not a base class",
                             loc);
                return false;
            }
        }
    } else if (!names_only_enumerators && nominated_record.valid()) {
        report_error("a using-declaration naming a class member must be a "
                     "member declaration", loc);
        return false;
    }

    bool all_types = std::all_of(
        selected_entities.begin(), selected_entities.end(),
        [&](cir::EntityId entity) {
            cir::EntityKind kind = file_.entity(entity).kind;
            return kind == cir::EntityKind::Record ||
                kind == cir::EntityKind::Enum ||
                kind == cir::EntityKind::TypeAlias;
        });
    if (uses_typename && !all_types) {
        report_error("'typename' using-declarator does not name a type",
                     loc);
        return false;
    }

    uint32_t using_fact_index = std::numeric_limits<uint32_t>::max();
    if (importing_record.valid()) {
        const cir::RecordFacts* existing =
            file_.record_facts(importing_record);
        if (existing) {
            for (const cir::RecordUsingDeclarationFact& prior :
                 existing->using_declarations) {
                bool duplicate = std::any_of(
                    prior.entries.begin(), prior.entries.end(),
                    [&](const cir::RecordUsingDeclarationEntry& entry) {
                        return std::find(selected_entities.begin(),
                                         selected_entities.end(),
                                         entry.entity) !=
                            selected_entities.end();
                    });
                if (duplicate) {
                    report_error("declaration named by using-declaration is "
                                 "already named in this class scope", loc);
                    return false;
                }
            }
        }
        bool access_ok = true;
        for (const MemberLookupDeclaration& declaration :
             selected_declarations) {
            access_ok = check_member_lookup_access(declaration, loc) &&
                access_ok;
            if (!declaration.found_through_using) {
                access_ok = check_member_lookup_base_access(
                    declaration, file_.entity(nominated_record).type, loc) &&
                    access_ok;
            }
        }
        if (!access_ok) {
            return false;
        }
        cir::RecordUsingDeclarationFact fact;
        fact.terminal_name = file_.intern_name(name);
        fact.nominated_entity = nominated_entity;
        fact.declared_access = import_access;
        fact.uses_typename = uses_typename;
        fact.loc = loc;
        for (cir::EntityId entity : selected_entities) {
            fact.entries.push_back(
                cir::RecordUsingDeclarationEntry{entity, {}});
        }
        using_fact_index = append_record_fact(std::move(fact));
    }

    cir::Binding source;
    source.name = file_.intern_name(name);
    source.lookup_namespace = cir::LookupNamespace::Ordinary;
    source.entities = selected_entities;
    source.entity_generations.resize(selected_entities.size(), 0);
    source.type = type_ref(file_.entity(selected_entities.back()).type);
    source.is_type_name = all_types;
    source.is_template_name = std::any_of(
        selected_entities.begin(), selected_entities.end(),
        [&](cir::EntityId entity) { return template_info(entity) != nullptr; });
    source.loc = loc;

    bump_lookup_generation();
    auto import_binding = [&](const cir::Binding& source_binding) {
        cir::Binding source_copy = source_binding;
        cir::BindingId alias =
            file_.add_alias_binding(context, source_copy, loc,
                                    lookup_generation());
        cir::Binding* destination = file_.binding_mut(alias);
        if (!destination || !importing_record.valid() ||
            !nominated_record.valid()) {
            return;
        }
        for (cir::EntityId entity : source_copy.entities) {
            if (!entity.valid() || !file_.valid(entity)) {
                continue;
            }
            const cir::Entity& declaration = file_.entity(entity);
            if (declaration.is_record_member) {
                (void)check_member_access_from(
                    entity, declaration.declared_member_access,
                    importing_record, {}, loc);
            }
            cir::MemberUsingOrigin origin;
            origin.entity = entity;
            origin.importing_record = importing_record;
            origin.nominated_record = nominated_record;
            origin.using_fact_index = using_fact_index;
            origin.declared_access = import_access;
            origin.loc = loc;
            if (std::find_if(
                    destination->member_using_origins.begin(),
                    destination->member_using_origins.end(),
                    [&](const cir::MemberUsingOrigin& existing) {
                        return existing.entity == origin.entity &&
                            existing.importing_record ==
                                origin.importing_record &&
                            existing.nominated_record ==
                                origin.nominated_record &&
                            existing.using_fact_index ==
                                origin.using_fact_index;
                    }) == destination->member_using_origins.end()) {
                destination->member_using_origins.push_back(origin);
            }
        }
    };
    import_binding(source);
    return true;
}

bool Session::collect_inherited_constructor_nomination(
    cir::DeclContextId base_context,
    cir::TypeRef dependent_qualifier,
    SrcLoc loc) {
    cir::EntityId base_entity = base_context.valid()
        ? file_.decl_context(base_context).owner
        : cir::EntityId{};
    cir::DeclContextId current = current_decl_context();
    cir::EntityId record_entity = current.valid()
        ? file_.decl_context(current).owner
        : cir::EntityId{};
    bool concrete_base = base_entity.valid() && file_.valid(base_entity) &&
        file_.entity(base_entity).kind == cir::EntityKind::Record;
    bool dependent_base = !base_context.valid() &&
        dependent_qualifier.type.valid();
    if ((!concrete_base && !dependent_base) ||
        !record_entity.valid() || !file_.valid(record_entity) ||
        file_.entity(record_entity).kind != cir::EntityKind::Record) {
        report_error(
            "constructor using-declaration requires a class scope naming a "
            "base class",
            loc);
        return false;
    }

    cir::RecordFacts updated;
    if (const cir::RecordFacts* existing =
            file_.record_facts(record_entity)) {
        updated = *existing;
    } else {
        updated.entity = record_entity;
        updated.type = type_ref(file_.entity(record_entity).type);
    }
    auto equivalent = [&](const cir::RecordInheritedConstructorNominationFact&
                              nomination) {
        return concrete_base
            ? nomination.nominated_record == base_entity
            : nomination.dependent_qualifier == dependent_qualifier;
    };
    if (std::any_of(updated.inherited_constructor_nominations.begin(),
                    updated.inherited_constructor_nominations.end(),
                    equivalent)) {
        report_error("constructor using-declaration names the same base more "
                     "than once", loc);
        return false;
    }
    cir::RecordInheritedConstructorNominationFact nomination;
    nomination.nominated_record = base_entity;
    nomination.dependent_qualifier = dependent_qualifier;
    nomination.base_validation_deferred = dependent_base;
    nomination.loc = loc;
    updated.inherited_constructor_nominations.push_back(
        std::move(nomination));
    updated.definition_data.has_inherited_constructor = true;
    file_.set_record_facts(record_entity, std::move(updated));
    return true;
}

bool Session::collect_using_enum_declaration(cir::DeclContextId enum_context,
                                             SrcLoc loc) {
    if (!enum_context.valid() || !file_.valid(enum_context) ||
        file_.decl_context(enum_context).kind != cir::DeclContextKind::Enum) {
        report_error("using-enum declaration does not name an enumeration",
                     loc);
        return false;
    }

    cir::DeclContextId destination = current_decl_context();
    bool imported_any = false;
    bump_lookup_generation();
    for (cir::BindingId binding_id :
         file_.decl_context(enum_context).bindings) {
        if (!file_.valid(binding_id)) {
            continue;
        }
        const cir::Binding& binding = file_.binding(binding_id);
        if (binding.lookup_namespace != cir::LookupNamespace::Ordinary ||
            binding.entities.empty()) {
            continue;
        }
        bool enumerators_only = std::all_of(
            binding.entities.begin(), binding.entities.end(),
            [&](cir::EntityId entity) {
                return file_.valid(entity) &&
                    file_.entity(entity).kind == cir::EntityKind::Enumerator;
            });
        if (!enumerators_only) {
            continue;
        }
        file_.add_alias_binding(destination, binding, loc,
                                lookup_generation());
        imported_any = true;
    }
    if (!imported_any) {

        cir::EntityId owner = file_.decl_context(enum_context).owner;
        if (!owner.valid() || !file_.valid(owner) ||
            file_.entity(owner).kind != cir::EntityKind::Enum) {
            report_error("using-enum declaration does not name an enumeration",
                         loc);
            return false;
        }
    }
    return true;
}

bool Session::entity_has_internal_name_linkage(cir::EntityId id) const {
    if (!id.valid() || !file_.valid(id)) {
        return false;
    }
    const cir::Entity& entity = file_.entity(id);
    if (entity.linkage == cir::LinkageKind::Internal) {
        return true;
    }
    cir::DeclContextId context = entity.semantic_context;
    while (context.valid() && file_.valid(context)) {
        const cir::DeclContext& decl_context = file_.decl_context(context);
        cir::EntityId owner = decl_context.owner;
        if (owner.valid() && file_.valid(owner) &&
            file_.entity(owner).kind == cir::EntityKind::Namespace &&
            file_.entity(owner).name.valid() &&
            file_.name(file_.entity(owner).name) == anonymous_namespace_name) {
            return true;
        }
        context = decl_context.parent;
    }
    return false;
}

void Session::finalize_name_linkage() {

    for (cir::EntityId id : file_.entity_ids()) {
        if (!file_.valid(id)) {
            continue;
        }
        cir::Entity& entity = file_.entity_mut(id);
        // A local object in an inline function or template specialization is
        // one program entity even when the enclosing definition appears in
        // several translation units. Declaration collection starts local
        // statics as internal because the function's final specialization
        // linkage can be assigned after its body. Resolve that ownership here,
        // once every enclosing function has its canonical ODR linkage.
        if (!entity.is_template_pattern &&
            entity.local_enclosing_function.valid() &&
            (entity.storage_duration == cir::StorageDuration::Static ||
             entity.storage_duration == cir::StorageDuration::Thread) &&
            file_.valid(entity.local_enclosing_function) &&
            (file_.entity(entity.local_enclosing_function).linkage ==
                 cir::LinkageKind::LinkOnceODR ||
             file_.entity(entity.local_enclosing_function)
                 .decl_flags.is_inline ||
             (file_.template_specialization(entity.local_enclosing_function) &&
              !file_.entity(entity.local_enclosing_function)
                   .is_explicit_template_specialization))) {
            entity.linkage = file_.odr_linkage_for_entity(
                entity.local_enclosing_function);
        }
        if ((entity.linkage != cir::LinkageKind::External &&
             entity.linkage != cir::LinkageKind::LinkOnceODR) ||
            entity.kind == cir::EntityKind::Namespace ||
            entity.is_extern_c) {
            continue;
        }
        if (entity_has_internal_name_linkage(id)) {
            file_.entity_mut(id).linkage = cir::LinkageKind::Internal;
        }
    }

    std::vector<uint8_t> state(file_.entity_table_size(), 0);
    std::function<cir::NameLinkageKind(cir::EntityId)> resolve_name_linkage;
    resolve_name_linkage = [&](cir::EntityId id) -> cir::NameLinkageKind {
        if (!id.valid() || !file_.valid(id)) {
            return cir::NameLinkageKind::None;
        }
        if (state[id.index] == 2) {
            return file_.entity(id).symbol_policy.name_linkage;
        }
        if (state[id.index] == 1) {

            return cir::NameLinkageKind::None;
        }
        state[id.index] = 1;
        cir::Entity& entity = file_.entity_mut(id);

        cir::EntityId inherited = entity.linkage_predecessor;
        if (!inherited.valid()) {
            inherited = entity.abi_owner;
        }
        if (!inherited.valid() && entity.declaring_record.valid()) {
            inherited = entity.declaring_record;
        }
        if (!inherited.valid() && entity.parent.valid() &&
            file_.valid(entity.parent)) {
            cir::EntityKind parent_kind = file_.entity(entity.parent).kind;
            if (parent_kind == cir::EntityKind::Record) {
                inherited = entity.parent;
            }
        }

        cir::NameLinkageKind result = cir::NameLinkageKind::None;
        if (entity.kind == cir::EntityKind::Namespace) {
            bool anonymous = entity.name.valid() &&
                file_.name(entity.name) == anonymous_namespace_name;
            result = anonymous ? cir::NameLinkageKind::Internal
                               : cir::NameLinkageKind::External;
            cir::DeclContextId context = entity.semantic_context;
            if (context.valid() && file_.valid(context) &&
                file_.decl_context(context).owner == id) {
                context = file_.decl_context(context).parent;
            }
            while (context.valid() && file_.valid(context)) {
                cir::EntityId owner = file_.decl_context(context).owner;
                if (owner.valid() && file_.valid(owner) &&
                    file_.entity(owner).kind == cir::EntityKind::Namespace &&
                    resolve_name_linkage(owner) ==
                        cir::NameLinkageKind::Internal) {
                    result = cir::NameLinkageKind::Internal;
                    break;
                }
                context = file_.decl_context(context).parent;
            }
        } else if (inherited.valid()) {
            result = resolve_name_linkage(inherited);
        } else if (entity.local_enclosing_function.valid() ||
                   entity.local_name_kind !=
                       cir::LocalNameComponentKind::None) {
            result = cir::NameLinkageKind::None;
        } else {
            cir::DeclContextId context = entity.semantic_context;
            if (context.valid() && file_.valid(context) &&
                (entity.kind == cir::EntityKind::Record ||
                 entity.kind == cir::EntityKind::Enum) &&
                file_.decl_context(context).owner == id) {
                context = file_.decl_context(context).parent;
            }
            bool block_owned = false;
            cir::EntityId namespace_owner{};
            while (context.valid() && file_.valid(context)) {
                const cir::DeclContext& dc = file_.decl_context(context);
                if (dc.kind == cir::DeclContextKind::Block ||
                    dc.kind == cir::DeclContextKind::Function) {
                    block_owned = true;
                    break;
                }
                if (dc.kind == cir::DeclContextKind::Namespace &&
                    dc.owner.valid()) {
                    namespace_owner = dc.owner;
                    break;
                }
                if (dc.kind == cir::DeclContextKind::TranslationUnit) {
                    break;
                }
                context = dc.parent;
            }
            if (block_owned) {
                result = cir::NameLinkageKind::None;
            } else if (entity.linkage == cir::LinkageKind::Internal ||
                       (!entity.is_extern_c && namespace_owner.valid() &&
                        resolve_name_linkage(namespace_owner) ==
                            cir::NameLinkageKind::Internal)) {
                result = cir::NameLinkageKind::Internal;
            } else {
                // [basic.link]p3: a non-template, non-volatile const
                // namespace variable is internal unless extern/inline or a
                // prior declaration supplied different linkage.
                // [basic.link]p3: the const-implies-internal default does
                // not apply in the purview of a module interface unit
                // (outside the private fragment) or of a module partition.
                bool module_purview_const_exception = false;
                if (entity.module_attachment.valid() &&
                    entity.origin_fragment == cir::ModuleFragment::Purview &&
                    file_.valid(entity.origin_unit)) {
                    cir::ModuleUnitFact::Kind unit_kind =
                        file_.module_unit(entity.origin_unit).kind;
                    module_purview_const_exception =
                        unit_kind !=
                            cir::ModuleUnitFact::Kind::Implementation &&
                        unit_kind != cir::ModuleUnitFact::Kind::HeaderUnit;
                }
                bool const_namespace_variable =
                    !module_purview_const_exception &&
                    entity.kind == cir::EntityKind::Variable &&
                    entity.object_origin !=
                        cir::EntityObjectOrigin::TemplateParameterObject &&
                    (entity.qualifiers & cir::QualConst) != 0 &&
                    (entity.qualifiers & cir::QualVolatile) == 0 &&
                    !entity.declared_with_extern &&
                    !entity.decl_flags.is_inline &&
                    !template_info(id) &&
                    !file_.template_specialization(id);
                result = const_namespace_variable
                    ? cir::NameLinkageKind::Internal
                    : cir::NameLinkageKind::External;
            }
        }

        if (result == cir::NameLinkageKind::External &&
            file_.effective_module_attachment(entity).valid() &&
            !entity.is_module_exported) {

            result = cir::NameLinkageKind::Module;
        }

        entity.symbol_policy.name_linkage = result;
        state[id.index] = 2;
        return result;
    };

    if (file_.has_module_units()) {
        for (cir::EntityId id : file_.entity_ids()) {
            if (!file_.valid(id)) {
                continue;
            }
            cir::Entity& entity = file_.entity_mut(id);
            if (!entity.is_module_exported &&
                entity.linkage_predecessor.valid() &&
                file_.valid(entity.linkage_predecessor) &&
                file_.entity(entity.linkage_predecessor).is_module_exported) {
                entity.is_module_exported = true;
            }
        }
    }

    for (cir::ClosureIdentityId identity_id :
         file_.closure_identity_ids()) {
        const cir::ClosureIdentityFact& identity =
            file_.closure_identity(identity_id);
        if (identity.abi_context !=
                cir::ClosureAbiContextKind::FunctionBody ||
            !identity.lexical_owner.valid() ||
            !file_.valid(identity.lexical_owner)) {
            continue;
        }
        auto stamp = [&](cir::EntityId member) {
            if (member.valid() && file_.valid(member) &&
                !file_.entity(member).abi_owner.valid()) {
                file_.entity_mut(member).abi_owner = identity.lexical_owner;
            }
        };
        stamp(identity.call_operator);
        stamp(identity.invoker);
        if (identity.record.valid() && file_.valid(identity.record)) {
            stamp(identity.record);
            if (const cir::RecordFacts* facts =
                    file_.record_facts(identity.record)) {
                for (const cir::RecordMethodFact& method : facts->methods) {
                    stamp(method.entity);
                }
            }
        }
    }

    // Attribute-defined aliases and indirect functions retain their target
    // through a symbol spelling rather than a CIR EntityId operand. Treat
    // matching same-translation-unit definitions as roots so the ordinary
    // reachability graph cannot discard an internal target behind that
    // textual edge. This intentionally follows the resolver's existing
    // source-name contract; overload-specific ABI spellings remain a
    // separate attribute-resolution concern.
    std::unordered_set<std::string> attribute_definition_targets;
    for (cir::EntityId id : file_.entity_ids()) {
        if (!file_.valid(id)) {
            continue;
        }
        const cir::EntityAttributeFacts& attrs = file_.entity(id).attr_facts;
        if (!attrs.alias_target.empty()) {
            attribute_definition_targets.insert(attrs.alias_target);
        }
        if (!attrs.weakref_target.empty()) {
            attribute_definition_targets.insert(attrs.weakref_target);
        }
        if (!attrs.ifunc_target.empty()) {
            attribute_definition_targets.insert(attrs.ifunc_target);
        }
    }

    for (cir::EntityId id : file_.entity_ids()) {
        if (!file_.valid(id)) {
            continue;
        }
        cir::Entity& entity = file_.entity_mut(id);
        cir::NameLinkageKind name_linkage = resolve_name_linkage(id);
        if (entity.is_module_exported &&
            name_linkage == cir::NameLinkageKind::Internal &&
            entity.name.valid()) {

            report_error("exported declaration of '" +
                             std::string(file_.name(entity.name)) +
                             "' has internal linkage",
                         entity.loc);
        }
        cir::LinkageKind emission = entity.linkage;
        if ((name_linkage == cir::NameLinkageKind::External ||
             name_linkage == cir::NameLinkageKind::Module) &&
            entity.decl_flags.is_inline && entity.is_definition &&
            !entity.is_explicit_template_specialization) {
            emission = file_.odr_linkage_for_entity(id);
        }
        if (name_linkage == cir::NameLinkageKind::Internal) {
            emission = cir::LinkageKind::Internal;
        } else if (entity.abi_owner.valid() && file_.valid(entity.abi_owner)) {
            cir::LinkageKind owner_emission =
                file_.entity(entity.abi_owner).linkage;
            if (owner_emission == cir::LinkageKind::Internal) {
                emission = cir::LinkageKind::Internal;
            } else if (emission == cir::LinkageKind::LinkOnceODR ||
                       owner_emission == cir::LinkageKind::LinkOnceODR) {
                emission = cir::LinkageKind::LinkOnceODR;
            }
        }
        // A no-linkage local class member is nevertheless one mergeable ODR
        // definition when its enclosing function is mergeable; otherwise its
        // implementation symbol is translation-unit local.
        if (name_linkage == cir::NameLinkageKind::None &&
            entity.local_enclosing_function.valid() &&
            file_.valid(entity.local_enclosing_function)) {
            cir::LinkageKind fn_linkage =
                file_.entity(entity.local_enclosing_function).linkage;
            const cir::Entity& function =
                file_.entity(entity.local_enclosing_function);
            bool mergeable = fn_linkage == cir::LinkageKind::LinkOnceODR ||
                function.decl_flags.is_inline ||
                (file_.template_specialization(
                     entity.local_enclosing_function) &&
                 !function.is_explicit_template_specialization);
            emission = mergeable
                ? cir::LinkageKind::LinkOnceODR
                : cir::LinkageKind::Internal;
        }
        entity.linkage = emission;
        entity.symbol_policy.emission = emission;
        cir::EntityId semantic_owner = entity.linkage_predecessor;
        if (!semantic_owner.valid()) {
            semantic_owner = entity.declaring_record;
        }
        if (!semantic_owner.valid()) {
            semantic_owner = entity.parent;
        }
        entity.symbol_policy.semantic_owner = semantic_owner;
        entity.symbol_policy.abi_owner = entity.abi_owner;
        entity.symbol_policy.generated_role = entity.generated_symbol_role;
        entity.symbol_policy.module_attachment =
            file_.effective_module_attachment(entity);
        entity.symbol_policy.imported_definition =
            entity.origin_unit.valid() &&
            entity.origin_unit != module_state_.unit &&
            file_.has_imported_definition(id);
        bool exact_generated_identity =
            entity.abi_identity == cir::AbiIdentityKind::Generated ||
            entity.abi_identity == cir::AbiIdentityKind::Exact;
        entity.symbol_policy.type_language =
            !exact_generated_identity &&
                    (entity.kind == cir::EntityKind::Function ||
                    entity.kind == cir::EntityKind::Method ||
                    entity.kind == cir::EntityKind::Constructor ||
                    entity.kind == cir::EntityKind::Destructor)
                ? (entity.is_extern_c ? cir::LanguageLinkageKind::C
                                      : cir::LanguageLinkageKind::CXX)
                : cir::LanguageLinkageKind::None;
        entity.symbol_policy.name_language =
            !exact_generated_identity &&
                    (name_linkage == cir::NameLinkageKind::External ||
                     name_linkage == cir::NameLinkageKind::Module)
                ? (entity.is_extern_c ? cir::LanguageLinkageKind::C
                                      : cir::LanguageLinkageKind::CXX)
                : cir::LanguageLinkageKind::None;
        if (emission == cir::LinkageKind::Internal) {
            entity.symbol_policy.visibility =
                cir::SymbolVisibilityKind::Default;
        } else if (entity.attr_facts.visibility == "hidden") {
            entity.symbol_policy.visibility =
                cir::SymbolVisibilityKind::Hidden;
        } else if (entity.attr_facts.visibility == "protected") {
            entity.symbol_policy.visibility =
                cir::SymbolVisibilityKind::Protected;
        } else {
            entity.symbol_policy.visibility =
                cir::SymbolVisibilityKind::Default;
        }
        bool defines_alias_or_ifunc =
            !entity.attr_facts.alias_target.empty() ||
            !entity.attr_facts.weakref_target.empty() ||
            !entity.attr_facts.ifunc_target.empty();
        bool has_backend_symbol =
            is_callable_entity_kind(entity.kind) ||
            entity.kind == cir::EntityKind::Variable;
        bool definition_is_available =
            has_backend_symbol &&
            (entity.is_definition || defines_alias_or_ifunc) &&
            !entity.is_deleted &&
            !entity.decl_flags.is_consteval &&
            !entity.is_template_pattern &&
            !entity.result_type_only_definition &&
            !entity.suppressed_by_explicit_instantiation_declaration &&
            !entity.suppressed_as_unselected_template_candidate &&
            !(entity.symbol_policy.imported_definition &&
              emission != cir::LinkageKind::LinkOnceODR);
        bool was_required =
            entity.symbol_policy.definition_emission ==
                cir::DefinitionEmissionKind::Required;
        bool is_attribute_definition_target =
            entity.name.valid() &&
            attribute_definition_targets.contains(
                std::string(file_.name(entity.name)));
        bool forced_definition =
            entity.is_explicit_instantiation_definition ||
            entity.is_module_exported ||
            entity.attr_facts.is_used ||
            defines_alias_or_ifunc ||
            is_attribute_definition_target ||
            entity.attr_facts.constructor_priority >= 0 ||
            entity.attr_facts.destructor_priority >= 0;

        bool deferrable_definition =
            emission == cir::LinkageKind::LinkOnceODR ||
            (emission == cir::LinkageKind::Internal &&
             is_callable_entity_kind(entity.kind));
        entity.symbol_policy.definition_emission =
            !definition_is_available
                ? cir::DefinitionEmissionKind::DeclarationOnly
                : deferrable_definition && !was_required && !forced_definition
                    ? cir::DefinitionEmissionKind::Deferred
                    : cir::DefinitionEmissionKind::Required;
        entity.symbol_policy.finalized = true;
    }

    if (file_.abi_policy().cxx_abi == CxxAbiKind::Itanium) {
        for (cir::EntityId id : file_.entity_ids()) {
            if (!file_.valid(id) ||
                file_.entity(id).kind != cir::EntityKind::Record) {
                continue;
            }
            const cir::RecordFacts* existing = file_.record_facts(id);
            if (!existing) {
                continue;
            }
            cir::RecordFacts facts = *existing;
            facts.key_function = {};
            const cir::Entity& record = file_.entity(id);
            bool externally_visible =
                record.symbol_policy.name_linkage ==
                    cir::NameLinkageKind::External ||
                record.symbol_policy.name_linkage ==
                    cir::NameLinkageKind::Module;
            bool template_instantiation =
                file_.template_specialization(id) &&
                !record.is_explicit_template_specialization;
            if (facts.is_polymorphic &&
                externally_visible &&
                !record.is_template_pattern &&
                !facts.is_template_pattern_provisional &&
                !template_instantiation) {
                for (const cir::RecordMethodFact& method : facts.methods) {
                    if (!method.is_key_function_candidate ||
                        !method.entity.valid() ||
                        !file_.valid(method.entity)) {
                        continue;
                    }
                    if (!file_.abi_policy().can_key_function_be_inline &&
                        file_.entity(method.entity).decl_flags.is_inline) {
                        continue;
                    }
                    facts.key_function = method.entity;
                    break;
                }
            }
            file_.set_record_facts(id, std::move(facts));
        }

        for (cir::EntityId id : file_.entity_ids()) {
            if (!file_.valid(id)) {
                continue;
            }
            cir::Entity& entity = file_.entity_mut(id);
            bool class_data =
                is_itanium_class_data_role(entity.generated_symbol_role);
            bool class_data_support =
                is_itanium_class_data_support_role(
                    entity.generated_symbol_role);
            if ((!class_data && !class_data_support) ||
                !entity.abi_owner.valid() ||
                !file_.valid(entity.abi_owner)) {
                continue;
            }
            const cir::RecordFacts* owner_facts =
                file_.record_facts(entity.abi_owner);
            if (!owner_facts) {
                continue;
            }
            const cir::Entity& owner = file_.entity(entity.abi_owner);
            bool suppressed =
                owner.suppressed_by_explicit_instantiation_declaration ||
                (entity.symbol_policy.imported_definition &&
                 entity.symbol_policy.emission !=
                     cir::LinkageKind::LinkOnceODR);
            bool forced =
                owner.is_explicit_instantiation_definition ||
                owner.is_module_exported;
            bool demanded =
                entity.symbol_policy.definition_emission ==
                    cir::DefinitionEmissionKind::Required;

            if (owner_facts->key_function.valid() &&
                file_.valid(owner_facts->key_function)) {
                const cir::Entity& key =
                    file_.entity(owner_facts->key_function);
                bool key_defined_here =
                    key.is_definition &&
                    !key.is_deleted &&
                    !key.is_template_pattern &&
                    !key.result_type_only_definition &&
                    !key.suppressed_by_explicit_instantiation_declaration &&
                    !key.suppressed_as_unselected_template_candidate &&
                    !(key.symbol_policy.imported_definition &&
                      key.symbol_policy.emission !=
                          cir::LinkageKind::LinkOnceODR);
                entity.linkage = cir::LinkageKind::External;
                entity.symbol_policy.emission =
                    cir::LinkageKind::External;
                entity.symbol_policy.comdat_key = {};
                entity.symbol_policy.definition_emission =
                    key_defined_here
                        ? (class_data
                               ? cir::DefinitionEmissionKind::Required
                               : demanded
                                   ? cir::DefinitionEmissionKind::Required
                                   : cir::DefinitionEmissionKind::Deferred)
                        : cir::DefinitionEmissionKind::DeclarationOnly;
                continue;
            }

            entity.symbol_policy.definition_emission =
                suppressed
                    ? cir::DefinitionEmissionKind::DeclarationOnly
                    : demanded || (forced && class_data)
                        ? cir::DefinitionEmissionKind::Required
                        : cir::DefinitionEmissionKind::Deferred;
        }
    }

    for (cir::EntityId id : file_.entity_ids()) {
        if (!file_.valid(id)) {
            continue;
        }
        cir::Entity& entity = file_.entity_mut(id);
        if (entity.symbol_policy.emission != cir::LinkageKind::LinkOnceODR) {
            continue;
        }
        std::string key;
        if (file_.valid(id)) {
            const cir::Entity& keyed_entity = file_.entity(id);
            if ((keyed_entity.abi_identity ==
                     cir::AbiIdentityKind::Generated ||
                 keyed_entity.abi_identity == cir::AbiIdentityKind::Exact) &&
                keyed_entity.name.valid()) {
                key = std::string(file_.name(keyed_entity.name));
            } else if (!keyed_entity.attr_facts.asm_label.empty()) {
                key = keyed_entity.attr_facts.asm_label;
            } else {
                key = abi::itanium_linkage_name(file_, id);
                if (key.empty() && keyed_entity.name.valid()) {
                    key = std::string(file_.name(keyed_entity.name));
                }
            }
        }
        if (!key.empty()) {
            entity.symbol_policy.comdat_key = file_.intern_name(key);
        }
    }
}

Session::QualifierResolution Session::resolve_qualifier_root() const {
    QualifierResolution result;
    result.context = translation_unit_context_;
    result.is_namespace = true;
    return result;
}

void Session::materialize_qualifier_entity(cir::EntityId entity, SrcLoc loc) {
    if (!entity.valid() || !file_.valid(entity)) {
        return;
    }
    const cir::EntityKind kind = file_.entity(entity).kind;
    const bool is_definition = file_.entity(entity).is_definition;
    const cir::DeclContextId semantic_context =
        file_.entity(entity).semantic_context;
    const cir::TypeId type = file_.entity(entity).type;
    if (kind == cir::EntityKind::Enum && !is_definition) {
        cir::DeclContextId context = semantic_context;
        while (context.valid() && file_.valid(context)) {
            const cir::DeclContext& declaration = file_.decl_context(context);
            context = declaration.parent;
            if (!context.valid() || !file_.valid(context)) {
                break;
            }
            const cir::DeclContext& parent = file_.decl_context(context);
            if (parent.kind == cir::DeclContextKind::Record &&
                parent.owner.valid() &&
                file_.template_specialization(parent.owner)) {
                (void)request_class_instantiation(
                    parent.owner,
                    cir::InstantiationDemandKind::ScopedEnumDefinition,
                    loc,
                    entity);
                break;
            }
        }
    }
    if (kind == cir::EntityKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts(entity);
        if (facts && facts->is_incomplete) {
            (void)require_complete_class_type(
                type,
                loc,
                cir::InstantiationDemandKind::BaseMemberList);
        }
    }
}

std::optional<Session::QualifierResolution>
Session::resolve_type_qualifier(cir::TypeRef type_ref,
                                SrcLoc loc,
                                std::string_view display_name) {
    if (!type_ref.type.valid()) {
        return std::nullopt;
    }
    while (file_.valid(type_ref.type) &&
           file_.type(type_ref.type).kind == cir::TypeKind::Typedef) {
        const auto* alias = std::get_if<cir::TypedefTypePayload>(
            &file_.type_payload(type_ref.type));
        if (!alias || !alias->underlying_type.type.valid()) {
            return std::nullopt;
        }
        type_ref.qualifiers = static_cast<uint8_t>(
            type_ref.qualifiers | alias->underlying_type.qualifiers);
        type_ref.type = alias->underlying_type.type;
    }

    QualifierResolution result;
    if (is_dependent_type(type_ref.type) ||
        type_contains_type_param(type_ref.type)) {
        result.dependent_type = type_ref;
        return result;
    }

    cir::TypeId resolved = file_.resolved_type(type_ref.type);
    if (!file_.valid(resolved) ||
        (file_.type(resolved).kind != cir::TypeKind::Record &&
         file_.type(resolved).kind != cir::TypeKind::Enum)) {
        return std::nullopt;
    }
    cir::EntityId owner = file_.type(resolved).kind == cir::TypeKind::Record
        ? file_.record_entity(resolved)
        : std::get<cir::EnumTypePayload>(file_.type_payload(resolved)).entity;
    if (!owner.valid() || !file_.valid(owner)) {
        return std::nullopt;
    }

    materialize_qualifier_entity(owner, loc);
    result.entity = owner;
    result.context = file_.entity(owner).semantic_context;
    result.is_namespace = false;
    result.has_error = !result.context.valid();
    if (result.has_error) {
        std::string label = display_name.empty()
            ? file_.format_type(type_ref)
            : std::string(display_name);
        report_error("scope of '" + label + "' is unavailable", loc);
    }
    return result;
}

Session::UnqualifiedQualifierLookup
Session::lookup_unqualified_qualifier(std::string_view name) const {
    UnqualifiedQualifierLookup result;
    for (cir::DeclContextId context = current_decl_context();
         context.valid() && file_.valid(context);
         context = file_.decl_context(context).parent) {
        if (file_.decl_context(context).kind ==
            cir::DeclContextKind::Record) {
            cir::EntityId owner = file_.decl_context(context).owner;
            if (owner.valid() && file_.valid(owner)) {
                MemberLookupResult member = lookup_member_name(
                    file_.entity(owner).type, name,
                    /*type_only=*/true);
                if (member.found_name) {
                    result.found_name = true;
                    if (member.ambiguous || member.declarations.empty()) {
                        return result;
                    }
                    cir::TypeRef designated{};
                    for (const MemberLookupDeclaration& declaration :
                         member.declarations) {
                        if (!declaration.designated_type.valid()) {
                            return result;
                        }
                        cir::TypeRef candidate =
                            declaration.designated_type;
                        candidate.type = file_.resolved_type(candidate.type);
                        if (designated.valid() && designated != candidate) {
                            return result;
                        }
                        designated = candidate;
                    }
                    result.type = designated;
                    return result;
                }

                cir::TypeRef provisional =
                    lookup_qualified_type_name_ref(context, name);
                if (provisional.valid()) {
                    result.found_name = true;
                    result.type = provisional;
                    return result;
                }
            }
        }

        if (const cir::Binding* binding =
                file_.lookup_qualifier_binding(
                    context, name, /*include_parents=*/false)) {
            result.found_name = true;
            if (binding->is_type_name && binding->type.valid()) {
                result.type = binding->type;
            } else {
                result.binding = binding;
            }
            return result;
        }
    }
    return result;
}

Session::QualifierResolution Session::resolve_qualifier_component(
    cir::DeclContextId scope,
    std::string_view name,
    SrcLoc loc) {
    QualifierResolution result;
    const cir::Binding* binding = nullptr;
    auto resolve_type_as_qualifier =
        [&](cir::TypeRef type_ref) -> std::optional<QualifierResolution> {
        return resolve_type_qualifier(type_ref, loc, name);
    };
    if (!scope.valid()) {
        if (const ParameterPackElement* replay = parameter_pack_replay_element(
                ParameterPackKind::Type, name)) {
            const cir::TypeRef* type = std::get_if<cir::TypeRef>(replay);
            if (type) {
                if (auto replay_result = resolve_type_as_qualifier(*type)) {
                    return *replay_result;
                }
            }
        }

        if (cir::TypeRef active =
                lookup_active_template_header_type_parameter(name);
            active.valid()) {
            if (auto active_result = resolve_type_as_qualifier(active)) {
                return *active_result;
            }
        }
        UnqualifiedQualifierLookup lookup =
            lookup_unqualified_qualifier(name);
        if (lookup.type.valid()) {
            if (auto member_result =
                    resolve_type_as_qualifier(lookup.type)) {
                return *member_result;
            }
        }
        if (lookup.found_name && !lookup.binding) {
            report_error("'" + std::string(name) +
                             "' is not a namespace or class name",
                         loc);
            result.has_error = true;
            return result;
        }
        binding = lookup.binding;
    } else if (file_.valid(scope)) {
        cir::EntityId owner = file_.decl_context(scope).owner;
        if (owner.valid() && file_.valid(owner) &&
            file_.entity(owner).kind == cir::EntityKind::Record) {
            cir::TypeRef member =
                lookup_qualified_type_name_ref(scope, name);
            if (member.valid()) {
                if (auto member_result =
                        resolve_type_as_qualifier(member)) {
                    return *member_result;
                }
            }
        }
    }
    if (scope.valid()) {
        binding = file_.lookup_namespace_name_binding(
            scope, name, /*include_parents=*/false);
    }
    if (scope.valid() && (!binding || binding->entities.empty())) {

        const cir::Binding* type_binding = file_.lookup_type_name_binding(
            scope, name, /*include_parents=*/false);
        if (!type_binding) {
            type_binding = file_.lookup_tag_binding(
                scope, name, /*include_parents=*/false);
        }
        if (type_binding) {
            if (!type_binding->entities.empty() &&
                (file_.entity(type_binding->entities.back()).kind ==
                     cir::EntityKind::Record ||
                 file_.entity(type_binding->entities.back()).kind ==
                     cir::EntityKind::Enum)) {
                binding = type_binding;
            } else if (type_binding->type.type.valid()) {
                if (auto type_result =
                        resolve_type_as_qualifier(type_binding->type)) {
                    return *type_result;
                }
            }
        }
    }
    if (!binding || binding->entities.empty()) {
        report_error("'" + std::string(name) +
                         "' is not a namespace or class name",
                     loc);
        result.has_error = true;
        return result;
    }
    cir::EntityId qualifier_entity = binding->entities.back();
    if (file_.valid(qualifier_entity) &&
        file_.entity(qualifier_entity).kind ==
            cir::EntityKind::NamespaceAlias) {
        const cir::Entity& alias = file_.entity(qualifier_entity);
        result.entity = qualifier_entity;
        result.is_namespace = true;
        if (alias.namespace_alias_is_dependent) {
            result.dependent_type =
                type_ref(file_.dependent_type("dependent namespace alias"));
            return result;
        }
        result.context = alias.semantic_context;
        if (!result.context.valid()) {
            report_error("namespace alias target is unavailable", loc);
            result.has_error = true;
        }
        return result;
    }
    if (file_.valid(qualifier_entity) &&
        file_.entity(qualifier_entity).kind == cir::EntityKind::TypeAlias) {
        cir::TypeRef alias_type = binding->type.type.valid()
            ? binding->type
            : type_ref(file_.entity(qualifier_entity).type);
        if (auto alias_result = resolve_type_as_qualifier(alias_type)) {
            return *alias_result;
        }
    }
    result.entity = qualifier_entity;
    materialize_qualifier_entity(result.entity, loc);
    result.context = file_.entity(result.entity).semantic_context;
    result.is_namespace =
        file_.entity(result.entity).kind == cir::EntityKind::Namespace;
    if (!result.context.valid()) {
        report_error("scope of '" + std::string(name) + "' is unavailable", loc);
        result.has_error = true;
    }
    return result;
}

Session::MemberLookupResult Session::lookup_member_name(
    cir::TypeId record_type,
    std::string_view name,
    bool type_only) const {
    MemberLookupResult result;
    cir::TypeId root_type = file_.resolved_type(record_type);
    const cir::RecordFacts* root_facts =
        file_.record_facts_for_type(root_type);
    if (!root_facts || root_facts->is_incomplete) {
        (void)const_cast<Session*>(this)->require_complete_class_type(
            root_type,
            SrcLoc(),
            cir::InstantiationDemandKind::BaseMemberList);
        root_facts = file_.record_facts_for_type(root_type);
    }
    if (!root_facts) {
        return result;
    }

    struct SubobjectNode {
        cir::TypeId type{};
        std::vector<cir::EntityId> path;
        std::vector<std::vector<MemberLookupBaseStep>> base_paths;
        std::vector<size_t> direct_bases;
    };
    std::vector<SubobjectNode> nodes;
    std::vector<bool> expanded;
    std::unordered_map<uint64_t, size_t> virtual_nodes;
    bool graph_has_dependent_bases = false;

    auto add_node = [&](cir::TypeId type,
                        std::vector<cir::EntityId> path,
                        std::vector<std::vector<MemberLookupBaseStep>>
                            base_paths) -> size_t {
        nodes.push_back(SubobjectNode{file_.resolved_type(type),
                                      std::move(path),
                                      std::move(base_paths), {}});
        expanded.push_back(false);
        return nodes.size() - 1;
    };
    add_node(root_type, {}, {{}});

    auto virtual_storage_path = [&](cir::EntityId record) {
        std::vector<cir::EntityId> path;
        for (const cir::RecordFacts::VirtualBase& base :
             root_facts->virtual_bases) {
            if (base.record_entity == record && base.storage_field.valid()) {
                path.push_back(base.storage_field);
                break;
            }
        }
        return path;
    };

    auto expand_node = [&](auto&& self, size_t node_index) -> void {
        if (node_index >= nodes.size() || expanded[node_index]) {
            return;
        }
        expanded[node_index] = true;
        cir::TypeId node_type = nodes[node_index].type;
        std::vector<cir::EntityId> node_path = nodes[node_index].path;
        std::vector<std::vector<MemberLookupBaseStep>> node_base_paths =
            nodes[node_index].base_paths;
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(node_type);
        if (!facts) {
            return;
        }
        graph_has_dependent_bases = graph_has_dependent_bases ||
            !facts->dependent_bases.empty();
        struct EffectiveBase {
            cir::TypeId type{};
            cir::EntityId record_entity{};
            cir::RecordMemberAccess declared_access =
                cir::RecordMemberAccess::Public;
            bool is_virtual = false;
            uint32_t declaration_index = 0;
        };
        std::vector<EffectiveBase> effective_bases;
        effective_bases.reserve(facts->bases.size());
        for (const cir::RecordBaseFact& base : facts->bases) {
            effective_bases.push_back(
                EffectiveBase{base.type.type,
                              base.record_entity,
                              base.declared_access,
                              base.is_virtual,
                              base.declaration_index});
        }
        if (facts->is_incomplete && facts->entity.valid() &&
            file_.valid(facts->entity)) {
            cir::DeclContextId record_context =
                file_.entity(facts->entity).semantic_context;
            for (ScopeId scope = current_scope_;
                 scope != InvalidScopeId && scope < scopes_.size();
                 scope = scopes_[scope].parent) {
                if (scopes_[scope].context != record_context) {
                    continue;
                }
                if (effective_bases.empty()) {
                    uint32_t index = 0;
                    for (const RecordBaseInput& base :
                         scopes_[scope].pending_bases) {
                        if (base.is_dependent ||
                            (in_template_definition() &&
                             is_dependent_type(base.type))) {
                            graph_has_dependent_bases = true;
                            ++index;
                            continue;
                        }
                        cir::TypeId resolved_base =
                            file_.resolved_type(base.type);
                        cir::EntityId base_record =
                            file_.valid(resolved_base) &&
                                    file_.type(resolved_base).kind ==
                                        cir::TypeKind::Record
                                ? file_.record_entity(resolved_base)
                                : cir::EntityId{};
                        effective_bases.push_back(
                            EffectiveBase{base.type,
                                          base_record,
                                          base.declared_access,
                                          base.is_virtual,
                                          index});
                        ++index;
                    }
                }
                break;
            }
        }
        for (const EffectiveBase& base : effective_bases) {
            std::vector<std::vector<MemberLookupBaseStep>> child_base_paths =
                node_base_paths;
            MemberLookupBaseStep access_step;
            access_step.derived_class = facts->entity;
            access_step.base_type = base.type;
            access_step.declared_access = base.declared_access;
            for (std::vector<MemberLookupBaseStep>& route :
                 child_base_paths) {
                route.push_back(access_step);
            }
            size_t child = std::numeric_limits<size_t>::max();
            if (base.is_virtual) {
                uint64_t key = static_cast<uint64_t>(base.record_entity.index);
                auto existing = virtual_nodes.find(key);
                if (existing != virtual_nodes.end()) {
                    child = existing->second;
                    for (std::vector<MemberLookupBaseStep>& route :
                         child_base_paths) {
                        if (std::find(nodes[child].base_paths.begin(),
                                      nodes[child].base_paths.end(), route) ==
                            nodes[child].base_paths.end()) {
                            nodes[child].base_paths.push_back(
                                std::move(route));
                        }
                    }
                } else {
                    std::vector<cir::EntityId> path =
                        virtual_storage_path(base.record_entity);
                    if (path.empty()) {

                        path = node_path;
                    }
                    child = add_node(base.type, std::move(path),
                                     std::move(child_base_paths));
                    virtual_nodes.emplace(key, child);
                }
            } else {
                cir::EntityId storage{};
                for (const cir::RecordFieldFact& field : facts->fields) {
                    if (!field.is_base_subobject ||
                        field.is_virtual_base_storage) {
                        continue;
                    }
                    if (base_declaration_index(*facts, field) ==
                        base.declaration_index) {
                        storage = field.entity;
                        break;
                    }
                }
                std::vector<cir::EntityId> path = node_path;
                if (storage.valid()) {
                    path.push_back(storage);
                }
                child = add_node(base.type, std::move(path),
                                 std::move(child_base_paths));
            }
            if (child == std::numeric_limits<size_t>::max()) {
                continue;
            }
            if (std::find(nodes[node_index].direct_bases.begin(),
                          nodes[node_index].direct_bases.end(), child) ==
                nodes[node_index].direct_bases.end()) {
                nodes[node_index].direct_bases.push_back(child);
            }
            self(self, child);
        }
    };
    expand_node(expand_node, 0);

    auto is_base_subobject_of = [&](size_t base, size_t derived) {
        if (base == derived) {
            return true;
        }
        std::vector<size_t> pending{derived};
        std::vector<bool> visited(nodes.size(), false);
        while (!pending.empty()) {
            size_t current = pending.back();
            pending.pop_back();
            if (current >= nodes.size() || visited[current]) {
                continue;
            }
            visited[current] = true;
            for (size_t child : nodes[current].direct_bases) {
                if (child == base) {
                    return true;
                }
                pending.push_back(child);
            }
        }
        return false;
    };

    struct LookupSet {
        bool found = false;
        bool invalid = false;
        std::vector<MemberLookupDeclaration> declarations;
        std::vector<size_t> subobjects;
    };

    auto declaration_equal = [&](const MemberLookupDeclaration& lhs,
                                 const MemberLookupDeclaration& rhs) {

        return lhs.entity == rhs.entity;
    };
    auto append_declaration = [&](LookupSet& set,
                                  MemberLookupDeclaration declaration) {
        auto existing = std::find_if(
            set.declarations.begin(), set.declarations.end(),
            [&](const MemberLookupDeclaration& item) {
                return declaration_equal(item, declaration);
            });
        if (existing == set.declarations.end()) {
            set.declarations.push_back(std::move(declaration));
            return;
        }
        for (std::vector<cir::EntityId>& path : declaration.object_paths) {
            if (std::find(existing->object_paths.begin(),
                          existing->object_paths.end(), path) ==
                existing->object_paths.end()) {
                existing->object_paths.push_back(std::move(path));
            }
        }
        for (std::vector<MemberLookupBaseStep>& path :
             declaration.base_paths) {
            if (std::find(existing->base_paths.begin(),
                          existing->base_paths.end(), path) ==
                existing->base_paths.end()) {
                existing->base_paths.push_back(std::move(path));
            }
        }
    };
    auto same_declaration_set = [&](const LookupSet& lhs,
                                    const LookupSet& rhs) {
        if (lhs.invalid || rhs.invalid ||
            lhs.declarations.size() != rhs.declarations.size()) {
            return false;
        }
        return std::all_of(lhs.declarations.begin(), lhs.declarations.end(),
                           [&](const MemberLookupDeclaration& declaration) {
                               return std::any_of(
                                   rhs.declarations.begin(),
                                   rhs.declarations.end(),
                                   [&](const MemberLookupDeclaration& other) {
                                       return declaration_equal(declaration,
                                                                other);
                                   });
                           });
    };
    auto append_subobjects = [&](LookupSet& into, const LookupSet& from) {
        for (size_t subobject : from.subobjects) {
            if (std::find(into.subobjects.begin(), into.subobjects.end(),
                          subobject) == into.subobjects.end()) {
                into.subobjects.push_back(subobject);
            }
        }
    };
    auto set_is_base_of = [&](const LookupSet& bases,
                              const LookupSet& derived) {
        return !bases.subobjects.empty() &&
            std::all_of(bases.subobjects.begin(), bases.subobjects.end(),
                        [&](size_t base) {
                            return std::any_of(
                                derived.subobjects.begin(),
                                derived.subobjects.end(),
                                [&](size_t candidate) {
                                    return is_base_subobject_of(base,
                                                                candidate);
                                });
                        });
    };

    auto direct_lookup = [&](size_t node_index) {
        LookupSet direct;
        const SubobjectNode& node = nodes[node_index];
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(node.type);
        if (!facts) {
            return direct;
        }
        cir::DeclContextId context =
            facts->entity.valid() && file_.valid(facts->entity)
                ? file_.entity(facts->entity).semantic_context
                : cir::DeclContextId{};
        cir::EntityId specialization_template =
            facts->entity.valid() && file_.valid(facts->entity)
                ? class_template_entity_for_record(facts->entity)
                : cir::EntityId{};
        const TemplateInfo* specialization_template_info =
            specialization_template.valid()
                ? template_info(specialization_template)
                : nullptr;
        if (specialization_template_info &&
            specialization_template_info->name == name) {
            direct.found = true;
            direct.subobjects.push_back(node_index);
            MemberLookupDeclaration declaration;
            declaration.entity = facts->entity;
            declaration.designated_type = file_.type_ref(node.type);
            declaration.declaring_class = node.type;
            declaration.object_paths.push_back(node.path);
            declaration.base_paths = node.base_paths;
            append_declaration(direct, std::move(declaration));
            return direct;
        }
        const cir::Binding* binding = context.valid()
            ? file_.lookup_ordinary_binding(context, name,
                                            /*include_parents=*/false)
            : nullptr;
        auto binding_has_non_structor_declaration = [&](const cir::Binding* item) {
            return item && std::any_of(
                item->entities.begin(), item->entities.end(),
                [&](cir::EntityId entity) {
                    if (!entity.valid() || !file_.valid(entity)) {
                        return false;
                    }
                    cir::EntityKind kind = file_.entity(entity).kind;
                    return kind != cir::EntityKind::Constructor &&
                        kind != cir::EntityKind::Destructor;
                });
        };
        auto binding_has_type_declaration = [&](const cir::Binding* item) {
            return item && std::any_of(
                item->entities.begin(), item->entities.end(),
                [&](cir::EntityId entity) {
                    if (!entity.valid() || !file_.valid(entity)) {
                        return false;
                    }
                    cir::EntityKind kind = file_.entity(entity).kind;
                    return kind == cir::EntityKind::Record ||
                        kind == cir::EntityKind::Enum ||
                        kind == cir::EntityKind::TypeAlias;
                });
        };
        if (context.valid() && binding &&
            !binding_has_non_structor_declaration(binding)) {

            const cir::DeclContext& declaration_context =
                file_.decl_context(context);
            for (auto candidate = declaration_context.bindings.rbegin();
                 candidate != declaration_context.bindings.rend();
                 ++candidate) {
                if (!file_.valid(*candidate)) {
                    continue;
                }
                const cir::Binding& previous = file_.binding(*candidate);
                if (previous.lookup_namespace !=
                        cir::LookupNamespace::Ordinary ||
                    !previous.name.valid() ||
                    file_.name(previous.name) != name ||
                    !binding_has_non_structor_declaration(&previous)) {
                    continue;
                }
                binding = &previous;
                break;
            }
        }

        if ((!binding ||
             (type_only && !binding_has_type_declaration(binding))) &&
            context.valid()) {
            binding = file_.lookup_tag_binding(context, name,
                                               /*include_parents=*/false);
        }
        if (binding && !binding->entities.empty()) {
            direct.subobjects.push_back(node_index);
            for (cir::EntityId entity : binding->entities) {
                if (!entity.valid() || !file_.valid(entity)) {
                    continue;
                }
                const cir::Entity& bound_entity = file_.entity(entity);
                if (type_only &&
                    bound_entity.kind != cir::EntityKind::Record &&
                    bound_entity.kind != cir::EntityKind::Enum &&
                    bound_entity.kind != cir::EntityKind::TypeAlias) {
                    continue;
                }
                if (bound_entity.kind == cir::EntityKind::Constructor ||
                    bound_entity.kind == cir::EntityKind::Destructor) {
                    continue;
                }
                const cir::MemberUsingOrigin* imported_origin = nullptr;
                bool has_import_origin = false;
                for (const cir::MemberUsingOrigin& origin :
                     binding->member_using_origins) {
                    if (origin.entity != entity ||
                        origin.importing_record != facts->entity) {
                        continue;
                    }
                    has_import_origin = true;
                    bool hidden = false;
                    if (origin.using_fact_index !=
                            std::numeric_limits<uint32_t>::max() &&
                        origin.using_fact_index <
                            facts->using_declarations.size()) {
                        const cir::RecordUsingDeclarationFact& using_fact =
                            facts->using_declarations[
                                origin.using_fact_index];
                        for (const cir::RecordUsingDeclarationEntry& entry :
                             using_fact.entries) {
                            if (entry.entity == entity &&
                                entry.hidden_by.valid()) {
                                hidden = true;
                                break;
                            }
                        }
                    }
                    if (!hidden) {
                        imported_origin = &origin;
                        break;
                    }
                }
                bool imported_here = imported_origin != nullptr;
                bool member_template_declared_here = false;
                if (const TemplateInfo* info = template_info(entity)) {
                    member_template_declared_here =
                        info->pattern_record == facts->entity;
                    for (cir::DeclContextId declaration_context =
                             info->lexical_context;
                         !member_template_declared_here &&
                             declaration_context.valid() &&
                             file_.valid(declaration_context);
                         declaration_context =
                             file_.decl_context(declaration_context).parent) {
                        if (declaration_context == context) {
                            member_template_declared_here = true;
                            break;
                        }
                        cir::DeclContextKind declaration_kind =
                            file_.decl_context(declaration_context).kind;
                        if (declaration_kind ==
                                cir::DeclContextKind::Namespace ||
                            declaration_kind ==
                                cir::DeclContextKind::TranslationUnit) {
                            break;
                        }
                    }
                }
                bool declared_here = entity == facts->entity ||
                    (binding->context == context && !has_import_origin) ||
                    (bound_entity.is_record_member &&
                     bound_entity.declaring_record == facts->entity) ||
                    bound_entity.parent == facts->entity ||
                    bound_entity.lexical_context == context ||
                    member_template_declared_here;
                if (!declared_here && !imported_here) {
                    continue;
                }
                cir::EntityId specialization_primary =
                    facts->entity.valid() && file_.valid(facts->entity)
                        ? class_template_entity_for_record(facts->entity)
                        : cir::EntityId{};
                const TemplateInfo* specialization_info =
                    specialization_primary.valid()
                        ? template_info(specialization_primary)
                        : nullptr;
                if (specialization_primary.valid() &&
                    (entity == specialization_primary ||
                     (specialization_info &&
                      entity == specialization_info->pattern_record))) {

                    entity = facts->entity;
                }
                MemberLookupDeclaration declaration;
                declaration.entity = entity;
                const cir::Entity& entity_record = file_.entity(entity);
                cir::EntityId declaration_owner =
                    entity_record.is_record_member
                    ? entity_record.declaring_record
                    : entity_record.parent;
                declaration.declaring_class =
                    declaration_owner.valid() &&
                            file_.valid(declaration_owner) &&
                            file_.entity(declaration_owner).kind ==
                                cir::EntityKind::Record
                        ? file_.entity(declaration_owner).type
                        : node.type;
                if (entity_record.is_record_member) {
                    declaration.access_owner =
                        entity_record.declaring_record;
                    declaration.declared_access =
                        entity_record.declared_member_access;
                    declaration.has_declared_access = true;
                }
                bool imported = false;
                if (imported_origin) {
                    const cir::MemberUsingOrigin& origin = *imported_origin;
                    imported = true;
                    declaration.found_through_using = true;
                    declaration.importing_class = origin.importing_record;
                    declaration.using_fact_index = origin.using_fact_index;
                    declaration.implicit_object_class = node.type;
                    declaration.access_owner = origin.importing_record;
                    declaration.declared_access = origin.declared_access;
                    declaration.has_declared_access = true;
                    cir::TypeId declaration_type = file_.resolved_type(
                        declaration.declaring_class);
                    for (size_t candidate = 0; candidate < nodes.size();
                         ++candidate) {
                        if (!is_base_subobject_of(candidate, node_index) ||
                            file_.resolved_type(nodes[candidate].type) !=
                                declaration_type) {
                            continue;
                        }
                        declaration.object_paths.push_back(
                            nodes[candidate].path);
                        for (const std::vector<MemberLookupBaseStep>& route :
                             nodes[candidate].base_paths) {
                            if (std::find(declaration.base_paths.begin(),
                                          declaration.base_paths.end(),
                                          route) ==
                                declaration.base_paths.end()) {
                                declaration.base_paths.push_back(route);
                            }
                        }
                    }
                }
                if (!imported) {
                    declaration.object_paths.push_back(node.path);
                    declaration.base_paths = node.base_paths;
                }
                cir::EntityKind kind = entity_record.kind;
                if (kind == cir::EntityKind::Record ||
                    kind == cir::EntityKind::Enum ||
                    kind == cir::EntityKind::TypeAlias) {
                    declaration.designated_type =
                        kind == cir::EntityKind::TypeAlias &&
                                binding->is_type_name &&
                                binding->type.valid()
                            ? binding->type
                            : file_.type_ref(entity_record.type,
                                             entity_record.qualifiers);
                }
                if (kind == cir::EntityKind::Field) {
                    declaration.member_path.push_back(entity);
                }
                append_declaration(direct, std::move(declaration));
            }
            if (!direct.declarations.empty()) {
                direct.found = true;
                return direct;
            }
            direct.subobjects.clear();
        }

        cir::EntityId injected_template =
            facts->entity.valid() && file_.valid(facts->entity)
                ? class_template_entity_for_record(facts->entity)
                : cir::EntityId{};
        const TemplateInfo* injected_template_info =
            injected_template.valid() ? template_info(injected_template)
                                      : nullptr;
        bool names_injected_class =
            facts->entity.valid() && file_.valid(facts->entity) &&
            ((file_.entity(facts->entity).name.valid() &&
              file_.name(file_.entity(facts->entity).name) == name) ||
             (injected_template_info &&
              injected_template_info->name == name));
        if (names_injected_class) {
            direct.found = true;
            direct.subobjects.push_back(node_index);
            MemberLookupDeclaration declaration;
            declaration.entity = facts->entity;
            declaration.designated_type = file_.type_ref(node.type);
            declaration.declaring_class = node.type;
            declaration.object_paths.push_back(node.path);
            declaration.base_paths = node.base_paths;
            append_declaration(direct, std::move(declaration));
            return direct;
        }

        auto search_anonymous = [&](auto&& self,
                                    cir::TypeId current,
                                    std::vector<cir::EntityId>& path,
                                    cir::EntityId access_field) -> void {
            const cir::RecordFacts* current_facts =
                file_.record_facts_for_type(file_.resolved_type(current));
            if (!current_facts) {
                return;
            }
            for (const cir::RecordFieldFact& field : current_facts->fields) {
                if (field.is_base_subobject) {
                    continue;
                }
                if (field.name.valid() && file_.name(field.name) == name) {
                    MemberLookupDeclaration declaration;
                    declaration.entity = field.entity;
                    declaration.declaring_class = node.type;
                    declaration.object_paths.push_back(node.path);
                    declaration.base_paths = node.base_paths;
                    cir::EntityId effective_access =
                        access_field.valid() ? access_field : field.entity;
                    if (file_.valid(effective_access) &&
                        file_.entity(effective_access).is_record_member) {
                        declaration.access_owner =
                            file_.entity(effective_access).declaring_record;
                        declaration.declared_access =
                            file_.entity(effective_access)
                                .declared_member_access;
                        declaration.has_declared_access = true;
                    }
                    declaration.member_path = path;
                    declaration.member_path.push_back(field.entity);
                    append_declaration(direct, std::move(declaration));
                    continue;
                }
                if (field.name.valid()) {
                    continue;
                }
                cir::TypeId field_type = file_.resolved_type(field.type.type);
                if (!file_.valid(field_type) ||
                    file_.type(field_type).kind != cir::TypeKind::Record) {
                    continue;
                }
                path.push_back(field.entity);
                cir::EntityId child_access = access_field;
                if (!child_access.valid()) {

                    child_access = field.entity;
                }
                self(self, field_type, path, child_access);
                path.pop_back();
            }
        };
        std::vector<cir::EntityId> anonymous_path;
        search_anonymous(search_anonymous, node.type, anonymous_path,
                         cir::EntityId{});
        if (!direct.declarations.empty()) {
            direct.found = true;
            direct.subobjects.push_back(node_index);
            if (direct.declarations.size() > 1) {
                direct.invalid = true;
            }
        }
        return direct;
    };

    auto lookup = [&](auto&& self, size_t node_index) -> LookupSet {
        LookupSet set = direct_lookup(node_index);
        if (set.found) {
            return set;
        }
        for (size_t base : nodes[node_index].direct_bases) {
            LookupSet candidate = self(self, base);
            if (!candidate.found) {
                continue;
            }
            if (!set.found) {
                set = std::move(candidate);
                continue;
            }

            if (set_is_base_of(candidate, set)) {
                continue;
            }
            if (set_is_base_of(set, candidate)) {
                set = std::move(candidate);
                continue;
            }
            bool same = same_declaration_set(set, candidate);
            append_subobjects(set, candidate);
            for (MemberLookupDeclaration declaration :
                 candidate.declarations) {
                append_declaration(set, std::move(declaration));
            }
            if (!same) {
                set.invalid = true;
            }
        }
        return set;
    };

    LookupSet set = lookup(lookup, 0);
    result.found_name = set.found;
    result.ambiguous = set.invalid;
    result.has_dependent_bases = graph_has_dependent_bases;
    result.declarations = std::move(set.declarations);
    for (size_t subobject : set.subobjects) {
        if (subobject >= nodes.size()) {
            continue;
        }
        result.subobjects.push_back(
            MemberLookupSubobject{nodes[subobject].type,
                                  nodes[subobject].path});
    }
    return result;
}

Session::MemberEntityLookup Session::lookup_member_entities(
    cir::TypeId record_type,
    std::string_view name) const {
    MemberLookupResult lookup = lookup_member_name(record_type, name);
    MemberEntityLookup result;
    result.found_name = lookup.found_name;
    result.ambiguous = lookup.ambiguous;
    result.entities.reserve(lookup.declarations.size());
    for (const MemberLookupDeclaration& declaration : lookup.declarations) {
        if (declaration.entity.valid()) {
            result.entities.push_back(declaration.entity);
        }
    }
    return result;
}

bool Session::record_has_member_name(cir::TypeId record_type,
                                     std::string_view name) const {
    return lookup_member_name(record_type, name).found_name;
}

bool Session::check_member_lookup_access(
    const MemberLookupDeclaration& declaration,
    SrcLoc loc,
    cir::TypeId designating_class) {
    if (!declaration.has_declared_access ||
        template_argument_access_exemption_depth_ != 0) {
        return true;
    }
    if (collecting_pattern_ &&
        exact_class_friend_access_depends_on_current_instantiation(
            declaration.access_owner)) {
        mark_pattern_unusable();
    }
    AccessObligation obligation;
    obligation.kind = AccessObligationKind::Member;
    obligation.member = declaration.entity;
    obligation.access_owner = declaration.access_owner;
    obligation.declared_access = declaration.declared_access;
    obligation.declaring_class = declaration.declaring_class;
    obligation.designating_class = designating_class;
    obligation.loc = loc;
    if (capture_access_obligation(obligation)) {
        return true;
    }
    return evaluate_access_obligation(obligation, current_access_context());
}

bool Session::check_member_lookup_base_access(
    const MemberLookupDeclaration& declaration,
    cir::TypeId derived_type,
    SrcLoc loc) {

    if (declaration.found_through_using) {
        return true;
    }
    if (template_argument_access_exemption_depth_ != 0) {
        return true;
    }
    AccessObligation obligation;
    obligation.kind = AccessObligationKind::MemberLookupBase;
    obligation.declaring_class = declaration.declaring_class;
    obligation.derived_type = derived_type;
    obligation.base_routes = declaration.base_paths;
    obligation.loc = loc;
    if (capture_access_obligation(std::move(obligation))) {
        return true;
    }
    if (declaration.base_paths.empty() ||
        std::any_of(
            declaration.base_paths.begin(), declaration.base_paths.end(),
            [&](const std::vector<MemberLookupBaseStep>& path) {
                return std::all_of(
                    path.begin(), path.end(),
                    [&](const MemberLookupBaseStep& step) {
                        return step.declared_access ==
                                   cir::RecordMemberAccess::Public ||
                            member_access_allowed(step.derived_class,
                                                  step.declared_access);
                    });
            })) {
        return true;
    }
    report_error("cannot name member of inaccessible base class '" +
                     file_.format_type(declaration.declaring_class) +
                     "' through '" + file_.format_type(derived_type) + "'",
                 loc);
    return false;
}

const MemberCandidateObjectPaths*
Session::member_candidate_paths_for_selected(
    const std::vector<MemberCandidateObjectPaths>& candidates,
    cir::EntityId selected) const {
    cir::EntityId lookup_entity = selected;
    if (selected.valid() && file_.valid(selected)) {
        if (const cir::TemplateSpecializationFact* specialization =
                file_.template_specialization(selected);
            specialization && specialization->template_entity.valid()) {
            lookup_entity = specialization->template_entity;
        }
    }
    for (const MemberCandidateObjectPaths& candidate : candidates) {
        if (candidate.entity == lookup_entity ||
            candidate.entity == selected) {
            return &candidate;
        }
    }
    return nullptr;
}

bool Session::check_selected_member_candidate_access(
    const MemberCandidateObjectPaths& candidate,
    cir::EntityId selected,
    SrcLoc loc,
    cir::TypeId designating_class) {
    MemberLookupDeclaration declaration;
    declaration.entity = selected;
    declaration.declaring_class = candidate.declaring_class;
    declaration.access_owner = candidate.access_owner;
    declaration.declared_access = candidate.declared_access;
    declaration.has_declared_access = candidate.has_declared_access;
    declaration.found_through_using = candidate.found_through_using;
    declaration.base_paths = candidate.base_paths;

    cir::TypeId lookup_class = candidate.lookup_class.valid()
        ? candidate.lookup_class
        : designating_class;
    cir::TypeId effective_designating_class = designating_class.valid()
        ? designating_class
        : lookup_class;
    bool member_ok = check_member_lookup_access(
        declaration, loc, effective_designating_class);
    bool base_ok = !lookup_class.valid() ||
        check_member_lookup_base_access(declaration, lookup_class, loc);
    return member_ok && base_ok;
}

std::optional<cir::Binding>
Session::qualified_namespace_direct_binding(
    cir::DeclContextId context,
    std::string_view name) const {
    if (!context.valid() || !file_.valid(context)) {
        return std::nullopt;
    }
    const cir::DeclContext& root = file_.decl_context(context);
    if (root.kind != cir::DeclContextKind::Namespace &&
        root.kind != cir::DeclContextKind::TranslationUnit) {
        return std::nullopt;
    }
    std::optional<cir::Binding> merged;
    std::vector<cir::DeclContextId> pending{context};
    std::unordered_set<uint32_t> visited;
    auto append = [&](const cir::Binding& candidate) {
        if (!merged) {
            merged = candidate;
            merged->context = context;
            return;
        }

        bool same_designated_type =
            merged->type.valid() && candidate.type.valid() &&
            merged->type == candidate.type;
        merged->is_type_name =
            merged->is_type_name && candidate.is_type_name &&
            same_designated_type;
        merged->is_template_name =
            merged->is_template_name && candidate.is_template_name;
        merged->dependent_member_using =
            merged->dependent_member_using ||
            candidate.dependent_member_using;
        merged->is_definition =
            merged->is_definition || candidate.is_definition;
        merged->generation =
            std::max(merged->generation, candidate.generation);
        merged->place = {};

        for (size_t index = 0; index < candidate.entities.size(); ++index) {
            cir::EntityId entity = candidate.entities[index];
            if (std::find(merged->entities.begin(),
                          merged->entities.end(),
                          entity) != merged->entities.end()) {
                continue;
            }
            merged->entities.push_back(entity);
            merged->entity_generations.push_back(
                index < candidate.entity_generations.size()
                    ? candidate.entity_generations[index]
                    : 0);
        }
        if (!merged->is_type_name && !merged->entities.empty()) {
            cir::EntityId last = merged->entities.back();
            if (file_.valid(last)) {
                merged->type = file_.type_ref(file_.entity(last).type);
            }
        } else if (!same_designated_type) {
            merged->type = {};
        }
    };

    while (!pending.empty()) {
        cir::DeclContextId current = pending.back();
        pending.pop_back();
        if (!file_.valid(current) ||
            !visited.insert(current.index).second) {
            continue;
        }
        const cir::DeclContext& declaration = file_.decl_context(current);
        if (const cir::Binding* candidate =
                file_.lookup_direct_ordinary_binding(current, name)) {
            append(*candidate);
        }

        for (cir::DeclContextId child : declaration.children) {
            if (file_.valid(child) &&
                file_.decl_context(child).is_inline_namespace) {
                pending.push_back(child);
            }
        }
    }
    return merged;
}

ExprResult Session::lookup_qualified_name(cir::DeclContextId context,
                                          std::string_view name,
                                          SrcLoc loc) {
    ExprResult error_result;
    error_result.has_error = true;
    error_result.type = builder_.unknown_type();
    error_result.category = ValueCategory::PrValue;
    if (!context.valid()) {

        return error_result;
    }
    std::optional<cir::Binding> namespace_direct =
        qualified_namespace_direct_binding(context, name);
    const cir::Binding* binding = namespace_direct
        ? &*namespace_direct
        : file_.lookup_ordinary_binding(
              context, name, /*include_parents=*/false);
    cir::Binding inherited_binding;
    cir::Binding validating_function_template_binding;
    std::optional<MemberLookupResult> canonical_lookup;
    cir::EntityId qualified_owner = file_.decl_context(context).owner;
    if (qualified_owner.valid() && file_.valid(qualified_owner) &&
        file_.entity(qualified_owner).kind == cir::EntityKind::Record) {
        canonical_lookup =
            lookup_member_name(file_.entity(qualified_owner).type, name);
        if (canonical_lookup->ambiguous) {
            report_error("member '" + std::string(name) +
                             "' is ambiguous through base classes",
                         loc);
            return error_result;
        }
    }
    if (canonical_lookup && canonical_lookup->found_name &&
        !canonical_lookup->declarations.empty()) {
        inherited_binding.name = file_.intern_name(name);
        inherited_binding.context = context;
        inherited_binding.lookup_namespace = cir::LookupNamespace::Ordinary;
        for (const MemberLookupDeclaration& declaration :
             canonical_lookup->declarations) {
            if (declaration.entity.valid() && file_.valid(declaration.entity)) {
                inherited_binding.entities.push_back(declaration.entity);
                inherited_binding.entity_generations.push_back(0);
            }
        }
        if (!inherited_binding.entities.empty()) {
            cir::EntityId last = inherited_binding.entities.back();
            inherited_binding.type = file_.type_ref(file_.entity(last).type);
            inherited_binding.is_type_name = std::all_of(
                canonical_lookup->declarations.begin(),
                canonical_lookup->declarations.end(),
                [](const MemberLookupDeclaration& declaration) {
                    return declaration.designated_type.valid();
                });
            inherited_binding.is_template_name = std::all_of(
                inherited_binding.entities.begin(),
                inherited_binding.entities.end(),
                [&](cir::EntityId entity) {
                    return template_info(entity) != nullptr;
                });
            binding = &inherited_binding;
        }
    } else if (!binding) {

        cir::EntityId active_function{};
        if (validating_template_info_ &&
            !validating_template_info_->is_class_template &&
            !validating_template_info_->is_alias_template &&
            !validating_template_info_->is_variable_template &&
            !validating_template_info_->is_concept &&
            validating_template_info_->name == name &&
            namespace_lookup_reaches_context(
                context,
                validating_template_info_->lexical_context) &&
            current_function_.valid() && file_.valid(current_function_)) {
            active_function = file_.function(current_function_).entity;
        }
        if (active_function.valid() && file_.valid(active_function) &&
            file_.entity(active_function).kind == cir::EntityKind::Function) {
            validating_function_template_binding.name =
                file_.intern_name(name);
            validating_function_template_binding.context = context;
            validating_function_template_binding.lookup_namespace =
                cir::LookupNamespace::Ordinary;
            validating_function_template_binding.entities.push_back(
                active_function);
            validating_function_template_binding.entity_generations.push_back(
                0);
            validating_function_template_binding.type =
                file_.type_ref(file_.entity(active_function).type);
            validating_function_template_binding.is_definition = true;
            validating_function_template_binding.loc =
                file_.entity(active_function).loc;
            binding = &validating_function_template_binding;
        }

        cir::EntityId owner = file_.decl_context(context).owner;
        if (!binding && owner.valid() && file_.valid(owner) &&
            file_.entity(owner).kind == cir::EntityKind::Record) {
            MemberLookupResult member_lookup =
                lookup_member_name(file_.entity(owner).type, name);
            if (member_lookup.ambiguous) {
                report_error("member '" + std::string(name) +
                                 "' is ambiguous through base classes",
                             loc);
                return error_result;
            }
            if (member_lookup.found_name &&
                !member_lookup.declarations.empty()) {
                inherited_binding.name = file_.intern_name(name);
                inherited_binding.context = context;
                inherited_binding.lookup_namespace =
                    cir::LookupNamespace::Ordinary;
                for (const MemberLookupDeclaration& declaration :
                     member_lookup.declarations) {
                    if (declaration.entity.valid() &&
                        file_.valid(declaration.entity)) {
                        inherited_binding.entities.push_back(
                            declaration.entity);
                        inherited_binding.entity_generations.push_back(0);
                    }
                }
                if (!inherited_binding.entities.empty()) {
                    cir::EntityId last = inherited_binding.entities.back();
                    inherited_binding.type =
                        file_.type_ref(file_.entity(last).type);
                    inherited_binding.is_type_name =
                        std::all_of(
                            member_lookup.declarations.begin(),
                            member_lookup.declarations.end(),
                            [](const MemberLookupDeclaration& declaration) {
                                return declaration.designated_type.valid();
                            });
                    inherited_binding.is_template_name =
                        std::all_of(
                            inherited_binding.entities.begin(),
                            inherited_binding.entities.end(),
                            [&](cir::EntityId entity) {
                                return template_info(entity) != nullptr;
                            });
                    binding = &inherited_binding;
                }
            }
        }
        if (!binding) {
            report_error("no member named '" + std::string(name) +
                             "' in the nominated scope",
                         loc);
            return error_result;
        }
    }
    bool defer_overload_access =
        canonical_lookup.has_value() && binding->entities.size() > 1 &&
        std::all_of(
            binding->entities.begin(), binding->entities.end(),
            [&](cir::EntityId candidate) {
                if (!candidate.valid() || !file_.valid(candidate)) {
                    return false;
                }
                if (file_.method_fact(candidate)) {
                    return true;
                }
                const TemplateInfo* info = template_info(candidate);
                return info && !info->is_class_template &&
                    !info->is_alias_template &&
                    !info->is_variable_template && !info->is_concept;
            });
    if (!binding->entities.empty()) {
        cir::EntityId entity = binding->entities.back();
        const MemberLookupDeclaration* selected_declaration = nullptr;
        if (canonical_lookup) {
            for (const MemberLookupDeclaration& declaration :
                 canonical_lookup->declarations) {
                if (declaration.entity == entity) {
                    selected_declaration = &declaration;
                    break;
                }
            }
        }
        if (selected_declaration && !defer_overload_access) {
            (void)check_member_lookup_access(
                *selected_declaration, loc,
                file_.entity(qualified_owner).type);
            (void)check_member_lookup_base_access(
                *selected_declaration,
                file_.entity(qualified_owner).type,
                loc);
        } else if (const cir::RecordStaticDataMemberFact* member =
                       static_data_member_fact(entity)) {
            check_member_access(entity, member->declared_access, loc);
        }
        if (file_.valid(entity) &&
            file_.entity(entity).kind == cir::EntityKind::Field) {
            const cir::RecordFacts* anonymous = file_.record_facts(
                file_.entity(entity).parent);
            if (anonymous &&
                (anonymous->anonymous_union_object_kind ==
                     cir::AnonymousUnionObjectKind::BlockVariable ||
                 anonymous->anonymous_union_object_kind ==
                     cir::AnonymousUnionObjectKind::NamespaceVariable)) {
                ExprResult result =
                    expr_result_for_binding(*binding, name, loc);
                result.qualified_name = true;
                return result;
            }
            ExprResult result;
            result.type = file_.entity(entity).type;
            result.entity = entity;
            result.name = std::string(name);
            result.qualified_name = true;
            result.qualified_member_owner =
                file_.entity(qualified_owner).type;
            result.category = ValueCategory::QualifiedMember;
            return result;
        }
    }
    ExprResult result = expr_result_for_binding(*binding, name, loc);
    result.qualified_name = true;
    result.qualified_member_owner = file_.entity(qualified_owner).type;
    result.member_access_object_type = file_.entity(qualified_owner).type;
    if (defer_overload_access && canonical_lookup) {
        for (const MemberLookupDeclaration& declaration :
             canonical_lookup->declarations) {
            if (!declaration.entity.valid() ||
                !file_.valid(declaration.entity)) {
                continue;
            }
            MemberCandidateObjectPaths candidate;
            candidate.entity = declaration.entity;
            candidate.paths = declaration.object_paths;
            candidate.implicit_object_class =
                declaration.implicit_object_class;
            candidate.found_through_using =
                declaration.found_through_using;
            candidate.access_owner = declaration.access_owner;
            candidate.declaring_class = declaration.declaring_class;
            candidate.lookup_class = file_.entity(qualified_owner).type;
            candidate.declared_access = declaration.declared_access;
            candidate.has_declared_access =
                declaration.has_declared_access;
            candidate.base_paths = declaration.base_paths;
            result.member_candidate_object_paths.push_back(
                std::move(candidate));
        }
    }
    return result;
}

cir::TypeRef Session::lookup_qualified_type_name_ref(
    cir::DeclContextId context,
    std::string_view name) const {
    if (!context.valid()) {
        return {};
    }
    cir::EntityId owner = file_.decl_context(context).owner;
    if (owner.valid() && file_.valid(owner) &&
        file_.entity(owner).kind == cir::EntityKind::Record) {
        MemberLookupResult lookup =
            lookup_member_name(file_.entity(owner).type, name);
        if (lookup.found_name) {
            if (lookup.ambiguous || lookup.declarations.empty()) {
                return {};
            }
            cir::TypeRef designated{};
            for (const MemberLookupDeclaration& declaration :
                 lookup.declarations) {
                if (!declaration.designated_type.valid()) {
                    return {};
                }
                cir::TypeRef candidate = declaration.designated_type;
                candidate.type = file_.resolved_type(candidate.type);
                if (designated.valid() && designated != candidate) {
                    return {};
                }
                designated = candidate;
            }
            return designated;
        }
    }

    std::optional<cir::Binding> namespace_direct =
        qualified_namespace_direct_binding(context, name);
    const cir::Binding* ordinary = namespace_direct
        ? &*namespace_direct
        : file_.lookup_ordinary_binding(
              context, name, /*include_parents=*/false);
    if (ordinary) {
        if (ordinary->is_type_name && ordinary->type.valid()) {
            return ordinary->type;
        }
        return {};
    }
    const cir::Binding* tag = file_.lookup_tag_binding(
        context, name, /*include_parents=*/false);
    if (tag && tag->type.valid()) {
        return tag->type;
    }
    auto canonical_record_lookup = [&]() -> cir::TypeRef {
        if (!owner.valid() || !file_.valid(owner) ||
            file_.entity(owner).kind != cir::EntityKind::Record) {
            return {};
        }
        MemberLookupResult lookup =
            lookup_member_name(file_.entity(owner).type, name);
        if (lookup.ambiguous || !lookup.found_name ||
            lookup.declarations.empty()) {
            return {};
        }
        cir::TypeRef designated{};
        for (const MemberLookupDeclaration& declaration :
             lookup.declarations) {
            if (!declaration.designated_type.valid()) {
                return {};
            }
            cir::TypeRef candidate = declaration.designated_type;
            candidate.type = file_.resolved_type(candidate.type);
            if (designated.valid() && designated != candidate) {
                return {};
            }
            designated = candidate;
        }
        return designated;
    };
    if (owner.valid() && file_.valid(owner)) {
        const cir::RecordFacts* facts = file_.record_facts(owner);
        if (facts && !facts->is_incomplete) {
            return canonical_record_lookup();
        }
    }
    for (ScopeId scope = current_scope_;
         scope != InvalidScopeId && scope < scopes_.size();
         scope = scopes_[scope].parent) {
        if (scopes_[scope].context != context) {
            continue;
        }
        for (const RecordBaseInput& base : scopes_[scope].pending_bases) {
            if (base.is_dependent ||
                (in_template_definition() && is_dependent_type(base.type))) {
                continue;
            }
            cir::TypeId resolved = file_.resolved_type(base.type);
            if (!file_.valid(resolved) ||
                file_.type(resolved).kind != cir::TypeKind::Record) {
                continue;
            }
            cir::EntityId record = file_.record_entity(resolved);
            if (!record.valid() || !file_.valid(record)) {
                continue;
            }
            cir::DeclContextId base_context =
                file_.entity(record).semantic_context;
            cir::TypeRef candidate = base_context.valid()
                ? lookup_qualified_type_name_ref(base_context, name)
                : cir::TypeRef{};
            if (candidate.valid()) {
                return candidate;
            }
        }
        break;
    }
    return canonical_record_lookup();
}

cir::TypeId Session::lookup_qualified_type_name(
    cir::DeclContextId context,
    std::string_view name) const {
    return lookup_qualified_type_name_ref(context, name).type;
}

cir::TypeRef Session::lookup_qualified_type_name_ref_checked(
    cir::DeclContextId context,
    std::string_view name,
    SrcLoc loc,
    cir::EntityId accessing_record,
    std::string_view accessing_function_name) {
    cir::TypeRef type = lookup_qualified_type_name_ref(context, name);
    if (!type.valid() || !context.valid() || !file_.valid(context)) {
        return type;
    }
    if (template_argument_access_exemption_depth_ != 0) {
        return type;
    }
    cir::EntityId owner = file_.decl_context(context).owner;
    if (!owner.valid() || !file_.valid(owner) ||
        file_.entity(owner).kind != cir::EntityKind::Record) {
        return type;
    }

    MemberLookupResult lookup =
        lookup_member_name(file_.entity(owner).type, name);
    if (lookup.ambiguous || !lookup.found_name) {
        return type;
    }
    cir::TypeId resolved = file_.resolved_type(type.type);
    for (const MemberLookupDeclaration& declaration : lookup.declarations) {
        if (!declaration.designated_type.valid() ||
            file_.resolved_type(declaration.designated_type.type) != resolved) {
            continue;
        }
        bool declaration_context_allows = false;
        if (declaration.has_declared_access &&
            accessing_record.valid()) {
            declaration_context_allows = member_access_allowed_from(
                declaration.access_owner,
                declaration.declared_access,
                accessing_record,
                {});
        }
        if (declaration.has_declared_access &&
            !declaration_context_allows &&
            !accessing_function_name.empty()) {
            const cir::RecordFacts* owner_facts =
                file_.record_facts(declaration.access_owner);
            if (owner_facts) {
                declaration_context_allows = std::any_of(
                    owner_facts->function_friends.begin(),
                    owner_facts->function_friends.end(),
                    [&](const cir::RecordFunctionFriendGrant& grant) {
                        return grant.kind ==
                                   cir::RecordFunctionFriendGrantKind::
                                       ExactFunction &&
                            grant.name.valid() &&
                            file_.name(grant.name) ==
                                accessing_function_name;
                    });
            }
        }
        if (!declaration_context_allows) {
            (void)check_member_lookup_access(declaration, loc);
        }
        (void)check_member_lookup_base_access(
            declaration, file_.entity(owner).type, loc);
        break;
    }
    return type;
}

cir::TypeId Session::lookup_qualified_type_name_checked(
    cir::DeclContextId context,
    std::string_view name,
    SrcLoc loc,
    cir::EntityId accessing_record,
    std::string_view accessing_function_name) {
    return lookup_qualified_type_name_ref_checked(
               context,
               name,
               loc,
               accessing_record,
               accessing_function_name)
        .type;
}

void Session::enter_template_argument_access_exemption() {
    ++template_argument_access_exemption_depth_;
}

void Session::leave_template_argument_access_exemption() {
    if (template_argument_access_exemption_depth_ != 0) {
        --template_argument_access_exemption_depth_;
    }
}

cir::TypeRef Session::peek_qualified_type_ref(
    bool global_qualifier,
    const std::vector<std::string_view>& qualifiers,
    std::string_view terminal,
    cir::DeclContextId* terminal_context) const {
    cir::DeclContextId context =
        global_qualifier ? translation_unit_context_ : cir::DeclContextId{};
    for (std::string_view component : qualifiers) {
        const cir::Binding* binding = context.valid()
            ? file_.lookup_namespace_name_binding(context, component,
                                                  /*include_parents=*/false)
            : file_.lookup_namespace_name_binding(current_decl_context(),
                                                  component,
                                                  /*include_parents=*/true);
        if (binding && !binding->entities.empty()) {
            context = file_.entity(binding->entities.back()).semantic_context;
            if (!context.valid()) {
                return {};
            }
            continue;
        }

        cir::TypeId component_type{};
        bool member_record_context = false;
        if (context.valid()) {
            cir::EntityId owner = file_.decl_context(context).owner;
            if (owner.valid() && file_.valid(owner) &&
                file_.entity(owner).kind == cir::EntityKind::Record) {
                member_record_context = true;
                component_type = lookup_qualified_type_name(context,
                                                            component);
            }
        }
        if (member_record_context && !component_type.valid()) {
            return {};
        }
        if (!component_type.valid()) {
            const cir::Binding* type_binding = context.valid()
                ? file_.lookup_type_name_binding(context,
                                                 component,
                                                 /*include_parents=*/false)
                : file_.lookup_type_name_binding(current_decl_context(),
                                                 component,
                                                 /*include_parents=*/true);
            if (!type_binding) {
                type_binding = context.valid()
                    ? file_.lookup_tag_binding(context,
                                               component,
                                               /*include_parents=*/false)
                    : file_.lookup_tag_binding(current_decl_context(),
                                               component,
                                               /*include_parents=*/true);
            }
            if (!type_binding || !type_binding->type.type.valid()) {
                return {};
            }
            component_type = type_binding->type.type;
        }
        cir::TypeId resolved = file_.resolved_type(component_type);
        if (!file_.valid(resolved) ||
            (file_.type(resolved).kind != cir::TypeKind::Record &&
             file_.type(resolved).kind != cir::TypeKind::Enum)) {
            return {};
        }
        cir::EntityId owner = file_.type(resolved).kind == cir::TypeKind::Record
            ? file_.record_entity(resolved)
            : std::get<cir::EnumTypePayload>(file_.type_payload(resolved)).entity;
        if (!owner.valid() || !file_.valid(owner)) {
            return {};
        }
        context = file_.entity(owner).semantic_context;
        if (!context.valid()) {
            return {};
        }
    }
    if (!context.valid()) {
        return {};
    }
    if (terminal_context) {
        *terminal_context = context;
    }
    cir::EntityId terminal_owner = file_.decl_context(context).owner;
    if (terminal_owner.valid() && file_.valid(terminal_owner) &&
        file_.entity(terminal_owner).kind == cir::EntityKind::Record) {
        cir::TypeId member_type = lookup_qualified_type_name(context,
                                                             terminal);
        if (member_type.valid()) {
            return cir::TypeRef{member_type, cir::QualNone,
                            cir::MemorySpace::Default};
        }
        return {};
    }
    const cir::Binding* type_binding = file_.lookup_type_name_binding(
        context, terminal, /*include_parents=*/false);
    if (type_binding && type_binding->type.valid()) {
        return type_binding->type;
    }
    const cir::Binding* tag = file_.lookup_tag_binding(
        context, terminal, /*include_parents=*/false);
    if (tag && tag->type.valid()) {
        return tag->type;
    }
    return {};
}

bool Session::qualified_type_name_denotes_concrete_type(
    cir::DeclContextId context,
    std::string_view name,
    const TemplateInfo* candidate_template) const {
    if (!context.valid() || !file_.valid(context)) {
        return false;
    }
    auto is_concrete_declaration = [&](cir::EntityId entity,
                                       cir::TypeRef designated_type) {
        if (!designated_type.valid() || !entity.valid() ||
            !file_.valid(entity)) {
            return false;
        }
        const TemplateInfo* declaration_info = template_info(entity);
        bool is_candidate_template =
            candidate_template &&
            (declaration_info == candidate_template ||
             entity == candidate_template->entity ||
             entity == candidate_template->pattern_record);
        cir::EntityKind kind = file_.entity(entity).kind;
        return !is_candidate_template &&
            (kind == cir::EntityKind::TypeAlias ||
             kind == cir::EntityKind::Record ||
             kind == cir::EntityKind::Enum);
    };

    cir::EntityId owner = file_.decl_context(context).owner;
    if (owner.valid() && file_.valid(owner) &&
        file_.entity(owner).kind == cir::EntityKind::Record) {
        MemberLookupResult lookup =
            lookup_member_name(file_.entity(owner).type, name);
        if (!lookup.found_name || lookup.ambiguous) {
            return false;
        }
        return std::any_of(
            lookup.declarations.begin(),
            lookup.declarations.end(),
            [&](const MemberLookupDeclaration& declaration) {
                return is_concrete_declaration(
                    declaration.entity,
                    declaration.designated_type);
            });
    }

    std::optional<cir::Binding> namespace_direct =
        qualified_namespace_direct_binding(context, name);
    const cir::Binding* binding = namespace_direct
        ? &*namespace_direct
        : file_.lookup_ordinary_binding(
              context, name, /*include_parents=*/false);
    if (!binding || !binding->is_type_name) {
        return false;
    }
    return std::any_of(
        binding->entities.begin(),
        binding->entities.end(),
        [&](cir::EntityId entity) {
            return is_concrete_declaration(entity, binding->type);
        });
}

ScopeEnterResult Session::enter_existing_context(cir::DeclContextId context,
                                                 ScopeFlags flags) {

    cleanup_scopes_.push_back(CleanupScope{control_stack_.size(), {},
                                           builder_.current_unwind_target()});
    ScopeFrame frame;
    frame.parent = current_scope_;
    frame.flags = flags;
    frame.context = context;
    scopes_.push_back(frame);
    current_scope_ = static_cast<ScopeId>(scopes_.size() - 1);
    return ScopeEnterResult{current_scope_, true};
}

} // namespace aburi::collect
