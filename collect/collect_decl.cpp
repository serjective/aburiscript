#include "collect.h"
#include "collect_template_state.h"

#include "../cir/layout.h"

#include <algorithm>
#include <optional>
#include <unordered_map>
#include <string>
#include <utility>
#include <vector>

namespace aburi::collect {

namespace {

bool compatible_redeclaration_type(Session& session,
                                   cir::TypeId lhs,
                                   cir::TypeId rhs) {

    return session.types_compatible(
        cir::TypeRef{lhs, cir::QualNone, cir::MemorySpace::Default},
        cir::TypeRef{rhs, cir::QualNone, cir::MemorySpace::Default});
}

bool is_incomplete_record_object_type(const cir::File& file,
                                      cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file.record_facts_for_type(resolved);
    return !facts || facts->is_incomplete;
}

bool defer_dependent_pattern_static_initializer(
    const Session& session,
    cir::TypeId type,
    const ExprResult& initializer) {
    return session.collecting_pattern() &&
           (session.is_dependent_type(type) ||
            session.expr_is_value_dependent(initializer));
}

bool global_module_refold_target(const Session& session,
                                 const cir::Binding& previous) {
    const cir::File& file = session.file();
    if (!file.has_module_units() || previous.entities.empty()) {
        return false;
    }
    cir::EntityId prior_id = previous.entities.back();
    if (!file.valid(prior_id)) {
        return false;
    }
    const cir::Entity& prior = file.entity(prior_id);
    return !prior.module_attachment.valid() &&
           prior.origin_unit != file.active_module_context().unit;
}

void diagnose_conflicting_redeclaration(Session& session,
                                        const cir::Binding& previous,
                                        std::string_view name,
                                        cir::TypeId new_type,
                                        SrcLoc loc) {
    if (global_module_refold_target(session, previous)) {
        return;
    }

    if (previous.is_type_name && !previous.entities.empty()) {
        cir::EntityId prior = previous.entities.back();
        const cir::File& file = session.file();
        if (file.valid(prior) &&
            file.entity(prior).kind == cir::EntityKind::Record) {
            return;
        }
    }
    if (previous.is_type_name ||
        !compatible_redeclaration_type(session, previous.type.type, new_type)) {
        session.report_error("conflicting types for '" + std::string(name) + "'", loc);
    }
}

void validate_declaration_qualifiers(Session& session,
                                     cir::File& file,
                                     cir::TypeId type,
                                     uint8_t qualifiers,
                                     SrcLoc loc) {
    cir::TypeId resolved = file.resolved_type(type);
    cir::TypeKind kind = file.valid(resolved) ? file.type(resolved).kind
                                              : cir::TypeKind::Invalid;
    if ((qualifiers & cir::QualRestrict) && kind != cir::TypeKind::Pointer &&
        kind != cir::TypeKind::Array) {
        session.report_error("restrict requires a pointer type", loc);
    }
    if ((qualifiers & cir::QualAtomic) &&
        (kind == cir::TypeKind::Array || kind == cir::TypeKind::Function)) {
        session.report_error("_Atomic cannot be applied to an array or function type",
                             loc);
    }
    if (kind == cir::TypeKind::Array) {
        const auto* array =
            std::get_if<cir::ArrayTypePayload>(&file.type_payload(resolved));
        if (array && (array->element_type.qualifiers & cir::QualAtomic)) {
            session.report_error("_Atomic cannot be applied to an array type", loc);
        }
    }
}

} // namespace

ExprResult Session::clone_initializer_for_probe(
    const ExprResult& initializer) const {
    ExprResult result = initializer;
    if (!initializer.init_list) {
        return result;
    }
    result.init_list = std::make_shared<InitListValue>(*initializer.init_list);
    for (size_t index = 0; index < result.init_list->elements.size(); ++index) {
        result.init_list->elements[index].value =
            clone_initializer_for_probe(
                initializer.init_list->elements[index].value);
    }
    return result;
}

DeclResult Session::declare_global_variable(std::string_view name, cir::TypeId type, SrcLoc loc) {
    return declare_global_variable(name, type, std::nullopt, loc);
}

void merge_entity_attribute_facts(cir::EntityAttributeFacts& into,
                                  const cir::EntityAttributeFacts& from) {
    into.is_weak |= from.is_weak;
    into.is_common |= from.is_common;
    into.is_used |= from.is_used;
    into.is_unused |= from.is_unused;
    into.is_deprecated |= from.is_deprecated;
    into.is_nodiscard |= from.is_nodiscard;
    into.is_warn_unused_result |= from.is_warn_unused_result;
    into.is_noreturn |= from.is_noreturn;
    into.is_gnu_inline |= from.is_gnu_inline;
    into.is_noinline |= from.is_noinline;
    into.is_always_inline |= from.is_always_inline;
    into.is_excluded_from_explicit_instantiation |=
        from.is_excluded_from_explicit_instantiation;
    into.is_cold |= from.is_cold;
    into.is_hot |= from.is_hot;
    into.is_nothrow |= from.is_nothrow;
    into.is_pure |= from.is_pure;
    into.is_const_function |= from.is_const_function;
    into.is_malloc |= from.is_malloc;
    into.returns_nonnull |= from.returns_nonnull;
    into.nonnull_all_pointer_params |= from.nonnull_all_pointer_params;
    into.has_format |= from.has_format;
    if (into.deprecated_message.empty()) {
        into.deprecated_message = from.deprecated_message;
    }
    if (into.section.empty()) {
        into.section = from.section;
    }
    if (into.visibility.empty()) {
        into.visibility = from.visibility;
    }
    if (into.weakref_target.empty()) {
        into.weakref_target = from.weakref_target;
    }
    if (into.nonnull_params.empty()) {
        into.nonnull_params = from.nonnull_params;
    }
    if (into.requested_alignment == 0) {
        into.requested_alignment = from.requested_alignment;
    }
    if (into.constructor_priority < 0) {
        into.constructor_priority = from.constructor_priority;
    }
    if (into.destructor_priority < 0) {
        into.destructor_priority = from.destructor_priority;
    }
}

namespace {

bool corresponding_function_entity(Session& session,
                                   const cir::File& file,
                                   cir::EntityId candidate,
                                   cir::TypeId function_type,
                                   bool is_cxx) {
    return file.valid(candidate) &&
           file.entity(candidate).kind == cir::EntityKind::Function &&
           (!is_cxx ||
            (!session.template_info(candidate) &&
             session.function_signatures_match(
                 file.entity(candidate).type, function_type)));
}

struct PriorFunctionFacts {
    cir::EntityId entity{};
    bool has_internal_linkage = false;
    bool is_extern_c = false;
    bool is_deleted = false;
    cir::EntityAttributeFacts attributes;
};

void apply_implicit_cxx_function_inline(DeclFlags& flags, bool is_cxx) {

    if (is_cxx && (flags.is_constexpr || flags.is_consteval)) {
        flags.is_inline = true;
    }
}

PriorFunctionFacts prior_function_facts(Session& session,
                                         const cir::File& file,
                                         const cir::Binding* previous,
                                         cir::TypeId function_type,
                                         bool is_cxx) {
    if (!previous || previous->entities.empty()) {
        return {};
    }
    for (auto it = previous->entities.rbegin();
         it != previous->entities.rend(); ++it) {
        cir::EntityId prior = *it;
        if (corresponding_function_entity(session,
                                          file,
                                          prior,
                                          function_type,
                                          is_cxx)) {
            const cir::Entity& declaration = file.entity(prior);
            return PriorFunctionFacts{
                prior,
                declaration.linkage == cir::LinkageKind::Internal,
                declaration.is_extern_c,
                declaration.is_deleted,
                declaration.attr_facts};
        }
    }
    return {};
}

std::string inherited_function_asm_label(Session& session,
                                         const cir::File& file,
                                         const DeclFlags& flags,
                                         cir::EntityId prior,
                                         SrcLoc loc) {
    std::string prior_label;
    if (prior.valid() && file.valid(prior)) {
        prior_label = file.entity(prior).attr_facts.asm_label;
    }
    if (!flags.asm_label.empty()) {
        if (!prior_label.empty() && prior_label != flags.asm_label) {
            session.report_error("asm label '" + flags.asm_label +
                                     "' conflicts with earlier asm label '" +
                                     prior_label + "'",
                                 loc);
        }
        return flags.asm_label;
    }
    return prior_label;
}

void unify_weak_across_binding(cir::File& file,
                               const cir::Binding* binding,
                               cir::EntityId definition_entity) {
    auto is_weak_carrier = [&](cir::EntityId id) {
        return file.valid(id) &&
               (file.entity(id).kind == cir::EntityKind::Function ||
                file.entity(id).kind == cir::EntityKind::Variable);
    };
    bool any_weak = file.valid(definition_entity) &&
                    file.entity(definition_entity).attr_facts.is_weak;
    if (binding) {
        for (cir::EntityId id : binding->entities) {
            if (is_weak_carrier(id) && file.entity(id).attr_facts.is_weak) {
                any_weak = true;
                break;
            }
        }
    }
    if (!any_weak) {
        return;
    }
    if (file.valid(definition_entity)) {
        file.entity_mut(definition_entity).attr_facts.is_weak = true;
    }
    if (binding) {
        for (cir::EntityId id : binding->entities) {
            if (is_weak_carrier(id)) {
                file.entity_mut(id).attr_facts.is_weak = true;
            }
        }
    }
}

void unify_function_weak_across_binding(Session& session,
                                        cir::File& file,
                                        const cir::Binding* binding,
                                        cir::EntityId entity,
                                        cir::TypeId function_type,
                                        bool is_cxx) {
    auto corresponds = [&](cir::EntityId candidate) {
        return corresponding_function_entity(session,
                                               file,
                                               candidate,
                                               function_type,
                                               is_cxx);
    };
    bool any_weak = file.valid(entity) &&
                    file.entity(entity).attr_facts.is_weak;
    if (binding) {
        for (cir::EntityId candidate : binding->entities) {
            if (corresponds(candidate) &&
                file.entity(candidate).attr_facts.is_weak) {
                any_weak = true;
                break;
            }
        }
    }
    if (!any_weak) {
        return;
    }
    if (file.valid(entity)) {
        file.entity_mut(entity).attr_facts.is_weak = true;
    }
    if (binding) {
        for (cir::EntityId candidate : binding->entities) {
            if (corresponds(candidate)) {
                file.entity_mut(candidate).attr_facts.is_weak = true;
            }
        }
    }
}

bool binding_contains_entity(const cir::Binding* binding,
                             cir::EntityId entity) {
    return binding && entity.valid() &&
           std::find(binding->entities.begin(),
                     binding->entities.end(),
                     entity) != binding->entities.end();
}

void apply_inline_linkage_rules(Session& session,
                                cir::File& file,
                                cir::EntityId entity,
                                const DeclFlags& flags,
                                const cir::Binding* previous,
                                bool is_cxx) {
    cir::Entity& record = file.entity_mut(entity);
    record.declared_with_extern = flags.is_extern;
    if (is_cxx || !flags.is_inline || flags.is_static) {
        record.inline_definition_only = false;
    } else {
        bool gnu_inline = record.attr_facts.is_gnu_inline;
        record.inline_definition_only =
            gnu_inline ? flags.is_extern : !flags.is_extern;
    }

    bool forces_external =
        !is_cxx && !flags.is_static &&
        (!flags.is_inline ||
         (flags.is_extern && !record.attr_facts.is_gnu_inline));
    bool keeps_inline_only = record.inline_definition_only;

    if (previous) {
        for (cir::EntityId prior : previous->entities) {
            if (!file.valid(prior) ||
                file.entity(prior).kind != cir::EntityKind::Function) {
                continue;
            }
            if (forces_external) {
                file.entity_mut(prior).inline_definition_only = false;
            } else if (keeps_inline_only &&
                       (!file.entity(prior).decl_flags.is_inline ||
                        (file.entity(prior).declared_with_extern &&
                         !file.entity(prior).attr_facts.is_gnu_inline))) {

                record.inline_definition_only = false;
            }
        }
    }
    (void)session;
}

std::string inherited_asm_label(Session& session,
                                const cir::File& file,
                                const DeclFlags& flags,
                                const cir::Binding* previous,
                                SrcLoc loc) {
    std::string prior;
    if (previous) {
        for (auto it = previous->entities.rbegin(); it != previous->entities.rend(); ++it) {
            const std::string& label = file.entity(*it).attr_facts.asm_label;
            if (!label.empty()) {
                prior = label;
                break;
            }
        }
    }
    if (!flags.asm_label.empty()) {
        if (!prior.empty() && prior != flags.asm_label) {
            session.report_error("asm label '" + flags.asm_label +
                                     "' conflicts with earlier asm label '" +
                                     prior + "'",
                                 loc);
        }
        return flags.asm_label;
    }
    return prior;
}

} // namespace

void Session::register_c_language_entity(cir::EntityId entity,
                                         std::string_view name,
                                         bool is_definition,
                                         SrcLoc loc) {
    if (!entity.valid() || !file_.valid(entity)) {
        return;
    }
    cir::Entity& declaration = file_.entity_mut(entity);
    if (!declaration.is_extern_c ||
        declaration.linkage == cir::LinkageKind::Internal) {
        return;
    }

    std::string key(name);
    auto [identity, inserted] = c_language_entities_.emplace(key, entity);
    if (inserted) {
        track_speculative_rollback([this, key, entity] {
            auto found = c_language_entities_.find(key);
            if (found != c_language_entities_.end() && found->second == entity) {
                c_language_entities_.erase(found);
            }
        });
    } else if (identity->second != entity && file_.valid(identity->second)) {
        const cir::Entity& previous = file_.entity(identity->second);
        bool compatible = previous.kind == declaration.kind;
        if (compatible && declaration.kind == cir::EntityKind::Function) {
            compatible = function_signatures_match(previous.type,
                                                   declaration.type) &&
                         compatible_redeclaration_type(*this,
                                                       previous.type,
                                                       declaration.type);
        } else if (compatible && declaration.kind == cir::EntityKind::Variable) {
            compatible = compatible_redeclaration_type(*this,
                                                       previous.type,
                                                       declaration.type) &&
                         previous.qualifiers == declaration.qualifiers;
        }
        if (!compatible) {
            report_error("conflicting C-language declaration of '" + key + "'",
                         loc);
        }
        declaration.linkage_predecessor = identity->second;
    }

    if (!is_definition) {
        return;
    }
    auto [definition, definition_inserted] =
        c_language_definitions_.emplace(key, entity);
    if (definition_inserted) {
        track_speculative_rollback([this, key, entity] {
            auto found = c_language_definitions_.find(key);
            if (found != c_language_definitions_.end() &&
                found->second == entity) {
                c_language_definitions_.erase(found);
            }
        });
    } else {
        report_error("redefinition of C-language entity '" + key + "'", loc);
    }
}

DeclResult Session::declare_global_variable(std::string_view name,
                                            cir::TypeId type,
                                            std::optional<ExprResult> initializer,
                                            SrcLoc loc,
                                            DeclFlags flags,
                                            bool assume_initializer) {
    bool will_have_initializer = initializer.has_value() || assume_initializer;
    validate_declaration_qualifiers(*this, file_, type, flags.type_qualifiers, loc);
    if (flags.is_inline && !lang_opts_.is_cxx_mode()) {

        report_error("'inline' can only appear on functions", loc);
    }
    const cir::Binding* previous_binding = lookup_ordinary_binding(name, false);
    if (previous_binding) {
        diagnose_conflicting_redeclaration(*this, *previous_binding, name, type, loc);
        if (!previous_binding->entities.empty()) {
            const cir::Entity& previous_entity =
                file_.entity(previous_binding->entities.back());
            if (previous_entity.kind == cir::EntityKind::Variable &&
                previous_entity.qualifiers != flags.type_qualifiers) {
                report_error("conflicting type qualifiers for '" + std::string(name) + "'",
                             loc);
            }
            if (previous_entity.kind == cir::EntityKind::Variable) {
                if (previous_entity.decl_flags.is_constexpr != flags.is_constexpr) {
                    report_error("redeclaration of '" + std::string(name) +
                                     "' disagrees about constexpr",
                                 loc);
                }
                if (previous_entity.is_definition &&
                    previous_entity.has_static_initializer &&
                    will_have_initializer) {
                    report_error("redefinition of '" + std::string(name) + "'", loc);
                }
            }
        }
    }

    const bool is_named_register = flags.is_register && !flags.asm_label.empty();
    if (flags.is_register && !is_named_register) {
        report_error("register storage class specifier used at file scope", loc);
    }
    if (is_named_register && will_have_initializer) {
        report_error("global register variable cannot have an initializer", loc);
    }
    if (flags.is_block_byref) {
        report_error("__block storage requires automatic local scope", loc);
    }
    if (variably_modified_type(type)) {
        report_error("variable-length array declaration not allowed at file scope",
                     loc);
    }
    if (flags.is_constexpr && !lang_opts_.is_cxx_mode()) {

        if (flags.is_extern || flags.is_thread_local) {
            report_error("constexpr cannot be combined with extern or thread-local storage",
                         loc);
        }
        if (!will_have_initializer) {
            report_error("constexpr object declaration requires an initializer", loc);
        }
    }
    std::string asm_label = inherited_asm_label(*this, file_, flags, previous_binding, loc);

    bool is_definition =
        !flags.is_declaration_only &&
        !((flags.is_extern || linkage_spec_implies_extern_storage()) &&
          !will_have_initializer);
    bool has_error = false;
    if (is_reference_type(type) && !will_have_initializer && is_definition) {
        report_error("declaration of reference '" + std::string(name) +
                         "' requires an initializer",
                     loc);
        has_error = true;
    }
    bool defer_incomplete_tentative_check = false;
    if (is_definition && !is_reference_type(type) &&
        !require_complete_class_type(type, loc) &&
        is_incomplete_record_object_type(file_, type)) {
        if (will_have_initializer) {

            report_error("variable '" + std::string(name) +
                             "' has incomplete type",
                         loc);
            has_error = true;
        } else {
            defer_incomplete_tentative_check = true;
        }
    }
    cir::StorageDuration storage_duration = flags.is_thread_local
        ? cir::StorageDuration::Thread
        : cir::StorageDuration::Static;
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                                 name,
                                                 type,
                                                 {},
                                                 loc,
                                                 storage_duration,
                                                 cir::MemorySpace::Default,
                                                 flags.to_cir());
    file_.entity_mut(entity).is_definition = is_definition;
    file_.entity_mut(entity).declared_with_extern =
        flags.is_extern || linkage_spec_implies_extern_storage();
    file_.entity_mut(entity).qualifiers = flags.type_qualifiers;
    file_.entity_mut(entity).linkage =
        flags.is_static ? cir::LinkageKind::Internal : cir::LinkageKind::External;
    finalize_variable_initializer_closure_linkage(entity);
    file_.entity_mut(entity).is_extern_c = in_extern_c_linkage();
    if (defer_incomplete_tentative_check) {
        deferred_incomplete_tentative_defs_.push_back({entity, loc});
    }
    if (previous_binding && !previous_binding->entities.empty()) {
        const cir::Entity& previous_entity =
            file_.entity(previous_binding->entities.back());

        if (previous_entity.kind == cir::EntityKind::Variable &&
            previous_entity.is_extern_c) {
            file_.entity_mut(entity).is_extern_c = true;
        }
        if (previous_entity.kind == cir::EntityKind::Variable) {
            file_.entity_mut(entity).linkage_predecessor =
                previous_binding->entities.back();
        }
    }
    register_c_language_entity(entity, name, is_definition, loc);
    apply_attributes(entity, AttributeTarget::Variable, flags.attrs, loc);
    apply_pragma_visibility_default(entity);
    unify_weak_across_binding(file_, previous_binding, entity);
    if (!asm_label.empty()) {
        file_.entity_mut(entity).attr_facts.asm_label = std::move(asm_label);
    }
    if (is_named_register) {
        file_.entity_mut(entity).attr_facts.is_named_register = true;
        file_.entity_mut(entity).is_definition = false;
        is_definition = false;
    }
    if (initializer.has_value()) {
        cir::EntityId active_union_member =
            union_active_member_from_initializer(type, *initializer);
        cir::Entity& declaration = file_.entity_mut(entity);
        declaration.has_initializer = true;
        declaration.initializer_is_value_dependent =
            expr_is_value_dependent(*initializer);
        register_template_value_parameter_equivalence(entity,
                                                      type,
                                                      *initializer);
        bool published_by_engine = false;
        bool diagnosed_constant_error = false;
        if (lang_opts_.is_cxx_mode() &&
            (flags.is_constexpr || flags.is_constinit)) {
            published_by_engine = try_publish_constant_initializer(
                entity, type, *initializer, loc, &diagnosed_constant_error);
        }
        if (diagnosed_constant_error) {
            has_error = true;
        } else if (!published_by_engine) {
            std::vector<cir::StaticInitializerRelocation> relocations;
            std::optional<std::vector<uint8_t>> bytes =
                static_initializer_bytes(type, std::move(*initializer), loc,
                                         &relocations);
            has_error = !bytes.has_value();
            if (bytes.has_value()) {
                cir::Entity& variable = file_.entity_mut(entity);
                variable.has_static_initializer = true;
                variable.static_initializer_bytes = std::move(*bytes);
                variable.static_initializer_relocations =
                    std::move(relocations);
                publish_constant_state_from_static_initializer(
                    entity, active_union_member);
            }
        }
    }

    if (!flags.suppress_name_binding) {
        bind_entity(name,
                    cir::LookupNamespace::Ordinary,
                    entity,
                    type,
                    false,
                    false,
                    is_definition,
                    {},
                    loc);
    }

    DeclResult result;
    result.entity = entity;
    result.type = type;
    result.has_error = has_error;
    return result;
}

bool Session::publish_automatic_constexpr_initializer(
    cir::EntityId entity,
    cir::TypeId type,
    const ExprResult& initializer,
    SrcLoc loc) {
    bool diagnosed_constant_error = false;
    if (try_publish_constant_initializer(
            entity, type, initializer, loc, &diagnosed_constant_error,
            /*require_static_image=*/false)) {
        return true;
    }
    if (diagnosed_constant_error) {
        return false;
    }

    ExprResult initializer_copy =
        clone_initializer_for_probe(initializer);
    cir::EntityId active_union_member =
        union_active_member_from_initializer(type, initializer);
    std::vector<cir::StaticInitializerRelocation> relocations;
    std::optional<std::vector<uint8_t>> constant_bytes =
        static_initializer_bytes(type,
                                 std::move(initializer_copy),
                                 loc,
                                 &relocations);
    if (!constant_bytes.has_value()) {
        return false;
    }

    cir::Entity& record = file_.entity_mut(entity);
    record.has_static_initializer = true;
    record.static_initializer_bytes = std::move(*constant_bytes);
    record.static_initializer_relocations = std::move(relocations);
    publish_constant_state_from_static_initializer(entity,
                                                   active_union_member);
    return true;
}

DeclResult Session::declare_local_variable(std::string_view name,
                                           cir::TypeId type,
                                           std::optional<ExprResult> initializer,
                                           SrcLoc loc,
                                           DeclFlags flags,
                                           bool assume_initializer) {
    if (collecting_pattern_) {

        if (is_dependent_type(type) ||
            (initializer.has_value() &&
             expr_is_value_dependent(*initializer))) {
            bump_pattern_taint();
        }
        if (flags.is_static || flags.is_thread_local || flags.is_block_byref ||
            variably_modified_type(type)) {
            mark_pattern_unusable();
        }
    }
    validate_declaration_qualifiers(*this, file_, type, flags.type_qualifiers, loc);
    if (flags.is_inline && !lang_opts_.is_cxx_mode()) {
        report_error("'inline' can only appear on functions", loc);
    }
    if (flags.is_extern && !flags.is_static && !flags.is_thread_local &&
        !flags.is_block_byref) {
        bool has_error = false;
        if (initializer.has_value() || assume_initializer) {
            report_error("block-scope extern declaration cannot have an initializer", loc);
            has_error = true;
        }

        if (const cir::Binding* previous = lookup_ordinary_binding(name, true)) {
            diagnose_conflicting_redeclaration(*this, *previous, name, type, loc);
            has_error = has_error ||
                previous->is_type_name ||
                !compatible_redeclaration_type(*this, previous->type.type, type);
        }

        cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                                   name,
                                                   type,
                                                   {},
                                                   loc,
                                                   cir::StorageDuration::Static,
                                                   cir::MemorySpace::Default,
                                                   flags.to_cir());
        file_.entity_mut(entity).is_definition = false;
        file_.entity_mut(entity).linkage = cir::LinkageKind::External;
        file_.entity_mut(entity).is_extern_c = in_extern_c_linkage();
        if (const cir::Binding* previous = lookup_ordinary_binding(name, true);
            previous && !previous->entities.empty()) {
            cir::EntityId previous_id = previous->entities.back();
            if (file_.valid(previous_id) &&
                file_.entity(previous_id).kind == cir::EntityKind::Variable) {
                file_.entity_mut(entity).linkage_predecessor = previous_id;
                if (file_.entity(previous_id).is_extern_c) {
                    file_.entity_mut(entity).is_extern_c = true;
                }
            }
        }
        register_c_language_entity(entity, name, false, loc);
        apply_attributes(entity, AttributeTarget::Variable, flags.attrs, loc);
        apply_pragma_visibility_default(entity);

        if (!flags.suppress_name_binding) {
            bind_entity(name,
                        cir::LookupNamespace::Ordinary,
                        entity,
                        type,
                        false,
                        false,
                        false,
                        {},
                        loc);
        }

        DeclResult result;
        result.entity = entity;
        result.type = type;
        result.has_error = has_error;
        return result;
    }

    if (const cir::Binding* previous = lookup_ordinary_binding(name, false)) {
        diagnose_conflicting_redeclaration(*this, *previous, name, type, loc);
    }

    if (!flags.asm_label.empty() && !flags.is_register && !flags.is_static &&
        !flags.is_thread_local) {
        report_error("asm label is not allowed on an automatic local variable",
                     loc);
    }

    if (flags.is_constexpr && !lang_opts_.is_cxx_mode()) {
        if (!initializer.has_value() && !assume_initializer) {
            report_error("constexpr object declaration requires an initializer", loc);
        }
        if (flags.is_auto_storage) {
            report_error("constexpr cannot be combined with 'auto' storage class", loc);
        }
        if (flags.is_thread_local) {
            report_error("constexpr cannot be combined with thread-local storage", loc);
        }
    }
    if (flags.is_constinit && !flags.is_static &&
        !flags.is_thread_local && !flags.is_extern) {
        report_error("constinit can only be applied to a variable with static or thread storage duration",
                     loc);
    }

    if (variably_modified_type(type) && !flags.is_static &&
        !flags.is_thread_local && !flags.is_block_byref) {
        bool has_error = false;
        if (initializer.has_value()) {
            report_error("variable-length array may not be initialized", loc);
            has_error = true;
        }
        cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                                   name,
                                                   type,
                                                   {},
                                                   loc,
                                                   cir::StorageDuration::Automatic,
                                                   cir::MemorySpace::Default,
                                                   flags.to_cir());
        file_.entity_mut(entity).is_definition = true;
        file_.entity_mut(entity).qualifiers = flags.type_qualifiers;
        apply_attributes(entity, AttributeTarget::Variable, flags.attrs, loc);

        ensure_vla_stack_slot(loc);

        ExprResult byte_size = collect_sizeof_type(type, loc);
        cir::Fragment fragment = chain(std::move(flags.vla_bounds),
                                       std::move(byte_size.fragment),
                                       loc);

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("vla.alloc");
        cir::InstId place = builder_.stack_alloc(file_.type_ref(type),
                                                 byte_size.value,
                                                 entity,
                                                 loc);
        cir::Fragment alloc_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(alloc_fragment), loc);

        if (!flags.suppress_name_binding) {
            bind_entity(name,
                        cir::LookupNamespace::Ordinary,
                        entity,
                        type,
                        false,
                        false,
                        true,
                        place,
                        loc);
        }

        DeclResult result;
        result.fragment = std::move(fragment);
        result.entity = entity;
        result.type = type;
        result.place = place;
        result.has_error = has_error || byte_size.has_error;
        return result;
    }

    if ((flags.is_static || flags.is_thread_local) && !flags.is_block_byref) {
        std::string symbol(name);
        cir::EntityId enclosing_function{};
        if (current_function_.valid()) {
            const cir::Function& function = file_.function(current_function_);
            if (function.entity.valid() &&
                file_.entity(function.entity).name.valid()) {
                enclosing_function = function.entity;
                symbol = file_.name(file_.entity(function.entity).name) + "." + symbol;
            }
        }
        symbol += "." + std::to_string(++local_static_counter_);

        cir::NameId local_source_name{};
        uint32_t local_name_ordinal = 0;
        if (enclosing_function.valid()) {
            local_source_name = file_.intern_name(name);
            for (cir::EntityId prior_id : file_.entity_ids()) {
                const cir::Entity& prior = file_.entity(prior_id);
                if (prior.local_enclosing_function == enclosing_function &&
                    prior.local_source_name == local_source_name) {
                    ++local_name_ordinal;
                }
            }
        }

        cir::StorageDuration duration = flags.is_thread_local
            ? cir::StorageDuration::Thread
            : cir::StorageDuration::Static;
        cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                                   symbol,
                                                   type,
                                                   {},
                                                   loc,
                                                   duration,
                                                   cir::MemorySpace::Default,
                                                   flags.to_cir());
        file_.entity_mut(entity).is_definition = true;
        file_.entity_mut(entity).linkage = cir::LinkageKind::Internal;
        file_.entity_mut(entity).qualifiers = flags.type_qualifiers;
        if (enclosing_function.valid()) {
            file_.entity_mut(entity).local_source_name = local_source_name;
            file_.entity_mut(entity).local_enclosing_function = enclosing_function;
            file_.entity_mut(entity).local_name_ordinal = local_name_ordinal;
        }
        apply_attributes(entity, AttributeTarget::Variable, flags.attrs, loc);
        if (!flags.asm_label.empty()) {
            file_.entity_mut(entity).attr_facts.asm_label = flags.asm_label;
        }

        bool has_error = false;
        if (!require_complete_class_type(type, loc) &&
            is_incomplete_record_object_type(file_, type)) {
            report_error("variable '" + std::string(name) +
                             "' has incomplete type",
                         loc);
            has_error = true;
        }
        if (initializer.has_value()) {
            cir::EntityId active_union_member =
                union_active_member_from_initializer(type, *initializer);
            cir::Entity& declaration = file_.entity_mut(entity);
            declaration.has_initializer = true;
            declaration.initializer_is_value_dependent =
                expr_is_value_dependent(*initializer);
            register_template_value_parameter_equivalence(entity,
                                                          type,
                                                          *initializer);
            bool defer_dependent_pattern_initializer =
                defer_dependent_pattern_static_initializer(
                    *this, type, *initializer);
            if (!defer_dependent_pattern_initializer) {
                std::vector<cir::StaticInitializerRelocation> relocations;
                std::optional<std::vector<uint8_t>> bytes =
                    static_initializer_bytes(type,
                                             std::move(*initializer),
                                             loc,
                                             &relocations);
                has_error = !bytes.has_value();
                if (bytes.has_value()) {
                    cir::Entity& variable = file_.entity_mut(entity);
                    variable.has_static_initializer = true;
                    variable.static_initializer_bytes = std::move(*bytes);
                    variable.static_initializer_relocations =
                        std::move(relocations);
                    publish_constant_state_from_static_initializer(
                        entity, active_union_member);
                }
            }
        }

        if (!flags.suppress_name_binding) {
            bind_entity(name,
                        cir::LookupNamespace::Ordinary,
                        entity,
                        type,
                        false,
                        false,
                        true,
                        {},
                        loc);
        }

        DeclResult result;
        result.entity = entity;
        result.type = type;
        result.has_error = has_error;
        return result;
    }

    if (flags.is_block_byref) {
        return declare_block_byref_variable(name, type, std::move(initializer),
                                            loc, flags);
    }

    bool has_error = false;
    if (!is_reference_type(type) &&
        !is_dependent_type(type) &&
        !require_complete_class_type(type, loc) &&
        is_incomplete_record_object_type(file_, type)) {
        report_error("variable '" + std::string(name) +
                         "' has incomplete type",
                     loc);
        has_error = true;
    }

    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                                 name,
                                                 type,
                                                 {},
                                                 loc,
                                                 cir::StorageDuration::Automatic,
                                                 cir::MemorySpace::Default,
                                                 flags.to_cir());
    file_.entity_mut(entity).is_definition = true;
    file_.entity_mut(entity).is_block_byref = flags.is_block_byref;
    file_.entity_mut(entity).qualifiers = flags.type_qualifiers;
    apply_attributes(entity, AttributeTarget::Variable, flags.attrs, loc);
    if (!flags.asm_label.empty()) {
        file_.entity_mut(entity).attr_facts.asm_label = flags.asm_label;

        if (flags.is_register) {
            file_.entity_mut(entity).attr_facts.is_named_register = true;
        }
    }
    register_cleanup_attr(entity, type, flags.attrs, loc);
    if (initializer.has_value()) {
        cir::Entity& declaration = file_.entity_mut(entity);
        declaration.has_initializer = true;
        declaration.initializer_is_value_dependent =
            expr_is_value_dependent(*initializer);
        register_template_value_parameter_equivalence(entity,
                                                      type,
                                                      *initializer);
    }

    if (flags.is_constexpr && initializer.has_value() &&
        !expr_is_value_dependent(*initializer)) {
        if (flags.suppress_name_binding) {
            (void)try_publish_constant_initializer(
                entity, type, *initializer, loc, nullptr,
                /*require_static_image=*/false);
        } else if (!publish_automatic_constexpr_initializer(
                       entity, type, *initializer, loc) &&
                   lang_opts_.is_cxx_mode()) {
            report_error("constexpr variable must be initialized by a constant expression",
                         loc);
            has_error = true;
        }
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId place_block = begin_fragment_block("local.place");
    cir::InstId place = builder_.local_place(entity, type, loc);
    note_local_lifetime_start(entity, type, place, flags, loc);
    cir::Fragment fragment = chain(std::move(flags.vla_bounds),
                                   finish_fragment_block(place_block, previous),
                                   loc);

    if (!flags.suppress_name_binding) {
        bind_entity(name,
                    cir::LookupNamespace::Ordinary,
                    entity,
                    type,
                    false,
                    false,
                    true,
                    place,
                    loc);
    }
    if (collecting_pattern_ && current_function_.valid()) {
        pattern_events_.push_back(PatternScopeEvent{
            PatternScopeEvent::Kind::DeclareLocal, entity, place});
    }

    bool is_reference = is_reference_type(type);
    if (is_reference && !initializer.has_value() && !assume_initializer &&
        !flags.is_extern) {
        report_error("declaration of reference '" + std::string(name) +
                         "' requires an initializer",
                     loc);
        has_error = true;
    }
    if (lang_opts_.is_cxx_mode() && is_reference &&
        initializer.has_value() &&
        initializer->category == ValueCategory::InitList) {
        cir::TypeRef referred = file_.reference_referred_ref(
            file_.resolved_type(type));
        if (initializer_list_element_type(referred.type).has_value()) {
            *initializer = materialize_list_initialization(
                std::move(*initializer),
                referred.type,
                UseContext::Init,
                loc);
        }
    }
    if (initializer.has_value()) {
        if (lang_opts_.is_cxx_mode() &&
            (file_.entity(entity).qualifiers & cir::QualConst) != 0 &&
            (file_.entity(entity).qualifiers & cir::QualVolatile) == 0 &&
            is_integer_type(type)) {
            if (!initializer->value.valid() && initializer->place.valid()) {
                *initializer = require_value(std::move(*initializer),
                                             UseContext::RValue, loc);
            }
            cir::IntegerValue constant_value;
            if (!initializer->has_error &&
                try_evaluate_integer_constant_value(*initializer,
                                                    constant_value)) {
                cir::Entity& constant = file_.entity_mut(entity);
                constant.has_constant_value = true;
                constant.constant_value_kind =
                    file_.template_value_kind_for_type(type);
                if (constant.constant_value_kind ==
                    cir::TemplateValueKind::Boolean) {
                    constant.constant_integer_value =
                        cir::IntegerValue::from_unsigned(
                            constant_value.is_zero() ? 0 : 1, 1);
                } else {
                    cir::IntegerTypeShape shape =
                        cir::integer_shape_for_type(file_, type);
                    constant.constant_integer_value =
                        constant_value.cast(shape.bit_width,
                                            shape.is_unsigned);
                }
            }
        }
        bool initializes_std_initializer_list =
            initializer->category == ValueCategory::InitList &&
            initializer_list_element_type(type).has_value();
        if (in_template_definition() && is_dependent_type(type)) {

            has_error = initializer->has_error;
            fragment = chain(std::move(fragment),
                             std::move(initializer->fragment), loc);
            bump_pattern_taint();
        } else if (!is_reference && initializes_std_initializer_list) {
            ExprResult value = materialize_list_initialization(
                std::move(*initializer), type, UseContext::Init, loc);
            has_error = value.has_error;
            fragment = chain(std::move(fragment),
                             std::move(value.fragment), loc);
            if (!value.has_error && value.value.valid()) {
                previous = builder_.current_block();
                cir::BlockId store_block =
                    begin_fragment_block("local.initializer_list.init");
                builder_.store(place, value.value, loc);
                fragment = chain(
                    std::move(fragment),
                    finish_fragment_block(store_block, previous), loc);
            }
            for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
                transfer_lifetime(lifetime, LifetimeOwnerKind::LexicalScope,
                                  entity.index);
            }
        } else if (!is_reference &&
                   (initializer->category == ValueCategory::InitList ||
                    is_aggregate_type(type))) {
            bool init_had_error = initializer->has_error;
            cir::Fragment init_fragment =
                emit_initializer_for_place(place, type, std::move(*initializer), loc);
            has_error = init_had_error;
            fragment = chain(std::move(fragment), std::move(init_fragment), loc);
        } else {
            ExprResult value = convert_to(std::move(*initializer), type, UseContext::Init, loc);
            bool adopted_prvalue = false;
            if (!is_reference && value.category == ValueCategory::PrValue &&
                value.type.valid() && type_equal(value.type, type)) {
                cir::TypeId resolved = file_.resolved_type(type);
                if (file_.valid(resolved) &&
                    file_.type(resolved).kind == cir::TypeKind::Record) {
                    adopted_prvalue = adopt_materialized_object_storage(
                        value, place, entity);
                    if (adopted_prvalue) {
                        for (cir::LifetimeId lifetime :
                             value.materialized_lifetimes) {
                            retire_lifetime(lifetime);
                        }
                    }
                }
            }
            has_error = value.has_error;
            fragment = chain(std::move(fragment), std::move(value.fragment), loc);
            if (!value.has_error && value.value.valid() &&
                !expr_is_value_dependent(value) &&
                !is_dependent_type(type)) {
                previous = builder_.current_block();
                cir::BlockId store_block = begin_fragment_block("local.init");
                cir::InstId store = builder_.store(place, value.value, loc);
                if (adopted_prvalue) {
                    file_.inst_mut(store).runtime_elided_object_operation = true;
                }
                cir::Fragment store_fragment = finish_fragment_block(store_block, previous);
                fragment = chain(std::move(fragment), std::move(store_fragment), loc);
            }
        }
    } else if (lang_opts_.trivial_auto_var_init_zero && !is_reference &&
               !flags.is_extern && !flags.is_static && !flags.is_thread_local &&
               !flags.is_block_byref && !assume_initializer &&
               !is_dependent_type(type) && !variably_modified_type(type)) {

        cir::Fragment zero_fragment = emit_zero_initializer(place, type, loc);
        fragment = chain(std::move(fragment), std::move(zero_fragment), loc);
    }

    DeclResult result;
    result.fragment = std::move(fragment);
    result.entity = entity;
    result.type = type;
    result.place = place;
    result.has_error = has_error;
    return result;
}

void Session::check_deferred_incomplete_tentative_defs() {

    for (const DeferredIncompleteTentativeDef& deferred :
         deferred_incomplete_tentative_defs_) {
        if (!file_.valid(deferred.entity)) {
            continue;
        }
        const cir::Entity& entity = file_.entity(deferred.entity);
        if (is_incomplete_record_object_type(file_, entity.type)) {
            report_error("variable '" +
                             std::string(file_.name(entity.name)) +
                             "' has incomplete type",
                         deferred.loc);
        }
    }
    deferred_incomplete_tentative_defs_.clear();
}

DeclResult Session::finish_variable_declaration(DeclResult started,
                                                cir::TypeId completed_type,
                                                std::optional<ExprResult> initializer,
                                                SrcLoc loc,
                                                DeclFlags flags,
                                                std::string_view binding_name,
                                                ConstructorInitializationKind init_kind) {
    if (!started.entity.valid()) {
        return started;
    }
    finalize_variable_initializer_closure_linkage(started.entity);
    if (completed_type.valid() && started.type.valid() &&
        completed_type != started.type) {
        started.type = completed_type;
        file_.entity_mut(started.entity).type = completed_type;
        const cir::Entity& entity = file_.entity(started.entity);
        if (entity.parent.valid()) {
            if (const cir::RecordFacts* facts =
                    file_.record_facts(entity.parent)) {
                cir::RecordFacts updated = *facts;
                for (cir::RecordStaticDataMemberFact& member :
                     updated.static_data_members) {
                    if (member.entity == started.entity) {
                        member.type = file_.type_ref(
                            completed_type,
                            entity.qualifiers,
                            entity.memory_space);
                    }
                }
                file_.set_record_facts(entity.parent, std::move(updated));
            }
        }
        std::string_view lookup_name =
            !binding_name.empty()
                ? binding_name
                : (entity.name.valid() ? file_.name(entity.name)
                                       : std::string_view{});
        if (!lookup_name.empty()) {
            if (cir::Binding* binding = file_.mutable_ordinary_binding(
                    current_decl_context(), lookup_name)) {
                binding->type = file_.type_ref(completed_type);
            }
        }
        file_.retype_entity_places(started.entity);
    }
    const cir::Entity& entity = file_.entity(started.entity);
    cir::StorageDuration storage_duration = entity.storage_duration;
    if (lang_opts_.is_cxx_mode() && entity.is_definition &&
        !is_reference_type(started.type) &&
        !validate_consteval_only_object_definition(
            started.entity, started.type, flags.is_constexpr, loc)) {
        started.has_error = true;
        return started;
    }
    if (lang_opts_.is_cxx_mode() && entity.is_definition &&
        !is_reference_type(started.type) &&
        diagnose_abstract_instantiation(started.type, loc)) {
        started.has_error = true;
        return started;
    }
    if (lang_opts_.is_cxx_mode() && entity.is_definition &&
        (storage_duration == cir::StorageDuration::Static ||
         storage_duration == cir::StorageDuration::Thread) &&
        !is_reference_type(started.type) &&
        !validate_potentially_invoked_destructor(started.type, loc)) {
        started.has_error = true;
    }
    if (!initializer.has_value()) {
        if (lang_opts_.is_cxx_mode()) {
            started = default_construct_if_needed(std::move(started), loc);
        }
        arc_finish_local_declaration(started, /*zero_initialize=*/true, loc);
        return started;
    }

    cir::TypeId type = started.type;
    {
        cir::Entity& declaration = file_.entity_mut(started.entity);
        declaration.has_initializer = true;
        declaration.initializer_is_value_dependent =
            expr_is_value_dependent(*initializer);
    }
    register_template_value_parameter_equivalence(started.entity,
                                                  type,
                                                  *initializer);
    if (collecting_pattern_ &&
        (entity.owning_function.valid() ||
         entity.local_enclosing_function.valid()) &&
        (is_dependent_type(type) ||
         expr_is_value_dependent(*initializer))) {
        bump_pattern_taint();
        started.has_error = started.has_error || initializer->has_error;
        return started;
    }

    if (std::optional<ExprResult> enum_value =
            try_materialize_fixed_enum_direct_list(
                *initializer,
                type,
                init_kind == ConstructorInitializationKind::Direct
                    ? UseContext::DirectInit
                    : UseContext::Init,
                loc)) {
        *initializer = std::move(*enum_value);
        started.has_error = started.has_error || initializer->has_error;
    }
    if (lang_opts_.is_cxx_mode() &&
        (file_.entity(started.entity).qualifiers & cir::QualConst) != 0 &&
        (file_.entity(started.entity).qualifiers & cir::QualVolatile) == 0 &&
        is_integer_type(type)) {
        if (!initializer->value.valid() && initializer->place.valid()) {
            *initializer = require_value(std::move(*initializer),
                                         UseContext::RValue, loc);
        }
        cir::IntegerValue constant_value;
        if (!initializer->has_error &&
            try_evaluate_integer_constant_value(*initializer,
                                                constant_value)) {
            cir::Entity& constant = file_.entity_mut(started.entity);
            constant.has_constant_value = true;
            constant.constant_value_kind =
                file_.template_value_kind_for_type(type);
            if (constant.constant_value_kind ==
                cir::TemplateValueKind::Boolean) {
                constant.constant_integer_value =
                    cir::IntegerValue::from_unsigned(
                        constant_value.is_zero() ? 0 : 1, 1);
            } else {
                cir::IntegerTypeShape shape =
                    cir::integer_shape_for_type(file_, type);
                constant.constant_integer_value =
                    constant_value.cast(shape.bit_width,
                                        shape.is_unsigned);
            }
        }
    }

    if (lang_opts_.is_cxx_mode() && is_reference_type(type) &&
        initializer->category == ValueCategory::InitList) {
        cir::TypeRef referred = file_.reference_referred_ref(
            file_.resolved_type(type));
        if (initializer_list_element_type(referred.type).has_value()) {
            *initializer = materialize_list_initialization(
                std::move(*initializer),
                referred.type,
                UseContext::Init,
                loc,
                storage_duration);
        }
    }
    if (lang_opts_.is_cxx_mode() && is_reference_type(type) &&
        (storage_duration == cir::StorageDuration::Static ||
         storage_duration == cir::StorageDuration::Thread) &&
        !flags.is_constexpr && !flags.is_constinit) {
        cir::TypeRef referred = file_.reference_referred_ref(
            file_.resolved_type(type));
        cir::TypeId source_type =
            file_.resolved_type(initializer->type);
        bool source_is_record =
            file_.valid(source_type) &&
            file_.type(source_type).kind == cir::TypeKind::Record;
        bool direct_prvalue_temporary =
            initializer->category == ValueCategory::PrValue &&
            (!source_is_record ||
             file_.resolved_type(referred.type) == source_type);
        bool extends_temporary =
            direct_prvalue_temporary ||
            initializer->category == ValueCategory::InitList;
        if (!extends_temporary) {
            begin_speculative_parse();
            ExprResult probe = convert_to(*initializer, type,
                                          UseContext::Init, loc);
            extends_temporary =
                !probe.has_error && probe.reference_binds_to_temporary;
            rollback_speculative_parse();
        }

        if (extends_temporary) {
            std::string backing_name =
                ".ref.extended." +
                std::to_string(compound_literal_counter_++);
            cir::EntityId backing_entity = builder_.add_entity(
                cir::EntityKind::Variable, backing_name, referred.type, {},
                loc, storage_duration, referred.memory_space, {});
            cir::Entity& backing_record = file_.entity_mut(backing_entity);
            backing_record.is_definition = true;
            backing_record.has_initializer = true;
            backing_record.linkage = cir::LinkageKind::Internal;
            backing_record.qualifiers = referred.qualifiers;
            backing_record.semantic_context =
                file_.entity(started.entity).semantic_context;

            DeclResult backing;
            backing.entity = backing_entity;
            backing.type = referred.type;
            if (storage_duration == cir::StorageDuration::Thread) {
                backing = construct_thread_variable(
                    std::move(backing), {}, loc, init_kind,
                    /*value_initialize=*/false, std::move(*initializer));
            } else if (is_namespace_scope_static_entity(started.entity)) {
                backing = construct_global_variable(
                    std::move(backing), {}, loc, init_kind,
                    /*value_initialize=*/false, std::move(*initializer));
            } else {
                backing = construct_local_static(
                    std::move(backing), {}, loc, init_kind,
                    /*value_initialize=*/false, std::move(*initializer));
            }
            started.has_error = started.has_error || backing.has_error;
            started.fragment = chain(std::move(started.fragment),
                                     std::move(backing.fragment), loc);

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("expr.ref.extended.place");
            cir::InstId place = builder_.global_place(backing_entity, loc);
            ExprResult stable;
            stable.fragment = finish_fragment_block(block, previous);
            stable.place = place;
            stable.entity = backing_entity;
            stable.type = referred.type;
            stable.category = ValueCategory::LValue;
            if (storage_duration == cir::StorageDuration::Static) {
                std::optional<size_t> reference_size = size_of_type(type, loc);
                if (!reference_size.has_value()) {
                    started.has_error = true;
                    return started;
                }
                cir::Entity& reference_record =
                    file_.entity_mut(started.entity);
                reference_record.has_static_initializer = true;
                reference_record.static_initializer_bytes.assign(
                    *reference_size, 0);
                reference_record.static_initializer_relocations = {
                    cir::StaticInitializerRelocation{0, backing_entity, 0}};
                return started;
            }
            initializer = std::move(stable);
        }
    }

    cir::TypeId type_resolved = file_.resolved_type(type);
    const cir::RecordFacts* initialization_record =
        file_.record_facts_for_type(type_resolved);
    const bool initializes_std_initializer_list =
        initializer_list_element_type(type_resolved).has_value();

    if (initializes_std_initializer_list &&
        storage_duration == cir::StorageDuration::Static &&
        initializer->category == ValueCategory::InitList &&
        initializer->init_list) {
        std::optional<cir::TypeRef> element =
            initializer_list_element_type(type_resolved);
        const cir::RecordFacts* list_facts =
            file_.record_facts_for_type(type_resolved);
        std::vector<cir::RecordFieldFact> fields;
        if (list_facts) {
            for (const cir::RecordFieldFact& field : list_facts->fields) {
                if (!field.is_base_subobject &&
                    !field.is_virtual_base_storage) {
                    fields.push_back(field);
                }
            }
        }
        bool representation_ok = element.has_value() && fields.size() == 2 &&
            is_pointer_type(fields[0].type.type) &&
            is_integer_type(fields[1].type.type);
        if (!representation_ok) {
            report_error(
                "std::initializer_list specialization has an unsupported "
                "object representation",
                loc);
            started.has_error = true;
            return started;
        }

        size_t count = initializer->init_list->elements.size();
        cir::TypeRef const_element = *element;
        const_element.qualifiers |= cir::QualConst;
        cir::TypeId backing_type = file_.array_type(
            const_element, cir::ArraySizeKind::Constant, count);
        begin_speculative_parse();
        cir::EntityId backing = builder_.add_entity(
            cir::EntityKind::Variable,
            ".initializer_list.static.backing." +
                std::to_string(compound_literal_counter_++),
            backing_type, {}, loc, cir::StorageDuration::Static,
            cir::MemorySpace::Default, {});
        cir::Entity& backing_entity = file_.entity_mut(backing);
        backing_entity.is_definition = true;
        backing_entity.qualifiers = cir::QualConst;
        backing_entity.linkage = cir::LinkageKind::Internal;
        backing_entity.lexical_context = current_decl_context();
        backing_entity.semantic_context = current_decl_context();

        std::vector<cir::StaticInitializerRelocation> backing_relocations;
        std::optional<std::vector<uint8_t>> backing_bytes =
            static_initializer_bytes(
                backing_type,
                clone_initializer_for_probe(*initializer), loc,
                &backing_relocations);
        std::optional<size_t> object_size = size_of_type(type, loc);
        std::optional<size_t> size_field_size =
            size_of_type(fields[1].type.type, loc);
        if (!backing_bytes.has_value() || !object_size.has_value() ||
            !size_field_size.has_value() || *size_field_size > 8 ||
            fields[1].offset + *size_field_size > *object_size) {
            rollback_speculative_parse();
        } else {
            backing_entity.has_static_initializer = true;
            backing_entity.static_initializer_bytes =
                std::move(*backing_bytes);
            backing_entity.static_initializer_relocations =
                std::move(backing_relocations);

            cir::Entity& object = file_.entity_mut(started.entity);
            object.has_static_initializer = true;
            object.static_initializer_bytes.assign(*object_size, 0);
            if (count != 0) {
                object.static_initializer_relocations.push_back(
                    cir::StaticInitializerRelocation{
                        fields[0].offset, backing, 0});
            }
            uint64_t encoded_count = static_cast<uint64_t>(count);
            for (size_t byte = 0; byte < *size_field_size; ++byte) {
                size_t destination = file_.target_info().endianness ==
                        EndiannessKind::Little
                    ? fields[1].offset + byte
                    : fields[1].offset + (*size_field_size - byte - 1);
                object.static_initializer_bytes[destination] =
                    static_cast<uint8_t>(
                        (encoded_count >> (byte * 8)) & 0xffu);
            }
            commit_speculative_parse();
            return started;
        }
    }
    bool same_type_class_initializer =
        initialization_record && initializer->type.valid() &&
        file_.resolved_type(initializer->type) == type_resolved;
    bool derived_type_class_initializer = false;
    if (initialization_record && initializer->type.valid()) {
        cir::TypeId source_type = file_.resolved_type(initializer->type);
        derived_type_class_initializer = file_.valid(source_type) &&
            file_.type(source_type).kind == cir::TypeKind::Record &&
            analyze_derived_to_base_path(source_type, type_resolved).kind !=
                DerivedToBasePathKind::NotFound;
    }
    bool copy_or_move_class_initializer =
        same_type_class_initializer || derived_type_class_initializer;
    bool empty_class_list_value_initialization =
        initialization_record &&
        initializer->category == ValueCategory::InitList &&
        initializer->init_list &&
        initializer->init_list->elements.empty() &&
        !is_aggregate_type(type_resolved);
    if (lang_opts_.is_cxx_mode() && !is_reference_type(type) &&
        initializer->category == ValueCategory::InitList &&
        initializer->init_list &&
        !initializes_std_initializer_list &&
        (record_has_user_constructor(type) ||
         (empty_class_list_value_initialization &&
          record_requires_default_constructor_selection(type)))) {
        std::vector<ExprResult> arguments;
        arguments.push_back(std::move(*initializer));
        return construct_variable(std::move(started),
                                  std::move(arguments),
                                  loc,
                                  init_kind,
                                  empty_class_list_value_initialization);
    }
    if (lang_opts_.is_cxx_mode() && !is_reference_type(type) &&
        initializer->category != ValueCategory::InitList &&
        (record_has_user_constructor(type) || copy_or_move_class_initializer)) {
        bool elide_prvalue = same_type_class_initializer &&
                             initializer->category == ValueCategory::PrValue;
        if (elide_prvalue) {
            if (!initializer->materialized_lifetimes.empty()) {
                for (cir::LifetimeId lifetime :
                     initializer->materialized_lifetimes) {
                    retire_lifetime(lifetime);
                }
            } else {
                remove_destructor_cleanup(
                    temporary_entity_of_value(initializer->value));
            }
        } else {
            std::vector<ExprResult> arguments;
            arguments.push_back(std::move(*initializer));
            return construct_variable(std::move(started),
                                      std::move(arguments), loc, init_kind);
        }
    }

    if (storage_duration == cir::StorageDuration::Static ||
        storage_duration == cir::StorageDuration::Thread) {
        if (defer_dependent_pattern_static_initializer(
                *this, type, *initializer)) {
            return started;
        }
        if (lang_opts_.is_cxx_mode() &&
            storage_duration == cir::StorageDuration::Thread &&
            !flags.is_constexpr && !flags.is_constinit) {
            ExprResult constant_candidate =
                clone_initializer_for_probe(*initializer);
            std::vector<cir::StaticInitializerRelocation> relocations;
            begin_speculative_parse();
            std::optional<std::vector<uint8_t>> bytes =
                static_initializer_bytes(type,
                                         std::move(constant_candidate),
                                         loc,
                                         &relocations);
            bool needs_thread_cleanup =
                record_destructor(type).valid() ||
                array_class_element_leaf(type).valid();
            bool references_thread_object =
                is_reference_type(type) && initializer->entity.valid() &&
                file_.valid(initializer->entity) &&
                file_.entity(initializer->entity).storage_duration ==
                    cir::StorageDuration::Thread;
            if (bytes.has_value() && !needs_thread_cleanup &&
                !references_thread_object) {
                commit_speculative_parse();
                cir::Entity& variable = file_.entity_mut(started.entity);
                variable.has_static_initializer = true;
                variable.static_initializer_bytes = std::move(*bytes);
                variable.static_initializer_relocations =
                    std::move(relocations);
                return started;
            }
            rollback_speculative_parse();
            return construct_thread_variable(
                std::move(started), {}, loc, init_kind,
                /*value_initialize=*/false, std::move(*initializer));
        }
        if (lang_opts_.is_cxx_mode() &&
            storage_duration == cir::StorageDuration::Static &&
            !is_namespace_scope_static_entity(started.entity) &&
            !flags.is_constexpr && !flags.is_constinit) {
            ExprResult constant_candidate =
                clone_initializer_for_probe(*initializer);
            std::vector<cir::StaticInitializerRelocation> relocations;
            begin_speculative_parse();
            std::optional<std::vector<uint8_t>> bytes =
                static_initializer_bytes(type,
                                         std::move(constant_candidate),
                                         loc,
                                         &relocations);
            if (bytes.has_value()) {
                commit_speculative_parse();
                cir::Entity& variable = file_.entity_mut(started.entity);
                variable.has_static_initializer = true;
                variable.static_initializer_bytes = std::move(*bytes);
                variable.static_initializer_relocations =
                    std::move(relocations);
                return started;
            }
            rollback_speculative_parse();
            return construct_local_static(
                std::move(started), {}, loc, init_kind,
                /*value_initialize=*/false, std::move(*initializer));
        }
        if (lang_opts_.is_cxx_mode() &&
            is_namespace_scope_static_entity(started.entity) &&
            !flags.is_constexpr && !flags.is_constinit) {
            ExprResult constant_candidate =
                clone_initializer_for_probe(*initializer);
            std::vector<cir::StaticInitializerRelocation> relocations;
            begin_speculative_parse();
            std::optional<std::vector<uint8_t>> bytes =
                static_initializer_bytes(type,
                                         std::move(constant_candidate),
                                         loc,
                                         &relocations);
            if (bytes.has_value()) {
                commit_speculative_parse();
                cir::Entity& variable = file_.entity_mut(started.entity);
                variable.has_static_initializer = true;
                variable.static_initializer_bytes = std::move(*bytes);
                variable.static_initializer_relocations =
                    std::move(relocations);
                return started;
            }
            rollback_speculative_parse();
            return initialize_global_variable(std::move(started),
                                              std::move(*initializer),
                                              loc,
                                              init_kind);
        }
        std::vector<cir::StaticInitializerRelocation> relocations;
        cir::EntityId active_union_member =
            union_active_member_from_initializer(type, *initializer);
        bool diagnosed_constant_error = false;
        if (lang_opts_.is_cxx_mode() &&
            (flags.is_constexpr || flags.is_constinit) &&
            try_publish_constant_initializer(started.entity, type,
                                             *initializer, loc,
                                             &diagnosed_constant_error)) {
            bool needs_cleanup = record_destructor(type).valid() ||
                array_class_element_leaf(type).valid();
            if (needs_cleanup &&
                is_namespace_scope_static_entity(started.entity)) {
                return construct_global_variable(
                    std::move(started), {}, loc, init_kind,
                    /*value_initialize=*/false,
                    std::move(*initializer));
            }
            return started;
        }
        if (diagnosed_constant_error) {
            started.has_error = true;
            return started;
        }
        std::optional<std::vector<uint8_t>> bytes =
            static_initializer_bytes(type, std::move(*initializer), loc, &relocations);
        started.has_error = started.has_error || !bytes.has_value();
        if (!bytes.has_value() && flags.is_constinit) {
            report_error("constinit variable does not have a constant initializer",
                         loc);
        }
        if (bytes.has_value()) {
            cir::Entity& variable = file_.entity_mut(started.entity);
            variable.has_static_initializer = true;
            variable.static_initializer_bytes = std::move(*bytes);
            variable.static_initializer_relocations = std::move(relocations);
            publish_constant_state_from_static_initializer(
                started.entity, active_union_member);
        }
        return started;
    }

    if (variably_modified_type(type)) {
        report_error("variable-sized object may not be initialized", loc);
        started.has_error = true;
        return started;
    }

    if (flags.is_constexpr && !expr_is_value_dependent(*initializer)) {
        if (flags.suppress_name_binding) {

            (void)try_publish_constant_initializer(
                started.entity, type, *initializer, loc, nullptr,
                /*require_static_image=*/false);
        } else if (!publish_automatic_constexpr_initializer(
                       started.entity, type, *initializer, loc) &&
                   lang_opts_.is_cxx_mode()) {
            report_error(
                "constexpr variable must be initialized by a constant expression",
                loc);
            started.has_error = true;
        }
    }

    if (!started.place.valid()) {
        report_error("cannot initialize this declaration", loc);
        started.has_error = true;
        return started;
    }

    if (in_template_definition() && is_dependent_type(type)) {
        started.has_error = started.has_error || initializer->has_error;
        started.fragment = chain(std::move(started.fragment),
                                 std::move(initializer->fragment), loc);
        bump_pattern_taint();
    } else if (!is_reference_type(type) && initializes_std_initializer_list &&
        initializer->category == ValueCategory::InitList) {
        ExprResult value = materialize_list_initialization(
            std::move(*initializer), type, UseContext::Init, loc,
            storage_duration);
        started.has_error = started.has_error || value.has_error;
        started.fragment = chain(std::move(started.fragment),
                                 std::move(value.fragment), loc);
        if (!value.has_error && value.value.valid()) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId store_block =
                begin_fragment_block("local.initializer_list.init");
            builder_.store(started.place, value.value, loc);
            started.fragment = chain(
                std::move(started.fragment),
                finish_fragment_block(store_block, previous), loc);
        }
        LifetimeOwnerKind owner =
            storage_duration == cir::StorageDuration::Thread
                ? LifetimeOwnerKind::ThreadExit
                : (storage_duration == cir::StorageDuration::Static
                       ? LifetimeOwnerKind::StaticExit
                       : LifetimeOwnerKind::LexicalScope);
        for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
            transfer_lifetime(lifetime, owner, started.entity.index);
        }
    } else if (!is_reference_type(type) &&
               (initializer->category == ValueCategory::InitList ||
                is_aggregate_type(type))) {
        bool init_had_error = initializer->has_error;
        cir::Fragment init_fragment =
            emit_initializer_for_place(started.place, type,
                                       std::move(*initializer), loc,
                                       init_kind ==
                                               ConstructorInitializationKind::Direct
                                           ? UseContext::DirectInit
                                           : UseContext::Init);
        started.has_error = started.has_error || init_had_error;
        started.fragment = chain(std::move(started.fragment), std::move(init_fragment), loc);
    } else {
        ExprResult value = convert_to(
            std::move(*initializer), type,
            init_kind == ConstructorInitializationKind::Direct
                ? UseContext::DirectInit
                : UseContext::Init,
            loc);
        bool adopted_prvalue = false;
        if (!is_reference_type(type) &&
            value.category == ValueCategory::PrValue &&
            value.type.valid() && type_equal(value.type, type)) {
            cir::TypeId resolved = file_.resolved_type(type);
            if (file_.valid(resolved) &&
                file_.type(resolved).kind == cir::TypeKind::Record) {
                adopted_prvalue = adopt_materialized_object_storage(
                    value, started.place, started.entity);
                if (adopted_prvalue) {
                    for (cir::LifetimeId lifetime :
                         value.materialized_lifetimes) {
                        retire_lifetime(lifetime);
                    }
                }
            }
        }

        if (arc_enabled() && !is_reference_type(type) &&
            storage_duration == cir::StorageDuration::Automatic &&
            arc_retainable_type(type) &&
            arc_ownership_of(started.entity) == cir::ObjCOwnership::Strong) {
            if (value.arc_plus_one) {
                arc_claim_plus_one(value);
            } else {
                value = arc_retain_value(std::move(value), loc);
            }
        }
        started.has_error = started.has_error || value.has_error;
        started.fragment = chain(std::move(started.fragment), std::move(value.fragment), loc);
        if (!value.has_error && value.value.valid() &&
            !expr_is_value_dependent(value) &&
            !is_dependent_type(type)) {

            bool arc_weak_local = arc_enabled() && !is_reference_type(type) &&
                storage_duration == cir::StorageDuration::Automatic &&
                arc_retainable_type(type) &&
                arc_ownership_of(started.entity) == cir::ObjCOwnership::Weak;
            cir::BlockId previous = builder_.current_block();
            cir::BlockId store_block = begin_fragment_block("local.init");
            cir::InstId store{};
            if (arc_weak_local) {
                cir::InstId slot = builder_.addr_of(started.place, loc);
                (void)builder_.objc_arc_op(cir::ObjCArcOpKind::InitWeak,
                                           {slot, value.value},
                                           file_.resolved_type(type), loc);
                if (value.arc_plus_one) {
                    arc_claim_plus_one(value);
                    (void)builder_.objc_arc_op(cir::ObjCArcOpKind::Release,
                                               {value.value}, {}, loc);
                }
            } else {
                store = builder_.store(started.place, value.value, loc);
            }
            if (adopted_prvalue && store.valid()) {
                file_.inst_mut(store).runtime_elided_object_operation = true;
            }
            cir::Fragment store_fragment = finish_fragment_block(store_block, previous);
            started.fragment = chain(std::move(started.fragment), std::move(store_fragment), loc);
        }
        if (is_reference_type(type) && !value.has_error) {
            LifetimeOwnerKind reference_owner =
                storage_duration == cir::StorageDuration::Thread
                    ? LifetimeOwnerKind::ThreadExit
                    : (storage_duration == cir::StorageDuration::Static
                           ? LifetimeOwnerKind::StaticExit
                           : LifetimeOwnerKind::LexicalScope);
            for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
                transfer_lifetime(lifetime, reference_owner,
                                  started.entity.index);
            }
        }
    }
    if (lang_opts_.is_cxx_mode()) {
        register_destructor_cleanup(started.entity, started.type, loc);
    }
    arc_finish_local_declaration(started, /*zero_initialize=*/false, loc);
    return started;
}

DeclResult Session::declare_typedef(std::string_view name,
                                    cir::TypeId type,
                                    SrcLoc loc,
                                    DeclFlags flags) {
    if (collecting_pattern_ && current_function_.valid() &&
        is_dependent_type(type)) {

        mark_pattern_unusable();
    }
    if (flags.is_constexpr && !lang_opts_.is_cxx_mode()) {
        report_error("constexpr cannot be combined with typedef", loc);
    }
    if (const cir::Binding* previous = lookup_ordinary_binding(name, false)) {

        if (!binding_out_of_line_member_head_ &&
            !global_module_refold_target(*this, *previous) &&
            (!previous->is_type_name ||
             !compatible_redeclaration_type(*this, previous->type.type, type))) {
            report_error("conflicting types for '" + std::string(name) + "'",
                         loc);
        }
    }

    if (lang_opts_.is_cxx_mode()) {
        cir::TypeId resolved = file_.resolved_type(type);
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Record) {
            cir::EntityId record = file_.record_entity(resolved);
            if (record.valid() && file_.valid(record) &&
                file_.entity(record).is_unnamed_record &&
                !file_.entity(record).unnamed_type_linkage_name.valid()) {
                file_.entity_mut(record).unnamed_type_linkage_name =
                    file_.intern_name(name);
                file_.entity_mut(record).unnamed_type_ordinal =
                    cir::Entity::NoUnnamedTypeOrdinal;
            }
        }
    }

    cir::EntityId entity = builder_.add_entity(cir::EntityKind::TypeAlias, name, type, {}, loc);
    file_.entity_mut(entity).is_definition = true;
    file_.entity_mut(entity).qualifiers = flags.type_qualifiers;
    apply_attributes(entity, AttributeTarget::Type, flags.attrs, loc);
    bind_entity(name,
                cir::LookupNamespace::Ordinary,
                entity,
                type,
                true,
                false,
                true,
                {},
                loc);
    if (flags.type_qualifiers != cir::QualNone) {
        if (cir::Binding* binding =
                file_.mutable_ordinary_binding(current_decl_context(), name)) {
            binding->type.qualifiers = flags.type_qualifiers;
        }
    }

    DeclResult result;
    result.entity = entity;
    result.type = type;
    return result;
}

bool Session::validate_consteval_only_function_type(
    cir::TypeId declared_type,
    bool is_consteval,
    SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode() || is_consteval) {
        return true;
    }
    cir::ClassPropertyState state =
        file_.consteval_only_type_state(declared_type);
    if (state != cir::ClassPropertyState::True) {
        return true;
    }
    report_error("function of consteval-only type must be an immediate "
                 "function",
                 loc);
    return false;
}

bool Session::consteval_only_function_type_immediately_escalates(
    cir::TypeId declared_type,
    bool is_constexpr,
    cir::EntityKind kind,
    bool instantiated_templated_entity) const {
    if (!lang_opts_.is_cxx26_or_later() || !is_constexpr ||
        !instantiated_templated_entity ||
        kind == cir::EntityKind::Destructor) {
        return false;
    }
    return file_.consteval_only_type_state(declared_type) ==
        cir::ClassPropertyState::True;
}

void Session::mark_function_immediate(cir::EntityId function) {
    if (!function.valid() || !file_.valid(function)) {
        return;
    }
    cir::Entity& function_entity = file_.entity_mut(function);
    function_entity.decl_flags.is_consteval = true;

    cir::EntityId parent = function_entity.parent;
    const cir::RecordFacts* existing =
        parent.valid() ? file_.record_facts(parent) : nullptr;
    if (!existing) {
        return;
    }
    cir::RecordFacts updated = *existing;
    for (cir::RecordMethodFact& method : updated.methods) {
        if (method.entity == function) {
            method.is_consteval = true;
            break;
        }
    }
    file_.set_record_facts(parent, std::move(updated));
}

bool Session::validate_consteval_only_object_definition(
    cir::EntityId entity,
    cir::TypeId type,
    bool is_constexpr,
    SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode() || is_constexpr || !entity.valid() ||
        !file_.valid(entity)) {
        return true;
    }
    const cir::Entity& declaration = file_.entity(entity);
    if (declaration.object_origin ==
        cir::EntityObjectOrigin::TemplateParameterObject) {
        return true;
    }
    cir::ClassPropertyState state = file_.consteval_only_type_state(type);
    if (state != cir::ClassPropertyState::True) {
        return true;
    }
    if (current_function_.valid() && file_.valid(current_function_) &&
        declaration.storage_duration == cir::StorageDuration::Automatic) {
        cir::EntityId function = file_.function(current_function_).entity;
        if (function.valid() && file_.valid(function)) {
            cir::Entity& function_entity = file_.entity_mut(function);
            if (function_entity.decl_flags.is_consteval) {
                return true;
            }

            bool immediately_escalates =
                lang_opts_.is_cxx26_or_later() &&
                in_template_instantiation() &&
                function_entity.decl_flags.is_constexpr &&
                function_entity.kind != cir::EntityKind::Destructor;
            if (immediately_escalates) {
                mark_function_immediate(function);
                return true;
            }
        }
    }
    std::string name = declaration.name.valid()
        ? std::string(file_.name(declaration.name))
        : std::string("<object>");
    report_error("object '" + name +
                     "' of consteval-only type must be declared constexpr",
                 loc);
    return false;
}

DeclResult Session::declare_function(
    std::string_view name,
    cir::TypeId result_type,
    const std::vector<std::pair<std::string, cir::TypeId>>& params,
    SrcLoc loc) {
    std::vector<ParamInput> param_inputs;
    param_inputs.reserve(params.size());
    std::vector<cir::TypeRef> param_types;
    param_types.reserve(params.size());
    for (const auto& param : params) {
        cir::TypeRef param_type = file_.type_ref(param.second);
        param_inputs.push_back(ParamInput{param.first, param_type, loc});
        param_types.push_back(param_type);
    }
    cir::TypeRef result_ref = file_.type_ref(result_type);
    cir::TypeId function_type = file_.function_type(result_ref, param_types);
    return declare_function_type(name, function_type, result_ref, param_inputs, loc);
}

void Session::register_function_default_arguments(
    cir::EntityId entity,
    const std::vector<ParamInput>& params,
    const cir::Binding* previous_binding,
    SrcLoc loc) {
    if (!entity.valid() || !file_.valid(entity) || params.empty()) {
        return;
    }
    std::vector<ParamInput::DefaultArgument> defaults(params.size());
    bool has_any = false;
    if (auto existing = function_default_arguments_.find(
            static_cast<uint64_t>(entity.index));
        existing != function_default_arguments_.end()) {
        size_t count = std::min(defaults.size(), existing->second.size());
        for (size_t i = 0; i < count; ++i) {
            if (!existing->second[i].loc.isInvalid()) {
                defaults[i] = existing->second[i];
                has_any = true;
            }
        }
    }
    if (previous_binding) {
        for (cir::EntityId prior : previous_binding->entities) {
            if (!prior.valid() || !file_.valid(prior) ||
                !function_signatures_match(file_.entity(prior).type,
                                           file_.entity(entity).type)) {
                continue;
            }
            auto found = function_default_arguments_.find(
                static_cast<uint64_t>(prior.index));
            if (found == function_default_arguments_.end()) {
                continue;
            }
            size_t count = std::min(defaults.size(), found->second.size());
            for (size_t i = 0; i < count; ++i) {
                if (!found->second[i].loc.isInvalid()) {
                    defaults[i] = found->second[i];
                    has_any = true;
                }
            }
        }
    }
    for (size_t i = 0; i < params.size(); ++i) {
        if (!params[i].default_argument.has_value()) {
            continue;
        }
        bool replaying_template_declaration =
            tstate().function_template_materialization_target_ == entity;
        bool replaying_same_declaration =
            !defaults[i].loc.isInvalid() &&
            !params[i].default_argument->loc.isInvalid() &&
            defaults[i].loc.offset ==
                params[i].default_argument->loc.offset;
        if (!defaults[i].loc.isInvalid() &&
            !replaying_template_declaration &&
            !replaying_same_declaration) {

            report_error("repeated default argument",
                         params[i].default_argument->loc.isInvalid()
                             ? loc
                             : params[i].default_argument->loc);
        }
        defaults[i] = *params[i].default_argument;
        has_any = true;
    }
    if (has_any) {
        bool saw_default = false;
        bool reported_missing_default = false;
        for (size_t i = 0; i < defaults.size(); ++i) {
            if (!defaults[i].loc.isInvalid()) {
                saw_default = true;
                continue;
            }
            if (saw_default && !reported_missing_default) {
                report_error("parameter without a default argument follows "
                             "parameter with a default argument",
                             params[i].loc.isInvalid() ? loc : params[i].loc);
                reported_missing_default = true;
            }
        }
        uint64_t key = static_cast<uint64_t>(entity.index);
        journal_speculative_map_entry(
            "function default-argument registry",
            function_default_arguments_,
            key);
        function_default_arguments_[key] = std::move(defaults);
    }
}

void Session::register_function_template_default_arguments(
    cir::EntityId entity,
    const std::vector<ParamInput>& params,
    SrcLoc loc) {
    register_function_default_arguments(entity, params, nullptr, loc);
}

void Session::register_hidden_friend_default_arguments(
    cir::EntityId entity,
    const std::vector<ParamInput>& params,
    SrcLoc loc) {
    register_function_default_arguments(entity, params, nullptr, loc);
}

void Session::refresh_callable_binding(std::string_view name,
                                       cir::EntityId entity,
                                       cir::TypeId type,
                                       bool is_definition,
                                       SrcLoc loc) {
    if (!entity.valid()) {
        return;
    }
    cir::Binding* binding =
        file_.mutable_ordinary_binding(current_decl_context(), name);
    if (!binding || !file_.binding_is_callable(*binding) ||
        !binding_contains_entity(binding, entity)) {
        return;
    }
    binding->type = file_.type_ref(type);
    binding->is_definition = binding->is_definition || is_definition;
    binding->loc = loc;
    bump_lookup_generation();
    binding->generation = lookup_generation();

}

DeclResult Session::declare_function_type(std::string_view name,
                                          cir::TypeId function_type,
                                          cir::TypeRef result_type,
                                          const std::vector<ParamInput>& params,
                                          SrcLoc loc,
                                          DeclFlags flags) {
    (void)result_type;
    apply_implicit_cxx_function_inline(flags, lang_opts_.is_cxx_mode());
    const cir::Binding* previous_binding = lookup_ordinary_binding(name, false);
    cir::DeclContextId declaration_context = current_decl_context();
    bool block_scope_function =
        lang_opts_.is_cxx_mode() && declaration_context.valid() &&
        file_.decl_context(declaration_context).kind ==
            cir::DeclContextKind::Block;
    cir::DeclContextId function_target_context{};
    const cir::Binding* target_binding = nullptr;
    cir::EntityId target_entity{};
    if (block_scope_function) {
        for (cir::DeclContextId context = declaration_context;
             context.valid();
             context = file_.decl_context(context).parent) {
            cir::DeclContextKind kind = file_.decl_context(context).kind;
            if (kind == cir::DeclContextKind::Namespace ||
                kind == cir::DeclContextKind::TranslationUnit) {
                function_target_context = context;
                break;
            }
        }
        target_binding = previous_binding;
        if (!target_binding && function_target_context.valid()) {
            target_binding = file_.lookup_callable_binding(
                function_target_context, name, /*include_parents=*/false);
        }
        if (target_binding) {
            for (auto it = target_binding->entities.rbegin();
                 it != target_binding->entities.rend(); ++it) {
                cir::EntityId candidate = *it;
                if (!candidate.valid() || !file_.valid(candidate) ||
                    file_.entity(candidate).kind != cir::EntityKind::Function ||
                    template_info(candidate) ||
                    !function_signatures_match(file_.entity(candidate).type,
                                               function_type)) {
                    continue;
                }
                target_entity = candidate;
                break;
            }
        }
    }
    bool cxx_overload_binding = false;
    if (previous_binding) {
        bool previous_is_callable =
            !previous_binding->is_type_name &&
            file_.binding_is_callable(*previous_binding);
        if (lang_opts_.is_cxx_mode() && previous_is_callable) {
            cxx_overload_binding = true;
            diagnose_cxx_callable_redeclaration(*previous_binding, name,
                                                function_type, loc);
        } else {
            diagnose_conflicting_redeclaration(*this, *previous_binding, name,
                                               function_type, loc);
        }
    } else if (target_entity.valid() && target_binding) {

        diagnose_cxx_callable_redeclaration(*target_binding, name,
                                            function_type, loc);
    }
    const cir::Binding* redeclaration_binding =
        previous_binding ? previous_binding
                         : (target_entity.valid() ? target_binding : nullptr);
    PriorFunctionFacts prior = prior_function_facts(*this,
                                                    file_,
                                                    redeclaration_binding,
                                                    function_type,
                                                    lang_opts_.is_cxx_mode());
    std::string asm_label = inherited_function_asm_label(
        *this, file_, flags, prior.entity, loc);
    if (flags.is_constexpr && !lang_opts_.is_cxx_mode()) {
        report_error("constexpr is not allowed on function declarations in C", loc);
    }
    if (flags.is_constinit) {
        report_error("constinit can only be applied to variables", loc);
    }
    flags.is_consteval = flags.is_consteval ||
        consteval_only_function_type_immediately_escalates(
            function_type,
            flags.is_constexpr,
            cir::EntityKind::Function,
            in_template_instantiation());
    validate_consteval_only_function_type(function_type,
                                           flags.is_consteval,
                                           loc);
    if (flags.is_deleted) {
        if (block_scope_function) {
            report_error("'= delete' is a function definition and must occur "
                         "at namespace scope",
                         loc);
            DeclResult result;
            result.type = function_type;
            result.has_error = true;
            return result;
        }
        if (prior.entity.valid()) {
            report_error("deleted definition of function '" +
                             std::string(name) +
                             "' must be the first declaration",
                         loc);
            report_note("previous declaration is here",
                        file_.entity(prior.entity).loc);
            DeclResult result;
            result.entity = prior.entity;
            result.type = function_type;
            result.has_error = true;
            return result;
        }

        flags.is_inline = true;
    }
    (void)cxx_overload_binding;

    if (target_entity.valid()) {

        apply_attributes(target_entity, AttributeTarget::Function,
                         flags.attrs, loc);
        if (!asm_label.empty()) {
            file_.entity_mut(target_entity).attr_facts.asm_label =
                std::move(asm_label);
        }
        register_function_default_arguments(target_entity, params,
                                            target_binding, loc);
        register_placeholder_result(target_entity, function_type,
                                    target_binding, loc);
        cir::DeclContextId saved_lexical =
            file_.entity(target_entity).lexical_context;
        cir::DeclContextId saved_semantic =
            file_.entity(target_entity).semantic_context;
        if (binding_contains_entity(previous_binding, target_entity)) {
            refresh_callable_binding(name, target_entity, function_type,
                                     false, loc);
        } else {
            bind_callable(name, target_entity, function_type, false, loc);
        }
        file_.entity_mut(target_entity).lexical_context = saved_lexical;
        file_.entity_mut(target_entity).semantic_context = saved_semantic;
        if (collecting_pattern_ && current_function_.valid()) {
            pattern_events_.push_back(PatternScopeEvent{
                PatternScopeEvent::Kind::DeclareBlockFunction,
                target_entity,
                {},
                lookup_generation_});
        }
        DeclResult result;
        result.entity = target_entity;
        result.type = function_type;
        return result;
    }

    cir::EntityId entity{};
    if (lang_opts_.is_cxx_mode() && !block_scope_function) {
        entity = friend_function_entity(name,
                                        function_type,
                                        current_decl_context());
    }
    bool reused_friend_function = entity.valid();
    if (!reused_friend_function) {
        entity = builder_.add_entity(cir::EntityKind::Function,
                                     name,
                                     function_type,
                                     {},
                                     loc,
                                     cir::StorageDuration::Unknown,
                                     cir::MemorySpace::Default,
                                     flags.to_cir());
        file_.entity_mut(entity).is_definition = flags.is_deleted;
    } else {
        cir::Entity& record = file_.entity_mut(entity);
        record.type = function_type;
        cir::DeclSemanticFlags written_flags = flags.to_cir();

        written_flags.is_inline =
            written_flags.is_inline || record.decl_flags.is_inline;
        record.decl_flags = written_flags;
        record.is_definition = record.is_definition || flags.is_deleted;
    }
    file_.entity_mut(entity).is_deleted =
        flags.is_deleted || prior.is_deleted;

    file_.entity_mut(entity).linkage =
        (flags.is_static ||
         prior.has_internal_linkage)
            ? cir::LinkageKind::Internal
            : cir::LinkageKind::External;
    file_.entity_mut(entity).is_extern_c = in_extern_c_linkage();
    apply_attributes(entity, AttributeTarget::Function, flags.attrs, loc);
    apply_pragma_visibility_default(entity);
    if (prior.entity.valid()) {
        if (prior.entity != entity) {
            file_.entity_mut(entity).linkage_predecessor = prior.entity;
        }
        merge_entity_attribute_facts(file_.entity_mut(entity).attr_facts,
                               prior.attributes);

        if (prior.is_extern_c) {
            file_.entity_mut(entity).is_extern_c = true;
        }
    }
    register_c_language_entity(entity, name, false, loc);
    unify_function_weak_across_binding(*this,
                                       file_,
                                       previous_binding,
                                       entity,
                                       function_type,
                                       lang_opts_.is_cxx_mode());
    apply_inline_linkage_rules(*this, file_, entity, flags, previous_binding,
                               lang_opts_.is_cxx_mode());
    if (!asm_label.empty()) {
        file_.entity_mut(entity).attr_facts.asm_label = std::move(asm_label);
    }
    register_function_default_arguments(entity, params, previous_binding, loc);
    register_placeholder_result(entity, function_type, previous_binding, loc);
    if (lang_opts_.is_cxx_mode()) {
        if (binding_contains_entity(previous_binding, entity)) {
            refresh_callable_binding(name, entity, function_type,
                                     flags.is_deleted, loc);
        } else {
            bind_callable(name, entity, function_type,
                          flags.is_deleted, loc);
        }
    } else {
        bind_entity(name,
                    cir::LookupNamespace::Ordinary,
                    entity,
                    function_type,
                    false,
                    false,
                    flags.is_deleted,
                    {},
                    loc);
    }
    if (block_scope_function && function_target_context.valid()) {

        file_.entity_mut(entity).semantic_context = function_target_context;
        if (collecting_pattern_ && current_function_.valid()) {
            pattern_events_.push_back(PatternScopeEvent{
                PatternScopeEvent::Kind::DeclareBlockFunction,
                entity,
                {},
                lookup_generation_});
        }
    }

    DeclResult result;
    result.entity = entity;
    result.type = function_type;
    return result;
}

FunctionDeclStart Session::begin_function(
    std::string_view name,
    cir::TypeId result_type,
    const std::vector<std::pair<std::string, cir::TypeId>>& params,
    SrcLoc loc) {
    std::vector<ParamInput> param_inputs;
    param_inputs.reserve(params.size());
    std::vector<cir::TypeRef> param_types;
    param_types.reserve(params.size());
    for (const auto& param : params) {
        cir::TypeRef param_type = file_.type_ref(param.second);
        param_inputs.push_back(ParamInput{param.first, param_type, loc});
        param_types.push_back(param_type);
    }
    cir::TypeRef result_ref = file_.type_ref(result_type);
    cir::TypeId function_type = file_.function_type(result_ref, param_types);
    return begin_function_type(name, function_type, result_ref, param_inputs, loc);
}

cir::TypeId Session::substitute_vla_parameter_bounds(
    cir::TypeId type,
    const std::unordered_map<std::string, cir::InstId>& parameter_values) {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return type;
    }
    if (file_.type(resolved).kind == cir::TypeKind::Pointer) {
        const auto* pointer =
            std::get_if<cir::PointerTypePayload>(&file_.type_payload(resolved));
        if (!pointer) {
            return type;
        }
        cir::TypeId new_pointee =
            substitute_vla_parameter_bounds(pointer->pointee.type, parameter_values);
        if (new_pointee == pointer->pointee.type) {
            return type;
        }
        return builder_.pointer_type(
            cir::TypeRef{new_pointee, pointer->pointee.qualifiers,
                         pointer->pointee.memory_space});
    }
    if (file_.type(resolved).kind != cir::TypeKind::Array) {
        return type;
    }
    const auto* array =
        std::get_if<cir::ArrayTypePayload>(&file_.type_payload(resolved));
    if (!array) {
        return type;
    }
    cir::TypeId new_element =
        substitute_vla_parameter_bounds(array->element_type.type, parameter_values);
    cir::InstId new_bound = array->size_expr;
    if (array->size_kind == cir::ArraySizeKind::Variable &&
        file_.valid(array->size_expr) &&
        file_.inst(array->size_expr).kind == cir::InstKind::NameRef) {
        std::vector<cir::Operand> operands =
            file_.operands(file_.inst(array->size_expr).operands);
        if (!operands.empty()) {
            if (const auto* name_id = std::get_if<cir::NameId>(&operands[0].data);
                name_id && file_.valid(*name_id)) {
                auto found = parameter_values.find(std::string(file_.name(*name_id)));
                if (found != parameter_values.end()) {
                    new_bound = found->second;
                }
            }
        }
    }
    if (new_element == array->element_type.type && new_bound == array->size_expr) {
        return type;
    }
    return file_.array_type(
        cir::TypeRef{new_element, array->element_type.qualifiers,
                     array->element_type.memory_space},
        array->size_kind,
        array->size,
        new_bound);
}

FunctionDeclStart Session::begin_function_type(std::string_view name,
                                               cir::TypeId function_type,
                                               cir::TypeRef result_type,
                                               const std::vector<ParamInput>& params,
                                               SrcLoc loc,
                                               DeclFlags flags) {
    apply_implicit_cxx_function_inline(flags, lang_opts_.is_cxx_mode());
    diagnose_abstract_function_use(function_type,
                                   AbstractFunctionUse::Definition,
                                   loc);
    current_prologue_ = {};
    function_labels_.clear();
    local_label_scopes_.clear();
    pending_orphan_label_blocks_.clear();
    vla_sp_slot_place_ = {};

    const cir::Binding* previous_binding = lookup_ordinary_binding(name, false);
    if (previous_binding) {
        bool previous_is_callable =
            !previous_binding->is_type_name &&
            file_.binding_is_callable(*previous_binding);
        if (lang_opts_.is_cxx_mode() && previous_is_callable) {
            diagnose_cxx_callable_redeclaration(*previous_binding, name,
                                                function_type, loc);
        } else {
            diagnose_conflicting_redeclaration(*this, *previous_binding, name,
                                               function_type, loc);
        }
    }
    PriorFunctionFacts prior = prior_function_facts(*this,
                                                    file_,
                                                    previous_binding,
                                                    function_type,
                                                    lang_opts_.is_cxx_mode());
    std::string asm_label = inherited_function_asm_label(
        *this, file_, flags, prior.entity, loc);
    if (flags.is_constexpr && !lang_opts_.is_cxx_mode()) {
        report_error("constexpr is not allowed on function declarations in C", loc);
    }
    if (flags.is_constinit) {
        report_error("constinit can only be applied to variables", loc);
    }
    flags.is_consteval = flags.is_consteval ||
        consteval_only_function_type_immediately_escalates(
            function_type,
            flags.is_constexpr,
            cir::EntityKind::Function,
            in_template_instantiation());
    validate_consteval_only_function_type(function_type,
                                           flags.is_consteval,
                                           loc);
    if (prior.is_deleted) {
        report_error("redefinition of deleted function '" +
                         std::string(name) + "'",
                     loc);
        report_note("deleted definition is here",
                    file_.entity(prior.entity).loc);
    }

    cir::EntityId fn_entity =
        tstate().function_template_materialization_target_;
    bool materializing_template_declaration =
        fn_entity.valid() && file_.valid(fn_entity);
    if ((!fn_entity.valid() || !file_.valid(fn_entity)) &&
        lang_opts_.is_cxx_mode()) {
        fn_entity = friend_function_entity(name,
                                           function_type,
                                           current_decl_context());
    }
    bool reused_friend_function = fn_entity.valid();
    if (reused_friend_function &&
        file_.entity(fn_entity).is_definition &&
        !materializing_template_declaration &&
        (!previous_binding || !previous_binding->is_definition)) {
        report_error("redefinition of function '" + std::string(name) + "'",
                     loc);
        report_note("previous definition is here",
                    file_.entity(fn_entity).loc);
    }
    if (!reused_friend_function) {
        fn_entity = builder_.add_entity(cir::EntityKind::Function,
                                        name,
                                        function_type,
                                        {},
                                        loc,
                                        cir::StorageDuration::Unknown,
                                        cir::MemorySpace::Default,
                                        flags.to_cir());
    } else {
        cir::Entity& record = file_.entity_mut(fn_entity);
        record.type = function_type;
        record.decl_flags = flags.to_cir();
        if (materializing_template_declaration) {
            record.is_template_pattern = false;
        }
    }
    file_.entity_mut(fn_entity).is_definition = true;

    file_.entity_mut(fn_entity).linkage =
        (flags.is_static ||
         prior.has_internal_linkage)
            ? cir::LinkageKind::Internal
            : cir::LinkageKind::External;
    file_.entity_mut(fn_entity).is_extern_c = in_extern_c_linkage();
    apply_attributes(fn_entity, AttributeTarget::Function, flags.attrs, loc);
    apply_pragma_visibility_default(fn_entity);
    if (prior.entity.valid()) {
        if (prior.entity != fn_entity) {
            file_.entity_mut(fn_entity).linkage_predecessor = prior.entity;
        }
        merge_entity_attribute_facts(file_.entity_mut(fn_entity).attr_facts,
                               prior.attributes);

        if (prior.is_extern_c) {
            file_.entity_mut(fn_entity).is_extern_c = true;
        }
    }
    register_c_language_entity(fn_entity, name, true, loc);
    unify_function_weak_across_binding(*this,
                                       file_,
                                       previous_binding,
                                       fn_entity,
                                       function_type,
                                       lang_opts_.is_cxx_mode());
    apply_inline_linkage_rules(*this, file_, fn_entity, flags, previous_binding,
                               lang_opts_.is_cxx_mode());
    if (!asm_label.empty()) {
        file_.entity_mut(fn_entity).attr_facts.asm_label = std::move(asm_label);
    }
    cir::EntityId materialized_template{};
    if (materializing_template_declaration) {
        if (const cir::TemplateSpecializationFact* specialization =
                file_.template_specialization(fn_entity)) {
            materialized_template = specialization->template_entity;
        }
    }
    if (materialized_template.valid()) {
        for (auto frame = tstate().current_instantiation_frames_.rbegin();
             frame != tstate().current_instantiation_frames_.rend(); ++frame) {
            const TemplateInfo* info = frame->info;
            if (!info || info->entity != materialized_template ||
                info->is_class_template || info->is_alias_template ||
                info->is_variable_template || info->is_concept ||
                !file_.valid(info->entity) ||
                file_.entity(info->entity).kind !=
                    cir::EntityKind::Function) {
                continue;
            }
            remember_template_specialization(
                fn_entity,
                *info,
                frame->arguments,
                loc,
                frame->point_lookup_generation);
            break;
        }
    }
    register_function_default_arguments(fn_entity, params, previous_binding, loc);
    register_placeholder_result(fn_entity, function_type, previous_binding,
                                loc);
    if (materializing_template_declaration) {
        tstate().function_template_materialization_target_ = {};
    }
    std::vector<std::pair<cir::EntityId, cir::TypeId>> param_entities;
    param_entities.reserve(params.size());
    tstate().function_parameter_pack_scope_stack_.push_back(
        FunctionParameterPackScopeState{
            std::move(tstate().function_parameter_pack_names_),
            std::move(tstate().function_parameter_pack_elements_),
            std::move(tstate().function_parameter_pack_template_indices_)});
    tstate().function_parameter_pack_names_ = {};
    tstate().function_parameter_pack_elements_ = {};
    tstate().function_parameter_pack_template_indices_ = {};
    std::unordered_map<uint64_t, std::string> source_pack_names_by_entity;
    for (const ParamInput& param : params) {
        if (param.is_parameter_pack_expansion_sentinel) {
            if (!param.source_parameter_pack_name.empty()) {
                tstate().function_parameter_pack_names_.insert(
                    param.source_parameter_pack_name);
                tstate().function_parameter_pack_elements_
                    [param.source_parameter_pack_name];
            }
            continue;
        }
        SrcLoc param_loc = param.loc.isInvalid() ? loc : param.loc;

        (void)require_complete_class_type(
            param.type.type,
            param_loc,
            cir::InstantiationDemandKind::CompleteClass);
        cir::EntityId entity = param.prototype_entity;
        if (entity.valid()) {
            file_.entity_mut(entity).parent = fn_entity;
        } else {
            entity = builder_.add_entity(cir::EntityKind::Parameter,
                                         param.name,
                                         param.type.type,
                                         fn_entity,
                                         param_loc,
                                         cir::StorageDuration::Parameter);
        }
        if (param.type_originates_from_template_parameter) {
            uint64_t entity_index = static_cast<uint64_t>(entity.index);
            journal_speculative_set_entry(
                "template-origin function parameter identity",
                tstate().template_type_origin_parameter_entities_,
                entity_index);
            tstate().template_type_origin_parameter_entities_.insert(
                entity_index);
        }
        if (param.is_parameter_pack) {
            uint64_t entity_index = static_cast<uint64_t>(entity.index);
            journal_speculative_set_entry(
                "function parameter pack identity",
                tstate().function_parameter_pack_params_,
                entity_index);
            tstate().function_parameter_pack_params_.insert(
                entity_index);
            tstate().function_parameter_pack_names_.insert(param.name);
            if (std::optional<uint32_t> pack_index =
                    type_parameter_pack_index(param.type.type)) {
                tstate().function_parameter_pack_template_indices_[param.name] =
                    *pack_index;
            }
        }
        if (!param.source_parameter_pack_name.empty()) {
            tstate().function_parameter_pack_names_.insert(
                param.source_parameter_pack_name);
            source_pack_names_by_entity[static_cast<uint64_t>(entity.index)] =
                param.source_parameter_pack_name;
        }
        file_.entity_mut(entity).qualifiers = param.type.qualifiers;
        apply_attributes(entity, AttributeTarget::Parameter, param.attrs, param_loc);
        param_entities.emplace_back(entity, param.type.type);
    }

    cir::FunctionStart fn =
        builder_.begin_function(fn_entity, result_type.type, param_entities, loc);
    current_function_ = fn.function;
    current_result_type_ = result_type.type;
    nrvo_return_candidates_.clear();
    nrvo_has_incompatible_return_ = false;
    active_catch_handlers_ = 0;
    active_constructor_function_try_handlers_ = 0;
    current_destructor_lifecycle_region_ = {};
    coroutine_state_.reset();
    first_plain_return_loc_ = {};
    has_plain_return_ = false;
    if (!materializing_template_declaration) {
        if (lang_opts_.is_cxx_mode()) {
            if (binding_contains_entity(previous_binding, fn.entity)) {
                refresh_callable_binding(name,
                                         fn.entity,
                                         file_.function(fn.function).type,
                                         true,
                                         loc);
            } else {
                bind_callable(name,
                              fn.entity,
                              file_.function(fn.function).type,
                              true,
                              loc);
            }
        } else {
            bind_entity(name,
                        cir::LookupNamespace::Ordinary,
                        fn.entity,
                        file_.function(fn.function).type,
                        false,
                        false,
                        true,
                        {},
                        loc);
        }
    }
    enter_scope_impl(ScopeFlags::FunctionScope, fn.entity, loc);
    begin_noexcept_body_region(function_type, loc);

    std::unordered_map<std::string, cir::InstId> parameter_values;
    for (const cir::FunctionParameter& parameter : fn.parameters) {
        const cir::Entity& param_record = file_.entity(parameter.entity);
        if (param_record.name.valid()) {
            parameter_values[std::string(file_.name(param_record.name))] =
                parameter.value.inst;
        }
    }
    size_t param_index = 0;
    for (const cir::FunctionParameter& parameter : fn.parameters) {
        cir::EntityId param_entity = parameter.entity;
        cir::TypeId substituted = substitute_vla_parameter_bounds(
            file_.entity(param_entity).type, parameter_values);
        if (substituted != file_.entity(param_entity).type) {
            file_.entity_mut(param_entity).type = substituted;

            file_.inst_mut(parameter.value.inst).result_type = substituted;
        }
        cir::TypeId param_type = file_.entity(param_entity).type;
        SrcLoc param_loc = file_.entity(param_entity).loc;
        bool arc_managed = arc_enabled() &&
            params.size() == fn.parameters.size() &&
            param_index < params.size() &&
            !params[param_index].arc_unretained &&
            arc_retainable_type(param_type) &&
            arc_ownership_of(param_entity) == cir::ObjCOwnership::Strong;
        bool arc_entry_retain = arc_managed &&
            !params[param_index].arc_consumed;

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("param.place");
        cir::InstId param_place = builder_.local_place(param_entity, param_type, param_loc);
        cir::InstId incoming = parameter.value.inst;
        if (arc_entry_retain) {
            incoming = builder_.objc_arc_op(cir::ObjCArcOpKind::Retain,
                                            {incoming},
                                            file_.resolved_type(param_type),
                                            param_loc);
        }
        builder_.store(param_place, incoming, param_loc);
        cir::Fragment param_fragment = finish_fragment_block(block, previous);
        current_prologue_ = chain(std::move(current_prologue_), std::move(param_fragment), param_loc);
        if (arc_managed) {
            (void)register_arc_cleanup(param_entity, param_type,
                                       arc_strong_destroy_helper(param_loc),
                                       param_loc);
        }
        ++param_index;

        bind_entity(file_.name(file_.entity(param_entity).name),
                    cir::LookupNamespace::Ordinary,
                    param_entity,
                    param_type,
                    false,
                    false,
                    true,
                    param_place,
                    param_loc);
        auto source_pack =
            source_pack_names_by_entity.find(
                static_cast<uint64_t>(param_entity.index));
        if (source_pack != source_pack_names_by_entity.end()) {
            tstate().function_parameter_pack_elements_[source_pack->second].push_back(
                FunctionParameterPackElement{param_entity,
                                             param_type,
                                             param_place,
                                             param_loc});
        }
    }

    for (const ParamInput& param : params) {
        if (!param.vla_bounds.empty()) {
            for (cir::BlockId block : param.vla_bounds.blocks) {

                std::string base(file_.name(file_.block(block).name));
                size_t dot = base.rfind('.');
                if (dot != std::string::npos && dot + 1 < base.size() &&
                    base.find_first_not_of("0123456789", dot + 1) ==
                        std::string::npos) {
                    base.resize(dot);
                }
                builder_.rename_block(block, base);
            }
            current_prologue_ = chain(std::move(current_prologue_),
                                      param.vla_bounds,
                                      param.loc.isInvalid() ? loc : param.loc);
        }
    }

    FunctionDeclStart start;
    start.decl.entity = fn.entity;
    start.decl.type = file_.function(fn.function).type;
    start.function = fn;
    return start;
}

FunctionDeclStart Session::begin_function_type_on_entity(
    cir::EntityId entity,
    std::string_view name,
    cir::TypeId function_type,
    cir::TypeRef result_type,
    const std::vector<ParamInput>& params,
    SrcLoc loc,
    DeclFlags flags) {
    cir::EntityId previous = tstate().function_template_materialization_target_;
    tstate().function_template_materialization_target_ = entity;
    FunctionDeclStart start = begin_function_type(name,
                                                  function_type,
                                                  result_type,
                                                  params,
                                                  loc,
                                                  flags);
    tstate().function_template_materialization_target_ = previous;
    return start;
}

cir::EntityId Session::bind_prototype_parameter(
    std::string_view name,
    cir::TypeRef type,
    SrcLoc loc,
    bool type_originates_from_template_parameter) {
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Parameter,
                                               name,
                                               type.type,
                                               cir::EntityId{},
                                               loc,
                                               cir::StorageDuration::Parameter);
    cir::Entity& record = file_.entity_mut(entity);
    record.is_definition = false;
    record.qualifiers = type.qualifiers;
    if (type_originates_from_template_parameter) {
        uint64_t entity_index = static_cast<uint64_t>(entity.index);
        journal_speculative_set_entry(
            "template-origin prototype parameter identity",
            tstate().template_type_origin_parameter_entities_,
            entity_index);
        tstate().template_type_origin_parameter_entities_.insert(
            entity_index);
    }
    bind_entity(name,
                cir::LookupNamespace::Ordinary,
                entity,
                type.type,
                false,
                false,
                false,
                cir::InstId{},
                loc);
    return entity;
}

Session::PrototypeParameterScope
Session::begin_prototype_parameter_scope() {
    PrototypeParameterScope scope;
    enter_scope(ScopeFlags::PrototypeScope);
    scope.active = true;
    tstate().function_parameter_pack_scope_stack_.push_back(
        FunctionParameterPackScopeState{
            std::move(tstate().function_parameter_pack_names_),
            std::move(tstate().function_parameter_pack_elements_),
            std::move(tstate().function_parameter_pack_template_indices_)});
    tstate().function_parameter_pack_names_.clear();
    tstate().function_parameter_pack_elements_.clear();
    tstate().function_parameter_pack_template_indices_.clear();
    return scope;
}

cir::EntityId Session::bind_prototype_parameter(
    PrototypeParameterScope& scope,
    const TemplateInfo::FunctionConstraintParameter& parameter) {
    if (!scope.active) {
        return {};
    }
    const std::string& source_pack_name =
        parameter.source_parameter_pack_name;
    if (parameter.is_parameter_pack_expansion_sentinel) {
        if (!source_pack_name.empty()) {
            tstate().function_parameter_pack_names_.insert(source_pack_name);
            tstate().function_parameter_pack_elements_[source_pack_name];
        }
        return {};
    }
    if (parameter.name == "<anonymous>" || !parameter.type.valid()) {
        return {};
    }
    cir::EntityId entity = bind_prototype_parameter(
        parameter.name,
        parameter.type,
        parameter.loc,
        parameter.type_originates_from_template_parameter);
    scope.entities.push_back(entity);
    if (parameter.is_parameter_pack) {
        uint64_t entity_index = static_cast<uint64_t>(entity.index);
        journal_speculative_set_entry(
            "prototype function parameter pack identity",
            tstate().function_parameter_pack_params_,
            entity_index);
        tstate().function_parameter_pack_params_.insert(
            entity_index);
        tstate().function_parameter_pack_names_.insert(parameter.name);
        if (std::optional<uint32_t> pack_index =
                type_parameter_pack_index(parameter.type.type)) {
            tstate().function_parameter_pack_template_indices_
                [parameter.name] = *pack_index;
        }
    }

    if (!source_pack_name.empty()) {
        tstate().function_parameter_pack_names_.insert(source_pack_name);
        tstate().function_parameter_pack_elements_[source_pack_name].push_back(
            FunctionParameterPackElement{
                entity, parameter.type.type, {}, parameter.loc});
    }
    return entity;
}

Session::PrototypeParameterScope
Session::begin_function_constraint_parameter_scope(
    const std::vector<TemplateInfo::FunctionConstraintParameter>& parameters) {
    PrototypeParameterScope scope;
    if (parameters.empty()) {
        return scope;
    }
    scope = begin_prototype_parameter_scope();
    for (const TemplateInfo::FunctionConstraintParameter& parameter :
         parameters) {
        bind_prototype_parameter(scope, parameter);
    }
    return scope;
}

void Session::finish_prototype_parameter_scope(
    PrototypeParameterScope scope) {
    if (!scope.active) {
        return;
    }
    leave_scope();
    for (cir::EntityId entity : scope.entities) {
        tstate().function_parameter_pack_params_.erase(
            static_cast<uint64_t>(entity.index));
        tstate().template_type_origin_parameter_entities_.erase(
            static_cast<uint64_t>(entity.index));
    }
    if (!tstate().function_parameter_pack_scope_stack_.empty()) {
        tstate().function_parameter_pack_names_ =
            std::move(tstate().function_parameter_pack_scope_stack_.back().names);
        tstate().function_parameter_pack_elements_ =
            std::move(tstate().function_parameter_pack_scope_stack_.back().elements);
        tstate().function_parameter_pack_template_indices_ =
            std::move(tstate().function_parameter_pack_scope_stack_.back()
                          .template_pack_indices);
        tstate().function_parameter_pack_scope_stack_.pop_back();
    } else {
        tstate().function_parameter_pack_names_.clear();
        tstate().function_parameter_pack_elements_.clear();
        tstate().function_parameter_pack_template_indices_.clear();
    }
}

void Session::finish_function_constraint_parameter_scope(
    PrototypeParameterScope scope) {
    finish_prototype_parameter_scope(std::move(scope));
}

DeclResult Session::collect_decl_sequence(std::vector<DeclResult> declarations, SrcLoc loc) {
    DeclResult result;
    bool initialized = false;
    for (DeclResult& declaration : declarations) {
        if (!initialized) {
            result = std::move(declaration);
            initialized = true;
            continue;
        }
        result.fragment = chain(std::move(result.fragment), std::move(declaration.fragment), loc);
        result.has_error = result.has_error || declaration.has_error;
        if (!result.entity.valid()) {
            result.entity = declaration.entity;
            result.type = declaration.type;
            result.place = declaration.place;
        }
    }
    return result;
}

void Session::finish_function(StmtResult body, SrcLoc loc) {
    if (!current_function_.valid()) {
        return;
    }
    builder_.set_current_unwind_target({});
    if (coroutine_state_ && !coroutine_state_->discovery_failed) {

        if (lang_opts_.enable_coroutine_pre_split_cir &&
            !coroutine_state_->emission_failed) {
            body = finish_coroutine_function(*coroutine_state_,
                                             std::move(body), loc);
        }
    } else {
        finalize_nrvo_for_current_function();
    }

    cir::Fragment body_fragment =
        chain(std::move(current_prologue_), std::move(body.fragment), loc);
    cir::Fragment unresolved_label_fragment;
    for (auto& [name, label] : function_labels_) {
        (void)name;
        if (label.referenced && !label.defined) {
            diagnose_unresolved_label(label, loc);
            if (label.block.valid()) {
                unresolved_label_fragment.blocks.push_back(label.block);
            }
        }
    }
    for (cir::BlockId block : pending_orphan_label_blocks_) {
        if (block.valid()) {
            if (!builder_.block_terminated(block)) {
                builder_.unreachable_from(block, loc);
            }
            unresolved_label_fragment.blocks.push_back(block);
        }
    }
    cir::BlockId entry = file_.function(current_function_).entry_block;

    // Terminate a block that control can fall through to the closing brace of
    // the function. Void functions return void; `main` implicitly returns 0
    // (C11 5.1.2.2.3 / C++ [basic.start.main]); any other non-void function
    // has an undefined return value but reaching the end is NOT a trap
    // (C11 6.9.1p12). Match GCC/Clang and return the contents of a fresh
    // (uninitialized) slot so callers that ignore the result keep running.
    auto terminate_fallthrough = [&](cir::BlockId block) {
        if (is_void_type(current_result_type_)) {
            builder_.return_void_from(block, loc);
            return;
        }
        builder_.switch_to_block(block);
        const cir::Entity& fn_entity =
            file_.entity(file_.function(current_function_).entity);
        bool is_program_main =
            fn_entity.linkage == cir::LinkageKind::External &&
            file_.name(fn_entity.name) == "main";
        cir::EntityId slot = builder_.add_entity(
            cir::EntityKind::Variable, ".ret.fallthrough",
            current_result_type_, {}, loc, cir::StorageDuration::Automatic);
        file_.entity_mut(slot).is_definition = true;
        cir::InstId place = builder_.local_place(slot, current_result_type_, loc);
        if (is_program_main) {

            builder_.zero_object(place, loc);
        }
        cir::InstId value = builder_.lvalue_to_rvalue(place, loc);
        builder_.return_value(value, loc);
    };

    if (!body_fragment.empty()) {
        if (!builder_.block_terminated(entry)) {
            builder_.branch_from(entry, body_fragment.entry, {}, loc);
        }
        builder_.attach_fragment_to_function(current_function_, body_fragment);
        builder_.attach_fragment_to_function(current_function_, unresolved_label_fragment);
        if (!builder_.block_terminated(body_fragment.exit)) {
            if (body_fragment.falls_through) {
                cir::Fragment exit_cleanup =
                    emit_cleanup_calls_from_depth(0, loc);
                if (!exit_cleanup.empty()) {
                    builder_.branch_from(body_fragment.exit,
                                         exit_cleanup.entry, {}, loc);
                    builder_.attach_fragment_to_function(current_function_,
                                                         exit_cleanup);
                    terminate_fallthrough(exit_cleanup.exit);
                } else {
                    terminate_fallthrough(body_fragment.exit);
                }
            } else {

                builder_.unreachable_from(body_fragment.exit, loc);
            }
        }
    } else if (!builder_.block_terminated(entry)) {
        builder_.attach_fragment_to_function(current_function_, unresolved_label_fragment);
        terminate_fallthrough(entry);
    }

    leave_scope();
    current_prologue_ = {};
    current_function_ = {};
    current_result_type_ = {};
    nrvo_return_candidates_.clear();
    nrvo_has_incompatible_return_ = false;
    active_catch_handlers_ = 0;
    active_constructor_function_try_handlers_ = 0;
    current_destructor_lifecycle_region_ = {};
    coroutine_state_.reset();
    first_plain_return_loc_ = {};
    has_plain_return_ = false;
    if (!tstate().function_parameter_pack_scope_stack_.empty()) {
        tstate().function_parameter_pack_names_ =
            std::move(tstate().function_parameter_pack_scope_stack_.back().names);
        tstate().function_parameter_pack_elements_ =
            std::move(tstate().function_parameter_pack_scope_stack_.back().elements);
        tstate().function_parameter_pack_template_indices_ =
            std::move(tstate().function_parameter_pack_scope_stack_.back()
                          .template_pack_indices);
        tstate().function_parameter_pack_scope_stack_.pop_back();
    } else {
        tstate().function_parameter_pack_names_.clear();
        tstate().function_parameter_pack_elements_.clear();
        tstate().function_parameter_pack_template_indices_.clear();
    }
    function_labels_.clear();
    local_label_scopes_.clear();
    pending_orphan_label_blocks_.clear();
}

void Session::ensure_vla_stack_slot(SrcLoc loc) {
    if (vla_sp_slot_place_.valid()) {
        return;
    }
    cir::TypeId slot_type = builder_.pointer_type(
        file_.builtin_type(cir::BuiltinTypeKind::Void));
    cir::EntityId slot = builder_.add_entity(cir::EntityKind::Variable,
                                             ".vla.saved_sp",
                                             slot_type,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(slot).is_definition = true;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("vla.sp_slot");
    cir::InstId place = builder_.local_place(slot, slot_type, loc);
    cir::InstId saved = builder_.stack_save(loc);
    builder_.store(place, saved, loc);
    cir::Fragment slot_fragment = finish_fragment_block(block, previous);
    current_prologue_ = chain(std::move(current_prologue_),
                              std::move(slot_fragment),
                              loc);
    vla_sp_slot_place_ = place;
}

void Session::collect_file_scope_asm(std::string asm_string, SrcLoc loc) {
    (void)loc;
    file_.add_module_asm(std::move(asm_string));
}

void Session::collect_static_assert(ExprResult condition,
                                    bool value_dependent,
                                    std::string message,
                                    bool has_message,
                                    LifetimeBoundary boundary,
                                    SrcLoc loc) {

    if (condition.has_error) {
        discard_lifetime_boundary(boundary);
        return;
    }
    if (value_dependent) {
        discard_lifetime_boundary(boundary);
        return;
    }
    condition = require_value(std::move(condition),
                              lang_opts_.is_cxx_mode()
                                  ? UseContext::Condition
                                  : UseContext::RValue,
                              loc);
    if (condition.has_error) {
        discard_lifetime_boundary(boundary);
        return;
    }
    condition.fragment = chain(
        std::move(condition.fragment),
        finish_lifetime_boundary(boundary, loc),
        loc);
    int64_t value = 0;
    if (!evaluate_integer_constant(
            condition,
            value,
            loc,
            "static assertion condition is not an integer constant expression")) {
        return;
    }
    if (value == 0) {

        if (collecting_pattern_) {
            bump_pattern_taint();
            return;
        }
        std::string diagnostic = "static assertion failed";
        if (has_message) {
            diagnostic += ": ";
            diagnostic += message;
        }
        report_error(std::move(diagnostic), loc);
    }
}

cir::FunctionExceptionSpec Session::evaluate_noexcept_spec(
    const ExprResult& operand,
    SrcLoc loc) {

    if (operand.has_error) {
        return cir::FunctionExceptionSpecKind::NonThrowing;
    }
    if ((expr_is_dependent(operand) || operand.value_dependent ||
         operand.references_template_value_parameter) &&
        operand.template_value_expr.valid()) {
        cir::TemplateValueExpression predicate = operand.template_value_expr;
        predicate.loc = loc;
        predicate.definition_context = current_decl_context();
        predicate.definition_lookup_generation = lookup_generation_;
        return {cir::FunctionExceptionSpecKind::Dependent,
                std::move(predicate)};
    }
    int64_t value = 0;
    if (try_evaluate_integer_constant(operand, value)) {
        cir::TypeId operand_type = file_.resolved_type(operand.type);
        bool already_bool = file_.valid(operand_type) &&
            file_.template_value_kind_for_type(operand_type) ==
                cir::TemplateValueKind::Boolean;
        if (!already_bool && value != 0 && value != 1) {

            note_substitution_hard_error();
            report_error(
                "contextual conversion of noexcept specifier operand to "
                "bool is narrowing",
                loc);
            return cir::FunctionExceptionSpecKind::NonThrowing;
        }
        return value != 0 ? cir::FunctionExceptionSpecKind::NonThrowing
                          : cir::FunctionExceptionSpecKind::PotentiallyThrowing;
    }
    if (expr_is_dependent(operand) || in_template_definition_) {
        cir::TemplateValueExpression predicate = operand.template_value_expr;
        if (!predicate.valid() &&
            operand.dependent_value_qualifier.type.valid() &&
            operand.dependent_value_name.valid()) {
            predicate = template_value_operand_expression(operand);
        }
        if (!predicate.valid()) {
            report_error(
                "dependent noexcept specifier has no canonical value graph",
                loc);
            return cir::FunctionExceptionSpecKind::NonThrowing;
        }
        predicate.loc = loc;
        predicate.definition_context = current_decl_context();
        predicate.definition_lookup_generation = lookup_generation_;
        return {cir::FunctionExceptionSpecKind::Dependent,
                std::move(predicate)};
    }
    evaluate_integer_constant(
        operand,
        value,
        loc,
        "noexcept specifier operand is not a constant expression");
    return cir::FunctionExceptionSpecKind::NonThrowing;
}

} // namespace aburi::collect
