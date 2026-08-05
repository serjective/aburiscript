#include "collect.h"

#include <algorithm>
#include <string>

namespace aburi::collect {

namespace {

bool valid_alignment(int64_t value) {
    return value >= 0 && (value == 0 || (value & (value - 1)) == 0);
}

std::optional<int64_t> integer_arg(const ParsedAttribute& attr, size_t index) {
    if (index >= attr.args.size()) {
        return std::nullopt;
    }
    const AttributeArg& arg = attr.args[index];
    if (arg.kind != AttributeArg::Kind::Integer) {
        return std::nullopt;
    }
    return arg.int_value;
}

std::optional<std::string> string_arg(const ParsedAttribute& attr, size_t index) {
    if (index >= attr.args.size()) {
        return std::nullopt;
    }
    const AttributeArg& arg = attr.args[index];
    if (arg.kind == AttributeArg::Kind::String ||
        arg.kind == AttributeArg::Kind::Identifier ||
        arg.kind == AttributeArg::Kind::TokenText) {
        return arg.value;
    }
    return std::nullopt;
}

void retain(std::vector<ParsedAttribute>& dst, const AttributeList& attrs) {
    dst.insert(dst.end(), attrs.attrs.begin(), attrs.attrs.end());
}

bool validate_attribute(Session& session,
                        const ParsedAttribute& attr,
                        AttributeTarget target,
                        SrcLoc fallback_loc) {
    if (attr.kind == AttributeKind::Unknown) {
        return false;
    }
    const AttributeDescriptor* desc = AttributeRegistry::instance().find(attr.kind);
    if (!desc) {
        return false;
    }
    SrcLoc loc = attr.loc.isInvalid() ? fallback_loc : attr.loc;
    if (!attribute_target_contains(desc->targets, target)) {
        bool ignored_always_inline_declaration =
            attr.kind == AttributeKind::AlwaysInline &&
            (target == AttributeTarget::Variable ||
             target == AttributeTarget::Type ||
             target == AttributeTarget::Field ||
             target == AttributeTarget::Label ||
             target == AttributeTarget::Enumerator ||
             target == AttributeTarget::Parameter ||
             target == AttributeTarget::Concept);
        if (ignored_always_inline_declaration) {

            session.report_warning(
                "attribute '" + attr.canonical_name() +
                    "' ignored because it only applies to functions and statements",
                loc);
            return false;
        }
        session.report_error("attribute '" + attr.canonical_name() +
                                 "' cannot be applied to this declaration",
                             loc);
        return false;
    }
    const int count = static_cast<int>(attr.args.size());
    if (count < desc->min_args || (desc->max_args >= 0 && count > desc->max_args)) {
        session.report_error("attribute '" + attr.canonical_name() +
                                 "' has the wrong number of arguments",
                             loc);
        return false;
    }
    return true;
}

void apply_common_entity_attribute(Session& session,
                                   cir::EntityAttributeFacts& facts,
                                   const ParsedAttribute& attr,
                                   SrcLoc fallback_loc) {
    SrcLoc loc = attr.loc.isInvalid() ? fallback_loc : attr.loc;
    switch (attr.kind) {
        case AttributeKind::Aligned: {
            if (auto value = integer_arg(attr, 0)) {
                if (!valid_alignment(*value)) {
                    session.report_error("alignment attribute requires a non-negative power-of-two value",
                                         loc);
                    break;
                }
                if (*value > 0) {
                    facts.requested_alignment =
                        std::max(facts.requested_alignment, static_cast<size_t>(*value));
                }
            }
            break;
        }
        case AttributeKind::Section:
            if (auto value = string_arg(attr, 0)) {
                facts.section = *value;
            }
            break;
        case AttributeKind::Visibility:
        case AttributeKind::TypeVisibility:
            if (auto value = string_arg(attr, 0)) {
                if (*value == "default" || *value == "hidden" || *value == "protected") {
                    facts.visibility = *value;
                } else {
                    session.report_error("visibility attribute expects 'default', 'hidden', or 'protected'",
                                         loc);
                }
            }
            break;
        case AttributeKind::Weak:
            facts.is_weak = true;
            break;
        case AttributeKind::WeakRef:
            if (auto value = string_arg(attr, 0)) {
                facts.weakref_target = *value;
            } else {
                session.report_error("weakref attribute requires a target name", loc);
            }
            break;
        case AttributeKind::Alias:
            if (auto value = string_arg(attr, 0)) {
                facts.alias_target = *value;
            } else {
                session.report_error("alias attribute requires a target name", loc);
            }
            break;
        case AttributeKind::Ifunc:
            if (auto value = string_arg(attr, 0)) {
                facts.ifunc_target = *value;
            } else {
                session.report_error("ifunc attribute requires a resolver name", loc);
            }
            break;
        case AttributeKind::Common:
            facts.is_common = true;
            break;
        case AttributeKind::Used:
            facts.is_used = true;
            break;
        case AttributeKind::ExcludeFromExplicitInstantiation:
            facts.is_excluded_from_explicit_instantiation = true;
            break;
        case AttributeKind::Unused:
        case AttributeKind::MaybeUnused:
            facts.is_unused = true;
            break;
        case AttributeKind::Deprecated:
            facts.is_deprecated = true;
            if (auto value = string_arg(attr, 0)) {
                facts.deprecated_message = *value;
            }
            break;
        case AttributeKind::NoDiscard:
            facts.is_nodiscard = true;
            break;
        case AttributeKind::WarnUnusedResult:
            facts.is_warn_unused_result = true;
            break;
        default:
            break;
    }
}

void apply_function_attribute(Session& session,
                              cir::EntityAttributeFacts& facts,
                              const ParsedAttribute& attr,
                              SrcLoc fallback_loc) {
    SrcLoc loc = attr.loc.isInvalid() ? fallback_loc : attr.loc;
    switch (attr.kind) {
        case AttributeKind::NoReturn:
            facts.is_noreturn = true;
            break;
        case AttributeKind::NoInstrumentFunction:
            // Aburi does not currently inject function-entry instrumentation,
            // so every function already has the behavior requested here.
            break;
        case AttributeKind::AssumeAligned:
            // This optimization hint does not alter the function ABI. Retain
            // it in CIR while lowering remains deliberately conservative.
            break;
        case AttributeKind::GnuInline:
            facts.is_gnu_inline = true;
            break;
        case AttributeKind::NoInline:
            facts.is_noinline = true;
            break;
        case AttributeKind::AlwaysInline:
            facts.is_always_inline = true;
            break;
        case AttributeKind::Cold:
            facts.is_cold = true;
            break;
        case AttributeKind::Hot:
            facts.is_hot = true;
            break;
        case AttributeKind::NoThrow:
            facts.is_nothrow = true;
            break;
        case AttributeKind::Pure:
            facts.is_pure = true;
            break;
        case AttributeKind::Const:
            facts.is_const_function = true;
            break;
        case AttributeKind::Malloc:
            facts.is_malloc = true;
            break;
        case AttributeKind::ReturnsNonNull:
            facts.returns_nonnull = true;
            break;
        case AttributeKind::NonNull:
            if (attr.args.empty()) {
                facts.nonnull_all_pointer_params = true;
            } else {
                for (const AttributeArg& arg : attr.args) {
                    if (arg.kind != AttributeArg::Kind::Integer || arg.int_value <= 0) {
                        session.report_error("nonnull attribute arguments must be positive parameter indices",
                                             arg.loc.isInvalid() ? loc : arg.loc);
                        continue;
                    }
                    facts.nonnull_params.push_back(static_cast<uint32_t>(arg.int_value));
                }
            }
            break;
        case AttributeKind::Constructor:
            facts.constructor_priority =
                static_cast<int>(integer_arg(attr, 0).value_or(65535));
            break;
        case AttributeKind::Destructor:
            facts.destructor_priority =
                static_cast<int>(integer_arg(attr, 0).value_or(65535));
            break;
        case AttributeKind::Format:
            facts.has_format = true;
            break;
        default:
            apply_common_entity_attribute(session, facts, attr, loc);
            break;
    }
}

} // namespace

void Session::apply_attributes(cir::EntityId entity_id,
                               AttributeTarget target,
                               const AttributeList& attrs,
                               SrcLoc loc) {
    if (!file_.valid(entity_id) || attrs.empty()) {
        return;
    }
    cir::Entity& entity = file_.entity_mut(entity_id);
    retain(entity.attr_facts.retained, attrs);

    auto is_function_semantics_attr = [](AttributeKind kind) {
        return kind == AttributeKind::NoReturn ||
               kind == AttributeKind::WarnUnusedResult ||
               kind == AttributeKind::Format ||
               kind == AttributeKind::NonNull ||
               kind == AttributeKind::ReturnsNonNull;
    };
    auto type_is_function_or_function_pointer = [&](cir::TypeId type) {
        cir::TypeId resolved = file_.resolved_type(type);
        if (!file_.valid(resolved)) {
            return false;
        }
        if (file_.type(resolved).kind == cir::TypeKind::Function) {
            return true;
        }
        if (file_.type(resolved).kind == cir::TypeKind::Pointer) {
            cir::TypeId pointee =
                file_.resolved_type(file_.pointer_pointee_ref(resolved).type);
            return file_.valid(pointee) &&
                   file_.type(pointee).kind == cir::TypeKind::Function;
        }

        if (file_.type(resolved).kind == cir::TypeKind::BlockPointer) {
            return true;
        }
        return false;
    };

    for (const ParsedAttribute& attr : attrs.attrs) {
        if (!validate_attribute(*this, attr, target, loc)) {
            continue;
        }

        if ((target == AttributeTarget::Variable ||
             target == AttributeTarget::Field ||
             target == AttributeTarget::Type ||
             (target == AttributeTarget::Parameter &&
              attr.kind != AttributeKind::NonNull)) &&
            is_function_semantics_attr(attr.kind) &&
            !type_is_function_or_function_pointer(entity.type)) {
            report_error("attribute '" + attr.canonical_name() +
                             "' cannot be applied to this declaration",
                         attr.loc.isInvalid() ? loc : attr.loc);
            continue;
        }
        const AttributeDescriptor* desc = AttributeRegistry::instance().find(attr.kind);
        if (!desc || !desc->active_support) {
            continue;
        }
        if (attr.kind == AttributeKind::TransparentUnion) {

            cir::TypeId record_type = file_.resolved_type(entity.type);
            const auto* record_payload = file_.valid(record_type)
                ? std::get_if<cir::RecordTypePayload>(&file_.type_payload(record_type))
                : nullptr;
            cir::RecordFacts* facts = record_payload
                ? file_.record_facts(record_payload->entity)
                : nullptr;
            if (facts && facts->kind == cir::RecordKind::Union) {
                facts->is_transparent_union = true;
            }
            continue;
        }
        if (target == AttributeTarget::Function) {
            apply_function_attribute(*this, entity.attr_facts, attr, loc);
        } else {
            apply_common_entity_attribute(*this, entity.attr_facts, attr, loc);
        }
    }
    if (entity.attr_facts.is_weak) {
        entity.linkage = cir::LinkageKind::External;
    }
}

void Session::register_cleanup_attr(cir::EntityId entity,
                                    cir::TypeId type,
                                    const AttributeList& attrs,
                                    SrcLoc loc) {
    for (const ParsedAttribute& attr : attrs.attrs) {
        if (attr.kind != AttributeKind::Cleanup) {
            continue;
        }
        SrcLoc attr_loc = attr.loc.isInvalid() ? loc : attr.loc;
        if (attr.args.size() != 1 ||
            attr.args[0].kind != AttributeArg::Kind::Identifier) {
            report_error("cleanup attribute requires a function name", attr_loc);
            continue;
        }
        const cir::Binding* binding = lookup_ordinary_binding(attr.args[0].value);
        cir::EntityId function = binding && !binding->entities.empty()
            ? binding->entities.back()
            : cir::EntityId{};
        if (!function.valid() ||
            file_.entity(function).kind != cir::EntityKind::Function) {
            report_error("cleanup argument '" + attr.args[0].value +
                             "' is not a function",
                         attr_loc);
            continue;
        }
        if (cleanup_scopes_.empty()) {
            report_error("cleanup attribute requires block scope", attr_loc);
            continue;
        }
        cleanup_scopes_.back().records.push_back(
            CleanupRecord{{}, entity, type, function, attr_loc,
                          LifetimeOwnerKind::LexicalScope, 0,
                          builder_.current_unwind_target()});
    }
}

size_t Session::requested_alignment_from_attributes(const AttributeList& attrs,
                                                    SrcLoc loc) {
    size_t best = 0;
    for (const ParsedAttribute& attr : attrs.attrs) {
        if (attr.kind != AttributeKind::Aligned) {
            continue;
        }
        if (auto value = integer_arg(attr, 0)) {
            SrcLoc attr_loc = attr.loc.isInvalid() ? loc : attr.loc;
            if (!valid_alignment(*value)) {
                report_error("alignment attribute requires a non-negative power-of-two value",
                             attr_loc);
                continue;
            }
            if (*value > 0) {
                best = std::max(best, static_cast<size_t>(*value));
            }
        }
    }
    return best;
}

void Session::apply_record_attributes(cir::RecordFacts& facts,
                                      cir::RecordKind kind,
                                      const AttributeList& attrs,
                                      SrcLoc loc) {
    retain(facts.attributes, attrs);
    for (const ParsedAttribute& attr : attrs.attrs) {
        if (!validate_attribute(*this, attr, AttributeTarget::Type, loc)) {
            continue;
        }
        const AttributeDescriptor* desc = AttributeRegistry::instance().find(attr.kind);
        if (!desc || !desc->active_support) {
            continue;
        }
        switch (attr.kind) {
            case AttributeKind::Packed:
                facts.is_packed = true;
                break;
            case AttributeKind::TransparentUnion:
                if (kind == cir::RecordKind::Union) {
                    facts.is_transparent_union = true;
                } else {
                    report_error("transparent_union attribute applies only to unions",
                                 attr.loc.isInvalid() ? loc : attr.loc);
                }
                break;
            case AttributeKind::Aligned:
                facts.requested_alignment =
                    std::max(facts.requested_alignment,
                             requested_alignment_from_attributes(AttributeList{{attr}}, loc));
                break;
            default:
                break;
        }
    }
}

void Session::apply_field_attributes(cir::RecordFieldFact& fact,
                                     const AttributeList& attrs,
                                     SrcLoc loc) {
    retain(fact.attributes, attrs);
    for (const ParsedAttribute& attr : attrs.attrs) {
        if (!validate_attribute(*this, attr, AttributeTarget::Field, loc)) {
            continue;
        }
        const AttributeDescriptor* desc = AttributeRegistry::instance().find(attr.kind);
        if (!desc || !desc->active_support) {
            continue;
        }
        switch (attr.kind) {
            case AttributeKind::Packed:
                if (fact.forced_alignment == 0) {
                    fact.storage_alignment_override = 1;
                }
                break;
            case AttributeKind::Aligned:
                fact.forced_alignment =
                    std::max(fact.forced_alignment,
                             requested_alignment_from_attributes(AttributeList{{attr}}, loc));
                break;
            case AttributeKind::Unused:
            case AttributeKind::MaybeUnused:
                break;
            case AttributeKind::NoUniqueAddress: {
                const bool cxx20 = lang_opts_.is_cxx_mode() &&
                    (lang_opts_.standard.empty() ||
                     lang_opts_.is_cxx20_or_later());
                const bool itanium =
                    file_.abi_policy().cxx_abi == CxxAbiKind::Itanium;
                SrcLoc attr_loc = attr.loc.isInvalid() ? loc : attr.loc;
                if (attr.syntax != AttributeSyntax::Standard ||
                    !attr.ns.empty() || !cxx20 || !itanium) {
                    report_warning("attribute '" + attr.canonical_name() +
                                       "' is ignored for this language mode and target ABI",
                                   attr_loc);
                    break;
                }
                if (fact.is_bitfield) {
                    report_error("no_unique_address attribute cannot be applied to a bit-field",
                                 attr_loc);
                    break;
                }
                fact.is_no_unique_address = true;
                break;
            }
            default:
                break;
        }
    }
}

bool Session::try_apply_weak_pragma(std::string_view alias_name,
                                    std::string_view target_name,
                                    SrcLoc loc) {
    const cir::Binding* binding = lookup_ordinary_binding(alias_name);
    if (binding && !binding->entities.empty()) {
        for (cir::EntityId entity_id : binding->entities) {
            cir::Entity& entity = file_.entity_mut(entity_id);
            if (target_name.empty()) {
                entity.attr_facts.is_weak = true;
                continue;
            }
            if (entity.is_definition) {
                report_warning("#pragma weak alias ignored: '" +
                                   std::string(alias_name) +
                                   "' is defined in this translation unit",
                               loc);
                continue;
            }
            entity.attr_facts.weakref_target = std::string(target_name);
            entity.attr_facts.is_weak = true;
        }
        return true;
    }
    if (target_name.empty()) {

        return false;
    }

    const cir::Binding* target_binding = lookup_ordinary_binding(target_name);
    if (!target_binding || target_binding->entities.empty()) {
        return false;
    }

    const cir::Entity target = file_.entity(target_binding->entities.front());
    cir::EntityId alias_entity = builder_.add_entity(target.kind,
                                                     alias_name,
                                                     target.type,
                                                     cir::EntityId{},
                                                     loc,
                                                     target.storage_duration);
    cir::Entity& alias = file_.entity_mut(alias_entity);
    alias.is_definition = false;
    alias.linkage = cir::LinkageKind::External;
    alias.attr_facts.weakref_target = std::string(target_name);
    alias.attr_facts.is_weak = true;
    bind_entity(alias_name,
                cir::LookupNamespace::Ordinary,
                alias_entity,
                target.type,
                false,
                false,
                false,
                cir::InstId{},
                loc);
    return true;
}

void Session::apply_weak_pragma(std::string_view alias_name,
                                std::string_view target_name,
                                SrcLoc loc) {
    if (!try_apply_weak_pragma(alias_name, target_name, loc)) {
        pending_weak_pragmas_.push_back(PendingWeakPragma{
            std::string(alias_name), std::string(target_name), loc});
    }
}

void Session::drain_weak_pragmas() {
    for (const PendingWeakPragma& pending : pending_weak_pragmas_) {
        if (try_apply_weak_pragma(pending.alias, pending.target, pending.loc)) {
            continue;
        }
        if (!pending.target.empty()) {
            report_warning("#pragma weak target '" + pending.target +
                               "' is not declared",
                           pending.loc);
        }
    }
    pending_weak_pragmas_.clear();
}

} // namespace aburi::collect
