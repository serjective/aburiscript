#include "collect.h"
#include "collect_template_state.h"

#include "../abi/endian.h"
#include "../abi/allocation_layout.h"
#include "../abi/mangle_cir.h"
#include "../cir/layout.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>

namespace aburi::collect {

namespace {

size_t align_to(size_t value, size_t alignment) {
    if (alignment <= 1) {
        return value;
    }
    size_t remainder = value % alignment;
    return remainder == 0 ? value : value + (alignment - remainder);
}

uint32_t bitfield_allocation_storage_bits(uint32_t type_bits,
                                          uint32_t declared_width) {
    if (declared_width <= type_bits) {
        return type_bits;
    }
    uint64_t storage = 8;
    while (storage < declared_width && storage <= (uint64_t{1} << 31)) {
        storage <<= 1;
    }
    return storage <= std::numeric_limits<uint32_t>::max()
        ? static_cast<uint32_t>(storage)
        : declared_width;
}

const cir::ArrayTypePayload* incomplete_array_payload(const cir::File& file,
                                                      cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Array) {
        return nullptr;
    }
    const auto* array = std::get_if<cir::ArrayTypePayload>(&file.type_payload(type));
    return array && array->size_kind == cir::ArraySizeKind::Incomplete ? array : nullptr;
}

bool is_complete_record_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file.record_facts_for_type(type);
    return facts && !facts->is_incomplete;
}

bool is_complete_static_data_definition_type(const cir::File& file,
                                             cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return false;
    }
    if (file.type(type).kind == cir::TypeKind::Record) {
        return is_complete_record_type(file, type);
    }
    if (file.type(type).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file.type_payload(type));
        return array &&
            array->size_kind == cir::ArraySizeKind::Constant &&
            is_complete_static_data_definition_type(file,
                                                    array->element_type.type);
    }
    if (file.type(type).kind == cir::TypeKind::Builtin) {
        const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
            &file.type_payload(type));
        return builtin && builtin->kind != cir::BuiltinTypeKind::Void;
    }
    return true;
}

std::string generated_owner_helper_name(const cir::File& file,
                                        cir::EntityId owner,
                                        std::string_view prefix,
                                        uint32_t fallback_index) {
    std::string owner_symbol = abi::itanium_linkage_name(file, owner);
    if (owner_symbol.empty() && owner.valid() && file.valid(owner) &&
        file.entity(owner).name.valid()) {
        owner_symbol = std::string(file.name(file.entity(owner).name));
    }
    if (owner_symbol.empty()) {
        return std::string(prefix) + std::to_string(fallback_index);
    }
    return std::string(prefix) + owner_symbol;
}

enum class NonStaticMemberTypeIssue : uint8_t {
    None,
    Incomplete,
    Abstract,
};

NonStaticMemberTypeIssue nonstatic_member_type_issue(const cir::File& file,
                                                      cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return NonStaticMemberTypeIssue::Incomplete;
    }
    if (file.type(type).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file.type_payload(type));
        if (!array || array->size_kind == cir::ArraySizeKind::Incomplete) {
            return NonStaticMemberTypeIssue::Incomplete;
        }
        return nonstatic_member_type_issue(file, array->element_type.type);
    }
    if (file.type(type).kind != cir::TypeKind::Record) {
        return NonStaticMemberTypeIssue::None;
    }
    const cir::RecordFacts* facts = file.record_facts_for_type(type);
    if (!facts || facts->is_incomplete) {
        return NonStaticMemberTypeIssue::Incomplete;
    }
    return facts->is_abstract ? NonStaticMemberTypeIssue::Abstract
                              : NonStaticMemberTypeIssue::None;
}

bool record_kinds_agree(cir::RecordKind lhs, cir::RecordKind rhs) {
    return (lhs == cir::RecordKind::Union) ==
           (rhs == cir::RecordKind::Union);
}

std::string enum_type_spelling(std::string_view tag, bool is_scoped) {
    return std::string(is_scoped ? "enum class " : "enum ") +
           std::string(tag);
}

bool enum_value_fits_underlying(const cir::File& file,
                                cir::TypeRef underlying,
                                int64_t value) {
    cir::IntegerTypeShape shape =
        cir::integer_shape_for_type(file, underlying.type);
    if (shape.bit_width == 0) {
        return true;
    }
    if (shape.is_unsigned) {
        if (shape.bit_width >= 64) {

            return true;
        }
        if (value < 0) {
            return false;
        }
        return shape.bit_width >= 63 ||
               static_cast<uint64_t>(value) <
                   (uint64_t{1} << shape.bit_width);
    }
    if (shape.bit_width >= 64) {
        return true;
    }
    int64_t minimum = -(int64_t{1} << (shape.bit_width - 1));
    int64_t maximum = (int64_t{1} << (shape.bit_width - 1)) - 1;
    return value >= minimum && value <= maximum;
}

bool is_anonymous_record_member(const cir::File& file, const cir::RecordFieldFact& field) {
    return !field.name.valid() &&
           !field.is_bitfield &&
           is_complete_record_type(file, field.type.type);
}

bool is_supported_literal_type(const cir::File& file, cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return false;
    }
    switch (file.type(resolved).kind) {
        case cir::TypeKind::Builtin: {
            const auto* builtin =
                std::get_if<cir::BuiltinTypePayload>(&file.type_payload(resolved));
            return builtin &&
                   builtin->kind != cir::BuiltinTypeKind::Other;
        }
        case cir::TypeKind::BitInt:
        case cir::TypeKind::Enum:
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
        case cir::TypeKind::MemberPointer:
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return true;
        case cir::TypeKind::Array: {
            const auto* array =
                std::get_if<cir::ArrayTypePayload>(&file.type_payload(resolved));
            return array && is_supported_literal_type(file,
                                                      array->element_type.type);
        }
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts = file.record_facts_for_type(resolved);
            return facts && facts->is_literal_class_type;
        }
        default:
            return false;
    }
}

bool record_has_supported_literal_class_shape(
    const cir::File& file,
    const cir::RecordFacts& facts) {
    if (facts.is_incomplete || facts.is_polymorphic ||
        facts.definition_data.has_deleted_destructor ||
        !facts.dependent_bases.empty() ||
        !facts.virtual_bases.empty()) {
        return false;
    }
    for (const cir::RecordMethodFact& method : facts.methods) {
        if (!method.entity.valid() ||
            file.entity(method.entity).kind != cir::EntityKind::Destructor) {
            continue;
        }
        if (!method.is_constexpr && !method.is_consteval &&
            !method.is_defaulted) {
            return false;
        }
    }
    for (const cir::RecordBaseFact& base : facts.bases) {
        const cir::RecordFacts* base_facts =
            file.record_facts_for_type(base.type.type);
        if (!base_facts || !base_facts->is_literal_class_type) {
            return false;
        }
    }
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage) {
            continue;
        }
        if (!is_supported_literal_type(file, field.type.type)) {
            return false;
        }
    }
    return true;
}

struct SpecialMemberSourceForm {
    ValueCategory category = ValueCategory::LValue;
    uint8_t qualifiers = cir::QualNone;
};

std::optional<SpecialMemberSourceForm> special_member_source_form(
    const cir::File& file,
    const cir::RecordMethodFact& method) {
    const auto* payload = std::get_if<cir::FunctionTypePayload>(
        &file.type_payload(file.resolved_type(method.type.type)));
    if (!payload || payload->parameters.empty()) {
        return std::nullopt;
    }
    cir::TypeId parameter =
        file.resolved_type(payload->parameters.front().type);
    if (!file.valid(parameter)) {
        return std::nullopt;
    }
    cir::TypeKind kind = file.type(parameter).kind;
    if (kind == cir::TypeKind::LValueReference ||
        kind == cir::TypeKind::RValueReference) {
        cir::TypeRef referred = file.reference_referred_ref(parameter);
        return SpecialMemberSourceForm{
            kind == cir::TypeKind::RValueReference
                ? ValueCategory::XValue
                : ValueCategory::LValue,
            referred.qualifiers};
    }

    return SpecialMemberSourceForm{};
}

const cir::RecordMethodFact* canonical_special_member(
    const cir::File& file,
    cir::TypeId type,
    cir::SpecialMemberKind kind,
    bool permit_copy_fallback = false,
    std::optional<SpecialMemberSourceForm> source = std::nullopt) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return nullptr;
    }
    if (file.type(type).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file.type_payload(type));
        return array ? canonical_special_member(file,
                                                array->element_type.type,
                                                kind,
                                                permit_copy_fallback,
                                                source)
                     : nullptr;
    }
    const cir::RecordFacts* facts = file.record_facts_for_type(type);
    if (!facts) {
        return nullptr;
    }
    auto find_unary = [&](cir::SpecialMemberKind requested)
        -> const cir::RecordMethodFact* {
        const cir::RecordMethodFact* deleted = nullptr;
        for (const cir::RecordMethodFact& method : facts->methods) {
            if (method.special_member_kind != requested ||
                method.constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Unsatisfied ||
                method.constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Invalid) {
                continue;
            }
            if (requested == cir::SpecialMemberKind::Destructor &&
                !method.is_selected_destructor) {
                continue;
            }
            if (!method.is_deleted) {
                return &method;
            }
            deleted = &method;
        }
        return deleted;
    };
    const bool is_transfer =
        kind == cir::SpecialMemberKind::CopyConstructor ||
        kind == cir::SpecialMemberKind::MoveConstructor ||
        kind == cir::SpecialMemberKind::CopyAssignment ||
        kind == cir::SpecialMemberKind::MoveAssignment;
    if (!is_transfer) {
        return find_unary(kind);
    }

    if (!source) {
        source = SpecialMemberSourceForm{
            kind == cir::SpecialMemberKind::MoveConstructor ||
                    kind == cir::SpecialMemberKind::MoveAssignment
                ? ValueCategory::XValue
                : ValueCategory::LValue,
            cir::QualNone};
    }
    struct RankedCandidate {
        const cir::RecordMethodFact* method = nullptr;
        bool by_value = false;
        int reference_rank = 0;
        int added_qualifiers = 0;
    };
    auto more_constrained = [](const cir::RecordMethodFact& lhs,
                               const cir::RecordMethodFact& rhs) {
        return std::find(lhs.more_constrained_than.begin(),
                         lhs.more_constrained_than.end(),
                         rhs.associated_constraint_fingerprint) !=
            lhs.more_constrained_than.end();
    };
    auto compare = [&](const RankedCandidate& lhs,
                       const RankedCandidate& rhs) {

        if (lhs.by_value != rhs.by_value) {
            return 0;
        }
        if (lhs.reference_rank != rhs.reference_rank) {
            return lhs.reference_rank < rhs.reference_rank ? -1 : 1;
        }
        if (lhs.added_qualifiers != rhs.added_qualifiers) {
            return lhs.added_qualifiers < rhs.added_qualifiers ? -1 : 1;
        }
        if (more_constrained(*lhs.method, *rhs.method)) {
            return -1;
        }
        if (more_constrained(*rhs.method, *lhs.method)) {
            return 1;
        }
        return 0;
    };

    std::optional<RankedCandidate> best;
    bool ambiguous = false;
    for (const cir::RecordMethodFact& method : facts->methods) {
        bool exact_kind = method.special_member_kind == kind;
        bool copy_fallback = permit_copy_fallback &&
            ((kind == cir::SpecialMemberKind::MoveConstructor &&
              method.special_member_kind ==
                  cir::SpecialMemberKind::CopyConstructor) ||
             (kind == cir::SpecialMemberKind::MoveAssignment &&
              method.special_member_kind ==
                  cir::SpecialMemberKind::CopyAssignment));
        if ((!exact_kind && !copy_fallback) ||
            method.constraint_satisfaction ==
                cir::ConstraintSatisfactionKind::Unsatisfied ||
            method.constraint_satisfaction ==
                cir::ConstraintSatisfactionKind::Invalid) {
            continue;
        }
        if (method.is_deleted && method.is_defaulted &&
            (method.special_member_kind ==
                 cir::SpecialMemberKind::MoveConstructor ||
             method.special_member_kind ==
                 cir::SpecialMemberKind::MoveAssignment)) {
            continue;
        }
        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &file.type_payload(file.resolved_type(method.type.type)));
        if (!payload || payload->parameters.empty()) {
            continue;
        }
        cir::TypeId parameter =
            file.resolved_type(payload->parameters.front().type);
        if (!file.valid(parameter)) {
            continue;
        }
        RankedCandidate candidate;
        candidate.method = &method;
        cir::TypeKind parameter_kind = file.type(parameter).kind;
        if (parameter_kind != cir::TypeKind::LValueReference &&
            parameter_kind != cir::TypeKind::RValueReference) {
            if (file.resolved_type(parameter) != type) {
                continue;
            }
            candidate.by_value = true;
        } else {
            cir::TypeRef referred = file.reference_referred_ref(parameter);
            if (file.resolved_type(referred.type) != type ||
                (source->qualifiers &
                 static_cast<uint8_t>(~referred.qualifiers)) != 0) {
                continue;
            }
            if (parameter_kind == cir::TypeKind::RValueReference) {
                if (source->category == ValueCategory::LValue) {
                    continue;
                }
            } else if (source->category != ValueCategory::LValue) {

                if ((referred.qualifiers & cir::QualConst) == 0 ||
                    (referred.qualifiers & cir::QualVolatile) != 0) {
                    continue;
                }
                candidate.reference_rank = 1;
            }
            uint8_t added = static_cast<uint8_t>(
                referred.qualifiers & ~source->qualifiers);
            candidate.added_qualifiers =
                ((added & cir::QualConst) != 0 ? 1 : 0) +
                ((added & cir::QualVolatile) != 0 ? 1 : 0);
        }
        if (!best) {
            best = candidate;
            ambiguous = false;
            continue;
        }
        int ordering = compare(candidate, *best);
        if (ordering < 0) {
            best = candidate;
            ambiguous = false;
        } else if (ordering == 0) {
            ambiguous = true;
        }
    }
    return best && !ambiguous ? best->method : nullptr;
}

bool scalar_or_reference_special_member_is_trivial(const cir::File& file,
                                                   cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return false;
    }
    if (file.type(type).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file.type_payload(type));
        return array && scalar_or_reference_special_member_is_trivial(
                            file, array->element_type.type);
    }
    return file.type(type).kind != cir::TypeKind::Record;
}

cir::TemplateParameterPattern template_parameter_pattern_from(
    const Session::TemplateParameter& parameter) {
    cir::TemplateParameterPattern pattern;
    pattern.is_parameter_pack = parameter.is_parameter_pack;
    switch (parameter.kind) {
        case Session::TemplateParameterKind::Type:
            pattern.kind = cir::TemplateParameterPatternKind::Type;
            pattern.type_param_type = parameter.type_param_type;
            break;
        case Session::TemplateParameterKind::NonType:
            pattern.kind = cir::TemplateParameterPatternKind::NonType;
            pattern.non_type_type = cir::TypeRef{
                parameter.non_type_type,
                cir::QualNone,
                cir::MemorySpace::Default};
            break;
        case Session::TemplateParameterKind::Template:
            pattern.kind = cir::TemplateParameterPatternKind::Template;
            pattern.template_parameters.reserve(
                parameter.nested_parameters().size());
            for (const Session::TemplateParameter& inner :
                 parameter.nested_parameters()) {
                pattern.template_parameters.push_back(
                    template_parameter_pattern_from(inner));
            }
            break;
    }
    return pattern;
}

std::vector<cir::TemplateParameterPattern> template_parameter_patterns_from(
    const std::vector<Session::TemplateParameter>& parameters) {
    std::vector<cir::TemplateParameterPattern> patterns;
    patterns.reserve(parameters.size());
    for (const Session::TemplateParameter& parameter : parameters) {
        patterns.push_back(template_parameter_pattern_from(parameter));
    }
    return patterns;
}

cir::RecordStaticDataMemberFact make_record_static_data_member_fact(
    cir::File& file,
    const RecordStaticDataMemberInput& member) {
    cir::RecordStaticDataMemberFact fact;
    fact.name = member.name.empty()
        ? cir::NameId{}
        : file.intern_name(member.name);
    fact.entity = member.entity;
    fact.type = file.type_ref(member.type,
                              member.flags.type_qualifiers);
    fact.declared_access = member.declared_access;
    fact.is_constexpr = member.flags.is_constexpr;
    fact.is_consteval = member.flags.is_consteval;
    fact.is_inline = member.flags.is_inline;
    fact.has_in_class_initializer =
        member.initializer.has_value() ||
        member.has_deferred_initializer;
    fact.initializer_begin = member.initializer_begin;
    fact.initializer_end = member.initializer_end;
    fact.initializer_loc = member.initializer_loc;
    fact.initializer_context = member.initializer_context;
    fact.initializer_lookup_generation =
        member.initializer_lookup_generation;
    fact.initializer_value_expression =
        member.initializer_value_expression;
    AttributeList member_attrs = member.flags.attrs;
    member_attrs.append(member.attrs);
    fact.attributes = std::move(member_attrs.attrs);
    return fact;
}

} // namespace

bool Session::is_literal_type(cir::TypeId type) const {
    return is_supported_literal_type(file_, type);
}

RecordDeclResult Session::declare_record_tag(cir::RecordKind kind,
                                             std::string_view tag_view,
                                             SrcLoc loc) {
    std::string tag(tag_view);
    if (tag.empty()) {
        tag = anonymous_record_name(kind);
    }

    TagLookupResult lookup = lookup_record_tag(tag, kind, TagLookupMode::Visible);
    if (lookup.found) {
        if (lookup.kind_mismatch) {
            report_error("tag '" + tag + "' was previously declared as a different kind", loc);
        } else if (!lookup.binding) {
            bind_entity(tag, cir::LookupNamespace::Tag, lookup.entity,
                        lookup.type, true, false, false, {}, loc);
            if (lang_opts_.is_cxx_mode()) {
                bind_entity(tag, cir::LookupNamespace::Ordinary,
                            lookup.entity, lookup.type, true, false, false,
                            {}, loc);
            }
        }
        return RecordDeclResult{lookup.entity, lookup.type, false, lookup.kind_mismatch};
    }

    return create_record_tag(kind, std::move(tag), loc);
}

RecordDeclResult Session::declare_record_tag_in_current_scope(cir::RecordKind kind,
                                                              std::string_view tag_view,
                                                              SrcLoc loc,
                                                              cir::EntityId record_to_redeclare) {
    std::string tag(tag_view);
    if (tag.empty()) {
        tag = anonymous_record_name(kind);
    }

    if (record_to_redeclare.valid() &&
        file_.valid(record_to_redeclare) &&
        file_.entity(record_to_redeclare).kind == cir::EntityKind::Record) {
        cir::Entity& entity = file_.entity_mut(record_to_redeclare);
        if (!entity.lexical_context.valid()) {
            entity.lexical_context = current_decl_context();
        }
        if (!entity.semantic_context.valid()) {
            entity.semantic_context = file_.create_decl_context(
                cir::DeclContextKind::Record,
                current_decl_context(),
                record_to_redeclare,
                loc);
        }
        bind_entity(tag,
                    cir::LookupNamespace::Tag,
                    record_to_redeclare,
                    entity.type,
                    true,
                    false,
                    false,
                    {},
                    loc);
        if (lang_opts_.is_cxx_mode() && !tag.empty()) {
            bind_entity(tag,
                        cir::LookupNamespace::Ordinary,
                        record_to_redeclare,
                        entity.type,
                        true,
                        false,
                        false,
                        {},
                        loc);
        }
        bool mismatch = false;
        if (const cir::RecordFacts* facts =
                file_.record_facts(record_to_redeclare)) {
            mismatch = !record_kinds_agree(facts->kind, kind);
        }
        if (mismatch) {
            report_error("tag '" + tag +
                             "' was previously declared as a different kind",
                         loc);
        }
        return RecordDeclResult{record_to_redeclare,
                                entity.type,
                                false,
                                mismatch};
    }

    TagLookupResult lookup = lookup_record_tag(tag, kind, TagLookupMode::CurrentOnly);
    if (lookup.found) {
        if (lookup.kind_mismatch) {
            report_error("tag '" + tag + "' was previously declared as a different kind", loc);
        } else if (!lookup.binding) {
            bind_entity(tag, cir::LookupNamespace::Tag, lookup.entity,
                        lookup.type, true, false, false, {}, loc);
            if (lang_opts_.is_cxx_mode()) {
                bind_entity(tag, cir::LookupNamespace::Ordinary,
                            lookup.entity, lookup.type, true, false, false,
                            {}, loc);
            }
        }
        return RecordDeclResult{lookup.entity, lookup.type, false, lookup.kind_mismatch};
    }

    return create_record_tag(kind, std::move(tag), loc);
}

cir::EntityId Session::hidden_friend_record_entity(
    std::string_view name,
    cir::DeclContextId context,
    cir::ModuleAttachmentId module_attachment) const {
    if (name.empty() || !context.valid()) {
        return {};
    }
    for (const TemplateState::HiddenFriendRecordIdentity& identity :
         tstate().hidden_friend_record_identities_) {
        if (identity.context == context && identity.name == name &&
            identity.module_attachment == module_attachment &&
            identity.entity.valid() && file_.valid(identity.entity)) {
            return identity.entity;
        }
    }
    return {};
}

RecordDeclResult Session::declare_hidden_friend_record(
    cir::RecordKind kind,
    std::string_view tag_view,
    cir::DeclContextId target_context,
    SrcLoc loc) {
    std::string tag(tag_view);
    if (tag.empty() || !target_context.valid() ||
        !file_.valid(target_context)) {
        return {};
    }

    cir::ModuleAttachmentId module_attachment{};
    for (cir::DeclContextId context = current_decl_context();
         context.valid() && file_.valid(context);
         context = file_.decl_context(context).parent) {
        cir::EntityId owner = file_.decl_context(context).owner;
        if (owner.valid() && file_.valid(owner) &&
            file_.entity(owner).module_attachment.valid()) {
            module_attachment = file_.entity(owner).module_attachment;
            break;
        }
    }
    if (cir::EntityId existing = hidden_friend_record_entity(
            tag, target_context, module_attachment);
        existing.valid()) {
        const cir::RecordFacts* prior = file_.record_facts(existing);
        bool mismatch = prior && !record_kinds_agree(prior->kind, kind);
        if (mismatch) {
            report_error("tag '" + tag +
                             "' was previously declared as a different kind",
                         loc);
        }
        return RecordDeclResult{existing, file_.entity(existing).type,
                                mismatch, mismatch};
    }

    cir::EntityId entity = builder_.add_entity(
        cir::EntityKind::Record, tag, {}, {}, loc);
    cir::TypeId type = builder_.record_type(
        entity, std::string(cir::record_kind_name(kind)) + " " + tag);
    cir::Entity& record = file_.entity_mut(entity);
    record.type = type;
    record.is_definition = false;
    record.lexical_context = target_context;
    record.semantic_context = file_.create_decl_context(
        cir::DeclContextKind::Record, target_context, entity, loc);
    record.module_attachment = module_attachment;

    cir::RecordFacts facts;
    facts.entity = entity;
    facts.type = file_.type_ref(type);
    facts.kind = kind;
    facts.is_incomplete = true;
    file_.set_record_facts(entity, std::move(facts));

    TemplateState::HiddenFriendRecordIdentity identity;
    identity.name = tag;
    identity.context = target_context;
    identity.kind = kind;
    identity.module_attachment = module_attachment;
    identity.entity = entity;
    tstate().hidden_friend_record_identities_.push_back(std::move(identity));
    track_speculative_rollback([this, entity] {
        auto found = std::find_if(
            tstate().hidden_friend_record_identities_.begin(),
            tstate().hidden_friend_record_identities_.end(),
            [entity](const TemplateState::HiddenFriendRecordIdentity& prior) {
                return prior.entity == entity;
            });
        if (found != tstate().hidden_friend_record_identities_.end()) {
            tstate().hidden_friend_record_identities_.erase(found);
        }
    });
    return RecordDeclResult{entity, type, false, false};
}

RecordDeclResult Session::begin_record_definition(cir::RecordKind kind,
                                                  std::string_view tag_view,
                                                  SrcLoc loc,
                                                  cir::EntityId record_to_complete) {
    if (collecting_pattern_ && current_function_.valid()) {

        mark_pattern_unusable();
    }

    TemplateState::CurrentInstantiationFrame* innermost_instantiation =
        tstate().current_instantiation_frames_.empty()
            ? nullptr
            : &tstate().current_instantiation_frames_.back();
    bool completing_named_shell =
        innermost_instantiation &&
        innermost_instantiation->record_to_complete.valid() &&
        file_.valid(innermost_instantiation->record_to_complete) &&
        file_.name(file_.entity(
                       innermost_instantiation->record_to_complete)
                       .name) == tag_view;
    bool claim_current_instantiation =
        innermost_instantiation && innermost_instantiation->info &&
        !innermost_instantiation->record.valid() &&
        (innermost_instantiation->info->name == tag_view ||
         innermost_instantiation->display_name == tag_view ||
         completing_named_shell);
    TemplateState::CurrentInstantiationFrame* current_instantiation_frame =
        claim_current_instantiation ? &tstate().current_instantiation_frames_.back()
                                    : nullptr;
    std::string tag(tag_view);
    bool anonymous = tag.empty();
    if (anonymous) {
        tag = anonymous_record_name(kind);
    }

    RecordDeclResult decl;
    if (anonymous) {
        decl = create_record_tag(kind, tag, loc, false);
    } else if (record_to_complete.valid()) {
        decl = declare_record_tag_in_current_scope(kind,
                                                   tag,
                                                   loc,
                                                   record_to_complete);
    } else if (current_instantiation_frame &&
               current_instantiation_frame->record_to_complete.valid() &&
               file_.valid(current_instantiation_frame->record_to_complete) &&
               file_.entity(current_instantiation_frame->record_to_complete).kind ==
                   cir::EntityKind::Record) {
        cir::EntityId entity =
            current_instantiation_frame->record_to_complete;

        file_.entity_mut(entity).is_template_pattern =
            current_instantiation_frame->replays_as_template_pattern;
        if (!file_.entity(entity).semantic_context.valid()) {
            file_.entity_mut(entity).semantic_context =
                file_.create_decl_context(cir::DeclContextKind::Record,
                                          current_decl_context(),
                                          entity,
                                          loc);
        }
        bind_entity(tag,
                    cir::LookupNamespace::Tag,
                    entity,
                    file_.entity(entity).type,
                    true,
                    false,
                    false,
                    {},
                    loc);
        if (lang_opts_.is_cxx_mode() && !tag.empty()) {
            bind_entity(tag,
                        cir::LookupNamespace::Ordinary,
                        entity,
                        file_.entity(entity).type,
                        true,
                        false,
                        false,
                        {},
                        loc);
        }
        decl = RecordDeclResult{entity, file_.entity(entity).type, false, false};
    } else {
        TagLookupResult current = lookup_record_tag(tag, kind, TagLookupMode::CurrentOnly);
        if (current.found) {
            if (current.kind_mismatch) {
                report_error("tag '" + tag + "' was previously declared as a different kind", loc);
            } else if (!current.binding) {
                bind_entity(tag, cir::LookupNamespace::Tag, current.entity,
                            current.type, true, false, false, {}, loc);
                if (lang_opts_.is_cxx_mode()) {
                    bind_entity(tag, cir::LookupNamespace::Ordinary,
                                current.entity, current.type, true, false,
                                false, {}, loc);
                }
            }
            decl = RecordDeclResult{current.entity, current.type, false, current.kind_mismatch};
        } else {
            decl = create_record_tag(kind, tag, loc);
        }
    }

    if (decl.entity.valid() && file_.valid(decl.entity)) {
        cir::Entity& record = file_.entity_mut(decl.entity);
        record.is_unnamed_record = anonymous;
        cir::DeclContextId context = current_decl_context();
        if (lang_opts_.is_cxx_mode() && anonymous &&
            !record.local_enclosing_function.valid() && context.valid() &&
            file_.valid(context) &&
            file_.decl_context(context).kind ==
                cir::DeclContextKind::Record) {
            uint32_t ordinal = 0;
            for (cir::EntityId prior_id : file_.entity_ids()) {
                if (prior_id == decl.entity || !file_.valid(prior_id)) {
                    continue;
                }
                const cir::Entity& prior = file_.entity(prior_id);
                if (prior.kind == cir::EntityKind::Record &&
                    prior.is_unnamed_record &&
                    prior.lexical_context == context &&
                    prior.unnamed_type_ordinal !=
                        cir::Entity::NoUnnamedTypeOrdinal &&
                    !prior.unnamed_type_linkage_name.valid()) {
                    ++ordinal;
                }
            }
            record.unnamed_type_ordinal = ordinal;
        }
        if (context.valid() && file_.valid(context) &&
            file_.decl_context(context).kind ==
                cir::DeclContextKind::Record) {
            auto active_access = record_member_access_by_context_.find(
                static_cast<uint64_t>(context.index));
            if (active_access != record_member_access_by_context_.end()) {
                record_member_declaration(
                    decl.entity,
                    file_.decl_context(context).owner,
                    active_access->second,
                    loc);
            }
        }
    }

    if (const cir::RecordFacts* facts = file_.record_facts(decl.entity)) {
        if (!facts->is_incomplete) {
            // The [module.unit] ODR invariant folds matching global-module
            // definitions across units while rejecting duplicates within one.
            const cir::Entity& existing = file_.entity(decl.entity);
            cir::File::ActiveModuleContext active =
                file_.active_module_context();
            bool global_module_refold =
                file_.has_module_units() &&
                !existing.module_attachment.valid() &&
                existing.origin_unit != active.unit &&
                (active.fragment == cir::ModuleFragment::Global ||
                 !active.unit.valid());
            if (global_module_refold) {
                decl.fold_duplicate_definition = true;
            } else {
                report_error("redefinition of " + std::string(cir::record_kind_name(kind)) + " '" + tag + "'", loc);
                decl.has_error = true;
            }
        }
        if (!record_kinds_agree(facts->kind, kind)) {
            report_error("tag '" + tag + "' was previously declared as a different kind", loc);
            decl.has_error = true;
        }
    }
    if (decl.entity.valid() && file_.valid(decl.entity) &&
        !file_.record_facts(decl.entity)) {

        cir::RecordFacts facts;
        facts.entity = decl.entity;
        facts.type = file_.type_ref(decl.type);
        facts.kind = kind;
        facts.is_incomplete = true;
        file_.set_record_facts(decl.entity, std::move(facts));
    }

    if (claim_current_instantiation && decl.entity.valid()) {
        TemplateState::CurrentInstantiationFrame& frame = *current_instantiation_frame;
        frame.record = decl.entity;
        if (!frame.display_name.empty()) {

            rename_entity(decl.entity, frame.display_name);
            remember_template_specialization(decl.entity, *frame.info,
                                           frame.arguments,
                                           frame.point_of_instantiation,
                                           frame.point_lookup_generation);
        }
        file_.entity_mut(decl.entity).is_definition = true;
    }
    return decl;
}

RecordDeclResult Session::begin_explicit_member_record_specialization(
    cir::RecordKind kind,
    std::string_view tag_view,
    SrcLoc loc) {
    std::string tag(tag_view);
    if (tag.empty()) {
        tag = anonymous_record_name(kind);
    }
    RecordDeclResult decl = create_record_tag(kind, tag, loc, true);
    if (decl.entity.valid() && file_.valid(decl.entity)) {
        file_.entity_mut(decl.entity).is_explicit_template_specialization =
            true;
    }
    return decl;
}

RecordDeclResult Session::define_record(cir::RecordKind kind,
                                        std::string_view tag,
                                        std::vector<RecordFieldInput> fields,
                                        SrcLoc loc,
                                        RecordLayoutOptions layout_options) {
    RecordDeclResult decl = begin_record_definition(kind, tag, loc);
    if (decl.fold_duplicate_definition) {

        return decl;
    }
    return finish_record_definition(std::move(decl),
                                    kind,
                                    std::move(fields),
                                    {},
                                    {},
                                    loc,
                                    layout_options);
}

bool Session::complete_anonymous_union_object(
    cir::TypeId union_type,
    cir::EntityId object,
    cir::AnonymousUnionObjectKind kind,
    cir::DeclContextId parent_context,
    SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(union_type);
    cir::EntityId record = file_.record_entity(resolved);
    const cir::RecordFacts* published =
        record.valid() ? file_.record_facts(record) : nullptr;
    if (!published || published->is_incomplete ||
        published->kind != cir::RecordKind::Union ||
        !file_.entity(record).is_unnamed_record) {
        report_error("anonymous union requires a complete unnamed union type",
                     loc);
        return false;
    }

    bool valid = true;
    cir::RecordFacts facts = *published;
    facts.is_anonymous_union_definition = true;
    facts.anonymous_union_object_kind = kind;
    facts.anonymous_union_object = object;
    facts.anonymous_union_parent_context = parent_context;
    facts.anonymous_union_promotions.clear();
    auto append_promotions =
        [&](auto&& self,
            const cir::RecordFacts& owner,
            std::vector<cir::EntityId>& path) -> void {
            for (const cir::RecordFieldFact& field : owner.fields) {
                if (field.is_base_subobject ||
                    field.is_virtual_base_storage) {
                    continue;
                }
                path.push_back(field.entity);
                if (field.name.valid()) {
                    cir::AnonymousUnionPromotionFact promotion;
                    promotion.name = field.name;
                    promotion.member = field.entity;
                    promotion.path = path;
                    facts.anonymous_union_promotions.push_back(
                        std::move(promotion));
                } else if (is_anonymous_record_member(file_, field)) {
                    const cir::RecordFacts* nested =
                        file_.record_facts_for_type(field.type.type);
                    if (nested && !nested->is_incomplete) {
                        self(self, *nested, path);
                    }
                }
                path.pop_back();
            }
        };
    std::vector<cir::EntityId> promotion_path;
    append_promotions(append_promotions, facts, promotion_path);
    for (const cir::AnonymousUnionPromotionFact& promotion :
         facts.anonymous_union_promotions) {
        if (promotion.member.valid() &&
            file_.valid(promotion.member)) {
            file_.entity_mut(promotion.member).declaring_record = record;
        }
    }
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage) {
            continue;
        }
        if (field.declared_access != cir::RecordMemberAccess::Public) {
            report_error("anonymous union members must be public",
                         file_.entity(field.entity).loc);
            valid = false;
        }
    }
    for (const cir::RecordMethodFact& method : facts.methods) {
        if (!method.is_implicitly_declared) {
            report_error("functions cannot be declared in an anonymous union",
                         method.entity.valid() && file_.valid(method.entity)
                             ? file_.entity(method.entity).loc
                             : loc);
            valid = false;
        }
    }
    if (!facts.static_data_members.empty()) {
        for (const cir::RecordStaticDataMemberFact& member :
             facts.static_data_members) {
            report_error(
                "static data members cannot be declared in an anonymous union",
                member.entity.valid() && file_.valid(member.entity)
                    ? file_.entity(member.entity).loc
                    : loc);
        }
        valid = false;
    }
    if (!facts.class_friends.empty() || !facts.function_friends.empty()) {
        report_error("friend declarations are not allowed in an anonymous union",
                     loc);
        valid = false;
    }
    cir::DeclContextId union_context = file_.entity(record).semantic_context;
    auto is_promoted_anonymous_record =
        [&](cir::EntityId candidate) {
            for (const cir::RecordFieldFact& field : facts.fields) {
                if (!is_anonymous_record_member(file_, field)) {
                    continue;
                }
                cir::EntityId field_record =
                    file_.record_entity(field.type.type);
                if (field_record == candidate) {
                    return true;
                }
            }
            return false;
        };
    if (union_context.valid() && file_.valid(union_context)) {
        const cir::DeclContext& context = file_.decl_context(union_context);
        for (cir::DeclContextId child_id : context.children) {
            if (!child_id.valid() || !file_.valid(child_id)) {
                continue;
            }
            const cir::DeclContext& child = file_.decl_context(child_id);
            if (child.owner.valid() && child.owner != record &&
                file_.valid(child.owner) &&
                (file_.entity(child.owner).kind == cir::EntityKind::Record ||
                 file_.entity(child.owner).kind == cir::EntityKind::Enum) &&
                !is_promoted_anonymous_record(child.owner)) {
                report_error("nested types cannot be declared in an anonymous union",
                             file_.entity(child.owner).loc);
                valid = false;
            }
        }
        for (cir::BindingId binding_id : context.bindings) {
            if (!binding_id.valid() || !file_.valid(binding_id)) {
                continue;
            }
            const cir::Binding& binding = file_.binding(binding_id);
            for (cir::EntityId entity : binding.entities) {
                if (!entity.valid() || !file_.valid(entity) ||
                    entity == record) {
                    continue;
                }
                cir::EntityKind entity_kind = file_.entity(entity).kind;
                if (entity_kind == cir::EntityKind::TypeAlias ||
                    entity_kind == cir::EntityKind::Record ||
                    entity_kind == cir::EntityKind::Enum) {
                    if (entity_kind == cir::EntityKind::Record &&
                        is_promoted_anonymous_record(entity)) {
                        continue;
                    }
                    report_error("nested types cannot be declared in an anonymous union",
                                 file_.entity(entity).loc);
                    valid = false;
                }
            }
        }
    }
    if (file_.valid(object)) {
        cir::Entity& object_entity = file_.entity_mut(object);
        object_entity.object_origin = cir::EntityObjectOrigin::AnonymousUnion;
        if (kind != cir::AnonymousUnionObjectKind::Member) {

            object_entity.name = !facts.anonymous_union_promotions.empty()
                ? facts.anonymous_union_promotions.front().name
                : file_.intern_name(
                      "__aburi_anonymous_union_object_" +
                      std::to_string(object.index));
            if (object_entity.local_enclosing_function.valid()) {
                object_entity.local_source_name = object_entity.name;
                object_entity.local_name_kind =
                    cir::LocalNameComponentKind::SourceName;
            }
        }
    }

    for (const cir::RecordMethodFact& method : facts.methods) {
        if (!method.is_implicitly_declared || !method.entity.valid() ||
            !file_.valid(method.entity)) {
            continue;
        }
        cir::Entity& entity = file_.entity_mut(method.entity);
        entity.name = file_.intern_name(
            "__aburi_anonymous_union_" + std::to_string(record.index) +
            "_special_" + std::to_string(method.entity.index));
        entity.linkage = cir::LinkageKind::Internal;
        entity.is_extern_c = true;
    }
    file_.set_record_facts(record, std::move(facts));
    return valid;
}

void Session::bind_anonymous_union_promotions(cir::TypeId union_type,
                                               cir::InstId object_place,
                                               SrcLoc loc) {
    const cir::RecordFacts* facts =
        file_.record_facts_for_type(file_.resolved_type(union_type));
    cir::DeclContextId context = current_decl_context();
    if (!facts || !context.valid()) {
        return;
    }
    for (const cir::AnonymousUnionPromotionFact& promotion :
         facts->anonymous_union_promotions) {
        std::string_view name = file_.name(promotion.name);
        if (const cir::Binding* previous =
                file_.lookup_ordinary_binding(context, name,
                                              /*include_parents=*/false)) {
            (void)previous;
            report_error("anonymous union member '" + std::string(name) +
                             "' conflicts with an existing declaration",
                         file_.entity(promotion.member).loc);
            continue;
        }
        diagnose_template_parameter_hiding(name,
                                           file_.entity(promotion.member).loc,
                                           context);
        cir::TypeId type = file_.entity(promotion.member).type;
        cir::BindingId binding = file_.bind_entity(
            context, promotion.name, cir::LookupNamespace::Ordinary,
            promotion.member, file_.type_ref(type), false, false, true,
            object_place, loc);
        if (binding.valid()) {
            bump_lookup_generation();
            cir::Binding* record_binding = file_.binding_mut(binding);
            record_binding->generation = lookup_generation_;
            if (!record_binding->entity_generations.empty()) {
                record_binding->entity_generations.back() = lookup_generation_;
            }
        }
    }
}

RecordFieldInput Session::declare_anonymous_union_member(
    cir::TypeId union_type,
    cir::RecordMemberAccess access,
    SrcLoc loc) {
    RecordFieldInput input;
    input.type = union_type;
    input.loc = loc;
    input.declared_access = access;
    input.is_anonymous_union_object = true;
    cir::DeclContextId context = current_decl_context();
    cir::EntityId owner = context.valid() && file_.valid(context)
        ? file_.decl_context(context).owner
        : cir::EntityId{};
    input.entity = builder_.add_entity(cir::EntityKind::Field,
                                       "",
                                       union_type,
                                       owner,
                                       loc);
    if (input.entity.valid()) {
        file_.entity_mut(input.entity).object_origin =
            cir::EntityObjectOrigin::AnonymousUnion;
    }
    (void)complete_anonymous_union_object(
        union_type, input.entity, cir::AnonymousUnionObjectKind::Member,
        context, loc);
    if (owner.valid() && file_.valid(owner)) {
        const cir::RecordFacts* anonymous =
            file_.record_facts_for_type(union_type);
        if (anonymous) {
            for (const cir::AnonymousUnionPromotionFact& promotion :
                 anonymous->anonymous_union_promotions) {
                if (!promotion.member.valid() ||
                    !file_.valid(promotion.member)) {
                    continue;
                }
                cir::Entity& member = file_.entity_mut(promotion.member);
                member.declaring_record = owner;
                member.declared_member_access = access;
                member.is_record_member = true;
            }
        }
    }
    return input;
}

DeclResult Session::declare_anonymous_union_variable(cir::TypeId union_type,
                                                     bool namespace_scope,
                                                     DeclFlags flags,
                                                     SrcLoc loc) {
    std::string internal_name =
        anonymous_record_name(cir::RecordKind::Union) + ".object";
    flags.suppress_name_binding = true;
    if (namespace_scope) {
        cir::DeclContextId context = current_decl_context();
        cir::EntityId owner =
            context.valid() && file_.valid(context)
                ? file_.decl_context(context).owner
                : cir::EntityId{};
        bool already_internal = entity_has_internal_name_linkage(owner);
        if (!flags.is_static && !already_internal) {
            report_error("namespace-scope anonymous union must be declared static",
                         loc);
        }

        flags.is_static = true;
    }
    DeclResult result = namespace_scope
        ? declare_global_variable(internal_name, union_type, std::nullopt,
                                  loc, flags)
        : declare_local_variable(internal_name, union_type, std::nullopt,
                                 loc, flags);
    if (result.entity.valid()) {
        cir::Entity& object = file_.entity_mut(result.entity);
        object.object_origin = cir::EntityObjectOrigin::AnonymousUnion;

        object.lexical_context = current_decl_context();
        object.semantic_context = current_decl_context();
        if (!namespace_scope) {
            object.owning_function = current_function_entity();
        }
    }
    bool valid = complete_anonymous_union_object(
        union_type, result.entity,
        namespace_scope
            ? cir::AnonymousUnionObjectKind::NamespaceVariable
            : cir::AnonymousUnionObjectKind::BlockVariable,
        current_decl_context(), loc);
    result = finish_variable_declaration(std::move(result), union_type,
                                         std::nullopt, loc, flags);
    bind_anonymous_union_promotions(union_type, result.place, loc);
    result.has_error = result.has_error || !valid;
    return result;
}

void Session::bind_record_injected_class_name(std::string_view name,
                                              cir::EntityId record_entity,
                                              SrcLoc loc) {
    if (name.empty() || !record_entity.valid() ||
        !file_.valid(record_entity)) {
        return;
    }
    const cir::Entity& record = file_.entity(record_entity);
    if (record.kind != cir::EntityKind::Record || !record.type.valid()) {
        return;
    }
    cir::DeclContextId lexical_context = record.lexical_context;
    bind_entity(name,
                cir::LookupNamespace::Ordinary,
                record_entity,
                record.type,
                /*is_type_name=*/true,
                /*is_template_name=*/false,
                record.is_definition,
                {},
                loc);
    if (file_.valid(record_entity)) {
        file_.entity_mut(record_entity).lexical_context = lexical_context;
    }
}

cir::EntityId Session::declare_record_static_data_member(
    const RecordStaticDataMemberInput& member) {
    if (member.entity.valid()) {
        return member.entity;
    }
    if (member.name.empty() || !member.type.valid()) {
        return {};
    }
    cir::DeclContextId context = current_decl_context();
    cir::EntityId owner = context.valid()
        ? file_.decl_context(context).owner
        : cir::EntityId{};
    cir::StorageDuration duration = member.flags.is_thread_local
        ? cir::StorageDuration::Thread
        : cir::StorageDuration::Static;
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                               member.name,
                                               member.type,
                                               owner,
                                               member.loc,
                                               duration,
                                               cir::MemorySpace::Default,
                                               member.flags.to_cir());
    cir::Entity& record = file_.entity_mut(entity);
    record.is_definition = member.flags.is_inline ||
        member.flags.is_constexpr;
    record.linkage = record.is_definition
        ? cir::LinkageKind::LinkOnceODR
        : cir::LinkageKind::External;
    record.qualifiers = member.flags.type_qualifiers;

    AttributeList member_attrs = member.flags.attrs;
    member_attrs.append(member.attrs);
    apply_attributes(entity, AttributeTarget::Variable, member_attrs, member.loc);
    bind_entity(member.name,
                cir::LookupNamespace::Ordinary,
                entity,
                member.type,
                false,
                false,
                false,
                {},
                member.loc);
    return entity;
}

void Session::stage_record_static_data_member_fact(
    const RecordStaticDataMemberInput& member) {
    if (!member.entity.valid() || !file_.valid(member.entity)) {
        return;
    }
    cir::EntityId owner = file_.entity(member.entity).parent;
    const cir::RecordFacts* published =
        owner.valid() && file_.valid(owner)
        ? file_.record_facts(owner)
        : nullptr;
    if (!published) {
        return;
    }
    cir::RecordFacts facts = *published;
    cir::RecordStaticDataMemberFact staged =
        make_record_static_data_member_fact(file_, member);
    auto existing = std::find_if(
        facts.static_data_members.begin(),
        facts.static_data_members.end(),
        [&](const cir::RecordStaticDataMemberFact& fact) {
            return fact.entity == member.entity;
        });
    if (existing == facts.static_data_members.end()) {
        facts.static_data_members.push_back(std::move(staged));
    } else {
        *existing = std::move(staged);
    }
    file_.set_record_facts(owner, std::move(facts));
}

bool Session::complete_record_static_data_member_type(
    cir::EntityId entity,
    std::string_view name,
    cir::TypeId type) {
    if (!entity.valid() || !file_.valid(entity) || !type.valid() ||
        !file_.valid(type)) {
        return false;
    }
    file_.entity_mut(entity).type = type;
    if (!name.empty()) {
        if (cir::Binding* binding =
                file_.mutable_ordinary_binding(current_decl_context(), name)) {
            binding->type = file_.type_ref(type);
        }
    }
    file_.retype_entity_places(entity);
    return true;
}

cir::EntityId Session::declare_record_method_shell(
    cir::EntityId record_entity,
    RecordMethodInput& method) {
    if (method.precreated_entity.valid()) {
        if (file_.valid(method.precreated_entity)) {
            cir::Entity& declaration =
                file_.entity_mut(method.precreated_entity);
            declaration.has_deferred_definition =
                declaration.has_deferred_definition ||
                method.has_deferred_definition;
            register_placeholder_result(method.precreated_entity,
                                        declaration.type,
                                        nullptr,
                                        method.loc);
        }
        return method.precreated_entity;
    }
    if (!record_entity.valid() || !file_.valid(record_entity) ||
        method.name.empty() || !method.type.valid()) {
        return {};
    }

    bool is_allocation_or_deallocation =
        method.operator_function.kind ==
            cir::OperatorFunctionKind::Allocation ||
        method.operator_function.kind ==
            cir::OperatorFunctionKind::Deallocation;
    bool is_static = method.is_static || is_allocation_or_deallocation;
    cir::EntityKind kind = cir::EntityKind::Method;
    if (method.is_constructor) {
        kind = cir::EntityKind::Constructor;
    } else if (method.is_destructor) {
        kind = cir::EntityKind::Destructor;
    }

    cir::TypeId entity_type = is_static
        ? method.type
        : member_function_type_with_this(file_.entity(record_entity).type,
                                         method.type);
    cir::EntityId entity = builder_.add_entity(kind,
                                               method.name,
                                               entity_type,
                                               record_entity,
                                               method.loc,
                                               cir::StorageDuration::None,
                                               cir::MemorySpace::Default,
                                               method.flags.to_cir());
    cir::Entity& declaration = file_.entity_mut(entity);
    declaration.operator_function = method.operator_function;
    declaration.is_static_member_function = is_static;
    declaration.is_definition = false;
    declaration.has_deferred_definition =
        method.has_deferred_definition;
    declaration.linkage = cir::LinkageKind::External;
    register_placeholder_result(entity, entity_type, nullptr, method.loc);
    record_member_declaration(entity,
                              record_entity,
                              method.declared_access,
                              method.loc);

    if (!method.is_function_template) {
        bind_callable(method.name,
                      entity,
                      method.type,
                      /*is_definition=*/false,
                      method.loc);
    }
    method.precreated_entity = entity;
    return entity;
}

bool Session::resolve_record_method_noexcept(
    cir::EntityId method_entity,
    cir::FunctionExceptionSpec exception_spec) {
    if (!method_entity.valid() || !file_.valid(method_entity)) {
        return false;
    }
    cir::EntityId record_entity = file_.entity(method_entity).parent;
    const cir::RecordFacts* published = file_.record_facts(record_entity);
    if (!published) {
        return false;
    }
    cir::RecordFacts facts = *published;
    auto found = std::find_if(
        facts.methods.begin(), facts.methods.end(),
        [&](const cir::RecordMethodFact& method) {
            return method.entity == method_entity;
        });
    if (found == facts.methods.end()) {
        return false;
    }
    const auto* old_payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(file_.resolved_type(found->type.type)));
    if (!old_payload) {
        return false;
    }
    cir::FunctionTypePayload payload = *old_payload;
    cir::TypeId rebuilt = function_type(
        payload.return_type,
        payload.parameters,
        payload.is_variadic,
        payload.has_prototype,
        payload.member_is_const,
        std::move(exception_spec),
        payload.parameter_pack_flags,
        payload.member_ref_qualifier,
        payload.member_is_volatile);
    found->type = file_.type_ref(rebuilt);
    found->has_deferred_noexcept_operand = false;

    cir::TypeId entity_type = found->is_static
        ? rebuilt
        : member_function_type_with_this(facts.type.type, rebuilt);
    cir::EntityKind kind = file_.entity(method_entity).kind;
    if (!facts.virtual_bases.empty() &&
        (kind == cir::EntityKind::Constructor ||
         kind == cir::EntityKind::Destructor)) {
        entity_type = structor_impl_type(entity_type);
    }
    file_.entity_mut(method_entity).type = entity_type;
    file_.set_record_facts(record_entity, std::move(facts));
    return true;
}

bool Session::resolve_record_field_initializer_exception(
    cir::EntityId field_entity,
    bool potentially_throwing,
    bool dependent) {
    if (!field_entity.valid() || !file_.valid(field_entity)) {
        return false;
    }
    cir::EntityId record_entity = file_.entity(field_entity).parent;
    const cir::RecordFacts* published = file_.record_facts(record_entity);
    if (!published) {
        return false;
    }
    cir::RecordFacts facts = *published;
    auto found = std::find_if(
        facts.fields.begin(), facts.fields.end(),
        [&](const cir::RecordFieldFact& field) {
            return field.entity == field_entity;
        });
    if (found == facts.fields.end()) {
        return false;
    }
    found->default_member_initializer_potentially_throwing =
        potentially_throwing;
    found->default_member_initializer_throwing_dependent = dependent;
    file_.set_record_facts(record_entity, std::move(facts));
    return true;
}

cir::InstId Session::make_complete_class_validation_object(
    cir::EntityId record,
    SrcLoc loc) {
    if (!record.valid() || !file_.valid(record)) {
        return {};
    }
    cir::EntityId entity = builder_.add_entity(
        cir::EntityKind::Variable,
        ".complete.class.object",
        file_.entity(record).type,
        {},
        loc,
        cir::StorageDuration::Static,
        cir::MemorySpace::Default,
        {});
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block(
        "complete.class.validation.object");
    cir::InstId place = builder_.global_place(entity, loc);
    (void)finish_fragment_block(block, previous);
    return place;
}

bool Session::validate_record_static_data_member_definition(
    cir::EntityId entity,
    bool has_initializer,
    const DeclFlags& flags,
    SrcLoc loc) {
    const cir::RecordStaticDataMemberFact* fact =
        static_data_member_fact(entity);
    if (!fact || !entity.valid() || !file_.valid(entity)) {
        return false;
    }

    cir::Entity& variable = file_.entity_mut(entity);
    bool declared_thread_local =
        variable.storage_duration == cir::StorageDuration::Thread;
    if (declared_thread_local != flags.is_thread_local) {
        report_error(std::string(flags.is_thread_local ? "thread-local"
                                                       : "non-thread-local") +
                         " declaration of static data member '" +
                         file_.name(fact->name) + "' follows " +
                         (declared_thread_local ? "thread-local"
                                                : "non-thread-local") +
                         " declaration",
                     loc);
        return false;
    }
    bool deprecated_constexpr_redeclaration =
        fact->is_constexpr && flags.is_constexpr && !has_initializer;
    if (deprecated_constexpr_redeclaration) {
        return true;
    }
    if (variable.is_definition) {
        report_error("redefinition of static data member '" +
                         file_.name(fact->name) + "'",
                     loc);
        return false;
    }
    if (fact->has_in_class_initializer && has_initializer) {
        report_error("static data member '" + file_.name(fact->name) +
                         "' already has an initializer",
                     loc);
        return false;
    }
    if (!flags.is_declaration_only) {
        cir::Entity previous = variable;
        track_speculative_rollback([this, entity, previous] {
            if (file_.valid(entity)) {
                file_.entity_mut(entity) = previous;
            }
        });
        variable.is_definition = true;
        variable.linkage = cir::LinkageKind::External;
        cir::DeclSemanticFlags definition_flags = flags.to_cir();
        definition_flags.is_constexpr =
            definition_flags.is_constexpr ||
            variable.decl_flags.is_constexpr;
        definition_flags.is_consteval =
            definition_flags.is_consteval ||
            variable.decl_flags.is_consteval;
        definition_flags.is_constinit =
            definition_flags.is_constinit ||
            variable.decl_flags.is_constinit;
        definition_flags.is_inline =
            definition_flags.is_inline ||
            variable.decl_flags.is_inline;
        definition_flags.is_thread_local =
            definition_flags.is_thread_local ||
            variable.decl_flags.is_thread_local;
        definition_flags.is_register =
            definition_flags.is_register ||
            variable.decl_flags.is_register;
        variable.decl_flags = definition_flags;
    }
    return true;
}

bool Session::is_namespace_scope_static_entity(cir::EntityId entity) const {
    if (!entity.valid() || !file_.valid(entity) ||
        (file_.entity(entity).storage_duration !=
             cir::StorageDuration::Static &&
         file_.entity(entity).storage_duration !=
             cir::StorageDuration::Thread)) {
        return false;
    }
    cir::DeclContextId context = file_.entity(entity).semantic_context;
    for (; context.valid() && file_.valid(context);
         context = file_.decl_context(context).parent) {
        switch (file_.decl_context(context).kind) {
            case cir::DeclContextKind::TranslationUnit:
            case cir::DeclContextKind::Namespace:
                return true;
            case cir::DeclContextKind::Function:
            case cir::DeclContextKind::Block:
                return false;
            default:
                break;
        }
    }
    return false;
}

cir::EntityId Session::find_record_static_data_member(
    cir::DeclContextId context,
    std::string_view name,
    cir::TypeRef type,
    std::optional<cir::StorageDuration> specialization_duration) {
    if (!context.valid()) {
        return {};
    }
    const cir::DeclContext& decl_context = file_.decl_context(context);
    if (decl_context.kind != cir::DeclContextKind::Record ||
        !decl_context.owner.valid() ||
        !file_.valid(decl_context.owner)) {
        return {};
    }
    const cir::RecordFacts* facts = file_.record_facts(decl_context.owner);
    if (!facts) {
        return {};
    }
    for (const cir::RecordStaticDataMemberFact& member :
         facts->static_data_members) {
        if (!member.entity.valid() || !member.name.valid() ||
            file_.name(member.name) != name ||
            !types_compatible(member.type, type)) {
            continue;
        }
        return member.entity;
    }

    if (const cir::Binding* binding =
            file_.lookup_value_binding(context, name,
                                       /*include_parents=*/false)) {
        for (cir::EntityId candidate : binding->entities) {
            if (!candidate.valid() || !file_.valid(candidate)) {
                continue;
            }
            const cir::Entity& entity = file_.entity(candidate);
            if (entity.kind == cir::EntityKind::Variable &&
                entity.parent == decl_context.owner &&
                (entity.storage_duration == cir::StorageDuration::Static ||
                 entity.storage_duration == cir::StorageDuration::Thread) &&
                types_compatible(file_.type_ref(entity.type), type)) {
                return candidate;
            }
        }
    }

    size_t template_arguments = name.find('<');
    if (specialization_duration.has_value() &&
        template_arguments != std::string_view::npos &&
        template_arguments != 0) {
        std::string_view primary_name = name.substr(0, template_arguments);
        const cir::Binding* template_binding =
            file_.lookup_template_name_binding(context, primary_name,
                                               /*include_parents=*/false);
        if (template_binding) {
            for (cir::EntityId primary_entity : template_binding->entities) {
                const TemplateInfo* info = template_info(primary_entity);
                if (!info || !info->is_variable_template) {
                    continue;
                }
                cir::EntityId specialization = builder_.add_entity(
                    cir::EntityKind::Variable,
                    std::string(name),
                    type.type,
                    decl_context.owner,
                    file_.entity(primary_entity).loc,
                    *specialization_duration);
                cir::Entity& entity = file_.entity_mut(specialization);
                entity.is_definition = false;
                entity.linkage = cir::LinkageKind::External;
                entity.qualifiers = type.qualifiers;
                entity.lexical_context = context;
                entity.semantic_context = context;

                cir::RecordFacts updated = *facts;
                cir::RecordStaticDataMemberFact specialization_fact;
                specialization_fact.name = file_.intern_name(name);
                specialization_fact.entity = specialization;
                specialization_fact.type = type;
                updated.static_data_members.push_back(
                    std::move(specialization_fact));
                file_.set_record_facts(decl_context.owner,
                                       std::move(updated));
                file_.bind_entity(context,
                                  file_.entity(specialization).name,
                                  cir::LookupNamespace::Ordinary,
                                  specialization,
                                  type,
                                  false,
                                  false,
                                  false,
                                  {},
                                  file_.entity(primary_entity).loc);
                return specialization;
            }
        }
    }
    return {};
}

bool Session::materialize_record_static_data_member_initializer(
    cir::EntityId entity,
    cir::TypeId type,
    const ExprResult& initializer,
    SrcLoc loc,
    ConstructorInitializationKind init_kind) {
    if (entity.valid() && file_.valid(entity)) {
        cir::Entity& declaration = file_.entity_mut(entity);
        declaration.has_initializer = true;
        declaration.initializer_is_value_dependent =
            expr_is_value_dependent(initializer);
    }
    if (!entity.valid() || !type.valid()) {
        return true;
    }

    const cir::Entity& member = file_.entity(entity);
    if (in_template_definition() && member.is_template_pattern) {
        return true;
    }
    std::vector<cir::StaticInitializerRelocation> relocations;
    bool is_const_integer =
        ((member.qualifiers & cir::QualConst) ||
         member.decl_flags.is_constexpr) &&
        cir::is_integer_like_type(file_, type);
    ExprResult initializer_copy = initializer;
    std::optional<ExprResult> constant_initializer;
    if (is_const_integer) {
        constant_initializer =
            require_value(initializer, UseContext::RValue, loc);
        if (!constant_initializer->has_error) {
            initializer_copy = *constant_initializer;
        }
    }
    cir::TypeId resolved_type = file_.resolved_type(type);
    bool is_class_object = file_.valid(resolved_type) &&
        file_.type(resolved_type).kind == cir::TypeKind::Record;
    bool permits_dynamic_initialization =
        lang_opts_.is_cxx_mode() && member.decl_flags.is_inline &&
        !member.decl_flags.is_constexpr &&
        !member.decl_flags.is_constinit &&
        is_namespace_scope_static_entity(entity);
    std::optional<std::vector<uint8_t>> bytes;

    if (lang_opts_.is_cxx_mode() && is_class_object) {
        DeclResult started;
        started.entity = entity;
        started.type = type;
        DeclFlags flags;
        flags.is_inline = member.decl_flags.is_inline;
        flags.is_constexpr = member.decl_flags.is_constexpr;
        flags.is_constinit = member.decl_flags.is_constinit;
        flags.is_thread_local = member.decl_flags.is_thread_local;
        flags.is_static = true;
        flags.type_qualifiers = member.qualifiers;
        started = finish_variable_declaration(
            std::move(started), type, initializer, loc, flags, {}, init_kind);
        return !started.has_error;
    }
    if (permits_dynamic_initialization) {
        begin_speculative_parse();
        bytes = static_initializer_bytes(type,
                                         std::move(initializer_copy),
                                         loc,
                                         &relocations);
        if (bytes.has_value()) {
            commit_speculative_parse();
        } else {
            rollback_speculative_parse();
            DeclResult started;
            started.entity = entity;
            started.type = type;
            started = initialize_global_variable(std::move(started),
                                                 initializer,
                                                 loc,
                                                 ConstructorInitializationKind::Copy);
            return !started.has_error;
        }
    } else {
        bytes = static_initializer_bytes(type,
                                         std::move(initializer_copy),
                                         loc,
                                         &relocations);
    }
    if (!bytes.has_value()) {
        return false;
    }
    cir::Entity& variable = file_.entity_mut(entity);
    variable.has_static_initializer = true;
    variable.static_initializer_bytes = std::move(*bytes);
    variable.static_initializer_relocations = std::move(relocations);
    if (is_const_integer && constant_initializer.has_value()) {
        cir::IntegerValue constant_value;
        if (!constant_initializer->has_error &&
            try_evaluate_integer_constant_value(*constant_initializer,
                                                constant_value)) {
            variable.has_constant_value = true;
            variable.constant_value_kind =
                file_.template_value_kind_for_type(type);
            if (variable.constant_value_kind ==
                cir::TemplateValueKind::Boolean) {
                variable.constant_integer_value =
                    cir::IntegerValue::from_unsigned(
                        constant_value.is_zero() ? 0 : 1, 1);
            } else {
                cir::IntegerTypeShape shape =
                    cir::integer_shape_for_type(file_, type);
                variable.constant_integer_value =
                    constant_value.cast(shape.bit_width,
                                        shape.is_unsigned);
            }
        }
    }
    return true;
}

RecordDeclResult Session::finish_record_definition(
    RecordDeclResult decl,
    cir::RecordKind kind,
    std::vector<RecordFieldInput> fields,
    std::vector<RecordStaticDataMemberInput> static_data_members,
    std::vector<RecordMethodInput> methods,
    SrcLoc loc,
    RecordLayoutOptions layout_options,
    std::vector<cir::EntityId>* method_entities_out,
    const std::vector<const TemplateInfo*>* method_template_heads,
    std::vector<RecordBaseInput> bases,
    bool is_final,
    bool is_anonymous_union_definition) {
    if (method_entities_out) {
        method_entities_out->assign(methods.size(), cir::EntityId{});
    }
    if (arc_enabled() && !lang_opts_.is_cxx_mode() &&
        !layout_options.arc_managed_aggregate) {

        for (const RecordFieldInput& field : fields) {
            if (arc_retainable_type(field.type) &&
                arc_ownership_of_ref(
                    cir::TypeRef{field.type, field.qualifiers, {}}) !=
                    cir::ObjCOwnership::UnsafeUnretained) {
                report_error("ARC forbids Objective-C objects in a struct "
                             "or union (mark the member "
                             "__unsafe_unretained)",
                             field.loc);
            }
        }
    }
    if (kind == cir::RecordKind::Union && !bases.empty()) {
        report_error("a union cannot have base classes", bases.front().loc);
        decl.has_error = true;
        bases.clear();
    }

    std::vector<cir::RecordBaseFact> base_facts;
    std::vector<cir::RecordDependentBaseFact> dependent_base_facts;
    std::vector<RecordFieldInput> base_fields;
    std::vector<size_t> base_data_sizes;
    std::vector<cir::RecordFacts::VirtualBase> virtual_base_list;
    auto add_virtual_base = [&](cir::EntityId record_entity, cir::TypeRef type) {
        for (const cir::RecordFacts::VirtualBase& existing : virtual_base_list) {
            if (existing.record_entity == record_entity) {
                return;
            }
        }
        cir::RecordFacts::VirtualBase entry;
        entry.record_entity = record_entity;
        entry.type = type;
        entry.vtable_index = virtual_base_list.size();
        virtual_base_list.push_back(entry);
    };

    auto non_virtual_data_size = [&](const cir::RecordFacts* record,
                                     SrcLoc size_loc) {
        size_t data_size = 0;
        for (const cir::RecordFieldFact& base_field : record->fields) {
            if (base_field.is_flexible_array_member ||
                base_field.is_virtual_base_storage ||
                base_field.subobject_size == cir::SubobjectSizeKind::Zero) {
                continue;
            }
            std::optional<size_t> field_size =
                size_of_type(base_field.type.type, size_loc);
            if (field_size.has_value()) {
                size_t occupied = base_field.storage_size_override > 0
                    ? base_field.storage_size_override
                    : *field_size;
                data_size = std::max(data_size, base_field.offset + occupied);
            }
        }
        return data_size;
    };
    for (const RecordBaseInput& base : bases) {
        if (base.is_dependent ||
            (in_template_definition() && is_dependent_type(base.type))) {
            cir::RecordDependentBaseFact fact;
            fact.type = file_.type_ref(base.type);
            fact.declared_access = base.declared_access;
            fact.is_virtual = base.is_virtual;
            fact.declaration_index = static_cast<uint32_t>(
                base_facts.size() + dependent_base_facts.size());
            dependent_base_facts.push_back(std::move(fact));
            continue;
        }
        cir::TypeId resolved = file_.resolved_type(base.type);
        if (!file_.valid(resolved) ||
            file_.type(resolved).kind != cir::TypeKind::Record) {
            report_error("base specifier must name a class type", base.loc);
            decl.has_error = true;
            continue;
        }
        (void)require_complete_class_type(
            resolved, base.loc,
            cir::InstantiationDemandKind::BaseMemberList);
        const cir::RecordFacts* base_record =
            file_.record_facts_for_type(resolved);
        if (!base_record || base_record->is_incomplete) {
            report_error("base class has incomplete type", base.loc);
            decl.has_error = true;
            continue;
        }
        if (base_record->kind == cir::RecordKind::Union) {
            report_error("a union cannot be a base class", base.loc);
            decl.has_error = true;
            continue;
        }
        if (base_record->is_final) {
            report_error("base class '" + file_.format_type(resolved) +
                             "' is marked final",
                         base.loc);
            decl.has_error = true;
        }
        bool duplicate = false;
        for (const cir::RecordBaseFact& existing_base : base_facts) {
            if (file_.resolved_type(existing_base.type.type) == resolved) {
                duplicate = true;
            }
        }
        if (duplicate) {
            report_error("duplicate direct base class", base.loc);
            decl.has_error = true;
            continue;
        }
        cir::RecordBaseFact fact;
        fact.name = base_record->entity.valid() &&
                            file_.entity(base_record->entity).name.valid()
            ? file_.entity(base_record->entity).name
            : cir::NameId{};
        fact.type = file_.type_ref(base.type);
        fact.declared_access = base.declared_access;
        fact.record_entity = base_record->entity;
        fact.is_virtual = base.is_virtual;
        fact.declaration_index = static_cast<uint32_t>(base_facts.size());
        base_facts.push_back(fact);

        for (const cir::RecordFacts::VirtualBase& inherited :
             base_record->virtual_bases) {
            add_virtual_base(inherited.record_entity, inherited.type);
        }
        if (base.is_virtual) {
            add_virtual_base(base_record->entity, file_.type_ref(base.type));
            continue;
        }

        // Non-virtual base subobjects occupy their non-virtual data size,
        // not their full size, so derived members reuse the base's tail
        // padding (Itanium dsize) and never overlap vbase storage.
        base_data_sizes.push_back(non_virtual_data_size(base_record, base.loc));

        RecordFieldInput field;
        field.type = base.type;
        field.loc = base.loc;
        field.declared_access = base.declared_access;
        base_fields.push_back(std::move(field));
    }
    bool has_virtual_bases = !virtual_base_list.empty();
    if (!base_fields.empty()) {
        fields.insert(fields.begin(),
                      std::make_move_iterator(base_fields.begin()),
                      std::make_move_iterator(base_fields.end()));
    }

    bool any_virtual_method = false;
    for (const RecordMethodInput& method : methods) {
        if (method.is_virtual) {
            any_virtual_method = true;
        }
    }
    bool primary_base_polymorphic = false;

    std::vector<size_t> secondary_polymorphic_bases;
    size_t nonvirtual_ordinal = 0;
    for (size_t i = 0; i < base_facts.size(); ++i) {
        if (base_facts[i].is_virtual) {
            continue;
        }
        size_t ordinal = nonvirtual_ordinal++;
        const cir::RecordFacts* base_record =
            file_.record_facts_for_type(file_.resolved_type(base_facts[i].type.type));
        if (!base_record || !base_record->is_polymorphic) {
            continue;
        }
        if (ordinal == 0) {
            primary_base_polymorphic = true;
        } else {
            secondary_polymorphic_bases.push_back(ordinal);
        }
    }
    if (!secondary_polymorphic_bases.empty() && !primary_base_polymorphic) {
        // Itanium 2.4: the primary base is the first polymorphic non-virtual
        // base and sits at offset zero, so its subobject field moves to the
        // front of the layout. The facts, leading fields, and data sizes
        // rotate together — every ordinal-positional invariant survives —
        // while declaration_index keeps construction and destruction in
        // source order.
        size_t primary_ordinal = secondary_polymorphic_bases.front();
        std::rotate(base_data_sizes.begin(),
                    base_data_sizes.begin() + primary_ordinal,
                    base_data_sizes.begin() + primary_ordinal + 1);
        std::rotate(fields.begin(),
                    fields.begin() + primary_ordinal,
                    fields.begin() + primary_ordinal + 1);
        std::vector<size_t> nonvirtual_positions;
        for (size_t i = 0; i < base_facts.size(); ++i) {
            if (!base_facts[i].is_virtual) {
                nonvirtual_positions.push_back(i);
            }
        }
        std::vector<cir::RecordBaseFact> reordered;
        reordered.reserve(nonvirtual_positions.size());
        for (size_t position : nonvirtual_positions) {
            reordered.push_back(base_facts[position]);
        }
        std::rotate(reordered.begin(),
                    reordered.begin() + primary_ordinal,
                    reordered.begin() + primary_ordinal + 1);
        for (size_t k = 0; k < nonvirtual_positions.size(); ++k) {
            base_facts[nonvirtual_positions[k]] = reordered[k];
        }
        primary_base_polymorphic = true;

        std::vector<size_t> remaining_secondaries;
        for (size_t ordinal : secondary_polymorphic_bases) {
            if (ordinal != primary_ordinal) {
                remaining_secondaries.push_back(ordinal);
            }
        }
        secondary_polymorphic_bases = std::move(remaining_secondaries);
    }

    bool has_primary_vtable =
        any_virtual_method || primary_base_polymorphic || has_virtual_bases;
    bool is_polymorphic_record =
        has_primary_vtable || !secondary_polymorphic_bases.empty();

    bool vptr_injected =
        (any_virtual_method || has_virtual_bases) && !primary_base_polymorphic;
    if (vptr_injected) {
        RecordFieldInput vptr;
        vptr.name = ".vptr";
        vptr.type = builder_.pointer_type(
            file_.builtin_type(cir::BuiltinTypeKind::Void));
        vptr.loc = loc;
        fields.insert(fields.begin(), std::move(vptr));
    }

    size_t vbase_field_start = fields.size();
    std::vector<size_t> vbase_data_sizes;
    for (const cir::RecordFacts::VirtualBase& vbase : virtual_base_list) {
        const cir::RecordFacts* vbase_record =
            file_.record_facts_for_type(file_.resolved_type(vbase.type.type));
        if (!vbase_record) {
            continue;
        }
        vbase_data_sizes.push_back(non_virtual_data_size(vbase_record, loc));
        RecordFieldInput field;
        field.type = vbase.type.type;
        field.loc = loc;
        fields.push_back(std::move(field));
    }
    size_t base_field_start = vptr_injected ? 1 : 0;
    cir::RecordFacts existing;
    if (const cir::RecordFacts* facts = file_.record_facts(decl.entity)) {
        existing = *facts;
        if (!record_kinds_agree(facts->kind, kind)) {
            report_error("record definition kind does not match prior declaration", loc);
            decl.has_error = true;
        }
    }
    if (is_polymorphic_record) {
        existing.is_polymorphic = true;
    }
    apply_record_attributes(existing, kind, layout_options.attrs, loc);
    if (layout_options.is_packed) {
        existing.is_packed = true;
    }
    if (layout_options.is_transparent_union) {
        existing.is_transparent_union = kind == cir::RecordKind::Union;
    }
    if (layout_options.requested_alignment > existing.requested_alignment) {
        existing.requested_alignment = layout_options.requested_alignment;
    }
    existing.pack_alignment = layout_options.pack_alignment;

    std::vector<cir::RecordFieldFact> field_facts;
    field_facts.reserve(fields.size());
    bool union_has_default_member_initializer = false;
    for (size_t index = 0; index < fields.size(); ++index) {
        const RecordFieldInput& field = fields[index];
        if (!field.type.valid()) {
            decl.has_error = true;
            continue;
        }
        bool is_base_storage =
            (index >= base_field_start &&
             index < base_field_start + base_data_sizes.size()) ||
            (index >= vbase_field_start &&
             index < vbase_field_start + vbase_data_sizes.size());
        bool is_flexible_array = incomplete_array_payload(file_, field.type) != nullptr;
        if (!is_base_storage && !is_flexible_array) {
            bool dependent_member_type =
                in_template_definition() && is_dependent_type(field.type);
            if (!dependent_member_type) {
                cir::TypeId completeness_type =
                    file_.resolved_type(field.type);
                while (file_.valid(completeness_type) &&
                       file_.type(completeness_type).kind ==
                           cir::TypeKind::Array) {
                    const auto* array = std::get_if<cir::ArrayTypePayload>(
                        &file_.type_payload(completeness_type));
                    completeness_type = array
                        ? file_.resolved_type(array->element_type.type)
                        : cir::TypeId{};
                }
                if (file_.valid(completeness_type) &&
                    file_.type(completeness_type).kind ==
                        cir::TypeKind::Record) {
                    (void)require_complete_class_type(
                        completeness_type,
                        field.loc,
                        cir::InstantiationDemandKind::CompleteClass);
                }
            }
            NonStaticMemberTypeIssue type_issue =
                nonstatic_member_type_issue(file_, field.type);
            if (type_issue == NonStaticMemberTypeIssue::Incomplete &&
                dependent_member_type) {
                type_issue = NonStaticMemberTypeIssue::None;
            }
            switch (type_issue) {
                case NonStaticMemberTypeIssue::Incomplete:
                    report_error("non-static data member '" + field.name +
                                     "' has incomplete type",
                                 field.loc);
                    decl.has_error = true;
                    break;
                case NonStaticMemberTypeIssue::Abstract:
                    report_error("non-static data member '" + field.name +
                                     "' has abstract class type",
                                 field.loc);
                    decl.has_error = true;
                    break;
                case NonStaticMemberTypeIssue::None:
                    break;
            }
        }
        if (is_flexible_array) {
            if (field.is_bitfield) {
                report_error("flexible array member cannot be a bit-field", field.loc);
                decl.has_error = true;
            }
            if (kind == cir::RecordKind::Union) {
                report_error("flexible array member is not allowed in a union", field.loc);
                decl.has_error = true;
            }
            if (index + 1 != fields.size()) {
                report_error("flexible array member must be the last field", field.loc);
                decl.has_error = true;
            }
            if (index == 0) {
                report_error("flexible array member requires a preceding field", field.loc);
                decl.has_error = true;
            }
        }
        cir::EntityId field_entity = field.entity;
        if (field_entity.valid()) {

            file_.entity_mut(field_entity).parent = decl.entity;
        } else {
            field_entity = builder_.add_entity(cir::EntityKind::Field,
                                               field.name,
                                               field.type,
                                               decl.entity,
                                               field.loc);
        }
        if (!is_base_storage) {
            record_member_declaration(field_entity, decl.entity,
                                      field.declared_access, field.loc);
        }
        file_.entity_mut(field_entity).qualifiers = field.qualifiers;
        cir::RecordFieldFact fact;
        fact.name = field.name.empty() ? cir::NameId{} : file_.intern_name(field.name);
        fact.entity = field_entity;
        fact.type = file_.type_ref(field.type, field.qualifiers);
        fact.lambda_capture_source = field.lambda_capture_source;
        fact.lambda_capture_kind = field.lambda_capture_kind;
        fact.declared_access = field.declared_access;
        fact.is_bitfield = field.is_bitfield;
        fact.forced_alignment = field.forced_alignment;
        if (field.is_packed && field.forced_alignment == 0) {
            fact.storage_alignment_override = 1;
        }
        if (index >= base_field_start &&
            index < base_field_start + base_data_sizes.size()) {
            fact.storage_size_override =
                base_data_sizes[index - base_field_start];
            fact.is_base_subobject = true;
        }
        if (index >= vbase_field_start &&
            index < vbase_field_start + vbase_data_sizes.size()) {
            fact.storage_size_override =
                vbase_data_sizes[index - vbase_field_start];
            fact.is_base_subobject = true;
            fact.is_virtual_base_storage = true;
        }
        apply_field_attributes(fact, field.attrs, field.loc);
        fact.is_potentially_overlapping =
            fact.is_base_subobject || fact.is_no_unique_address;
        fact.is_flexible_array_member = is_flexible_array;
        fact.bit_width = field.bit_width;
        fact.bit_width_expression = field.bit_width_expression;
        file_.canonicalize_template_value_expression(
            fact.bit_width_expression);
        fact.bit_width_is_dependent =
            field.bit_width_is_dependent;
        fact.is_mutable = field.is_mutable;
        fact.is_anonymous_union_object =
            field.is_anonymous_union_object;
        fact.has_default_member_initializer =
            field.has_default_member_initializer;
        fact.default_member_initializer_braced =
            field.default_member_initializer_braced;
        fact.default_member_initializer_begin =
            field.default_member_initializer_begin;
        fact.default_member_initializer_end =
            field.default_member_initializer_end;
        fact.default_member_initializer_loc =
            field.default_member_initializer_loc;
        fact.default_member_initializer_context =
            field.default_member_initializer_context;
        fact.default_member_initializer_lookup_generation =
            lookup_generation_;
        fact.default_member_initializer_potentially_throwing =
            field.default_member_initializer_potentially_throwing;
        fact.default_member_initializer_throwing_dependent =
            field.default_member_initializer_throwing_dependent;
        if (kind == cir::RecordKind::Union &&
            fact.has_default_member_initializer) {
            if (union_has_default_member_initializer) {
                report_error(
                    "at most one union member may have a default member initializer",
                    field.default_member_initializer_loc);
                decl.has_error = true;
            }
            union_has_default_member_initializer = true;
        }
        if (kind == cir::RecordKind::Union &&
            is_reference_type(field.type)) {
            report_error("union member cannot have reference type", field.loc);
            decl.has_error = true;
        }
        if (fact.is_bitfield) {
            bool dependent_bitfield_type =
                in_template_definition() &&
                is_dependent_type(field.type);
            if (!dependent_bitfield_type &&
                !cir::is_integer_like_type(file_, field.type)) {
                report_error("bit-field has non-integer type", field.loc);
                decl.has_error = true;
            }
            if (!fact.bit_width_is_dependent &&
                fact.bit_width == 0 && fact.name.valid()) {
                report_error("zero-width bitfield must be anonymous", field.loc);
                decl.has_error = true;
            }
            if (!fact.name.valid() && lang_opts_.is_cxx_mode() &&
                (fact.type.qualifiers &
                 (cir::QualConst | cir::QualVolatile)) != 0) {
                report_error("unnamed bit-field cannot have cv-qualified type",
                             field.loc);
                decl.has_error = true;
            }
            cir::IntegerTypeShape shape = cir::integer_shape_for_type(file_, field.type);
            if (!fact.bit_width_is_dependent &&
                !dependent_bitfield_type &&
                shape.bit_width > 0 &&
                fact.bit_width > shape.bit_width) {
                if (lang_opts_.is_cxx_mode()) {
                    report_warning("bit-field width exceeds the width of its "
                                   "type; excess bits are padding",
                                   field.loc);
                } else {
                    report_error("bit-field width exceeds the width of its type",
                                 field.loc);
                    decl.has_error = true;
                }
            }
        } else if (!fact.name.valid() && !is_anonymous_record_member(file_, fact)) {
            report_error("anonymous field must be a complete struct or union type", field.loc);
            decl.has_error = true;
        }
        field_facts.push_back(std::move(fact));
    }

    std::vector<cir::RecordStaticDataMemberFact> static_member_facts;
    static_member_facts.reserve(static_data_members.size());
    bool static_members_forbidden_by_owner = false;
    if (decl.entity.valid() && file_.valid(decl.entity)) {
        cir::DeclContextId context =
            file_.entity(decl.entity).semantic_context;
        for (; context.valid() && file_.valid(context);
             context = file_.decl_context(context).parent) {
            const cir::DeclContext& scope = file_.decl_context(context);
            if (scope.kind == cir::DeclContextKind::Function ||
                scope.kind == cir::DeclContextKind::Block) {
                static_members_forbidden_by_owner = true;
                break;
            }
            if (scope.kind == cir::DeclContextKind::Record &&
                scope.owner.valid() && file_.valid(scope.owner) &&
                file_.entity(scope.owner).is_unnamed_record) {
                static_members_forbidden_by_owner = true;
                break;
            }
        }
    }
    for (const RecordStaticDataMemberInput& member : static_data_members) {
        if (member.has_error) {
            decl.has_error = true;
            continue;
        }
        if (!member.type.valid()) {
            decl.has_error = true;
            continue;
        }
        if (member.flags.is_mutable) {
            report_error("static data member '" + member.name +
                             "' cannot be mutable",
                         member.loc);
            decl.has_error = true;
        }
        if (static_members_forbidden_by_owner) {
            report_error("static data member '" + member.name +
                             "' is not allowed in a local or unnamed class "
                             "or a class nested within one",
                         member.loc);
            decl.has_error = true;
        }
        cir::TypeId resolved_member_type = file_.resolved_type(member.type);
        if (is_void_type(resolved_member_type)) {
            report_error("static data member '" + member.name +
                             "' cannot have void type",
                         member.loc);
            decl.has_error = true;
        }
        bool is_inline_definition = member.flags.is_inline ||
            member.flags.is_constexpr;
        if (is_inline_definition &&
            !is_dependent_type(member.type) &&
            !is_complete_static_data_definition_type(file_, member.type)) {
            report_error("inline static data member '" + member.name +
                             "' has incomplete type",
                         member.loc);
            decl.has_error = true;
        }
        bool has_initializer =
            member.initializer.has_value() || member.has_deferred_initializer;
        if (member.flags.is_constexpr && !has_initializer) {
            report_error("constexpr static data member '" + member.name +
                             "' requires an initializer",
                         member.loc);
            decl.has_error = true;
        }
        if (has_initializer && !is_inline_definition) {
            bool dependent_member_type =
                in_template_definition() &&
                is_dependent_type(member.type);
            bool is_const =
                (member.flags.type_qualifiers & cir::QualConst) != 0;
            bool is_volatile =
                (member.flags.type_qualifiers & cir::QualVolatile) != 0;
            if (!is_const || is_volatile ||
                (!dependent_member_type &&
                 !cir::is_integer_like_type(file_, member.type))) {
                report_error("non-inline static data member '" + member.name +
                                 "' cannot have an in-class initializer",
                             member.loc);
                decl.has_error = true;
            }
        }
        AttributeList member_attrs = member.flags.attrs;
        member_attrs.append(member.attrs);
        cir::EntityId entity = member.entity.valid()
            ? member.entity
            : builder_.add_entity(cir::EntityKind::Variable,
                                  member.name,
                                  member.type,
                                  decl.entity,
                                  member.loc,
                                  cir::StorageDuration::Static,
                                  cir::MemorySpace::Default,
                                  member.flags.to_cir());
        if (!member.entity.valid()) {
            file_.entity_mut(entity).is_definition = false;
            file_.entity_mut(entity).linkage = cir::LinkageKind::External;
            file_.entity_mut(entity).qualifiers = member.flags.type_qualifiers;
            apply_attributes(entity, AttributeTarget::Variable, member_attrs, member.loc);
        }
        if (member.initializer.has_value()) {
            register_template_value_parameter_equivalence(entity,
                                                          member.type,
                                                          *member.initializer);
            if (!member.initializer_materialization_attempted &&
                !in_template_definition() &&
                !file_.entity(entity).has_static_initializer) {
                if (!materialize_record_static_data_member_initializer(
                        entity,
                        member.type,
                        *member.initializer,
                        member.loc,
                        member.initialization_kind)) {
                    decl.has_error = true;
                }
            }
        }

        cir::RecordStaticDataMemberFact fact =
            make_record_static_data_member_fact(file_, member);
        fact.entity = entity;
        record_member_declaration(entity, decl.entity,
                                  member.declared_access, member.loc);
        static_member_facts.push_back(std::move(fact));
    }

    if (lang_opts_.is_cxx20_or_later()) {
        bool has_declared_equality = std::any_of(
            methods.begin(), methods.end(),
            [](const RecordMethodInput& method) {
                return method.name == "operator==";
            });
        auto pending_friends = tstate().pending_function_friends_.find(
            static_cast<uint64_t>(decl.entity.index));
        if (pending_friends != tstate().pending_function_friends_.end()) {
            for (const cir::RecordFunctionFriendGrant& grant :
                 pending_friends->second) {
                std::string_view friend_name;
                if (grant.name.valid()) {
                    friend_name = file_.name(grant.name);
                } else if (grant.entity.valid() && file_.valid(grant.entity) &&
                           file_.entity(grant.entity).name.valid()) {
                    friend_name = file_.name(file_.entity(grant.entity).name);
                }
                has_declared_equality =
                    has_declared_equality || friend_name == "operator==";
            }
        }
        if (!has_declared_equality) {
            size_t original_method_count = methods.size();
            for (size_t i = 0; i < original_method_count; ++i) {
                const RecordMethodInput& spaceship = methods[i];
                if (spaceship.name != "operator<=>" ||
                    !spaceship.is_defaulted || spaceship.is_static ||
                    spaceship.is_function_template) {
                    continue;
                }
                const auto* payload =
                    std::get_if<cir::FunctionTypePayload>(
                        &file_.type_payload(file_.resolved_type(
                            spaceship.type)));
                if (!payload) {
                    continue;
                }
                RecordMethodInput equality = spaceship;
                equality.name = "operator==";
                equality.type = function_type(
                    file_.type_ref(builder_.bool_type()),
                    payload->parameters,
                    payload->is_variadic,
                    payload->has_prototype,
                    payload->member_is_const,
                    payload->exception_spec,
                    payload->parameter_pack_flags,
                    payload->member_ref_qualifier,
                    payload->member_is_volatile);
                equality.operator_function.kind =
                    cir::OperatorFunctionKind::Symbolic;
                equality.operator_function.spelling =
                    cir::OperatorFunctionSpelling::Equal;
                equality.operator_function.conversion_type = {};
                equality.operator_function.literal_suffix = {};
                equality.precreated_entity = {};
                equality.is_implicitly_declared = true;
                equality.implicit_equality_source_index = i;
                equality.is_defaulted = true;
                equality.has_explicit_exception_spec = false;
                equality.has_deferred_noexcept_operand = false;
                equality.noexcept_operand_begin = 0;
                equality.noexcept_operand_end = 0;
                methods.push_back(std::move(equality));
            }
        }
    }
    if (method_entities_out && method_entities_out->size() < methods.size()) {
        method_entities_out->resize(methods.size());
    }

    std::vector<cir::EntityId> completed_method_entities(methods.size());
    std::vector<cir::RecordMethodFact> method_facts;
    method_facts.reserve(methods.size());
    std::vector<const TemplateInfo*> method_fact_template_heads;
    method_fact_template_heads.reserve(methods.size());
    for (size_t method_index = 0; method_index < methods.size(); ++method_index) {
        const RecordMethodInput& method = methods[method_index];
        if (!method.type.valid()) {
            decl.has_error = true;
            continue;
        }
        if (method.operator_function.kind ==
            cir::OperatorFunctionKind::Literal) {
            report_error(
                "literal operator must be declared at namespace scope",
                method.loc);
            decl.has_error = true;
        }
        bool is_allocation_or_deallocation =
            method.operator_function.kind ==
                cir::OperatorFunctionKind::Allocation ||
            method.operator_function.kind ==
                cir::OperatorFunctionKind::Deallocation;
        bool is_deallocation =
            method.operator_function.kind ==
                cir::OperatorFunctionKind::Deallocation;
        bool is_static_method = method.is_static ||
            is_allocation_or_deallocation;
        if (kind == cir::RecordKind::Union && method.is_virtual) {
            report_error("a union cannot have virtual functions", method.loc);
            decl.has_error = true;
        }
        if (method.is_virtual &&
            function_has_placeholder_return(method.type)) {
            report_error("a function with a deduced return type cannot be virtual",
                         method.loc);
            decl.has_error = true;
        }
        cir::TypeId method_type = method.type;

        if (method.precreated_entity.valid() &&
            file_.valid(method.precreated_entity)) {
            cir::PlaceholderResultFactId placeholder =
                file_.entity(method.precreated_entity).placeholder_result;
            if (file_.valid(placeholder)) {
                const cir::PlaceholderResultFact& result =
                    file_.placeholder_result_fact(placeholder);
                if (result.state ==
                        cir::PlaceholderResultState::Complete &&
                    result.result.type.valid()) {
                    method_type = rebuild_function_result(method_type,
                                                          result.result);
                }
            }
        }
        if (is_deallocation && !method.has_explicit_exception_spec) {
            const auto* payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(method_type)));
            if (payload) {
                method_type = function_type(
                    payload->return_type, payload->parameters,
                    payload->is_variadic, payload->has_prototype,
                    payload->member_is_const,
                    cir::FunctionExceptionSpecKind::NonThrowing,
                    payload->parameter_pack_flags,
                    payload->member_ref_qualifier,
                    payload->member_is_volatile);
            }
        }
        cir::EntityKind entity_kind = cir::EntityKind::Method;
        if (method.is_constructor) {
            entity_kind = cir::EntityKind::Constructor;
        } else if (method.is_destructor) {
            entity_kind = cir::EntityKind::Destructor;
        }
        bool is_consteval = method.flags.is_consteval ||
            consteval_only_function_type_immediately_escalates(
                method_type,
                method.flags.is_constexpr,
                entity_kind,
                in_template_instantiation());
        if (!validate_consteval_only_function_type(
                method_type, is_consteval, method.loc)) {
            decl.has_error = true;
        }
        if (is_allocation_or_deallocation && method.is_virtual) {
            report_error("allocation and deallocation functions cannot be virtual",
                         method.loc);
            decl.has_error = true;
        }
        if (is_static_method &&
            !validate_static_member_function_type(method_type, method.loc)) {
            decl.has_error = true;
        }
        if (method.is_constructor) {
            existing.definition_data.has_user_declared_constructor = true;
        } else if (method.is_destructor) {
            existing.definition_data.has_user_declared_destructor = true;
            if (method.is_deleted) {
                existing.definition_data.has_deleted_destructor = true;
            }
            if (method.is_virtual) {
                existing.has_virtual_destructor = true;
            }
        }
        if (method.is_virtual) {
            existing.is_polymorphic = true;
        }
        if (method.is_pure) {
            existing.is_abstract = true;
        }

        cir::TypeId entity_type = is_static_method
            ? method_type
            : member_function_type_with_this(decl.type, method_type);
        if (has_virtual_bases &&
            (entity_kind == cir::EntityKind::Constructor ||
             entity_kind == cir::EntityKind::Destructor)) {
            entity_type = structor_impl_type(entity_type);
        }
        cir::EntityId entity = method.precreated_entity;
        if (entity.valid()) {

            file_.entity_mut(entity).type = entity_type;
            file_.entity_mut(entity).decl_flags.is_consteval = is_consteval;
        } else {
            cir::DeclSemanticFlags entity_flags = method.flags.to_cir();
            entity_flags.is_consteval = is_consteval;
            entity = builder_.add_entity(entity_kind,
                                         method.name,
                                         entity_type,
                                         decl.entity,
                                         method.loc,
                                         cir::StorageDuration::None,
                                         cir::MemorySpace::Default,
                                         entity_flags);
            file_.entity_mut(entity).is_definition = false;
            file_.entity_mut(entity).linkage = cir::LinkageKind::External;
        }
        file_.entity_mut(entity).operator_function =
            method.operator_function;
        file_.entity_mut(entity).is_static_member_function =
            is_static_method;
        if (method_entities_out) {
            (*method_entities_out)[method_index] = entity;
        }
        completed_method_entities[method_index] = entity;
        register_placeholder_result(entity, entity_type, nullptr, method.loc);
        if (!method.is_function_template && method_type != method.type) {
            refresh_callable_binding(method.name,
                                     entity,
                                     method_type,
                                     file_.entity(entity).is_definition,
                                     method.loc);
        }
        record_member_declaration(entity, decl.entity,
                                  method.declared_access, method.loc);
        AttributeList method_attrs = method.flags.attrs;
        method_attrs.append(method.attrs);
        apply_attributes(entity, AttributeTarget::Function, method_attrs, method.loc);
        if (entity_kind == cir::EntityKind::Method ||
            entity_kind == cir::EntityKind::Constructor) {
            register_function_default_arguments(entity,
                                                method.params,
                                                nullptr,
                                                method.loc);
        }

        cir::RecordMethodFact fact;
        fact.name = method.name.empty() ? cir::NameId{} : file_.intern_name(method.name);
        fact.entity = entity;
        fact.operator_function = method.operator_function;
        fact.type = file_.type_ref(method_type);
        fact.declared_access = method.declared_access;
        fact.is_static = is_static_method;
        fact.is_function_template = method.is_function_template;
        fact.is_conversion_function = method.is_conversion_function ||
            method.operator_function.kind ==
                cir::OperatorFunctionKind::Conversion;
        fact.is_virtual = method.is_virtual;
        fact.is_override = method.is_override;
        fact.is_final = method.is_final;
        fact.is_deleted = method.is_deleted;
        fact.is_defaulted = method.is_defaulted;
        fact.is_implicitly_declared = method.is_implicitly_declared;
        if (method.implicit_equality_source_index <
            completed_method_entities.size()) {
            fact.implicit_equality_origin = completed_method_entities[
                method.implicit_equality_source_index];
        }
        fact.is_pure = method.is_pure;
        fact.is_constexpr = method.flags.is_constexpr;
        fact.is_consteval = is_consteval;
        fact.has_explicit_exception_spec =
            method.has_explicit_exception_spec;
        fact.has_deferred_noexcept_operand =
            method.has_deferred_noexcept_operand;
        fact.noexcept_operand_begin = static_cast<uint32_t>(
            method.noexcept_operand_begin);
        fact.noexcept_operand_end = static_cast<uint32_t>(
            method.noexcept_operand_end);
        fact.noexcept_operand_loc = method.noexcept_operand_loc;
        fact.noexcept_declaration_context =
            method.noexcept_declaration_context;
        fact.noexcept_lookup_generation =
            method.noexcept_lookup_generation;
        fact.declarator_parameters.reserve(method.params.size());
        for (const ParamInput& parameter : method.params) {
            cir::FunctionParameterScopeFact parameter_fact;
            if (!parameter.name.empty()) {
                parameter_fact.name = file_.intern_name(parameter.name);
            }
            parameter_fact.type = parameter.type;
            parameter_fact.loc = parameter.loc;
            parameter_fact.is_parameter_pack =
                parameter.is_parameter_pack;
            if (!parameter.source_parameter_pack_name.empty()) {
                parameter_fact.source_parameter_pack_name =
                    file_.intern_name(parameter.source_parameter_pack_name);
            }
            parameter_fact.is_parameter_pack_expansion_sentinel =
                parameter.is_parameter_pack_expansion_sentinel;
            parameter_fact.type_originates_from_template_parameter =
                parameter.type_originates_from_template_parameter;
            fact.declarator_parameters.push_back(
                std::move(parameter_fact));
        }
        fact.is_explicit = method.is_explicit;
        fact.explicit_specifier = method.explicit_specifier;
        fact.explicit_expression_begin = method.explicit_expression_begin;
        fact.explicit_expression_end = method.explicit_expression_end;
        fact.explicit_value_expression =
            method.explicit_value_expression;
        file_.canonicalize_template_value_expression(
            fact.explicit_value_expression);
        fact.explicit_declaration_context =
            method.explicit_declaration_context;
        fact.explicit_lookup_generation = method.explicit_lookup_generation;
        fact.constraint_satisfaction = method.constraint_satisfaction;
        fact.associated_constraint_fingerprint =
            method.associated_constraint_fingerprint;
        fact.more_constrained_than = method.more_constrained_than;
        fact.attributes = method_attrs.attrs;
        method_facts.push_back(std::move(fact));
        method_fact_template_heads.push_back(
            method_template_heads &&
                    method_index < method_template_heads->size()
                ? (*method_template_heads)[method_index]
                : nullptr);
    }

    auto all_parameters_defaulted_from = [&](cir::EntityId entity,
                                              size_t start,
                                              size_t count) {
        for (size_t i = start; i < count; ++i) {
            if (!callable_default_argument(entity, i)) {
                return false;
            }
        }
        return true;
    };
    auto is_defaulted_comparison_name = [&](std::string_view name) {
        return name == "operator==" || name == "operator!=" ||
               name == "operator<" || name == "operator<=" ||
               name == "operator>" || name == "operator>=" ||
               name == "operator<=>";
    };
    auto comparison_requires_bool_result = [&](std::string_view name) {
        return name != "operator<=>";
    };
    auto is_const_self_lvalue_reference = [&](cir::TypeRef parameter) {
        cir::TypeId type = file_.resolved_type(parameter.type);
        if (!file_.valid(type) ||
            file_.type(type).kind != cir::TypeKind::LValueReference) {
            return false;
        }
        cir::TypeRef referred = file_.reference_referred_ref(type);
        return file_.resolved_type(referred.type) ==
                   file_.resolved_type(decl.type) &&
               referred.qualifiers == cir::QualConst;
    };
    for (cir::RecordMethodFact& fact : method_facts) {
        if (!fact.is_defaulted || !fact.name.valid()) {
            continue;
        }
        std::string_view name = file_.name(fact.name);
        if (!is_defaulted_comparison_name(name)) {
            continue;
        }
        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(fact.type.type)));
        SrcLoc comparison_loc = fact.entity.valid() && file_.valid(fact.entity)
            ? file_.entity(fact.entity).loc
            : SrcLoc{};
        auto reject = [&](std::string message) {
            report_error(std::move(message), comparison_loc);
            fact.is_deleted = true;
            decl.has_error = true;
        };
        if (!payload) {
            reject("defaulted comparison operator has invalid function type");
            continue;
        }
        if (fact.is_static || fact.is_function_template ||
            template_info(fact.entity) != nullptr) {
            reject("defaulted comparison operator must be a non-template "
                   "non-static member or friend");
            continue;
        }
        bool valid_member_parameters =
            payload->parameters.size() == 1 && payload->member_is_const &&
            !payload->member_is_volatile &&
            payload->member_ref_qualifier !=
                cir::FunctionRefQualifierKind::RValue &&
            is_const_self_lvalue_reference(payload->parameters.front());
        if (!valid_member_parameters) {
            reject("defaulted comparison operator parameters must both have "
                   "type 'const " + file_.format_type(decl.type) + "&'");
            continue;
        }
        if (comparison_requires_bool_result(name) &&
            !is_bool_type(payload->return_type.type)) {
            reject("defaulted '" + std::string(name) +
                   "' operator must return 'bool'");
            continue;
        }
        if (name == "operator==" || name == "operator<=>") {
            bool has_reference_member = std::any_of(
                field_facts.begin(), field_facts.end(),
                [&](const cir::RecordFieldFact& field) {
                    return !field.is_base_subobject &&
                           is_reference_type(field.type.type);
                });
            bool has_variant_members =
                (kind == cir::RecordKind::Union ||
                 std::any_of(field_facts.begin(), field_facts.end(),
                             [](const cir::RecordFieldFact& field) {
                                 return field.is_anonymous_union_object;
                             })) &&
                std::any_of(field_facts.begin(), field_facts.end(),
                            [](const cir::RecordFieldFact& field) {
                                return !field.is_base_subobject;
                            });
            if (has_reference_member || has_variant_members) {

                fact.is_deleted = true;
            }
        }
    }
    auto self_reference_kind = [&](cir::TypeRef parameter)
        -> cir::SpecialMemberKind {
        cir::TypeId type = file_.resolved_type(parameter.type);
        if (!file_.valid(type)) {
            return cir::SpecialMemberKind::None;
        }
        cir::TypeKind reference_kind = file_.type(type).kind;
        if (reference_kind != cir::TypeKind::LValueReference &&
            reference_kind != cir::TypeKind::RValueReference) {
            return cir::SpecialMemberKind::None;
        }
        if (file_.resolved_type(file_.reference_referred_type(type)) !=
            file_.resolved_type(decl.type)) {
            return cir::SpecialMemberKind::None;
        }
        return reference_kind == cir::TypeKind::RValueReference
            ? cir::SpecialMemberKind::MoveConstructor
            : cir::SpecialMemberKind::CopyConstructor;
    };
    auto classify_declared_special_member = [&](cir::RecordMethodFact& fact) {
        if (!fact.entity.valid() || !file_.valid(fact.entity)) {
            return;
        }
        cir::EntityKind entity_kind = file_.entity(fact.entity).kind;
        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(fact.type.type)));
        if (!payload) {
            return;
        }
        if (entity_kind == cir::EntityKind::Destructor) {
            fact.special_member_kind = cir::SpecialMemberKind::Destructor;
        } else if (entity_kind == cir::EntityKind::Constructor) {

            if (fact.is_function_template ||
                template_info(fact.entity) != nullptr) {
                return;
            }
            if (!payload->parameters.empty() &&
                file_.resolved_type(payload->parameters.front().type) ==
                    file_.resolved_type(decl.type) &&
                all_parameters_defaulted_from(
                    fact.entity, 1, payload->parameters.size())) {
                report_error(
                    "copy/move constructor first parameter must be a reference",
                    file_.entity(fact.entity).loc);
                fact.is_deleted = true;
                decl.has_error = true;
                return;
            }
            if (payload->parameters.empty() ||
                all_parameters_defaulted_from(fact.entity, 0,
                                              payload->parameters.size())) {
                fact.special_member_kind =
                    cir::SpecialMemberKind::DefaultConstructor;
            } else if (all_parameters_defaulted_from(
                           fact.entity, 1, payload->parameters.size())) {
                fact.special_member_kind =
                    self_reference_kind(payload->parameters.front());
            }
        } else if (entity_kind == cir::EntityKind::Method &&
                   !fact.is_static && fact.name.valid() &&
                   file_.name(fact.name) == "operator=" &&
                   payload->parameters.size() == 1 &&
                   template_info(fact.entity) == nullptr) {
            cir::TypeId parameter =
                file_.resolved_type(payload->parameters.front().type);
            if (parameter == file_.resolved_type(decl.type)) {
                fact.special_member_kind =
                    cir::SpecialMemberKind::CopyAssignment;
                if (fact.is_defaulted) {
                    report_error(
                        "explicitly defaulted copy assignment operator "
                        "parameter must be an lvalue reference",
                        file_.entity(fact.entity).loc);
                    fact.is_deleted = true;
                    decl.has_error = true;
                }
            } else {
                cir::SpecialMemberKind constructor_kind =
                    self_reference_kind(payload->parameters.front());
                if (constructor_kind ==
                    cir::SpecialMemberKind::CopyConstructor) {
                    fact.special_member_kind =
                        cir::SpecialMemberKind::CopyAssignment;
                } else if (constructor_kind ==
                           cir::SpecialMemberKind::MoveConstructor) {
                    fact.special_member_kind =
                        cir::SpecialMemberKind::MoveAssignment;
                }
            }
        }
        if (fact.special_member_kind == cir::SpecialMemberKind::None) {
            return;
        }
        if (fact.is_defaulted &&
            (fact.special_member_kind ==
                 cir::SpecialMemberKind::CopyAssignment ||
             fact.special_member_kind ==
                 cir::SpecialMemberKind::MoveAssignment)) {
            cir::TypeId result =
                file_.resolved_type(payload->return_type.type);
            bool returns_self_lvalue = file_.valid(result) &&
                file_.type(result).kind == cir::TypeKind::LValueReference;
            if (returns_self_lvalue) {
                cir::TypeRef referred = file_.reference_referred_ref(result);
                returns_self_lvalue =
                    file_.resolved_type(referred.type) ==
                        file_.resolved_type(decl.type) &&
                    referred.qualifiers == cir::QualNone;
            }
            if (!returns_self_lvalue) {
                report_error(
                    "explicitly defaulted copy/move assignment operator "
                    "must return an lvalue reference to its class",
                    file_.entity(fact.entity).loc);
                fact.is_deleted = true;
                decl.has_error = true;
            }
        }
        fact.is_user_provided = !fact.is_defaulted && !fact.is_deleted;
        fact.is_eligible =
            fact.constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Unsatisfied &&
            fact.constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Invalid;
        switch (fact.special_member_kind) {
            case cir::SpecialMemberKind::DefaultConstructor:
                existing.definition_data.has_default_constructor = true;
                existing.definition_data.default_constructor_is_deleted |=
                    fact.is_deleted;
                break;
            case cir::SpecialMemberKind::CopyConstructor:
                existing.definition_data.has_copy_constructor = true;
                existing.definition_data.has_user_declared_copy_constructor =
                    true;
                break;
            case cir::SpecialMemberKind::MoveConstructor:
                existing.definition_data.has_move_constructor = true;
                existing.definition_data.has_user_declared_move_constructor =
                    true;
                break;
            case cir::SpecialMemberKind::CopyAssignment:
                existing.definition_data.has_copy_assignment = true;
                existing.definition_data.has_user_declared_copy_assignment =
                    true;
                break;
            case cir::SpecialMemberKind::MoveAssignment:
                existing.definition_data.has_move_assignment = true;
                existing.definition_data.has_user_declared_move_assignment =
                    true;
                break;
            case cir::SpecialMemberKind::Destructor:
            case cir::SpecialMemberKind::None:
                break;
        }
    };
    for (cir::RecordMethodFact& fact : method_facts) {
        classify_declared_special_member(fact);
    }

    enum class MemberNameCategory : uint8_t { Data, Function };
    struct SeenMemberName {
        MemberNameCategory category = MemberNameCategory::Data;
        SrcLoc loc{};
    };
    std::unordered_map<std::string, SeenMemberName> seen_member_names;
    struct SeenMethodSignature {
        cir::TypeId type{};
        uint64_t constraint_fingerprint = 0;
        const TemplateInfo* template_head = nullptr;
    };
    std::unordered_map<std::string, std::vector<SeenMethodSignature>>
        seen_method_signatures;
    auto note_member_name = [&](std::string_view name,
                                MemberNameCategory category,
                                SrcLoc member_loc) {
        if (name.empty()) {
            return;
        }
        auto [it, inserted] = seen_member_names.emplace(
            std::string(name), SeenMemberName{category, member_loc});
        if (!inserted &&
            (category == MemberNameCategory::Data ||
             it->second.category == MemberNameCategory::Data)) {
            report_error("member '" + std::string(name) +
                             "' is declared more than once",
                         member_loc);
            decl.has_error = true;
        }
    };

    std::string class_name = decl.entity.valid() && file_.valid(decl.entity) &&
            file_.entity(decl.entity).name.valid()
        ? std::string(file_.name(file_.entity(decl.entity).name))
        : std::string{};
    for (const cir::RecordFieldFact& field : field_facts) {
        if (!field.name.valid()) {
            continue;
        }
        std::string_view name = file_.name(field.name);
        if (!class_name.empty() && name == class_name &&
            existing.definition_data.has_user_declared_constructor) {
            report_error("non-static data member '" + std::string(name) +
                             "' has the same name as its class with a user-declared constructor",
                         file_.entity(field.entity).loc);
            decl.has_error = true;
        }
        note_member_name(name,
                         MemberNameCategory::Data,
                         file_.entity(field.entity).loc);
    }
    for (const cir::RecordStaticDataMemberFact& member : static_member_facts) {
        if (!member.name.valid()) {
            continue;
        }
        std::string_view name = file_.name(member.name);
        if (!class_name.empty() && name == class_name) {
            report_error("static data member '" + std::string(name) +
                             "' has the same name as its class",
                         file_.entity(member.entity).loc);
            decl.has_error = true;
        }
        note_member_name(name,
                         MemberNameCategory::Data,
                         file_.entity(member.entity).loc);
    }
    for (size_t method_index = 0; method_index < method_facts.size();
         ++method_index) {
        const cir::RecordMethodFact& method = method_facts[method_index];
        if (!method.name.valid() || !method.entity.valid()) {
            continue;
        }
        cir::EntityKind entity_kind = file_.entity(method.entity).kind;
        std::string_view name = file_.name(method.name);
        if (!class_name.empty() && name == class_name &&
            entity_kind != cir::EntityKind::Constructor) {
            report_error("member function '" + std::string(name) +
                             "' has the same name as its class",
                         file_.entity(method.entity).loc);
            decl.has_error = true;
        }
        std::vector<SeenMethodSignature>& signatures =
            seen_method_signatures[std::string(name)];
        const TemplateInfo* method_template =
            method_fact_template_heads[method_index];
        bool redeclared = std::any_of(
            signatures.begin(), signatures.end(),
            [&](const SeenMethodSignature& prior) {
                if (prior.template_head || method_template) {
                    return prior.template_head && method_template &&
                        function_template_declarations_correspond(
                            *prior.template_head, *method_template);
                }
                return function_signatures_match(prior.type,
                                                 method.type.type) &&
                    prior.constraint_fingerprint ==
                        method.associated_constraint_fingerprint;
            });
        bool incompatible_ref_overload = std::any_of(
            signatures.begin(), signatures.end(),
            [&](const SeenMethodSignature& prior) {
                const auto* lhs = std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(file_.resolved_type(prior.type)));
                const auto* rhs = std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(
                        file_.resolved_type(method.type.type)));
                if (!lhs || !rhs ||
                    lhs->member_is_const != rhs->member_is_const ||
                    lhs->member_is_volatile != rhs->member_is_volatile ||
                    lhs->is_variadic != rhs->is_variadic ||
                    lhs->parameters.size() != rhs->parameters.size()) {
                    return false;
                }
                for (size_t index = 0; index < lhs->parameters.size();
                     ++index) {
                    if (!types_compatible(lhs->parameters[index],
                                          rhs->parameters[index])) {
                        return false;
                    }
                }
                bool lhs_unqualified = lhs->member_ref_qualifier ==
                    cir::FunctionRefQualifierKind::None;
                bool rhs_unqualified = rhs->member_ref_qualifier ==
                    cir::FunctionRefQualifierKind::None;
                return lhs_unqualified != rhs_unqualified;
            });
        if (redeclared) {
            report_error("member function '" + std::string(name) +
                             "' is declared more than once with the same parameter-type-list",
                         file_.entity(method.entity).loc);
            decl.has_error = true;
        } else if (incompatible_ref_overload) {
            report_error("member function '" + std::string(name) +
                             "' cannot be overloaded with and without a ref-qualifier",
                         file_.entity(method.entity).loc);
            decl.has_error = true;
        } else {
            signatures.push_back(SeenMethodSignature{
                method.type.type,
                method.associated_constraint_fingerprint,
                method_template});
        }
        note_member_name(name,
                         MemberNameCategory::Function,
                         file_.entity(method.entity).loc);
    }

    cir::EntityId implicit_destructor{};
    cir::EntityId implicit_default_constructor{};
    cir::EntityId implicit_copy_constructor{};
    cir::EntityId implicit_move_constructor{};
    cir::EntityId implicit_copy_assignment{};
    cir::EntityId implicit_move_assignment{};

    auto add_implicit_special = [&](cir::SpecialMemberKind special_kind,
                                    cir::EntityKind entity_kind,
                                    std::string_view name,
                                    cir::TypeId declared_type,
                                    bool deleted) {
        cir::TypeId entity_type =
            member_function_type_with_this(decl.type, declared_type);
        if (has_virtual_bases &&
            (entity_kind == cir::EntityKind::Constructor ||
             entity_kind == cir::EntityKind::Destructor)) {
            entity_type = structor_impl_type(entity_type);
        }
        cir::EntityId entity = builder_.add_entity(
            entity_kind, name, entity_type, decl.entity, loc,
            cir::StorageDuration::None);
        file_.entity_mut(entity).is_definition = false;
        file_.entity_mut(entity).linkage = cir::LinkageKind::External;
        file_.entity_mut(entity).decl_flags.is_inline = true;
        cir::RecordMethodFact fact;
        fact.name = file_.intern_name(name);
        fact.entity = entity;
        fact.type = file_.type_ref(declared_type);
        fact.is_defaulted = true;
        fact.is_deleted = deleted;
        fact.special_member_kind = special_kind;
        fact.is_implicitly_declared = true;
        fact.is_eligible = true;
        method_facts.push_back(std::move(fact));
        return entity;
    };

    const std::string constructor_name =
        std::string(file_.name(file_.entity(decl.entity).name));
    const std::string destructor_name = "~" + constructor_name;
    const cir::TypeRef void_ref =
        file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::Void));
    auto copy_constructor_accepts_const =
        [&](auto&& self, cir::TypeId type) -> bool {
            type = file_.resolved_type(type);
            if (!file_.valid(type)) {
                return false;
            }
            if (file_.type(type).kind == cir::TypeKind::Array) {
                const auto* array = std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(type));
                return array && self(self, array->element_type.type);
            }
            if (file_.type(type).kind != cir::TypeKind::Record) {
                return true;
            }
            const cir::RecordFacts* subobject =
                file_.record_facts_for_type(type);
            if (!subobject) {
                return false;
            }
            for (const cir::RecordMethodFact& method : subobject->methods) {
                if (method.special_member_kind !=
                        cir::SpecialMemberKind::CopyConstructor ||
                    method.constraint_satisfaction ==
                        cir::ConstraintSatisfactionKind::Unsatisfied ||
                    method.constraint_satisfaction ==
                        cir::ConstraintSatisfactionKind::Invalid) {
                    continue;
                }
                const auto* method_type =
                    std::get_if<cir::FunctionTypePayload>(
                        &file_.type_payload(
                            file_.resolved_type(method.type.type)));
                if (!method_type || method_type->parameters.empty()) {
                    continue;
                }
                cir::TypeId parameter = file_.resolved_type(
                    method_type->parameters.front().type);
                if (!file_.valid(parameter) ||
                    file_.type(parameter).kind !=
                        cir::TypeKind::LValueReference) {
                    continue;
                }
                cir::TypeRef referred =
                    file_.reference_referred_ref(parameter);
                if (file_.resolved_type(referred.type) == type &&
                    (referred.qualifiers & cir::QualConst) != 0) {
                    return true;
                }
            }
            return false;
        };
    bool implicit_copy_accepts_const = true;
    for (const cir::RecordBaseFact& base : base_facts) {
        implicit_copy_accepts_const = implicit_copy_accepts_const &&
            copy_constructor_accepts_const(
                copy_constructor_accepts_const, base.type.type);
    }
    for (const cir::RecordFieldFact& field : field_facts) {
        implicit_copy_accepts_const = implicit_copy_accepts_const &&
            copy_constructor_accepts_const(
                copy_constructor_accepts_const, field.type.type);
    }
    cir::TypeRef copy_self = file_.type_ref(decl.type);
    if (implicit_copy_accepts_const) {
        copy_self.qualifiers |= cir::QualConst;
    }
    cir::TypeId copy_ref =
        file_.reference_type(copy_self, cir::ReferenceKind::LValue);
    auto copy_assignment_accepts_const =
        [&](auto&& self, cir::TypeId type) -> bool {
            type = file_.resolved_type(type);
            if (!file_.valid(type)) {
                return false;
            }
            if (file_.type(type).kind == cir::TypeKind::Array) {
                const auto* array = std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(type));
                return array && self(self, array->element_type.type);
            }
            if (file_.type(type).kind != cir::TypeKind::Record) {
                return true;
            }
            const cir::RecordFacts* subobject =
                file_.record_facts_for_type(type);
            if (!subobject) {
                return false;
            }
            for (const cir::RecordMethodFact& method : subobject->methods) {
                if (method.special_member_kind !=
                        cir::SpecialMemberKind::CopyAssignment ||
                    method.constraint_satisfaction ==
                        cir::ConstraintSatisfactionKind::Unsatisfied ||
                    method.constraint_satisfaction ==
                        cir::ConstraintSatisfactionKind::Invalid) {
                    continue;
                }
                const auto* method_type =
                    std::get_if<cir::FunctionTypePayload>(
                        &file_.type_payload(
                            file_.resolved_type(method.type.type)));
                if (!method_type || method_type->parameters.size() != 1) {
                    continue;
                }
                cir::TypeId parameter = file_.resolved_type(
                    method_type->parameters.front().type);
                if (parameter == type) {
                    return true;
                }
                if (!file_.valid(parameter) ||
                    file_.type(parameter).kind !=
                        cir::TypeKind::LValueReference) {
                    continue;
                }
                cir::TypeRef referred =
                    file_.reference_referred_ref(parameter);
                if (file_.resolved_type(referred.type) == type &&
                    (referred.qualifiers & cir::QualConst) != 0) {
                    return true;
                }
            }
            return false;
        };
    bool implicit_assignment_accepts_const = true;
    for (const cir::RecordBaseFact& base : base_facts) {
        implicit_assignment_accepts_const =
            implicit_assignment_accepts_const &&
            copy_assignment_accepts_const(
                copy_assignment_accepts_const, base.type.type);
    }
    for (const cir::RecordFieldFact& field : field_facts) {
        implicit_assignment_accepts_const =
            implicit_assignment_accepts_const &&
            copy_assignment_accepts_const(
                copy_assignment_accepts_const, field.type.type);
    }
    cir::TypeRef assignment_self = file_.type_ref(decl.type);
    if (implicit_assignment_accepts_const) {
        assignment_self.qualifiers |= cir::QualConst;
    }
    cir::TypeId assignment_copy_ref =
        file_.reference_type(assignment_self,
                             cir::ReferenceKind::LValue);
    cir::TypeId move_ref = file_.reference_type(
        file_.type_ref(decl.type), cir::ReferenceKind::RValue);
    cir::TypeId self_lref = file_.reference_type(
        file_.type_ref(decl.type), cir::ReferenceKind::LValue);

    if (lang_opts_.is_cxx_mode() &&
        !existing.definition_data.has_user_declared_destructor) {
        implicit_destructor = add_implicit_special(
            cir::SpecialMemberKind::Destructor,
            cir::EntityKind::Destructor, destructor_name,
            function_type(void_ref, {}, false, true), false);
    }
    if (lang_opts_.is_cxx_mode() &&
        !existing.definition_data.has_user_declared_constructor) {
        implicit_default_constructor = add_implicit_special(
            cir::SpecialMemberKind::DefaultConstructor,
            cir::EntityKind::Constructor, constructor_name,
            function_type(void_ref, {}, false, true),
            existing.is_lambda_closure && !field_facts.empty());
        existing.definition_data.has_default_constructor = true;
    }
    bool suppress_copy =
        existing.definition_data.has_user_declared_move_constructor ||
        existing.definition_data.has_user_declared_move_assignment;
    if (lang_opts_.is_cxx_mode() &&
        !existing.definition_data.has_user_declared_copy_constructor) {
        implicit_copy_constructor = add_implicit_special(
            cir::SpecialMemberKind::CopyConstructor,
            cir::EntityKind::Constructor, constructor_name,
            function_type(void_ref, {file_.type_ref(copy_ref)}, false, true),
            suppress_copy);
        existing.definition_data.has_copy_constructor = true;
    }
    bool declare_move = lang_opts_.is_cxx_mode() &&
        !existing.definition_data.has_user_declared_copy_constructor &&
        !existing.definition_data.has_user_declared_move_constructor &&
        !existing.definition_data.has_user_declared_copy_assignment &&
        !existing.definition_data.has_user_declared_move_assignment &&
        !existing.definition_data.has_user_declared_destructor;
    if (declare_move) {
        implicit_move_constructor = add_implicit_special(
            cir::SpecialMemberKind::MoveConstructor,
            cir::EntityKind::Constructor, constructor_name,
            function_type(void_ref, {file_.type_ref(move_ref)}, false, true),
            false);
        existing.definition_data.has_move_constructor = true;
    }
    if (lang_opts_.is_cxx_mode() &&
        !existing.definition_data.has_user_declared_copy_assignment) {
        implicit_copy_assignment = add_implicit_special(
            cir::SpecialMemberKind::CopyAssignment,
            cir::EntityKind::Method, "operator=",
            function_type(file_.type_ref(self_lref),
                          {file_.type_ref(assignment_copy_ref)}, false, true),
            suppress_copy);
        existing.definition_data.has_copy_assignment = true;
    }
    if (declare_move) {
        implicit_move_assignment = add_implicit_special(
            cir::SpecialMemberKind::MoveAssignment,
            cir::EntityKind::Method, "operator=",
            function_type(file_.type_ref(self_lref),
                          {file_.type_ref(move_ref)}, false, true),
            false);
        existing.definition_data.has_move_assignment = true;
    }

    // The [class.inhctor.init] ABI invariant retains the ultimate constructor
    // and resolves its route only after base-subobject identities stabilize.
    struct InheritedConstructorPlan {
        struct NominationRoute {
            cir::EntityId direct_base{};
            cir::TypeId direct_base_type{};
            std::string direct_base_name;
            std::vector<uint32_t> base_origin_subobjects;
            SrcLoc using_loc{};
        };
        cir::EntityId entity{};
        cir::EntityId origin{};
        cir::EntityId origin_record{};
        std::vector<NominationRoute> nominations;
        bool deleted = false;
    };
    std::vector<InheritedConstructorPlan> inherited_constructor_plans;
    std::unordered_map<uint64_t, size_t> inherited_plan_by_origin;
    for (const cir::RecordInheritedConstructorNominationFact& nomination :
         existing.inherited_constructor_nominations) {
        cir::EntityId base_entity = nomination.nominated_record;
        if (!base_entity.valid()) {

            if (!in_template_definition() &&
                !existing.is_template_pattern_provisional) {
                report_error("constructor using-declaration does not resolve "
                             "to a direct base class", nomination.loc);
                decl.has_error = true;
            }
            continue;
        }
        cir::TypeId nominated_base_type{};
        for (const cir::RecordBaseFact& base_entry : base_facts) {
            if (base_entry.record_entity == base_entity) {
                nominated_base_type = base_entry.type.type;
                break;
            }
        }
        if (!nominated_base_type.valid()) {
            report_error(
                "constructors can only be inherited from a direct base "
                "class",
                nomination.loc);
            decl.has_error = true;
            continue;
        }
        const cir::RecordFacts* nominated_facts =
            file_.record_facts(base_entity);
        if (!nominated_facts) {
            continue;
        }
        std::string base_name =
            std::string(file_.name(file_.entity(base_entity).name));
        for (const cir::RecordMethodFact& origin :
             nominated_facts->methods) {
            if (!origin.entity.valid() || !file_.valid(origin.entity) ||
                file_.entity(origin.entity).kind !=
                    cir::EntityKind::Constructor ||
                origin.special_member_kind !=
                    cir::SpecialMemberKind::None) {
                continue;
            }
            const TemplateInfo* origin_template =
                template_info(origin.entity);
            cir::EntityId ultimate_origin = origin.entity;
            cir::EntityId ultimate_record = base_entity;
            if (origin.inherited_constructor) {
                ultimate_origin =
                    origin.inherited_constructor->origin_constructor;
                ultimate_record =
                    origin.inherited_constructor->origin_record;
            }
            InheritedConstructorPlan::NominationRoute route;
            route.direct_base = base_entity;
            route.direct_base_type = nominated_base_type;
            route.direct_base_name = base_name;
            route.using_loc = nomination.loc;
            if (origin.inherited_constructor) {
                for (const cir::InheritedConstructorRouteFact& inherited_route :
                     origin.inherited_constructor->routes) {
                    if (std::find(route.base_origin_subobjects.begin(),
                                  route.base_origin_subobjects.end(),
                                  inherited_route.origin_subobject) ==
                        route.base_origin_subobjects.end()) {
                        route.base_origin_subobjects.push_back(
                            inherited_route.origin_subobject);
                    }
                }
            } else {
                route.base_origin_subobjects.push_back(0);
            }

            auto prior = inherited_plan_by_origin.find(
                static_cast<uint64_t>(ultimate_origin.index));
            if (prior != inherited_plan_by_origin.end()) {
                inherited_constructor_plans[prior->second]
                    .nominations.push_back(std::move(route));
                continue;
            }
            cir::TypeId entity_type = member_function_type_with_this(
                decl.type, origin.type.type);
            if (has_virtual_bases) {
                entity_type = structor_impl_type(entity_type);
            }
            cir::EntityId inherited = builder_.add_entity(
                cir::EntityKind::Constructor, constructor_name,
                entity_type, decl.entity, loc,
                cir::StorageDuration::None);
            file_.entity_mut(inherited).is_definition = false;
            file_.entity_mut(inherited).linkage =
                cir::LinkageKind::External;
            file_.entity_mut(inherited).decl_flags.is_inline = true;
            file_.entity_mut(inherited).decl_flags.is_constexpr =
                origin.is_constexpr;
            file_.entity_mut(inherited).decl_flags.is_consteval =
                origin.is_consteval;
            record_member_declaration(inherited, decl.entity,
                                      origin.declared_access, loc);
            cir::RecordMethodFact fact;
            fact.name = file_.intern_name(constructor_name);
            fact.entity = inherited;
            fact.type = origin.type;
            fact.declared_access = origin.declared_access;
            fact.is_explicit = origin.is_explicit;
            fact.explicit_specifier = origin.explicit_specifier;
            fact.explicit_value_expression =
                origin.explicit_value_expression;
            fact.is_deleted = origin.is_deleted;
            fact.is_consteval = origin.is_consteval;
            fact.is_constexpr = origin.is_constexpr;
            fact.has_explicit_exception_spec =
                origin.has_explicit_exception_spec;
            fact.has_computed_exception_spec =
                origin.has_computed_exception_spec;
            fact.constraint_satisfaction =
                origin.constraint_satisfaction;
            fact.associated_constraint_fingerprint =
                origin.associated_constraint_fingerprint;
            fact.more_constrained_than = origin.more_constrained_than;
            fact.attributes = origin.attributes;
            fact.is_eligible = origin.is_eligible;
            fact.is_function_template = origin_template != nullptr;
            cir::InheritedConstructorFact inherited_fact;
            inherited_fact.origin_constructor = ultimate_origin;
            inherited_fact.origin_record = ultimate_record;
            fact.inherited_constructor = std::move(inherited_fact);
            method_facts.push_back(std::move(fact));
            if (origin_template) {
                TemplateInfo inherited_template = *origin_template;
                inherited_template.name = constructor_name;
                inherited_template.entity = {};
                (void)register_template_entity(
                    std::move(inherited_template), inherited,
                    nomination.loc);
            }
            InheritedConstructorPlan plan;
            plan.entity = inherited;
            plan.origin = ultimate_origin;
            plan.origin_record = ultimate_record;
            plan.nominations.push_back(std::move(route));
            plan.deleted = origin.is_deleted;
            inherited_plan_by_origin.emplace(
                static_cast<uint64_t>(ultimate_origin.index),
                inherited_constructor_plans.size());
            inherited_constructor_plans.push_back(std::move(plan));
        }
    }

    RecordLayoutInfo layout = compute_record_layout(kind,
                                                    existing.is_packed,
                                                    existing.requested_alignment,
                                                    existing.pack_alignment,
                                                    field_facts,
                                                    loc);
    decl.has_error = decl.has_error || layout.has_error;

    {
        size_t ordinal = 0;
        for (size_t i = 0; i < base_facts.size(); ++i) {
            if (base_facts[i].is_virtual) {
                continue;
            }
            size_t field_index = base_field_start + ordinal++;
            if (field_index >= layout.fields.size()) {
                break;
            }
            layout.fields[field_index].is_base_subobject = true;
            base_facts[i].has_non_virtual_offset = true;
            base_facts[i].non_virtual_offset = layout.fields[field_index].offset;
        }
    }
    size_t non_virtual_size_bits = layout.size_bits;
    for (size_t i = 0; i < virtual_base_list.size(); ++i) {
        size_t field_index = vbase_field_start + i;
        if (field_index >= layout.fields.size()) {
            break;
        }
        layout.fields[field_index].is_base_subobject = true;
        layout.fields[field_index].is_virtual_base_storage = true;
        virtual_base_list[i].storage_field = layout.fields[field_index].entity;
        virtual_base_list[i].storage_offset_bytes =
            layout.fields[field_index].offset;
        if (i == 0) {
            non_virtual_size_bits = layout.fields[field_index].offset * 8;
        }
    }

    if (has_virtual_bases) {
        cir::DeclContextId early_context =
            file_.entity(decl.entity).semantic_context;
        if (!early_context.valid()) {
            early_context =
                file_.create_decl_context(cir::DeclContextKind::Record,
                                          current_decl_context(),
                                          decl.entity,
                                          loc);
            file_.entity_mut(decl.entity).semantic_context = early_context;
        }
        for (const cir::RecordMethodFact& fact : method_facts) {
            if (!fact.entity.valid()) {
                continue;
            }
            cir::EntityKind fact_kind = file_.entity(fact.entity).kind;
            if (fact_kind != cir::EntityKind::Constructor &&
                fact_kind != cir::EntityKind::Destructor) {
                continue;
            }
            file_.entity_mut(fact.entity).semantic_context = early_context;
            cir::EntityId inherited_origin =
                fact.inherited_constructor
                ? fact.inherited_constructor->origin_record
                : cir::EntityId{};
            synthesize_structor_variant(fact.entity, true, loc,
                                        inherited_origin);
            synthesize_structor_variant(fact.entity, false, loc,
                                        inherited_origin);
        }
    }

    std::vector<cir::VirtualSubobjectFact> virtual_subobjects;
    std::vector<cir::VirtualSubobjectEdgeFact> virtual_subobject_edges;
    std::vector<cir::VirtualOverrideEdgeFact> virtual_override_edges;
    std::vector<cir::VirtualFinalOverriderFact> virtual_final_overriders;
    {
        cir::VirtualSubobjectFact root;
        root.id = 0;
        root.record_entity = decl.entity;
        root.type = file_.type_ref(decl.type);
        virtual_subobjects.push_back(std::move(root));

        std::unordered_map<uint64_t, uint32_t> virtual_nodes;
        auto facts_for_node = [&](uint32_t node)
            -> const cir::RecordFacts* {
            if (node == 0 || node >= virtual_subobjects.size()) {
                return nullptr;
            }
            return file_.record_facts(
                virtual_subobjects[node].record_entity);
        };
        auto bases_for_node = [&](uint32_t node)
            -> const std::vector<cir::RecordBaseFact>* {
            if (node == 0) {
                return &base_facts;
            }
            const cir::RecordFacts* record = facts_for_node(node);
            return record ? &record->bases : nullptr;
        };
        auto fields_for_node = [&](uint32_t node)
            -> const std::vector<cir::RecordFieldFact>* {
            if (node == 0) {
                return &layout.fields;
            }
            const cir::RecordFacts* record = facts_for_node(node);
            return record ? &record->fields : nullptr;
        };
        auto direct_storage_field =
            [&](uint32_t node,
                const cir::RecordBaseFact& base) -> const cir::RecordFieldFact* {
            const std::vector<cir::RecordFieldFact>* fields_for_record =
                fields_for_node(node);
            if (!fields_for_record) {
                return nullptr;
            }
            for (const cir::RecordFieldFact& field : *fields_for_record) {
                if (!field.is_base_subobject ||
                    field.is_virtual_base_storage ||
                    file_.record_entity(file_.resolved_type(field.type.type)) !=
                        base.record_entity) {
                    continue;
                }
                if (!base.has_non_virtual_offset ||
                    field.offset == base.non_virtual_offset) {
                    return &field;
                }
            }
            return nullptr;
        };
        auto root_virtual_storage =
            [&](cir::EntityId record) -> const cir::RecordFacts::VirtualBase* {
            for (const cir::RecordFacts::VirtualBase& base :
                 virtual_base_list) {
                if (base.record_entity == record) {
                    return &base;
                }
            }
            return nullptr;
        };

        std::function<void(uint32_t)> expand_node;
        expand_node = [&](uint32_t node) {
            const std::vector<cir::RecordBaseFact>* node_bases =
                bases_for_node(node);
            if (!node_bases) {
                return;
            }
            std::vector<const cir::RecordBaseFact*> ordered;
            ordered.reserve(node_bases->size());
            for (const cir::RecordBaseFact& base : *node_bases) {
                ordered.push_back(&base);
            }
            std::stable_sort(
                ordered.begin(), ordered.end(),
                [](const cir::RecordBaseFact* lhs,
                   const cir::RecordBaseFact* rhs) {
                    return lhs->declaration_index < rhs->declaration_index;
                });
            for (const cir::RecordBaseFact* base : ordered) {
                if (!base || !base->record_entity.valid()) {
                    continue;
                }
                uint32_t base_node = 0;
                bool created = false;
                if (base->is_virtual) {
                    uint64_t key =
                        static_cast<uint64_t>(base->record_entity.index);
                    auto found = virtual_nodes.find(key);
                    if (found != virtual_nodes.end()) {
                        base_node = found->second;
                    } else {
                        const cir::RecordFacts::VirtualBase* storage =
                            root_virtual_storage(base->record_entity);
                        if (!storage || !storage->storage_field.valid()) {
                            continue;
                        }
                        cir::VirtualSubobjectFact subobject;
                        subobject.id = static_cast<uint32_t>(
                            virtual_subobjects.size());
                        subobject.record_entity = base->record_entity;
                        subobject.type = base->type;
                        subobject.storage_path.push_back(
                            storage->storage_field);
                        subobject.static_offset_bytes =
                            storage->storage_offset_bytes;
                        subobject.is_virtual = true;
                        base_node = subobject.id;
                        virtual_subobjects.push_back(std::move(subobject));
                        virtual_nodes.emplace(key, base_node);
                        created = true;
                    }
                } else {
                    const cir::RecordFieldFact* storage =
                        direct_storage_field(node, *base);
                    if (!storage) {
                        continue;
                    }
                    cir::VirtualSubobjectFact subobject;
                    subobject.id = static_cast<uint32_t>(
                        virtual_subobjects.size());
                    subobject.record_entity = base->record_entity;
                    subobject.type = base->type;
                    subobject.storage_path =
                        virtual_subobjects[node].storage_path;
                    subobject.storage_path.push_back(storage->entity);
                    subobject.static_offset_bytes =
                        virtual_subobjects[node].static_offset_bytes +
                        storage->offset;
                    base_node = subobject.id;
                    virtual_subobjects.push_back(std::move(subobject));
                    created = true;
                }
                cir::VirtualSubobjectEdgeFact edge;
                edge.derived_subobject = node;
                edge.base_subobject = base_node;
                edge.declared_access = base->declared_access;
                edge.declaration_index = base->declaration_index;
                edge.is_virtual = base->is_virtual;
                virtual_subobject_edges.push_back(std::move(edge));
                if (created) {
                    expand_node(base_node);
                }
            }
        };
        expand_node(0);

        auto node_reaches = [&](uint32_t derived, uint32_t base) {
            if (derived == base) {
                return true;
            }
            std::vector<uint32_t> worklist{derived};
            std::vector<bool> visited(virtual_subobjects.size(), false);
            while (!worklist.empty()) {
                uint32_t current = worklist.back();
                worklist.pop_back();
                if (current >= visited.size() || visited[current]) {
                    continue;
                }
                visited[current] = true;
                for (const cir::VirtualSubobjectEdgeFact& edge :
                     virtual_subobject_edges) {
                    if (edge.derived_subobject != current) {
                        continue;
                    }
                    if (edge.base_subobject == base) {
                        return true;
                    }
                    worklist.push_back(edge.base_subobject);
                }
            }
            return false;
        };
        auto method_corresponds =
            [&](const cir::RecordMethodFact& overriding,
                const cir::RecordMethodFact& overridden) {
            if (!overriding.entity.valid() || !overridden.entity.valid() ||
                overriding.is_static || overridden.is_static) {
                return false;
            }
            bool overriding_destructor =
                file_.entity(overriding.entity).kind ==
                cir::EntityKind::Destructor;
            bool overridden_destructor =
                file_.entity(overridden.entity).kind ==
                cir::EntityKind::Destructor;
            if (overriding_destructor != overridden_destructor) {
                return false;
            }
            return overriding_destructor ||
                (overriding.name.valid() && overridden.name.valid() &&
                 file_.name(overriding.name) == file_.name(overridden.name) &&
                 function_signatures_match(overriding.type.type,
                                           overridden.type.type));
        };
        auto methods_for_node = [&](uint32_t node)
            -> const std::vector<cir::RecordMethodFact>* {
            if (node == 0) {
                return &method_facts;
            }
            const cir::RecordFacts* record = facts_for_node(node);
            return record ? &record->methods : nullptr;
        };

        for (uint32_t overriding_node = 0;
             overriding_node < virtual_subobjects.size();
             ++overriding_node) {
            const std::vector<cir::RecordMethodFact>* overriding_methods =
                methods_for_node(overriding_node);
            if (!overriding_methods) {
                continue;
            }
            for (size_t overriding_index = 0;
                 overriding_index < overriding_methods->size();
                 ++overriding_index) {
                const cir::RecordMethodFact& overriding =
                    (*overriding_methods)[overriding_index];
                if (!overriding.entity.valid() || overriding.is_static ||
                    file_.entity(overriding.entity).kind ==
                        cir::EntityKind::Constructor) {
                    continue;
                }
                bool overrides_any = false;
                for (uint32_t overridden_node = 1;
                     overridden_node < virtual_subobjects.size();
                     ++overridden_node) {
                    if (overriding_node == overridden_node ||
                        !node_reaches(overriding_node, overridden_node)) {
                        continue;
                    }
                    const std::vector<cir::RecordMethodFact>*
                        overridden_methods = methods_for_node(overridden_node);
                    if (!overridden_methods) {
                        continue;
                    }
                    for (const cir::RecordMethodFact& overridden :
                         *overridden_methods) {
                        if (!overridden.is_virtual ||
                            !method_corresponds(overriding, overridden)) {
                            continue;
                        }
                        cir::VirtualOverrideEdgeFact edge;
                        edge.overriding = overriding.entity;
                        edge.overridden = overridden.entity;
                        edge.overriding_subobject = overriding_node;
                        edge.overridden_subobject = overridden_node;
                        edge.predicate_dependent =
                            overriding.constraint_satisfaction ==
                                cir::ConstraintSatisfactionKind::Dependent ||
                            overridden.constraint_satisfaction ==
                                cir::ConstraintSatisfactionKind::Dependent;
                        auto duplicate = std::find_if(
                            virtual_override_edges.begin(),
                            virtual_override_edges.end(),
                            [&](const cir::VirtualOverrideEdgeFact& prior) {
                                return prior.overriding == edge.overriding &&
                                    prior.overridden == edge.overridden &&
                                    prior.overriding_subobject ==
                                        edge.overriding_subobject &&
                                    prior.overridden_subobject ==
                                        edge.overridden_subobject;
                            });
                        if (duplicate == virtual_override_edges.end()) {
                            virtual_override_edges.push_back(std::move(edge));
                        }
                        overrides_any = true;
                    }
                }
                if (overriding_node == 0 && overrides_any) {
                    cir::RecordMethodFact& mutable_method =
                        method_facts[overriding_index];
                    mutable_method.is_virtual = true;
                    mutable_method.overrides_base = true;
                }
            }
        }

        struct OverriderCandidate {
            cir::EntityId method{};
            uint32_t subobject = 0;
        };
        for (uint32_t declaration_node = 0;
             declaration_node < virtual_subobjects.size();
             ++declaration_node) {
            const std::vector<cir::RecordMethodFact>* declarations =
                methods_for_node(declaration_node);
            if (!declarations) {
                continue;
            }
            for (const cir::RecordMethodFact& declaration : *declarations) {
                if (!declaration.is_virtual || !declaration.entity.valid()) {
                    continue;
                }
                std::vector<OverriderCandidate> candidates{
                    {declaration.entity, declaration_node}};
                for (const cir::VirtualOverrideEdgeFact& edge :
                     virtual_override_edges) {
                    if (edge.overridden == declaration.entity &&
                        edge.overridden_subobject == declaration_node) {
                        OverriderCandidate candidate{
                            edge.overriding, edge.overriding_subobject};
                        auto duplicate = std::find_if(
                            candidates.begin(), candidates.end(),
                            [&](const OverriderCandidate& prior) {
                                return prior.method == candidate.method &&
                                    prior.subobject == candidate.subobject;
                            });
                        if (duplicate == candidates.end()) {
                            candidates.push_back(candidate);
                        }
                    }
                }
                std::vector<OverriderCandidate> maximal;
                for (const OverriderCandidate& candidate : candidates) {
                    bool dominated = false;
                    for (const OverriderCandidate& other : candidates) {
                        if (candidate.method == other.method &&
                            candidate.subobject == other.subobject) {
                            continue;
                        }
                        if (node_reaches(other.subobject,
                                         candidate.subobject) &&
                            other.subobject != candidate.subobject) {
                            dominated = true;
                            break;
                        }
                    }
                    if (!dominated) {
                        maximal.push_back(candidate);
                    }
                }
                std::stable_sort(
                    maximal.begin(), maximal.end(),
                    [](const OverriderCandidate& lhs,
                       const OverriderCandidate& rhs) {
                        if (lhs.subobject != rhs.subobject) {
                            return lhs.subobject < rhs.subobject;
                        }
                        return lhs.method.index < rhs.method.index;
                    });
                cir::VirtualFinalOverriderFact final;
                final.virtual_declaration = declaration.entity;
                final.declaration_subobject = declaration_node;
                if (maximal.size() == 1) {
                    final.final_overrider = maximal.front().method;
                    final.final_subobject = maximal.front().subobject;
                } else {
                    for (const OverriderCandidate& candidate : maximal) {
                        final.conflict_candidates.push_back(candidate.method);
                    }
                    std::string name = declaration.name.valid()
                        ? std::string(file_.name(declaration.name))
                        : std::string("<virtual>");
                    report_error("virtual function '" + name +
                                     "' has no unique final overrider in '" +
                                     file_.format_type(decl.type) + "'",
                                 loc);
                    for (const OverriderCandidate& candidate : maximal) {
                        if (candidate.method.valid() &&
                            file_.valid(candidate.method)) {
                            report_note("final overrider candidate declared here",
                                        file_.entity(candidate.method).loc);
                        }
                    }
                    decl.has_error = true;
                }
                virtual_final_overriders.push_back(std::move(final));
            }
        }
    }

    auto inherited_node_reaches =
        [&](uint32_t derived, uint32_t base) {
            if (derived == base) {
                return true;
            }
            std::vector<uint32_t> worklist{derived};
            std::vector<bool> visited(virtual_subobjects.size(), false);
            while (!worklist.empty()) {
                uint32_t current = worklist.back();
                worklist.pop_back();
                if (current >= visited.size() || visited[current]) {
                    continue;
                }
                visited[current] = true;
                for (const cir::VirtualSubobjectEdgeFact& edge :
                     virtual_subobject_edges) {
                    if (edge.derived_subobject != current) {
                        continue;
                    }
                    if (edge.base_subobject == base) {
                        return true;
                    }
                    worklist.push_back(edge.base_subobject);
                }
            }
            return false;
        };
    for (InheritedConstructorPlan& plan : inherited_constructor_plans) {
        auto method = std::find_if(
            method_facts.begin(), method_facts.end(),
            [&](const cir::RecordMethodFact& fact) {
                return fact.entity == plan.entity;
            });
        if (method == method_facts.end() ||
            !method->inherited_constructor) {
            continue;
        }
        std::vector<uint32_t> unique_origins;
        for (const InheritedConstructorPlan::NominationRoute& nomination :
             plan.nominations) {
            std::vector<uint32_t> direct_nodes;
            for (const cir::VirtualSubobjectEdgeFact& edge :
                 virtual_subobject_edges) {
                if (edge.derived_subobject == 0 &&
                    edge.base_subobject < virtual_subobjects.size() &&
                    virtual_subobjects[edge.base_subobject].record_entity ==
                        nomination.direct_base) {
                    direct_nodes.push_back(edge.base_subobject);
                }
            }
            const cir::RecordFacts* base_record =
                file_.record_facts(nomination.direct_base);
            for (uint32_t direct_node : direct_nodes) {
                for (uint32_t base_origin :
                     nomination.base_origin_subobjects) {
                    uint32_t resolved_origin =
                        std::numeric_limits<uint32_t>::max();
                    if (base_origin == 0 &&
                        virtual_subobjects[direct_node].record_entity ==
                            plan.origin_record) {
                        resolved_origin = direct_node;
                    } else if (base_record &&
                               base_origin <
                                   base_record->virtual_subobjects.size()) {
                        const cir::VirtualSubobjectFact& relative =
                            base_record->virtual_subobjects[base_origin];
                        for (const cir::VirtualSubobjectFact& candidate :
                             virtual_subobjects) {
                            if (candidate.record_entity !=
                                    plan.origin_record ||
                                !inherited_node_reaches(direct_node,
                                                        candidate.id)) {
                                continue;
                            }
                            if (relative.is_virtual && candidate.is_virtual) {
                                resolved_origin = candidate.id;
                                break;
                            }
                            if (!relative.is_virtual &&
                                candidate.storage_path.size() ==
                                    virtual_subobjects[direct_node]
                                            .storage_path.size() +
                                        relative.storage_path.size() &&
                                std::equal(
                                    virtual_subobjects[direct_node]
                                        .storage_path.begin(),
                                    virtual_subobjects[direct_node]
                                        .storage_path.end(),
                                    candidate.storage_path.begin()) &&
                                std::equal(
                                    relative.storage_path.begin(),
                                    relative.storage_path.end(),
                                    candidate.storage_path.begin() +
                                        virtual_subobjects[direct_node]
                                            .storage_path.size())) {
                                resolved_origin = candidate.id;
                                break;
                            }
                        }
                    }
                    if (resolved_origin ==
                        std::numeric_limits<uint32_t>::max()) {
                        continue;
                    }
                    cir::InheritedConstructorRouteFact route;
                    route.nominated_direct_base = nomination.direct_base;
                    route.origin_subobject = resolved_origin;
                    route.using_loc = nomination.using_loc;
                    auto duplicate = std::find_if(
                        method->inherited_constructor->routes.begin(),
                        method->inherited_constructor->routes.end(),
                        [&](const cir::InheritedConstructorRouteFact& prior) {
                            return prior.nominated_direct_base ==
                                    route.nominated_direct_base &&
                                prior.origin_subobject ==
                                    route.origin_subobject;
                        });
                    if (duplicate ==
                        method->inherited_constructor->routes.end()) {
                        method->inherited_constructor->routes.push_back(route);
                    }
                    if (std::find(unique_origins.begin(), unique_origins.end(),
                                  resolved_origin) == unique_origins.end()) {
                        unique_origins.push_back(resolved_origin);
                    }
                }
            }
        }
        if (unique_origins.size() > 1) {
            method->is_deleted = true;
            plan.deleted = true;
        }
        if (method->inherited_constructor->routes.empty()) {
            method->is_deleted = true;
            method->is_eligible = false;
            plan.deleted = true;
        }
        if (plan.deleted) {
            continue;
        }

        auto default_constructor_unusable = [&](cir::TypeId type) {
            type = file_.resolved_type(type);
            if (!file_.valid(type) ||
                file_.type(type).kind != cir::TypeKind::Record) {
                return false;
            }
            bool ambiguous = false;
            cir::EntityId constructor = select_constructor(
                type, {}, &ambiguous, plan.nominations.front().using_loc,
                ConstructorInitializationKind::Direct,
                /*demand_selected=*/false);
            if (!constructor.valid()) {
                return ambiguous ||
                    record_requires_default_constructor_selection(type);
            }
            const cir::RecordMethodFact* constructor_fact =
                file_.method_fact(constructor);
            if (!constructor_fact || constructor_fact->is_deleted) {
                return true;
            }
            cir::EntityId constructor_owner =
                file_.entity(constructor).parent;
            bool accessible = member_access_allowed_from(
                constructor_owner,
                constructor_fact->declared_access,
                decl.entity, plan.entity,
                /*infer_active_template_function=*/false);
            if (!accessible && constructor_fact->declared_access ==
                                   cir::RecordMemberAccess::Protected) {

                accessible = std::any_of(
                    virtual_subobjects.begin(), virtual_subobjects.end(),
                    [&](const cir::VirtualSubobjectFact& subobject) {
                        return subobject.record_entity == constructor_owner;
                    });
            }
            return !accessible;
        };

        uint32_t selected_origin =
            method->inherited_constructor->routes.front().origin_subobject;
        bool origin_is_virtual =
            selected_origin < virtual_subobjects.size() &&
            virtual_subobjects[selected_origin].is_virtual;
        cir::EntityId forwarded_direct = origin_is_virtual
            ? cir::EntityId{}
            : method->inherited_constructor->routes.front()
                  .nominated_direct_base;
        std::unordered_set<uint64_t> checked_virtual_bases;
        for (const cir::RecordBaseFact& base : base_facts) {
            if (base.record_entity == forwarded_direct) {
                continue;
            }
            if (base.is_virtual) {
                checked_virtual_bases.insert(
                    static_cast<uint64_t>(base.record_entity.index));
            }
            if (default_constructor_unusable(base.type.type)) {
                method->is_deleted = true;
                plan.deleted = true;
                break;
            }
        }
        if (!plan.deleted) {
            for (const cir::RecordFacts::VirtualBase& base :
                 virtual_base_list) {
                if ((origin_is_virtual &&
                     base.record_entity == plan.origin_record) ||
                    checked_virtual_bases.contains(
                        static_cast<uint64_t>(base.record_entity.index))) {
                    continue;
                }
                if (default_constructor_unusable(base.type.type)) {
                    method->is_deleted = true;
                    plan.deleted = true;
                    break;
                }
            }
        }
        if (!plan.deleted) {
            for (const cir::RecordFieldFact& field : layout.fields) {
                if (field.is_base_subobject ||
                    (field.name.valid() &&
                     file_.name(field.name) == ".vptr") ||
                    field.has_default_member_initializer) {
                    continue;
                }
                cir::TypeId field_type = file_.resolved_type(field.type.type);
                if (is_reference_type(field_type)) {
                    method->is_deleted = true;
                    plan.deleted = true;
                    break;
                }
                cir::TypeId class_leaf =
                    array_class_element_leaf(field_type);
                if ((field.type.qualifiers & cir::QualConst) != 0) {
                    cir::TypeId const_class = class_leaf.valid()
                        ? class_leaf
                        : field_type;
                    const cir::RecordFacts* const_facts =
                        file_.record_facts_for_type(const_class);
                    bool user_provided_default = const_facts &&
                        std::any_of(
                            const_facts->methods.begin(),
                            const_facts->methods.end(),
                            [](const cir::RecordMethodFact& candidate) {
                                return candidate.special_member_kind ==
                                           cir::SpecialMemberKind::
                                               DefaultConstructor &&
                                    candidate.is_eligible &&
                                    !candidate.is_deleted &&
                                    candidate.is_user_provided;
                            });
                    if (!user_provided_default) {
                        method->is_deleted = true;
                        plan.deleted = true;
                        break;
                    }
                }
                if (class_leaf.valid()
                        ? default_constructor_unusable(class_leaf)
                        : default_constructor_unusable(field_type)) {
                    method->is_deleted = true;
                    plan.deleted = true;
                    break;
                }
            }
        }
    }

    std::vector<cir::EntityId> vtable_slots;
    std::vector<cir::EntityId> vtable_slot_declarations;
    struct SecondaryTable {
        uint32_t subobject_id = 0;
        bool is_virtual = false;
        std::vector<cir::EntityId> slots;
        std::vector<cir::EntityId> declarations;
        cir::TypeId base_type{};
    };
    std::vector<SecondaryTable> secondary_tables;

    auto nonvirtual_base_fact = [&](size_t ordinal) -> const cir::RecordBaseFact* {
        size_t seen = 0;
        for (const cir::RecordBaseFact& fact : base_facts) {
            if (fact.is_virtual) {
                continue;
            }
            if (seen == ordinal) {
                return &fact;
            }
            ++seen;
        }
        return nullptr;
    };
    if (is_polymorphic_record) {
        if (primary_base_polymorphic) {
            const cir::RecordBaseFact* primary_fact = nonvirtual_base_fact(0);
            const cir::RecordFacts* primary = primary_fact
                ? file_.record_facts_for_type(
                      file_.resolved_type(primary_fact->type.type))
                : nullptr;
            if (primary) {
                vtable_slots = primary->vtable_slots;
                if (primary->primary_vtable_slot_facts.size() ==
                    primary->vtable_slots.size()) {
                    for (const cir::VirtualTableSlotFact& slot :
                         primary->primary_vtable_slot_facts) {
                        vtable_slot_declarations.push_back(slot.declaration);
                    }
                } else {
                    vtable_slot_declarations = primary->vtable_slots;
                }
            }
        }

        for (bool want_virtual : {false, true}) {
            for (const cir::VirtualSubobjectFact& subobject :
                 virtual_subobjects) {
                if (subobject.id == 0 ||
                    subobject.is_virtual != want_virtual) {
                    continue;
                }
                const cir::RecordFacts* base_record =
                    file_.record_facts(subobject.record_entity);
                if (!base_record || !base_record->is_polymorphic ||
                    base_record->vtable_slots.empty()) {
                    continue;
                }
                bool shares_parent_primary = false;
                if (!subobject.is_virtual) {
                    for (const cir::VirtualSubobjectEdgeFact& edge :
                         virtual_subobject_edges) {
                        if (edge.base_subobject != subobject.id ||
                            edge.is_virtual) {
                            continue;
                        }
                        shares_parent_primary =
                            virtual_subobjects[edge.derived_subobject]
                                .static_offset_bytes ==
                            subobject.static_offset_bytes;
                        break;
                    }
                }
                if (shares_parent_primary) {
                    continue;
                }
                SecondaryTable table;
                table.subobject_id = subobject.id;
                table.is_virtual = subobject.is_virtual;
                table.slots = base_record->vtable_slots;
                if (base_record->primary_vtable_slot_facts.size() ==
                    base_record->vtable_slots.size()) {
                    for (const cir::VirtualTableSlotFact& slot :
                         base_record->primary_vtable_slot_facts) {
                        table.declarations.push_back(slot.declaration);
                    }
                } else {
                    table.declarations = base_record->vtable_slots;
                }
                table.base_type = subobject.type.type;
                secondary_tables.push_back(std::move(table));
            }
        }
        for (cir::RecordMethodFact& fact : method_facts) {
            if (!fact.entity.valid()) {
                continue;
            }
            cir::EntityKind fact_kind = file_.entity(fact.entity).kind;
            if (fact.is_static || fact_kind == cir::EntityKind::Constructor) {
                continue;
            }
            bool is_destructor = fact_kind == cir::EntityKind::Destructor;
            auto matches_slot = [&](cir::EntityId slot) {
                const cir::RecordMethodFact* base_fact = file_.method_fact(slot);
                if (!base_fact || !base_fact->entity.valid()) {
                    return false;
                }
                bool base_is_destructor =
                    file_.entity(base_fact->entity).kind ==
                    cir::EntityKind::Destructor;
                if (is_destructor != base_is_destructor) {
                    return false;
                }
                return is_destructor ||
                       (fact.name.valid() && base_fact->name.valid() &&
                        file_.name(fact.name) == file_.name(base_fact->name) &&
                        function_signatures_match(fact.type.type,
                                                  base_fact->type.type));
            };
            int found = -1;
            for (size_t j = 0; j < vtable_slots.size(); ++j) {
                cir::EntityId declaration =
                    j < vtable_slot_declarations.size()
                    ? vtable_slot_declarations[j]
                    : vtable_slots[j];
                if (matches_slot(declaration)) {
                    found = static_cast<int>(j);
                    break;
                }
            }

            bool overrides_secondary = false;
            for (SecondaryTable& table : secondary_tables) {
                for (size_t j = 0; j < table.slots.size(); ++j) {
                    cir::EntityId declaration =
                        j < table.declarations.size()
                        ? table.declarations[j]
                        : table.slots[j];
                    if (!matches_slot(declaration)) {
                        continue;
                    }
                    overrides_secondary = true;
                    table.slots[j] = fact.entity;
                    if (is_destructor) {
                        existing.has_virtual_destructor = true;
                        if (j + 1 < table.slots.size()) {
                            table.slots[j + 1] = fact.entity;
                        }
                    }
                    break;
                }
            }
            if (found >= 0) {
                fact.is_virtual = true;
                fact.vtable_slot = fact.is_consteval ? -1 : found;
                vtable_slots[static_cast<size_t>(found)] = fact.entity;
                if (is_destructor) {
                    existing.has_virtual_destructor = true;
                    if (static_cast<size_t>(found) + 1 < vtable_slots.size()) {
                        vtable_slots[static_cast<size_t>(found) + 1] = fact.entity;
                    }
                }
            } else if ((fact.is_virtual || overrides_secondary) &&
                       !fact.is_consteval) {

                fact.is_virtual = true;
                fact.vtable_slot = static_cast<int32_t>(vtable_slots.size());
                vtable_slots.push_back(fact.entity);
                vtable_slot_declarations.push_back(fact.entity);
                if (is_destructor) {
                    existing.has_virtual_destructor = true;
                    vtable_slots.push_back(fact.entity);
                    vtable_slot_declarations.push_back(fact.entity);
                }
            }
            fact.overrides_base = fact.overrides_base || found >= 0 ||
                overrides_secondary;
        }

        for (SecondaryTable& table : secondary_tables) {
            if (!table.is_virtual) {
                continue;
            }
            cir::TypeId vbase_type = file_.resolved_type(table.base_type);
            const cir::RecordFacts* vbase_record =
                file_.record_facts_for_type(vbase_type);
            if (!vbase_record) {
                continue;
            }
            for (size_t j = 0; j < table.slots.size() &&
                               j < vbase_record->vtable_slots.size();
                 ++j) {
                uint32_t declaration_node = 0;
                for (const cir::VirtualSubobjectFact& subobject :
                     virtual_subobjects) {
                    if (subobject.is_virtual &&
                        file_.resolved_type(subobject.type.type) ==
                            vbase_type) {
                        declaration_node = subobject.id;
                        break;
                    }
                }
                for (const cir::VirtualFinalOverriderFact& final :
                     virtual_final_overriders) {
                    if (final.declaration_subobject == declaration_node &&
                        final.virtual_declaration ==
                            vbase_record->vtable_slots[j] &&
                        final.final_overrider.valid()) {
                        table.slots[j] = final.final_overrider;
                        break;
                    }
                }
            }
        }
    }

    existing.is_abstract = false;
    for (const cir::VirtualFinalOverriderFact& final :
         virtual_final_overriders) {
        if (!final.final_overrider.valid()) {
            continue;
        }
        const cir::RecordMethodFact* method = nullptr;
        for (const cir::RecordMethodFact& own : method_facts) {
            if (own.entity == final.final_overrider) {
                method = &own;
                break;
            }
        }
        if (!method) {
            method = file_.method_fact(final.final_overrider);
        }
        existing.is_abstract = existing.is_abstract ||
            (method && method->is_pure);
    }

    bool may_override_dependent_base =
        in_template_definition() && !dependent_base_facts.empty();
    for (const cir::RecordMethodFact& fact : method_facts) {
        if (fact.is_override && !fact.overrides_base &&
            !may_override_dependent_base) {
            report_error("member function '" +
                             std::string(file_.name(fact.name)) +
                             "' marked override does not override a base class function",
                         fact.entity.valid() && file_.valid(fact.entity)
                             ? file_.entity(fact.entity).loc
                             : loc);
            decl.has_error = true;
        }
        if (fact.is_final && !fact.is_virtual &&
            !may_override_dependent_base) {
            report_error("final virt-specifier requires a virtual member function",
                         fact.entity.valid() && file_.valid(fact.entity)
                             ? file_.entity(fact.entity).loc
                             : loc);
            decl.has_error = true;
        }
        if (!fact.is_pure || fact.is_virtual || may_override_dependent_base) {
            continue;
        }
        report_error("pure-specifier requires a virtual member function",
                     fact.entity.valid() && file_.valid(fact.entity)
                         ? file_.entity(fact.entity).loc
                         : loc);
        decl.has_error = true;
    }

    cir::RecordFacts facts = std::move(existing);
    facts.bases = std::move(base_facts);
    facts.dependent_bases = std::move(dependent_base_facts);
    facts.entity = decl.entity;
    facts.type = file_.type_ref(decl.type);
    facts.kind = kind;
    facts.is_incomplete = false;
    facts.is_final = is_final;
    facts.is_anonymous_union_definition =
        is_anonymous_union_definition;
    facts.fields = std::move(layout.fields);
    facts.is_union_like = kind == cir::RecordKind::Union;
    facts.variant_members.clear();
    std::unordered_map<std::string, cir::EntityId> direct_member_names;
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage ||
            (field.name.valid() && file_.name(field.name) == ".vptr")) {
            continue;
        }
        if (field.name.valid()) {
            direct_member_names.emplace(std::string(file_.name(field.name)),
                                        field.entity);
        }
        if (field.is_anonymous_union_object) {
            facts.is_union_like = true;
            const cir::RecordFacts* anonymous =
                file_.record_facts_for_type(field.type.type);
            if (!anonymous) {
                continue;
            }
            for (const cir::AnonymousUnionPromotionFact& promotion :
                 anonymous->anonymous_union_promotions) {

                if (promotion.member.valid() &&
                    file_.valid(promotion.member)) {
                    cir::Entity& promoted =
                        file_.entity_mut(promotion.member);
                    promoted.declaring_record = facts.entity;
                    promoted.declared_member_access =
                        field.declared_access;
                    promoted.is_record_member = true;
                }
                cir::VariantMemberFact variant;
                variant.member = promotion.member;
                variant.owning_union = anonymous->entity;
                variant.path.push_back(field.entity);
                variant.path.insert(variant.path.end(),
                                    promotion.path.begin(),
                                    promotion.path.end());
                facts.variant_members.push_back(std::move(variant));
            }
            continue;
        }
        if (kind == cir::RecordKind::Union) {
            cir::VariantMemberFact variant;
            variant.member = field.entity;
            variant.owning_union = facts.entity;
            variant.path.push_back(field.entity);
            facts.variant_members.push_back(std::move(variant));
        }
    }
    {
        std::unordered_map<std::string, cir::EntityId> promoted_names;
        for (const cir::RecordFieldFact& field : facts.fields) {
            if (!field.is_anonymous_union_object) {
                continue;
            }
            const cir::RecordFacts* anonymous =
                file_.record_facts_for_type(field.type.type);
            if (!anonymous) {
                continue;
            }
            for (const cir::AnonymousUnionPromotionFact& promotion :
                 anonymous->anonymous_union_promotions) {
                std::string name(file_.name(promotion.name));
                auto direct = direct_member_names.find(name);
                if (direct != direct_member_names.end()) {
                    report_error("anonymous union member '" + name +
                                     "' conflicts with a member of the enclosing class",
                                 file_.entity(promotion.member).loc);
                    decl.has_error = true;
                }
                auto [previous, inserted] = promoted_names.emplace(
                    name, promotion.member);
                if (!inserted && previous->second != promotion.member) {
                    report_error("anonymous union member '" + name +
                                     "' is promoted more than once",
                                 file_.entity(promotion.member).loc);
                    decl.has_error = true;
                }
                if (facts.entity.valid() && file_.valid(facts.entity) &&
                    file_.entity(facts.entity).name.valid() &&
                    file_.name(file_.entity(facts.entity).name) == name) {
                    report_error("anonymous union member '" + name +
                                     "' has the same name as its enclosing class",
                                 file_.entity(promotion.member).loc);
                    decl.has_error = true;
                }
            }
        }
    }
    if (kind == cir::RecordKind::Union) {
        cir::EntityId first_dmi;
        for (const cir::VariantMemberFact& variant : facts.variant_members) {
            const cir::RecordFieldFact* member =
                file_.field_fact(variant.member);
            if (!member || !member->has_default_member_initializer) {
                continue;
            }
            if (first_dmi.valid() && first_dmi != variant.member) {
                report_error(
                    "at most one union variant may have a default member initializer",
                    member->default_member_initializer_loc);
                decl.has_error = true;
                break;
            }
            first_dmi = variant.member;
        }
    }
    facts.methods = std::move(method_facts);
    facts.static_data_members = std::move(static_member_facts);

    cir::DeclContextId using_record_context =
        file_.entity(decl.entity).semantic_context;
    if (using_record_context.valid() &&
        file_.valid(using_record_context)) {
        auto is_callable_entity = [&](cir::EntityId entity) {
            if (!entity.valid() || !file_.valid(entity)) {
                return false;
            }
            cir::EntityKind entity_kind = file_.entity(entity).kind;
            return entity_kind == cir::EntityKind::Function ||
                entity_kind == cir::EntityKind::Method;
        };
        const cir::DeclContext& record_context =
            file_.decl_context(using_record_context);
        for (const cir::RecordUsingDeclarationFact& using_fact :
             facts.using_declarations) {
            if (using_fact.entries.empty()) {

                continue;
            }
            bool imported_callables = std::all_of(
                using_fact.entries.begin(), using_fact.entries.end(),
                [&](const cir::RecordUsingDeclarationEntry& entry) {
                    return is_callable_entity(entry.entity);
                });
            bool diagnosed = false;
            auto diagnose_conflict = [&](cir::EntityId entity) {
                report_error(
                    "declaration conflicts with class-scope "
                    "using-declaration for '" +
                        std::string(file_.name(
                            using_fact.terminal_name)) + "'",
                    entity.valid() && file_.valid(entity)
                        ? file_.entity(entity).loc
                        : using_fact.loc);
                decl.has_error = true;
                diagnosed = true;
            };
            for (const cir::RecordFieldFact& field : facts.fields) {
                if (diagnosed || field.is_base_subobject ||
                    !field.name.valid() ||
                    field.name != using_fact.terminal_name) {
                    continue;
                }
                diagnose_conflict(field.entity);
            }
            for (const cir::RecordStaticDataMemberFact& member :
                 facts.static_data_members) {
                if (diagnosed || !member.name.valid() ||
                    member.name != using_fact.terminal_name) {
                    continue;
                }
                diagnose_conflict(member.entity);
            }
            if (!imported_callables) {
                for (const cir::RecordMethodFact& method : facts.methods) {
                    if (diagnosed || !method.name.valid() ||
                        method.name != using_fact.terminal_name) {
                        continue;
                    }
                    diagnose_conflict(method.entity);
                }
            }
            for (cir::BindingId binding_id : record_context.bindings) {
                if (diagnosed || !file_.valid(binding_id)) {
                    continue;
                }
                const cir::Binding& binding = file_.binding(binding_id);
                if (!binding.name.valid() ||
                    binding.name != using_fact.terminal_name) {
                    continue;
                }
                for (cir::EntityId entity : binding.entities) {
                    if (!entity.valid() || !file_.valid(entity) ||
                        std::any_of(
                            using_fact.entries.begin(),
                            using_fact.entries.end(),
                            [&](const cir::RecordUsingDeclarationEntry& entry) {
                                return entry.entity == entity;
                            })) {
                        continue;
                    }
                    const cir::Entity& local = file_.entity(entity);
                    bool declared_here = local.parent == decl.entity ||
                        local.declaring_record == decl.entity ||
                        local.lexical_context == using_record_context;
                    if (!declared_here ||
                        (imported_callables && is_callable_entity(entity))) {
                        continue;
                    }
                    diagnose_conflict(entity);
                    break;
                }
            }
        }
    }

    for (cir::RecordUsingDeclarationFact& using_fact :
         facts.using_declarations) {
        for (cir::RecordUsingDeclarationEntry& entry :
             using_fact.entries) {
            entry.hidden_by = {};
            if (!entry.entity.valid() || !file_.valid(entry.entity)) {
                continue;
            }
            const cir::RecordMethodFact* imported =
                file_.method_fact(entry.entity);
            if (!imported || !imported->name.valid()) {
                continue;
            }
            const TemplateInfo* imported_template =
                template_info(entry.entity);
            for (const cir::RecordMethodFact& local : facts.methods) {
                if (!local.entity.valid() ||
                    !file_.valid(local.entity) ||
                    local.name != imported->name) {
                    continue;
                }
                const TemplateInfo* local_template =
                    template_info(local.entity);
                bool corresponds = false;
                if (imported_template || local_template) {
                    corresponds = imported_template && local_template &&
                        function_template_declarations_correspond(
                            *imported_template, *local_template);
                } else {
                    corresponds = function_signatures_match(
                        imported->type.type, local.type.type);
                }
                if (corresponds) {
                    entry.hidden_by = local.entity;
                    break;
                }
            }
        }
    }
    facts.virtual_subobjects = std::move(virtual_subobjects);
    facts.virtual_subobject_edges = std::move(virtual_subobject_edges);
    facts.virtual_override_edges = std::move(virtual_override_edges);
    facts.virtual_final_overriders = std::move(virtual_final_overriders);
    facts.virtual_graph_dependent = !facts.dependent_bases.empty();
    {
        bool dependent_consteval_only = false;
        facts.is_consteval_only = cir::ClassPropertyState::False;
        for (const cir::RecordFieldFact& field : facts.fields) {
            if (field.is_base_subobject || field.is_virtual_base_storage) {
                continue;
            }
            cir::ClassPropertyState state =
                file_.consteval_only_type_state(field.type.type);
            if (state == cir::ClassPropertyState::True) {
                facts.is_consteval_only = cir::ClassPropertyState::True;
                break;
            }
            dependent_consteval_only = dependent_consteval_only ||
                state == cir::ClassPropertyState::Dependent ||
                state == cir::ClassPropertyState::Unavailable;
        }
        if (facts.is_consteval_only != cir::ClassPropertyState::True &&
            dependent_consteval_only) {
            facts.is_consteval_only = cir::ClassPropertyState::Dependent;
        }
    }
    facts.has_flexible_array_member = layout.has_flexible_array_member;
    facts.size_bits = layout.size_bits;
    facts.alignment = layout.alignment;
    facts.non_virtual_size_bits = non_virtual_size_bits;
    facts.non_virtual_alignment = layout.alignment;
    facts.virtual_bases = virtual_base_list;
    facts.vtable_slots = vtable_slots;
    auto is_vptr = [&](const cir::RecordFieldFact& field) {
        return field.name.valid() && file_.name(field.name) == ".vptr";
    };
    {
        bool empty = facts.kind != cir::RecordKind::Union &&
            !facts.is_polymorphic && facts.virtual_bases.empty();
        bool dependent_empty = !facts.dependent_bases.empty();
        for (const cir::RecordFieldFact& field : facts.fields) {
            if (is_vptr(field) ||
                (field.is_bitfield && !field.bit_width_is_dependent &&
                 field.bit_width == 0)) {
                continue;
            }
            if (field.is_bitfield && field.bit_width_is_dependent) {
                dependent_empty = true;
                continue;
            }
            if (field.subobject_size == cir::SubobjectSizeKind::Zero) {
                continue;
            }
            if (field.subobject_size == cir::SubobjectSizeKind::Dependent) {
                dependent_empty = true;
                continue;
            }
            empty = false;
        }
        facts.is_empty = empty
            ? (dependent_empty ? cir::ClassPropertyState::Dependent
                               : cir::ClassPropertyState::True)
            : cir::ClassPropertyState::False;
    }
    auto subobject_method = [&](const cir::RecordFieldFact& field,
                                cir::SpecialMemberKind special_kind,
                                const cir::RecordMethodFact* outer_method) {
        return canonical_special_member(
            file_, field.type.type, special_kind,
            special_kind == cir::SpecialMemberKind::MoveConstructor ||
                special_kind == cir::SpecialMemberKind::MoveAssignment,
            outer_method ? special_member_source_form(file_, *outer_method)
                         : std::nullopt);
    };
    auto subobject_operation_is_dependent =
        [&](const cir::RecordFieldFact& field) {

            return in_template_definition() &&
                is_dependent_type(field.type.type);
        };
    auto subobject_operation_is_trivial = [&](const cir::RecordFieldFact& field,
                                              cir::SpecialMemberKind special_kind,
                                              const cir::RecordMethodFact& outer_method) {
        if (subobject_operation_is_dependent(field)) {
            return true;
        }
        if (scalar_or_reference_special_member_is_trivial(file_,
                                                          field.type.type)) {
            return true;
        }
        const cir::RecordMethodFact* operation =
            subobject_method(field, special_kind, &outer_method);
        return operation && !operation->is_deleted && operation->is_trivial;
    };
    auto subobject_operation_is_nothrow = [&](const cir::RecordFieldFact& field,
                                              cir::SpecialMemberKind special_kind,
                                              const cir::RecordMethodFact& outer_method) {
        if (subobject_operation_is_dependent(field)) {
            return true;
        }
        if (scalar_or_reference_special_member_is_trivial(file_,
                                                          field.type.type)) {
            return true;
        }
        const cir::RecordMethodFact* operation =
            subobject_method(field, special_kind, &outer_method);
        if (!operation) {
            return false;
        }

        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(operation->type.type)));
        return payload && payload->exception_spec.kind ==
            cir::FunctionExceptionSpecKind::NonThrowing;
    };
    auto subobject_operation_is_constexpr = [&](const cir::RecordFieldFact& field,
                                                cir::SpecialMemberKind special_kind,
                                                const cir::RecordMethodFact& outer_method) {
        if (subobject_operation_is_dependent(field)) {
            return true;
        }
        if (scalar_or_reference_special_member_is_trivial(file_,
                                                          field.type.type)) {
            return true;
        }
        const cir::RecordMethodFact* operation =
            subobject_method(field, special_kind, &outer_method);
        return operation && !operation->is_deleted &&
            (operation->is_constexpr || operation->is_consteval);
    };
    auto publish_exception_spec = [&](cir::RecordMethodFact& method,
                                      bool nothrow) {
        method.has_computed_exception_spec = true;
        const auto* old_payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(method.type.type)));
        if (!old_payload) {
            return;
        }
        cir::FunctionTypePayload payload_copy = *old_payload;
        cir::TypeId rebuilt = function_type(
            payload_copy.return_type, payload_copy.parameters,
            payload_copy.is_variadic, payload_copy.has_prototype,
            payload_copy.member_is_const,
            nothrow ? cir::FunctionExceptionSpecKind::NonThrowing
                    : cir::FunctionExceptionSpecKind::PotentiallyThrowing,
            payload_copy.parameter_pack_flags,
            payload_copy.member_ref_qualifier,
            payload_copy.member_is_volatile);
        method.type = file_.type_ref(rebuilt);
        cir::TypeId entity_type =
            member_function_type_with_this(decl.type, rebuilt);
        cir::EntityKind entity_kind = file_.entity(method.entity).kind;
        if (has_virtual_bases &&
            (entity_kind == cir::EntityKind::Constructor ||
             entity_kind == cir::EntityKind::Destructor)) {
            entity_type = structor_impl_type(entity_type);
        }
        file_.entity_mut(method.entity).type = entity_type;
    };
    auto special_member_is_usable =
        [&](const cir::RecordMethodFact* operation,
            const cir::RecordMethodFact& accessing_method,
            const cir::RecordFieldFact& subobject) {
            if (!operation || operation->is_deleted ||
                !operation->entity.valid() ||
                !file_.valid(operation->entity)) {
                return false;
            }

            if (operation->declared_access ==
                    cir::RecordMemberAccess::Protected &&
                subobject.is_base_subobject) {
                return true;
            }
            return member_access_allowed_from(
                file_.entity(operation->entity).parent,
                operation->declared_access,
                facts.entity,
                accessing_method.entity);
        };
    auto subobject_operation_is_deleted =
        [&](const cir::RecordFieldFact& field,
            cir::SpecialMemberKind special_kind,
            const cir::RecordMethodFact& accessing_method) {
        if (subobject_operation_is_dependent(field)) {
            return false;
        }
        if (scalar_or_reference_special_member_is_trivial(file_,
                                                          field.type.type)) {
            return false;
        }
        const cir::RecordMethodFact* operation =
            subobject_method(field, special_kind, &accessing_method);
        if (operation &&
            (special_kind == cir::SpecialMemberKind::CopyAssignment ||
             special_kind == cir::SpecialMemberKind::MoveAssignment)) {
            const auto* operation_type =
                std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(
                        file_.resolved_type(operation->type.type)));
            if (!operation_type ||
                (((field.type.qualifiers & cir::QualConst) != 0) &&
                 !operation_type->member_is_const) ||
                (((field.type.qualifiers & cir::QualVolatile) != 0) &&
                 !operation_type->member_is_volatile)) {
                return true;
            }
        }
        return !special_member_is_usable(operation, accessing_method, field);
    };

    for (cir::RecordMethodFact& method : facts.methods) {
        cir::SpecialMemberKind special_kind = method.special_member_kind;
        if (special_kind == cir::SpecialMemberKind::None) {
            continue;
        }
        method.potentially_constructed_subobjects.clear();
        if (special_kind == cir::SpecialMemberKind::DefaultConstructor ||
            special_kind == cir::SpecialMemberKind::CopyConstructor ||
            special_kind == cir::SpecialMemberKind::MoveConstructor ||
            special_kind == cir::SpecialMemberKind::Destructor) {
            for (const cir::RecordFieldFact& field : facts.fields) {
                if (is_vptr(field) ||
                    (facts.is_abstract && field.is_virtual_base_storage &&
                     special_kind != cir::SpecialMemberKind::Destructor)) {
                    continue;
                }
                cir::PotentiallyConstructedSubobjectFact subobject;
                subobject.kind = field.is_virtual_base_storage
                    ? cir::PotentiallyConstructedSubobjectKind::VirtualBase
                    : field.is_base_subobject
                        ? cir::PotentiallyConstructedSubobjectKind::DirectBase
                        : cir::PotentiallyConstructedSubobjectKind::NonStaticDataMember;
                subobject.entity = field.entity;
                subobject.type = field.type;
                method.potentially_constructed_subobjects.push_back(subobject);
            }
        }

        if (!method.is_defaulted) {
            method.is_trivial = false;
            method.is_eligible = !method.is_deleted &&
                method.constraint_satisfaction !=
                    cir::ConstraintSatisfactionKind::Unsatisfied &&
                method.constraint_satisfaction !=
                    cir::ConstraintSatisfactionKind::Invalid;
            if (special_kind == cir::SpecialMemberKind::Destructor &&
                !method.has_explicit_exception_spec) {
                bool nothrow = true;
                for (const cir::RecordFieldFact& field : facts.fields) {
                    if (!is_vptr(field)) {
                        nothrow = nothrow && subobject_operation_is_nothrow(
                            field, special_kind, method);
                    }
                }
                publish_exception_spec(method, nothrow);
            }
            continue;
        }

        bool deleted = method.is_deleted;
        if (facts.is_lambda_closure && !facts.fields.empty() &&
            (special_kind == cir::SpecialMemberKind::CopyAssignment ||
             special_kind == cir::SpecialMemberKind::MoveAssignment)) {
            deleted = true;
        }
        bool trivial = !facts.is_polymorphic && facts.virtual_bases.empty();
        bool nothrow = true;
        bool constexpr_candidate = facts.virtual_bases.empty();
        if (special_kind == cir::SpecialMemberKind::Destructor) {
            trivial = !method.is_virtual;
        }
        for (const cir::RecordFieldFact& field : facts.fields) {
            if (is_vptr(field)) {
                continue;
            }
            cir::TypeId resolved_field_type =
                file_.resolved_type(field.type.type);
            bool is_rvalue_reference =
                file_.valid(resolved_field_type) &&
                file_.type(resolved_field_type).kind ==
                    cir::TypeKind::RValueReference;
            bool is_reference = file_.valid(resolved_field_type) &&
                (file_.type(resolved_field_type).kind ==
                     cir::TypeKind::LValueReference ||
                 is_rvalue_reference);
            bool is_const = (field.type.qualifiers & cir::QualConst) != 0;
            if (special_kind == cir::SpecialMemberKind::DefaultConstructor) {
                bool const_default_constructible = false;
                if (is_const && !is_reference) {
                    const cir::RecordFacts* field_facts =
                        file_.record_facts_for_type(resolved_field_type);
                    if (field_facts) {
                        for (const cir::RecordMethodFact& candidate :
                             field_facts->methods) {
                            if (candidate.special_member_kind ==
                                    cir::SpecialMemberKind::DefaultConstructor &&
                                candidate.is_eligible &&
                                !candidate.is_deleted &&
                                candidate.is_user_provided) {
                                const_default_constructible = true;
                                break;
                            }
                        }
                    }
                }
                if (!field.is_base_subobject &&
                    (is_reference ||
                     (is_const && !const_default_constructible)) &&
                    !field.has_default_member_initializer) {
                    deleted = true;
                }

                if (facts.kind == cir::RecordKind::Union &&
                    !field.is_base_subobject &&
                    !scalar_or_reference_special_member_is_trivial(
                        file_, field.type.type) &&
                    !subobject_operation_is_trivial(
                        field, cir::SpecialMemberKind::DefaultConstructor,
                        method)) {
                    deleted = true;
                }
            } else if ((special_kind ==
                            cir::SpecialMemberKind::CopyAssignment ||
                        special_kind ==
                            cir::SpecialMemberKind::MoveAssignment) &&
                       !field.is_base_subobject &&
                       (is_reference ||
                        (is_const &&
                         scalar_or_reference_special_member_is_trivial(
                             file_, field.type.type)))) {
                deleted = true;
            }
            if (special_kind == cir::SpecialMemberKind::CopyConstructor &&
                !field.is_base_subobject && is_rvalue_reference) {
                deleted = true;
            }
            if (facts.kind == cir::RecordKind::Union &&
                !field.is_base_subobject &&
                (special_kind == cir::SpecialMemberKind::CopyConstructor ||
                 special_kind == cir::SpecialMemberKind::MoveConstructor ||
                 special_kind == cir::SpecialMemberKind::CopyAssignment ||
                 special_kind == cir::SpecialMemberKind::MoveAssignment) &&
                !scalar_or_reference_special_member_is_trivial(
                    file_, field.type.type) &&
                !subobject_operation_is_trivial(field, special_kind,
                                                method)) {
                deleted = true;
            }

            if (facts.kind == cir::RecordKind::Union &&
                !field.is_base_subobject &&
                special_kind == cir::SpecialMemberKind::Destructor &&
                !scalar_or_reference_special_member_is_trivial(
                    file_, field.type.type) &&
                !subobject_operation_is_trivial(
                    field, cir::SpecialMemberKind::Destructor, method)) {
                deleted = true;
            }
            if (subobject_operation_is_deleted(field, special_kind, method)) {
                deleted = true;
            }
            if (special_kind == cir::SpecialMemberKind::DefaultConstructor ||
                special_kind == cir::SpecialMemberKind::CopyConstructor ||
                special_kind == cir::SpecialMemberKind::MoveConstructor) {
                if (!subobject_operation_is_dependent(field) &&
                    !scalar_or_reference_special_member_is_trivial(
                        file_, field.type.type)) {
                    const cir::RecordMethodFact* destructor =
                        canonical_special_member(
                            file_, field.type.type,
                            cir::SpecialMemberKind::Destructor);
                    if (!special_member_is_usable(destructor, method, field)) {
                        deleted = true;
                    }
                }
            }

            if (special_kind == cir::SpecialMemberKind::DefaultConstructor &&
                field.has_default_member_initializer &&
                !field.is_base_subobject) {
                trivial = false;
            }
            trivial = trivial &&
                subobject_operation_is_trivial(field, special_kind, method);
            nothrow = nothrow &&
                subobject_operation_is_nothrow(field, special_kind, method);
            constexpr_candidate = constexpr_candidate &&
                subobject_operation_is_constexpr(field, special_kind, method);
        }
        method.is_deleted = deleted;
        method.is_trivial = !deleted && trivial;
        method.is_eligible = !deleted &&
            method.constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Unsatisfied &&
            method.constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Invalid;
        method.is_constexpr = method.is_constexpr ||
            (!deleted && constexpr_candidate);
        if (method.entity.valid() && file_.valid(method.entity)) {
            file_.entity_mut(method.entity).decl_flags.is_constexpr =
                method.is_constexpr;
        }

        if (method.has_explicit_exception_spec) {
            const auto* written = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(method.type.type)));
            nothrow = written && written->exception_spec.kind ==
                cir::FunctionExceptionSpecKind::NonThrowing;
        }
        publish_exception_spec(method, nothrow);
    }

    std::vector<std::pair<cir::EntityId, cir::EntityId>>
        diagnosed_override_pairs;
    for (cir::VirtualOverrideEdgeFact& edge :
         facts.virtual_override_edges) {

        if (edge.overriding_subobject != 0) {
            cir::EntityId owner = file_.entity(edge.overriding).parent;
            const cir::RecordFacts* owner_facts =
                file_.record_facts(owner);
            if (owner_facts) {
                auto inherited = std::find_if(
                    owner_facts->virtual_override_edges.begin(),
                    owner_facts->virtual_override_edges.end(),
                    [&](const cir::VirtualOverrideEdgeFact& candidate) {
                        return candidate.overriding == edge.overriding &&
                            candidate.overridden == edge.overridden &&
                            candidate.overriding_subobject == 0;
                    });
                if (inherited !=
                    owner_facts->virtual_override_edges.end()) {
                    edge.predicate_dependent =
                        inherited->predicate_dependent;
                    edge.return_relation = inherited->return_relation;
                    edge.covariance_path = inherited->covariance_path;
                }
            }
            continue;
        }
        cir::EntityId overrider_entity = edge.overriding;
        cir::EntityId base_entity = edge.overridden;
        std::pair<cir::EntityId, cir::EntityId> pair{overrider_entity,
                                                     base_entity};
        bool diagnose = std::find(diagnosed_override_pairs.begin(),
                                  diagnosed_override_pairs.end(), pair) ==
            diagnosed_override_pairs.end();
        if (diagnose) {
            diagnosed_override_pairs.push_back(pair);
        }
        const cir::RecordMethodFact* overrider = nullptr;
        for (const cir::RecordMethodFact& method : facts.methods) {
            if (method.entity == overrider_entity) {
                overrider = &method;
                break;
            }
        }
        const cir::RecordMethodFact* base = file_.method_fact(base_entity);
        if (!overrider || !base) {
            continue;
        }
        if (base->is_final && diagnose) {
            report_error("member function '" +
                             std::string(file_.name(overrider->name)) +
                             "' overrides a final function",
                         file_.entity(overrider_entity).loc);
            decl.has_error = true;
        }
        if (base->is_deleted != overrider->is_deleted && diagnose) {
            report_error(
                std::string(overrider->is_deleted ? "deleted"
                                                  : "non-deleted") +
                    " function '" +
                    std::string(file_.name(overrider->name)) +
                    "' cannot override a " +
                    (overrider->is_deleted ? "non-deleted" : "deleted") +
                    " function",
                file_.entity(overrider_entity).loc);
            decl.has_error = true;
        }
        const auto* overrider_type = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(overrider->type.type)));
        const auto* base_type = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(base->type.type)));
        if (!overrider_type || !base_type) {
            continue;
        }
        bool dependent_exception =
            overrider_type->exception_spec.kind ==
                cir::FunctionExceptionSpecKind::Dependent ||
            base_type->exception_spec.kind ==
                cir::FunctionExceptionSpecKind::Dependent;
        edge.predicate_dependent = edge.predicate_dependent ||
            dependent_exception;
        if (!dependent_exception &&
            base_type->exception_spec.kind ==
                cir::FunctionExceptionSpecKind::NonThrowing &&
            overrider_type->exception_spec.kind !=
                cir::FunctionExceptionSpecKind::NonThrowing && diagnose) {
            report_error(
                "exception specification of overriding function is more "
                "lax than base version",
                file_.entity(overrider_entity).loc);
            decl.has_error = true;
        }

        if (file_.entity(overrider_entity).kind ==
            cir::EntityKind::Destructor) {
            edge.return_relation = cir::VirtualReturnRelation::Identical;
        } else {
            cir::TypeRef overrider_ret = overrider_type->return_type;
            cir::TypeRef base_ret = base_type->return_type;
            bool dependent_return = is_dependent_type(overrider_ret.type) ||
                is_dependent_type(base_ret.type);
            bool identical =
                type_equal(overrider_ret.type, base_ret.type) &&
                overrider_ret.qualifiers == base_ret.qualifiers;
            bool covariant = false;
            bool covariance_access_ok = true;
            if (dependent_return) {
                edge.return_relation = cir::VirtualReturnRelation::Dependent;
                edge.predicate_dependent = true;
            } else if (!identical) {
                auto unwrap = [&](cir::TypeRef ref, int& kind_out)
                    -> cir::TypeRef {
                    cir::TypeId resolved = file_.resolved_type(ref.type);
                    if (!file_.valid(resolved)) {
                        kind_out = 0;
                        return {};
                    }
                    switch (file_.type(resolved).kind) {
                        case cir::TypeKind::Pointer:
                            kind_out = 1;
                            return file_.pointer_pointee_ref(resolved);
                        case cir::TypeKind::LValueReference:
                            kind_out = 2;
                            return file_.reference_referred_ref(resolved);
                        case cir::TypeKind::RValueReference:
                            kind_out = 3;
                            return file_.reference_referred_ref(resolved);
                        default:
                            kind_out = 0;
                            return {};
                    }
                };
                int overrider_kind = 0;
                int base_kind = 0;
                cir::TypeRef overrider_referred =
                    unwrap(overrider_ret, overrider_kind);
                cir::TypeRef base_referred = unwrap(base_ret, base_kind);
                auto referred_is_record = [&](cir::TypeId type) {
                    cir::TypeId resolved = file_.resolved_type(type);
                    return file_.valid(resolved) &&
                        file_.type(resolved).kind == cir::TypeKind::Record;
                };
                if (overrider_kind != 0 && overrider_kind == base_kind &&
                    referred_is_record(overrider_referred.type) &&
                    referred_is_record(base_referred.type)) {
                    bool outer_qualifiers_match =
                        overrider_ret.qualifiers == base_ret.qualifiers;
                    bool qualifiers_widen_only =
                        (overrider_referred.qualifiers &
                         ~base_referred.qualifiers) == 0;
                    if (type_equal(overrider_referred.type,
                                   base_referred.type)) {
                        covariant = outer_qualifiers_match &&
                            qualifiers_widen_only;
                    } else if (file_.resolved_type(overrider_referred.type) ==
                               file_.resolved_type(decl.type)) {
                        cir::TypeId target =
                            file_.resolved_type(base_referred.type);
                        std::vector<const cir::VirtualSubobjectFact*> matches;
                        for (const cir::VirtualSubobjectFact& subobject :
                             facts.virtual_subobjects) {
                            if (subobject.id != 0 &&
                                file_.resolved_type(subobject.type.type) ==
                                    target) {
                                matches.push_back(&subobject);
                            }
                        }
                        if (matches.size() == 1) {
                            edge.covariance_path =
                                matches.front()->storage_path;
                            covariant = outer_qualifiers_match &&
                                qualifiers_widen_only;
                        }
                    } else {
                        const cir::RecordFacts* returned_record =
                            file_.record_facts_for_type(
                                file_.resolved_type(overrider_referred.type));
                        DerivedToBasePathResult path =
                            analyze_derived_to_base_path(
                                overrider_referred.type,
                                base_referred.type);
                        bool complete = returned_record &&
                            !returned_record->is_incomplete;
                        covariant = complete && outer_qualifiers_match &&
                            path.kind == DerivedToBasePathKind::Unique &&
                            qualifiers_widen_only;
                        if (covariant) {
                            edge.covariance_path = path.path;
                            AccessContext covariance_context;
                            covariance_context.accessing_record = decl.entity;
                            covariance_context.accessing_function =
                                overrider_entity;
                            covariance_context.lexical_context =
                                file_.entity(overrider_entity)
                                    .semantic_context;
                            covariance_context.exact = true;
                            covariance_access_ok =
                                check_base_path_access_in_context(
                                    path.path,
                                    overrider_referred.type,
                                    base_referred.type,
                                    covariance_context,
                                    file_.entity(overrider_entity).loc);
                            covariant = covariance_access_ok;
                        }
                    }
                }
            }
            if (!dependent_return) {
                edge.return_relation = identical
                    ? cir::VirtualReturnRelation::Identical
                    : covariant ? cir::VirtualReturnRelation::Covariant
                                : cir::VirtualReturnRelation::Invalid;
            }
            if (!dependent_return && !identical && !covariant && diagnose &&
                covariance_access_ok) {
                report_error(
                    "virtual function '" +
                        std::string(file_.name(overrider->name)) +
                        "' has a return type that is neither identical to "
                        "nor covariant with the function it overrides",
                    file_.entity(overrider_entity).loc);
                decl.has_error = true;
            }
        }

        if (!overrider->is_consteval && base->is_consteval && diagnose) {
            report_error(
                "non-consteval function '" +
                    std::string(file_.name(overrider->name)) +
                    "' cannot override a consteval function",
                file_.entity(overrider_entity).loc);
            decl.has_error = true;
        } else if (overrider->is_consteval && !base->is_consteval) {
            if (facts.is_consteval_only ==
                    cir::ClassPropertyState::Dependent) {
                edge.predicate_dependent = true;
            } else if (facts.is_consteval_only !=
                           cir::ClassPropertyState::True && diagnose) {
                report_error(
                    "class '" + file_.format_type(decl.type) +
                        "' must have consteval-only type because immediate "
                        "virtual function '" +
                        std::string(file_.name(overrider->name)) +
                        "' overrides a non-immediate virtual function",
                    file_.entity(overrider_entity).loc);
                decl.has_error = true;
            }
        }
    }

    auto virtual_adjustment_for_path =
        [&](const std::vector<cir::EntityId>& path) {
        cir::VirtualAdjustmentFact adjustment;
        adjustment.path = path;
        for (cir::EntityId step : path) {
            const cir::RecordFieldFact* field = nullptr;
            for (const cir::RecordFieldFact& own : facts.fields) {
                if (own.entity == step) {
                    field = &own;
                    break;
                }
            }
            if (!field) {
                field = file_.field_fact(step);
            }
            if (!field) {
                continue;
            }
            if (field->is_virtual_base_storage) {
                adjustment.kind = cir::VirtualAdjustmentKind::Virtual;
                cir::EntityId owner = file_.entity(step).parent;
                const cir::RecordFacts* owner_facts =
                    owner == facts.entity ? &facts
                                          : file_.record_facts(owner);
                size_t index = 0;
                if (owner_facts) {
                    for (const cir::RecordFacts::VirtualBase& vbase :
                         owner_facts->virtual_bases) {
                        if (vbase.storage_field == step) {
                            index = vbase.vtable_index;
                            break;
                        }
                    }
                }
                const int64_t ptr = static_cast<int64_t>(
                    std::max<uint32_t>(1,
                        file_.target_info().pointer_width / 8));
                adjustment.vtable_offset_bytes =
                    -static_cast<int64_t>(3 + index) * ptr;
                continue;
            }
            adjustment.static_offset_bytes +=
                static_cast<int64_t>(field->offset);
        }
        if (adjustment.kind != cir::VirtualAdjustmentKind::Virtual &&
            adjustment.static_offset_bytes != 0) {
            adjustment.kind = cir::VirtualAdjustmentKind::NonVirtual;
        }
        return adjustment;
    };
    auto covariance_adjustment =
        [&](cir::EntityId target, cir::EntityId declaration) {
        for (const cir::VirtualOverrideEdgeFact& edge :
             facts.virtual_override_edges) {
            if (edge.overriding == target &&
                edge.overridden == declaration &&
                edge.return_relation ==
                    cir::VirtualReturnRelation::Covariant) {
                return virtual_adjustment_for_path(edge.covariance_path);
            }
        }
        return cir::VirtualAdjustmentFact{};
    };
    auto graph_reaches_fact = [&](uint32_t derived, uint32_t base) {
        if (derived == base) {
            return true;
        }
        std::vector<uint32_t> worklist{derived};
        std::vector<bool> visited(facts.virtual_subobjects.size(), false);
        while (!worklist.empty()) {
            uint32_t current = worklist.back();
            worklist.pop_back();
            if (current >= visited.size() || visited[current]) {
                continue;
            }
            visited[current] = true;
            for (const cir::VirtualSubobjectEdgeFact& edge :
                 facts.virtual_subobject_edges) {
                if (edge.derived_subobject != current) {
                    continue;
                }
                if (edge.base_subobject == base) {
                    return true;
                }
                worklist.push_back(edge.base_subobject);
            }
        }
        return false;
    };

    size_t inherited_primary_slots = vtable_slots.size();
    for (size_t i = 0; i < inherited_primary_slots &&
                       i < vtable_slot_declarations.size(); ++i) {
        cir::EntityId target = vtable_slots[i];
        cir::EntityId declaration = vtable_slot_declarations[i];
        if (target == declaration ||
            !covariance_adjustment(target, declaration).required() ||
            !target.valid() || file_.entity(target).parent != facts.entity) {
            continue;
        }
        auto method = std::find_if(
            facts.methods.begin(), facts.methods.end(),
            [&](const cir::RecordMethodFact& candidate) {
                return candidate.entity == target;
            });
        if (method == facts.methods.end() || method->is_consteval) {
            continue;
        }
        method->vtable_slot = static_cast<int32_t>(vtable_slots.size());
        vtable_slots.push_back(target);
        vtable_slot_declarations.push_back(target);
    }
    facts.vtable_slots = vtable_slots;
    facts.primary_vtable_slot_facts.clear();
    facts.primary_vtable_slot_facts.reserve(vtable_slots.size());
    uint32_t primary_table_subobject = 0;
    if (primary_base_polymorphic) {
        const cir::RecordBaseFact* primary_fact = nonvirtual_base_fact(0);
        if (primary_fact) {
            for (const cir::VirtualSubobjectFact& subobject :
                 facts.virtual_subobjects) {
                if (!subobject.is_virtual && subobject.id != 0 &&
                    subobject.record_entity == primary_fact->record_entity &&
                    subobject.static_offset_bytes ==
                        primary_fact->non_virtual_offset) {
                    primary_table_subobject = subobject.id;
                    break;
                }
            }
        }
    }
    for (size_t i = 0; i < vtable_slots.size(); ++i) {
        cir::VirtualTableSlotFact slot;
        slot.final_overrider = vtable_slots[i];
        slot.declaration = i < vtable_slot_declarations.size()
            ? vtable_slot_declarations[i]
            : vtable_slots[i];
        for (const cir::VirtualFinalOverriderFact& final :
             facts.virtual_final_overriders) {
            if (final.virtual_declaration != slot.declaration ||
                !final.final_overrider.valid() ||
                !graph_reaches_fact(primary_table_subobject,
                                    final.declaration_subobject)) {
                continue;
            }
            slot.final_overrider = final.final_overrider;
            slot.declaration_subobject = final.declaration_subobject;
            slot.final_subobject = final.final_subobject;
            int64_t delta = static_cast<int64_t>(
                facts.virtual_subobjects[final.final_subobject]
                    .static_offset_bytes) -
                static_cast<int64_t>(
                    facts.virtual_subobjects[primary_table_subobject]
                        .static_offset_bytes);
            if (delta != 0) {
                slot.this_adjustment.kind =
                    cir::VirtualAdjustmentKind::NonVirtual;
                slot.this_adjustment.static_offset_bytes = delta;
            }
            break;
        }
        slot.result_adjustment = covariance_adjustment(
            slot.final_overrider, slot.declaration);
        const cir::RecordMethodFact* final_method = nullptr;
        for (const cir::RecordMethodFact& method : facts.methods) {
            if (method.entity == slot.final_overrider) {
                final_method = &method;
                break;
            }
        }
        if (!final_method) {
            final_method = file_.method_fact(slot.final_overrider);
        }
        slot.runtime_callable = !final_method ||
            !final_method->is_consteval;
        slot.is_deleting_destructor = i > 0 &&
            vtable_slots[i] == vtable_slots[i - 1] &&
            vtable_slots[i].valid() && file_.valid(vtable_slots[i]) &&
            file_.entity(vtable_slots[i]).kind ==
                cir::EntityKind::Destructor;
        facts.primary_vtable_slot_facts.push_back(std::move(slot));
    }

    for (cir::RecordMethodFact& method : facts.methods) {
        if (!method.is_eligible ||
            method.special_member_kind == cir::SpecialMemberKind::None) {
            continue;
        }
        for (const cir::RecordMethodFact& other : facts.methods) {
            if (&method == &other || !other.is_eligible ||
                other.special_member_kind != method.special_member_kind) {
                continue;
            }
            if (std::find(other.more_constrained_than.begin(),
                          other.more_constrained_than.end(),
                          method.associated_constraint_fingerprint) !=
                other.more_constrained_than.end()) {
                method.is_eligible = false;
                break;
            }
        }
    }

    if (lang_opts_.is_cxx_mode()) {
        std::vector<cir::RecordMethodFact*> candidates;
        bool dependent = false;
        for (cir::RecordMethodFact& method : facts.methods) {
            if (method.special_member_kind !=
                cir::SpecialMemberKind::Destructor) {
                continue;
            }
            method.is_selected_destructor = false;
            if (method.constraint_satisfaction ==
                cir::ConstraintSatisfactionKind::Dependent) {
                dependent = true;
                continue;
            }
            if (method.constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Unsatisfied ||
                method.constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Invalid) {
                continue;
            }
            candidates.push_back(&method);
        }
        std::vector<cir::RecordMethodFact*> best;
        for (cir::RecordMethodFact* candidate : candidates) {
            bool dominated = false;
            for (cir::RecordMethodFact* other : candidates) {
                if (candidate == other) {
                    continue;
                }
                if (std::find(other->more_constrained_than.begin(),
                              other->more_constrained_than.end(),
                              candidate->associated_constraint_fingerprint) !=
                    other->more_constrained_than.end()) {
                    dominated = true;
                    break;
                }
            }
            if (!dominated) {
                best.push_back(candidate);
            }
        }
        if (!dependent && best.size() == 1) {
            best.front()->is_selected_destructor = true;
        } else if (!dependent) {
            report_error(best.empty()
                             ? "no viable destructor found for class"
                             : "destructor selection is ambiguous",
                         loc);
            decl.has_error = true;
        }
    }
    facts.definition_data.default_constructor_is_deleted = false;
    facts.definition_data.has_deleted_destructor = false;
    for (const cir::RecordMethodFact& method : facts.methods) {
        if (method.special_member_kind ==
                cir::SpecialMemberKind::DefaultConstructor &&
            method.is_deleted) {
            facts.definition_data.default_constructor_is_deleted = true;
        }
        if (method.is_selected_destructor && method.is_deleted) {
            facts.definition_data.has_deleted_destructor = true;
        }
    }

    bool aggregate = !facts.is_lambda_closure &&
        !facts.definition_data.has_user_declared_constructor &&
        !facts.definition_data.has_inherited_constructor &&
        !facts.is_polymorphic && facts.virtual_bases.empty();
    cir::RecordMemberAccess data_access = cir::RecordMemberAccess::Public;
    bool have_data_access = false;
    for (const cir::RecordBaseFact& base : facts.bases) {
        aggregate = aggregate &&
            base.declared_access == cir::RecordMemberAccess::Public &&
            !base.is_virtual;
    }
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_base_subobject || is_vptr(field)) {
            continue;
        }
        aggregate = aggregate &&
            field.declared_access == cir::RecordMemberAccess::Public;
        if (!have_data_access) {
            data_access = field.declared_access;
            have_data_access = true;
        }
    }
    facts.is_aggregate = aggregate ? cir::ClassPropertyState::True
                                   : cir::ClassPropertyState::False;

    bool have_eligible_copy_or_move = false;
    bool all_eligible_copy_or_move_trivial = true;
    bool trivial_destructor = false;
    bool destructor_user_provided = false;
    bool have_trivial_eligible_constructor = false;
    bool have_eligible_default_constructor = false;
    bool all_eligible_default_constructors_trivial = true;
    bool all_copy_move_deleted = true;
    bool abi_nontrivial_copy_or_move = false;
    bool have_destructor_fact = false;
    bool have_copy_move_constructor_fact = false;
    for (const cir::RecordMethodFact& method : facts.methods) {
        switch (method.special_member_kind) {
            case cir::SpecialMemberKind::DefaultConstructor:
                have_trivial_eligible_constructor |=
                    method.is_eligible && method.is_trivial;
                if (method.is_eligible) {
                    have_eligible_default_constructor = true;
                    all_eligible_default_constructors_trivial &=
                        method.is_trivial;
                }
                break;
            case cir::SpecialMemberKind::CopyConstructor:
            case cir::SpecialMemberKind::MoveConstructor:
                have_copy_move_constructor_fact = true;
                all_copy_move_deleted =
                    all_copy_move_deleted && method.is_deleted;
                if (method.is_eligible) {
                    have_eligible_copy_or_move = true;
                    all_eligible_copy_or_move_trivial &= method.is_trivial;
                    abi_nontrivial_copy_or_move |= !method.is_trivial;
                    have_trivial_eligible_constructor |= method.is_trivial;
                }
                break;
            case cir::SpecialMemberKind::CopyAssignment:
            case cir::SpecialMemberKind::MoveAssignment:
                if (method.is_eligible) {
                    have_eligible_copy_or_move = true;
                    all_eligible_copy_or_move_trivial &= method.is_trivial;
                }
                break;
            case cir::SpecialMemberKind::Destructor:
                have_destructor_fact = true;
                if (method.is_eligible) {
                    trivial_destructor = method.is_trivial;
                    destructor_user_provided = method.is_user_provided;
                }
                break;
            case cir::SpecialMemberKind::None:
                break;
        }
    }
    bool trivially_copyable = have_eligible_copy_or_move &&
        all_eligible_copy_or_move_trivial && trivial_destructor;
    facts.is_trivially_copyable = trivially_copyable
        ? cir::ClassPropertyState::True
        : cir::ClassPropertyState::False;
    bool trivial = trivially_copyable &&
        have_eligible_default_constructor &&
        all_eligible_default_constructors_trivial;
    facts.is_trivial = trivial ? cir::ClassPropertyState::True
                               : cir::ClassPropertyState::False;
    bool implicit_lifetime =
        (aggregate && !destructor_user_provided) ||
        (have_trivial_eligible_constructor && trivial_destructor);
    facts.is_implicit_lifetime = implicit_lifetime
        ? cir::ClassPropertyState::True
        : cir::ClassPropertyState::False;

    bool standard_layout = !facts.is_polymorphic && facts.virtual_bases.empty();
    bool member_and_base_have_storage = false;
    size_t bases_with_data = 0;
    std::unordered_set<uint32_t> base_types;
    std::function<void(cir::TypeId, std::unordered_set<uint32_t>&)> add_m_set;
    add_m_set = [&](cir::TypeId type, std::unordered_set<uint32_t>& result) {
        type = file_.resolved_type(type);
        if (!file_.valid(type)) {
            return;
        }
        if (file_.type(type).kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(type));
            if (array) {
                add_m_set(array->element_type.type, result);
            }
            return;
        }
        if (file_.type(type).kind != cir::TypeKind::Record) {
            result.insert(type.index);
            return;
        }
        result.insert(type.index);
        const cir::RecordFacts* nested = type == file_.resolved_type(decl.type)
            ? &facts
            : file_.record_facts_for_type(type);
        if (!nested) {
            return;
        }
        for (const cir::RecordFieldFact& nested_field : nested->fields) {
            if (nested_field.is_base_subobject ||
                (nested_field.name.valid() &&
                 file_.name(nested_field.name) == ".vptr")) {
                continue;
            }
            add_m_set(nested_field.type.type, result);
            if (nested->kind != cir::RecordKind::Union &&
                nested_field.subobject_size != cir::SubobjectSizeKind::Zero) {
                break;
            }
        }
    };
    std::unordered_set<uint32_t> m_set;
    bool own_data = false;
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_base_subobject || is_vptr(field)) {
            continue;
        }
        own_data = true;
        standard_layout = standard_layout &&
            (!have_data_access || field.declared_access == data_access);
        cir::TypeId member_type = file_.resolved_type(field.type.type);
        if (file_.valid(member_type) &&
            (file_.type(member_type).kind == cir::TypeKind::LValueReference ||
             file_.type(member_type).kind == cir::TypeKind::RValueReference)) {
            standard_layout = false;
        }
        while (file_.valid(member_type) &&
               file_.type(member_type).kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(member_type));
            member_type = array
                ? file_.resolved_type(array->element_type.type)
                : cir::TypeId{};
        }
        const cir::RecordFacts* nested =
            file_.record_facts_for_type(member_type);
        if (nested) {
            standard_layout = standard_layout &&
                nested->is_standard_layout == cir::ClassPropertyState::True;
        }
    }
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_base_subobject || is_vptr(field)) {
            continue;
        }
        add_m_set(field.type.type, m_set);
        if (facts.kind != cir::RecordKind::Union &&
            field.subobject_size != cir::SubobjectSizeKind::Zero) {
            break;
        }
    }
    for (const cir::RecordBaseFact& base : facts.bases) {
        cir::TypeId base_type = file_.resolved_type(base.type.type);
        standard_layout = standard_layout && !base.is_virtual &&
            base.declared_access == cir::RecordMemberAccess::Public &&
            base_types.insert(base_type.index).second &&
            m_set.find(base_type.index) == m_set.end();
        const cir::RecordFacts* base_record =
            file_.record_facts_for_type(base_type);
        if (!base_record) {
            standard_layout = false;
            continue;
        }
        standard_layout = standard_layout &&
            base_record->is_standard_layout == cir::ClassPropertyState::True;
        bool base_has_data = false;
        for (const cir::RecordFieldFact& base_field : base_record->fields) {
            if (!base_field.is_base_subobject &&
                !(base_field.name.valid() &&
                  file_.name(base_field.name) == ".vptr")) {
                base_has_data = true;
                break;
            }
        }
        bases_with_data += base_has_data ? 1 : 0;
    }
    member_and_base_have_storage = own_data && bases_with_data != 0;
    standard_layout = standard_layout && !member_and_base_have_storage &&
        bases_with_data <= 1;
    facts.is_standard_layout = !facts.dependent_bases.empty()
        ? cir::ClassPropertyState::Dependent
        : standard_layout ? cir::ClassPropertyState::True
                          : cir::ClassPropertyState::False;

    facts.is_non_trivial_for_calls = abi_nontrivial_copy_or_move ||
        (have_destructor_fact && !trivial_destructor) ||
        (have_copy_move_constructor_fact && all_copy_move_deleted);
    facts.is_literal_class_type =
        record_has_supported_literal_class_shape(file_, facts);

    for (cir::RecordMethodFact& method : facts.methods) {
        const cir::Entity* entity =
            method.entity.valid() && file_.valid(method.entity)
                ? &file_.entity(method.entity)
                : nullptr;
        method.is_key_function_candidate =
            entity &&
            method.is_virtual &&
            !method.is_pure &&
            !method.is_implicitly_declared &&
            (!method.is_defaulted || method.is_user_provided) &&
            !method.is_deleted &&
            !method.is_constexpr &&
            !method.is_consteval &&
            !method.is_function_template &&
            !entity->decl_flags.is_inline &&
            !entity->has_deferred_definition;
    }

    for (const cir::RecordMethodFact& method : facts.methods) {
        if (!method.is_defaulted || method.is_deleted ||
            !method.entity.valid() ||
            file_.entity(method.entity).is_definition) {
            continue;
        }
        switch (method.special_member_kind) {
            case cir::SpecialMemberKind::DefaultConstructor:
                implicit_default_constructor = method.entity;
                break;
            case cir::SpecialMemberKind::CopyConstructor:
                implicit_copy_constructor = method.entity;
                break;
            case cir::SpecialMemberKind::MoveConstructor:
                implicit_move_constructor = method.entity;
                break;
            case cir::SpecialMemberKind::CopyAssignment:
                implicit_copy_assignment = method.entity;
                break;
            case cir::SpecialMemberKind::MoveAssignment:
                implicit_move_assignment = method.entity;
                break;
            case cir::SpecialMemberKind::Destructor:
                implicit_destructor = method.entity;
                break;
            case cir::SpecialMemberKind::None:
                break;
        }
    }

    // Publish the completed semantic/layout facts before ABI image emission.
    // D0 synthesis runs while building the vtable and therefore must be able
    // to perform canonical member lookup against this complete class rather
    // than the earlier incomplete shell.
    file_.set_record_facts(decl.entity, facts);
    if (!facts.is_template_pattern_provisional && !in_template_definition()) {
        for (cir::RecordMethodFact& method : facts.methods) {
            if (!method.is_virtual || !method.entity.valid() ||
                file_.entity(method.entity).kind !=
                    cir::EntityKind::Destructor) {
                continue;
            }
            DeallocationSelection selection = select_deallocation_function(
                decl.type, /*is_array=*/false, /*force_global=*/false,
                /*placement_matching=*/false, nullptr, {},
                file_.entity(method.entity).loc);
            method.deleting_destructor_deallocation.entity = selection.entity;
            method.deleting_destructor_deallocation.form = selection.form;
        }
        file_.set_record_facts(decl.entity, facts);
    }

    if (is_polymorphic_record) {

        cir::DeclContextId early_context =
            file_.entity(decl.entity).semantic_context;
        if (!early_context.valid()) {
            early_context =
                file_.create_decl_context(cir::DeclContextKind::Record,
                                          current_decl_context(),
                                          decl.entity,
                                          loc);
            file_.entity_mut(decl.entity).semantic_context = early_context;
        }
        for (const cir::RecordMethodFact& method : facts.methods) {
            if (method.entity.valid()) {
                file_.entity_mut(method.entity).semantic_context = early_context;
            }
        }
        std::string ztv_symbol =
            abi::itanium_record_data_symbol(file_, decl.entity, "_ZTV");
        cir::EntityId zti_entity =
            class_typeinfo_entity(decl.entity, facts, loc);

        auto table_prefix_words = [&](cir::TypeId base_type) -> size_t {
            if (!base_type.valid()) {
                return virtual_base_list.size();
            }
            const cir::RecordFacts* record = file_.record_facts_for_type(
                file_.resolved_type(base_type));
            return record ? record->virtual_bases.size() : 0;
        };
        size_t primary_prefix = virtual_base_list.size();
        size_t total_words = primary_prefix + 2 + vtable_slots.size();
        for (SecondaryTable& table : secondary_tables) {
            total_words += table_prefix_words(table.base_type) + 2 +
                           table.slots.size();
        }

        const size_t ptr = std::max<size_t>(
            1, (file_.target_info().pointer_width + 7) / 8);
        size_t vtable_bytes = total_words * ptr;
        cir::TypeId vtable_type = builder_.array_type(
            builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void)),
            total_words);
        cir::EntityId vtable_entity =
            builder_.add_entity(cir::EntityKind::Variable, ztv_symbol,
                                vtable_type, {}, loc,
                                cir::StorageDuration::Static);
        cir::Entity& vtable_record = file_.entity_mut(vtable_entity);
        vtable_record.is_definition = true;
        vtable_record.linkage = cir::LinkageKind::LinkOnceODR;
        vtable_record.is_extern_c = true;
        mark_generated_abi_entity(vtable_entity, decl.entity,
                                  cir::GeneratedSymbolRole::VTable);
        vtable_record.qualifiers = cir::QualConst;
        vtable_record.has_static_initializer = true;
        vtable_record.static_initializer_bytes.assign(vtable_bytes, 0);
        auto write_word = [&](size_t byte_offset, int64_t value) {
            abi::write_scalar_bits(
                file_.entity_mut(vtable_entity)
                        .static_initializer_bytes.data() + byte_offset,
                ptr, static_cast<uint64_t>(value), 0,
                file_.target_info().endianness);
        };

        auto virtual_base_offset = [&](cir::EntityId record_entity,
                                       bool* found) -> size_t {
            for (const cir::RecordFacts::VirtualBase& vbase :
                 virtual_base_list) {
                if (vbase.record_entity == record_entity) {
                    if (found) {
                        *found = true;
                    }
                    return vbase.storage_offset_bytes;
                }
            }
            if (found) {
                *found = false;
            }
            return 0;
        };
        size_t primary_ap = (primary_prefix + 2) * ptr;
        facts.vtable_address_point = primary_ap;
        for (size_t i = 0; i < virtual_base_list.size(); ++i) {
            write_word(primary_ap - 3 * ptr - ptr * i,
                       static_cast<int64_t>(
                           virtual_base_list[i].storage_offset_bytes));
        }
        if (zti_entity.valid()) {
            vtable_record.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{primary_ap - ptr, zti_entity,
                                                 0});
        }
        auto resolve_slot_target =
            [&](const cir::VirtualTableSlotFact& plan) -> cir::EntityId {
            cir::EntityId target = plan.final_overrider;
            cir::EntityId slot_declaration = plan.declaration.valid()
                ? plan.declaration
                : plan.final_overrider;
            if (!plan.runtime_callable || !target.valid()) {
                return {};
            }
            const cir::RecordMethodFact* slot_fact = nullptr;
            for (const cir::RecordMethodFact& own : facts.methods) {
                if (own.entity == target) {
                    slot_fact = &own;
                    break;
                }
            }
            if (!slot_fact) {
                slot_fact = file_.method_fact(target);
            }
            if (slot_fact && slot_fact->is_pure) {
                return runtime_function(
                    "__cxa_pure_virtual",
                    function_type(
                        file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::Void)),
                        {}, false, true),
                    loc);
            }
            if (plan.is_deleting_destructor) {

                target = synthesize_deleting_destructor(target, loc);
                slot_declaration =
                    synthesize_deleting_destructor(slot_declaration, loc);
            } else if (target.valid() && file_.valid(target) &&
                       file_.entity(target).kind ==
                           cir::EntityKind::Destructor) {

                target = structor_complete_variant(target);
                slot_declaration =
                    structor_complete_variant(slot_declaration);
            }
            if (plan.this_adjustment.required() ||
                plan.result_adjustment.required()) {
                return synthesize_vtable_thunk(
                    target,
                    slot_declaration,
                    plan.this_adjustment,
                    plan.result_adjustment,
                    loc);
            }
            return target;
        };
        auto slot_is_deleting = [&](const std::vector<cir::EntityId>& slots,
                                    size_t i) {
            return i > 0 && slots[i] == slots[i - 1] && slots[i].valid() &&
                   file_.valid(slots[i]) &&
                   file_.entity(slots[i]).kind == cir::EntityKind::Destructor;
        };
        for (size_t i = 0; i < vtable_slots.size(); ++i) {

            cir::VirtualTableSlotFact plan =
                i < facts.primary_vtable_slot_facts.size()
                ? facts.primary_vtable_slot_facts[i]
                : cir::VirtualTableSlotFact{};
            if (!plan.final_overrider.valid()) {
                plan.final_overrider = vtable_slots[i];
                plan.declaration = vtable_slots[i];
                plan.is_deleting_destructor =
                    slot_is_deleting(vtable_slots, i);
            }
            cir::EntityId slot_target = resolve_slot_target(plan);
            if (slot_target.valid()) {
                file_.entity_mut(vtable_entity)
                    .static_initializer_relocations.push_back(
                    cir::StaticInitializerRelocation{primary_ap + ptr * i,
                                                     slot_target, 0});
            }
        }
        size_t word = primary_prefix + 2 + vtable_slots.size();
        for (SecondaryTable& table : secondary_tables) {
            if (table.subobject_id >= facts.virtual_subobjects.size()) {
                continue;
            }
            const cir::VirtualSubobjectFact& table_object =
                facts.virtual_subobjects[table.subobject_id];
            cir::EntityId base_field_entity =
                table_object.storage_path.empty()
                ? cir::EntityId{}
                : table_object.storage_path.back();
            size_t base_offset = table_object.static_offset_bytes;
            size_t prefix = table_prefix_words(table.base_type);
            size_t table_ap = (word + prefix + 2) * ptr;

            const cir::RecordFacts* base_record = file_.record_facts_for_type(
                file_.resolved_type(table.base_type));
            if (base_record) {
                for (size_t i = 0; i < base_record->virtual_bases.size() &&
                                   i < prefix; ++i) {
                    bool found = false;
                    size_t storage = virtual_base_offset(
                        base_record->virtual_bases[i].record_entity, &found);
                    if (found) {
                        write_word(table_ap - 3 * ptr - ptr * i,
                                   static_cast<int64_t>(storage) -
                                       static_cast<int64_t>(base_offset));
                    }
                }
            }

            write_word(table_ap - 2 * ptr, -static_cast<int64_t>(base_offset));
            if (zti_entity.valid()) {
                file_.entity_mut(vtable_entity)
                    .static_initializer_relocations.push_back(
                        cir::StaticInitializerRelocation{table_ap - ptr,
                                                         zti_entity, 0});
            }
            uint32_t table_subobject = table.subobject_id;
            std::vector<cir::VirtualTableSlotFact> table_slot_facts;
            table_slot_facts.reserve(table.slots.size());
            for (size_t i = 0; i < table.slots.size(); ++i) {
                cir::EntityId slot_entity = table.slots[i];
                cir::VirtualTableSlotFact plan;
                plan.final_overrider = slot_entity;
                plan.declaration = i < table.declarations.size()
                    ? table.declarations[i]
                    : slot_entity;
                plan.is_deleting_destructor =
                    slot_is_deleting(table.slots, i);
                for (const cir::VirtualFinalOverriderFact& final :
                     facts.virtual_final_overriders) {
                    if (final.virtual_declaration != plan.declaration ||
                        !final.final_overrider.valid() ||
                        !graph_reaches_fact(table_subobject,
                                            final.declaration_subobject)) {
                        continue;
                    }
                    plan.final_overrider = final.final_overrider;
                    plan.declaration_subobject =
                        final.declaration_subobject;
                    plan.final_subobject = final.final_subobject;
                    if (final.final_subobject <
                        facts.virtual_subobjects.size()) {
                        int64_t final_offset = static_cast<int64_t>(
                            facts.virtual_subobjects[final.final_subobject]
                                .static_offset_bytes);
                        int64_t delta = final_offset -
                            static_cast<int64_t>(base_offset);
                        if (delta != 0) {
                            plan.this_adjustment.kind =
                                cir::VirtualAdjustmentKind::NonVirtual;
                            plan.this_adjustment.static_offset_bytes = delta;
                        }
                    }
                    break;
                }
                plan.result_adjustment = covariance_adjustment(
                    plan.final_overrider, plan.declaration);
                const cir::RecordMethodFact* final_method =
                    file_.method_fact(plan.final_overrider);
                plan.runtime_callable = !final_method ||
                    !final_method->is_consteval;
                table.slots[i] = plan.final_overrider;
                cir::EntityId slot_target = resolve_slot_target(plan);
                if (slot_target.valid()) {
                    file_.entity_mut(vtable_entity)
                        .static_initializer_relocations.push_back(
                        cir::StaticInitializerRelocation{table_ap + ptr * i,
                                                         slot_target, 0});
                }
                table_slot_facts.push_back(std::move(plan));
            }
            cir::RecordFacts::SecondaryVtable secondary;
            secondary.base_field = base_field_entity;
            secondary.storage_path = table_object.storage_path;
            secondary.base_offset_bytes = base_offset;
            secondary.address_point_bytes = table_ap;
            secondary.base_type = file_.type_ref(table.base_type);
            secondary.is_virtual = table.is_virtual;
            secondary.slots = table.slots;
            secondary.slot_facts = std::move(table_slot_facts);
            facts.secondary_vtables.push_back(secondary);
            word += prefix + 2 + table.slots.size();
        }
        facts.vtable_entity = vtable_entity;
        facts.typeinfo_entity = zti_entity;

        emit_virtual_table_table(facts, loc);
    }

    if (auto pending_friends = tstate().pending_class_friends_.find(
            static_cast<uint64_t>(decl.entity.index));
        pending_friends != tstate().pending_class_friends_.end()) {
        facts.class_friends = std::move(pending_friends->second);
        tstate().pending_class_friends_.erase(pending_friends);
    }
    if (auto pending_function_friends =
            tstate().pending_function_friends_.find(
                static_cast<uint64_t>(decl.entity.index));
        pending_function_friends != tstate().pending_function_friends_.end()) {
        facts.function_friends = std::move(pending_function_friends->second);
        tstate().pending_function_friends_.erase(pending_function_friends);
    }

    file_.set_record_facts(decl.entity, std::move(facts));

    cir::DeclContextId record_context = file_.entity(decl.entity).semantic_context;
    if (!record_context.valid()) {
        record_context =
            file_.create_decl_context(cir::DeclContextKind::Record,
                                      current_decl_context(),
                                      decl.entity,
                                      loc);
        file_.entity_mut(decl.entity).semantic_context = record_context;
    }
    bool lambda_closure_fields =
        file_.record_facts(decl.entity)->is_lambda_closure;
    bool record_is_template_pattern =
        file_.record_facts(decl.entity)->is_template_pattern_provisional ||
        file_.entity(decl.entity).is_template_pattern;
    bool synthesize_special_member_bodies =
        !record_is_template_pattern;
    for (const cir::RecordFieldFact& field : file_.record_facts(decl.entity)->fields) {
        if (field.name.valid()) {

            if (!lambda_closure_fields) {
                diagnose_template_parameter_hiding(
                    file_.name(field.name),
                    file_.entity(field.entity).loc,
                    record_context);
            }
            file_.bind_entity(record_context,
                              field.name,
                              cir::LookupNamespace::Ordinary,
                              field.entity,
                              field.type,
                              false,
                              false,
                              true,
                              {},
                              file_.entity(field.entity).loc);
            file_.entity_mut(field.entity).lexical_context = record_context;
            file_.entity_mut(field.entity).semantic_context = record_context;
        }
    }
    for (const cir::RecordStaticDataMemberFact& member : file_.record_facts(decl.entity)->static_data_members) {
        if (member.name.valid()) {
            diagnose_template_parameter_hiding(file_.name(member.name),
                                               file_.entity(member.entity).loc,
                                               record_context);
            file_.bind_entity(record_context,
                              member.name,
                              cir::LookupNamespace::Ordinary,
                              member.entity,
                              member.type,
                              false,
                              false,
                              false,
                              {},
                              file_.entity(member.entity).loc);
            file_.entity_mut(member.entity).lexical_context = record_context;
            file_.entity_mut(member.entity).semantic_context = record_context;
        }
    }
    for (const cir::RecordMethodFact& method : file_.record_facts(decl.entity)->methods) {
        if (method.name.valid()) {
            cir::EntityKind method_kind = file_.entity(method.entity).kind;

            file_.bind_callable_overload(record_context,
                                         method.name,
                                         method.entity,
                                         method.type,
                                         method.is_deleted || method.is_defaulted,
                                         file_.entity(method.entity).loc);
            file_.entity_mut(method.entity).lexical_context = record_context;
            file_.entity_mut(method.entity).semantic_context = record_context;
        }
    }

    plan_and_synthesize_defaulted_comparisons(
        decl.entity, synthesize_special_member_bodies, loc);

    if (synthesize_special_member_bodies && implicit_destructor.valid() &&
        !file_.method_fact(implicit_destructor)->is_deleted) {

        std::unique_ptr<BlockContextState> saved = save_function_context();
        FunctionDeclStart start =
            begin_member_function(implicit_destructor, {}, loc, true);
        if (!start.decl.has_error) {
            StmtResult body = collect_destructor_epilogue(loc);
            finish_member_function(std::move(body), loc);
            file_.entity_mut(implicit_destructor).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        restore_function_context(std::move(saved));
    }

    if (synthesize_special_member_bodies &&
        implicit_default_constructor.valid() &&
        !file_.method_fact(implicit_default_constructor)->is_deleted) {

        std::unique_ptr<BlockContextState> saved = save_function_context();
        FunctionDeclStart start =
            begin_member_function(implicit_default_constructor, {}, loc, true);
        if (!start.decl.has_error) {
            StmtResult body = collect_constructor_initializers({}, loc);
            finish_member_function(std::move(body), loc);
            file_.entity_mut(implicit_default_constructor).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        restore_function_context(std::move(saved));
    }

    for (const InheritedConstructorPlan& plan : inherited_constructor_plans) {
        if (!synthesize_special_member_bodies || plan.deleted ||
            template_info(plan.entity) ||
            plan.nominations.empty()) {
            continue;
        }
        const cir::RecordMethodFact* origin_fact =
            file_.method_fact(plan.origin);
        const auto* origin_type = origin_fact
            ? std::get_if<cir::FunctionTypePayload>(&file_.type_payload(
                  file_.resolved_type(origin_fact->type.type)))
            : nullptr;
        if (!origin_type) {
            continue;
        }
        std::unique_ptr<BlockContextState> saved = save_function_context();
        std::vector<ParamInput> params;
        for (size_t i = 0; i < origin_type->parameters.size(); ++i) {
            ParamInput param;
            param.name = ".inherited." + std::to_string(i);
            param.type = origin_type->parameters[i];
            param.loc = loc;
            params.push_back(std::move(param));
        }
        FunctionDeclStart start =
            begin_member_function(plan.entity, params, loc, true);
        if (!start.decl.has_error) {
            MemberInitializerInput forward;
            forward.name = plan.nominations.front().direct_base_name;
            forward.base_type =
                plan.nominations.front().direct_base_type;
            const cir::RecordMethodFact* inherited_fact =
                file_.method_fact(plan.entity);
            const cir::RecordFacts* completed_record =
                file_.record_facts(decl.entity);
            if (inherited_fact && inherited_fact->inherited_constructor &&
                completed_record &&
                !inherited_fact->inherited_constructor->routes.empty()) {
                uint32_t origin_subobject =
                    inherited_fact->inherited_constructor->routes.front()
                        .origin_subobject;
                if (origin_subobject <
                        completed_record->virtual_subobjects.size() &&
                    completed_record->virtual_subobjects[origin_subobject]
                        .is_virtual) {
                    forward.base_type =
                        completed_record->virtual_subobjects[origin_subobject]
                            .type.type;
                    if (plan.origin_record.valid() &&
                        file_.valid(plan.origin_record) &&
                        file_.entity(plan.origin_record).name.valid()) {
                        forward.name = std::string(file_.name(
                            file_.entity(plan.origin_record).name));
                    }
                }
            }
            forward.loc = loc;
            for (const ParamInput& param : params) {
                forward.arguments.push_back(
                    inherited_constructor_forwarding_argument(param, loc));
            }
            std::vector<MemberInitializerInput> initializers;
            initializers.push_back(std::move(forward));
            enter_template_argument_access_exemption();
            StmtResult body =
                collect_constructor_initializers(std::move(initializers),
                                                 loc);
            leave_template_argument_access_exemption();
            finish_member_function(std::move(body), loc);
            file_.entity_mut(plan.entity).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        restore_function_context(std::move(saved));
    }

    auto synthesize_implicit_transfer_constructor =
        [&](cir::EntityId constructor, bool is_move) {
        if (!synthesize_special_member_bodies) {
            return;
        }
        const cir::RecordMethodFact* constructor_fact =
            constructor.valid() ? file_.method_fact(constructor) : nullptr;
        if (!constructor.valid() ||
            (constructor_fact && constructor_fact->is_deleted)) {
            return;
        }

        std::unique_ptr<BlockContextState> saved = save_function_context();
        std::vector<ParamInput> params;
        {
            ParamInput source;
            source.name = is_move ? ".move.src" : ".copy.src";
            const auto* constructor_type = constructor_fact
                ? std::get_if<cir::FunctionTypePayload>(
                      &file_.type_payload(file_.resolved_type(
                          constructor_fact->type.type)))
                : nullptr;
            if (constructor_type &&
                !constructor_type->parameters.empty()) {
                source.type = constructor_type->parameters.front();
            } else {
                cir::TypeRef referred = file_.type_ref(decl.type);
                if (!is_move) {
                    referred.qualifiers = cir::QualConst;
                }
                source.type = file_.type_ref(
                    file_.reference_type(
                        referred, is_move ? cir::ReferenceKind::RValue
                                          : cir::ReferenceKind::LValue));
            }
            source.loc = loc;
            params.push_back(std::move(source));
        }
        FunctionDeclStart start =
            begin_member_function(constructor, params, loc, true);
        if (!start.decl.has_error &&
            start.function.parameters.size() >= 2) {
            const cir::RecordFacts* published = file_.record_facts(decl.entity);
            cir::InstId source_value = start.function.parameters[1].value.inst;
            cir::Fragment fragment;
            RecordLifecyclePlan lifecycle = record_lifecycle_plan(
                *published,
                is_move ? RecordLifecycleOperation::MoveConstruct
                        : RecordLifecycleOperation::CopyConstruct);
            if (published->kind == cir::RecordKind::Union) {
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("ctor.copy.union");
                cir::InstId this_value =
                    builder_.lvalue_to_rvalue(current_this_place_, loc);
                cir::InstId destination = builder_.deref(this_value, loc);
                cir::InstId source_place = builder_.deref(source_value, loc);
                cir::InstId value =
                    builder_.lvalue_to_rvalue(source_place, loc);
                builder_.store(destination, value, loc);
                fragment = chain(
                    std::move(fragment),
                    finish_fragment_block(block, previous), loc);
            }
            auto copy_fields = [&](bool base_subobjects, bool virtual_storage) {
                cir::Fragment copied;
                for (const RecordLifecycleStep& step : lifecycle.steps) {
                    const cir::RecordFieldFact& field = step.field;
                    if (field.is_base_subobject != base_subobjects ||
                        (base_subobjects &&
                         field.is_virtual_base_storage != virtual_storage)) {
                        continue;
                    }
                    cir::BlockId previous = builder_.current_block();
                    cir::BlockId block =
                        begin_fragment_block("ctor.copy.subobject");
                    cir::InstId this_value =
                        builder_.lvalue_to_rvalue(current_this_place_, loc);
                    cir::InstId destination = builder_.field_addr(
                        builder_.deref(this_value, loc), field.entity,
                        field.type.type, loc);
                    cir::InstId source_place = builder_.field_addr(
                        builder_.deref(source_value, loc), field.entity,
                        field.type.type, loc);

                    bool transfer_error = false;
                    if (cir::TypeId member_array_leaf =
                            step.array_shape.leaf_type;
                        member_array_leaf.valid()) {
                        const cir::RecordMethodFact* leaf_transfer =
                            canonical_special_member(
                                file_, member_array_leaf,
                                is_move
                                    ? cir::SpecialMemberKind::MoveConstructor
                                    : cir::SpecialMemberKind::CopyConstructor,
                                is_move,
                                constructor_fact
                                    ? special_member_source_form(
                                          file_, *constructor_fact)
                                    : std::nullopt);
                        if (leaf_transfer && leaf_transfer->entity.valid() &&
                            !leaf_transfer->is_deleted &&
                            !leaf_transfer->is_trivial) {
                            copied = chain(
                                std::move(copied),
                                finish_fragment_block(block, previous), loc);
                            std::function<cir::InstId(SrcLoc)> remat =
                                [this, field_entity = field.entity,
                                 field_type = field.type.type](SrcLoc l) {
                                    cir::InstId this_place =
                                        rematerialize_entity_place(
                                            current_this_place_, l);
                                    cir::InstId this_ptr =
                                        builder_.lvalue_to_rvalue(this_place,
                                                                  l);
                                    return builder_.field_addr(
                                        builder_.deref(this_ptr, l),
                                        field_entity, field_type, l);
                                };
                            copied = chain(
                                std::move(copied),
                                array_transfer_loop_fragment(
                                    destination, source_place,
                                    field.type.type, leaf_transfer->entity,
                                    /*assign=*/false, is_move, loc,
                                    &transfer_error, &remat),
                                loc);
                        } else {
                            if (field.subobject_size !=
                                cir::SubobjectSizeKind::Zero) {
                                cir::InstId value =
                                    builder_.lvalue_to_rvalue(source_place,
                                                             loc);
                                builder_.store(destination, value, loc);
                            }
                            copied = chain(
                                std::move(copied),
                                finish_fragment_block(block, previous), loc);
                        }
                    } else {
                        const cir::RecordMethodFact* member_transfer =
                            canonical_special_member(
                                file_, field.type.type,
                                is_move
                                    ? cir::SpecialMemberKind::MoveConstructor
                                    : cir::SpecialMemberKind::CopyConstructor,
                                is_move,
                                constructor_fact
                                    ? special_member_source_form(
                                          file_, *constructor_fact)
                                    : std::nullopt);
                        cir::EntityId member_copy = member_transfer
                            ? member_transfer->entity
                            : cir::EntityId{};
                        if (member_copy.valid()) {
                            member_copy = base_subobjects
                                ? structor_base_variant(member_copy)
                                : structor_complete_variant(member_copy);
                            cir::InstId source_address =
                                builder_.addr_of(source_place, loc);
                            std::vector<cir::InstId> ctor_arguments{
                                source_address};

                            if (base_subobjects &&
                                current_structor_vtt_place_.valid()) {
                                const cir::RecordFacts* subobject_facts =
                                    file_.record_facts_for_type(
                                        field.type.type);
                                if (subobject_facts &&
                                    !subobject_facts->virtual_bases.empty()) {
                                    VttInfo info = compute_vtt_info(*published);
                                    const auto& slices =
                                        field.is_virtual_base_storage
                                        ? info.vbase_slices
                                        : info.base_slices;
                                    cir::EntityId subobject_record =
                                        file_.record_entity(field.type.type);
                                    for (const VttInfo::Slice& slice : slices) {
                                        if (slice.record_entity ==
                                            subobject_record) {
                                            ctor_arguments.insert(
                                                ctor_arguments.begin(),
                                                vtt_slice_value(slice.start,
                                                                loc));
                                            break;
                                        }
                                    }
                                }
                            }
                            emit_construct_in_place(destination, member_copy,
                                                    ctor_arguments, loc);
                        } else if (field.subobject_size !=
                                   cir::SubobjectSizeKind::Zero) {
                            cir::InstId value =
                                builder_.lvalue_to_rvalue(source_place, loc);
                            builder_.store(destination, value, loc);
                        }
                        copied = chain(
                            std::move(copied),
                            finish_fragment_block(block, previous), loc);
                    }

                    if (!transfer_error) {
                        std::function<cir::InstId(SrcLoc)> remat =
                            [this, field_entity = field.entity,
                             field_type = field.type.type](SrcLoc action_loc) {
                                cir::InstId this_place =
                                    rematerialize_entity_place(
                                        current_this_place_, action_loc);
                                cir::InstId this_ptr =
                                    builder_.lvalue_to_rvalue(this_place,
                                                              action_loc);
                                return builder_.field_addr(
                                    builder_.deref(this_ptr, action_loc),
                                    field_entity, field_type, action_loc);
                            };
                        install_subobject_rollback(step, loc, remat);
                    }
                }
                fragment = chain(std::move(fragment), std::move(copied), loc);
            };

            if (!published->virtual_bases.empty()) {
                cir::Fragment saved = std::move(fragment);
                fragment = {};
                copy_fields(true, true);
                cir::Fragment vbase_fragment = std::move(fragment);
                fragment = std::move(saved);
                fragment = chain(
                    std::move(fragment),
                    guard_on_structor_flag(std::move(vbase_fragment), loc),
                    loc);
            }
            copy_fields(true, false);
            StmtResult vptr_store = store_vptr_fragment(loc);
            if (current_structor_flag_.valid()) {

                vptr_store.fragment = branch_on_structor_flag(
                    std::move(vptr_store.fragment),
                    vtt_vptr_store_fragment(loc), loc);
            }
            fragment = chain(std::move(fragment),
                             std::move(vptr_store.fragment), loc);
            copy_fields(false, false);
            finish_member_function(make_stmt_result(std::move(fragment)), loc);
            file_.entity_mut(constructor).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        restore_function_context(std::move(saved));
    };
    synthesize_implicit_transfer_constructor(implicit_copy_constructor, false);
    synthesize_implicit_transfer_constructor(implicit_move_constructor, true);

    auto synthesize_implicit_assignment =
        [&](cir::EntityId assignment, bool is_move) {
        if (!synthesize_special_member_bodies) {
            return;
        }
        const cir::RecordMethodFact* assignment_fact =
            assignment.valid() ? file_.method_fact(assignment) : nullptr;
        if (!assignment.valid() ||
            (assignment_fact && assignment_fact->is_deleted)) {
            return;
        }
        std::unique_ptr<BlockContextState> saved = save_function_context();
        ParamInput source;
        source.name = is_move ? ".move.src" : ".copy.src";
        const auto* assignment_type = assignment_fact
            ? std::get_if<cir::FunctionTypePayload>(
                  &file_.type_payload(file_.resolved_type(
                      assignment_fact->type.type)))
            : nullptr;
        if (assignment_type && !assignment_type->parameters.empty()) {
            source.type = assignment_type->parameters.front();
        } else {
            cir::TypeRef referred = file_.type_ref(decl.type);
            if (!is_move) {
                referred.qualifiers |= cir::QualConst;
            }
            source.type = file_.type_ref(file_.reference_type(
                referred, is_move ? cir::ReferenceKind::RValue
                                  : cir::ReferenceKind::LValue));
        }
        source.loc = loc;
        FunctionDeclStart start =
            begin_member_function(assignment, {source}, loc, true);
        if (!start.decl.has_error && start.function.parameters.size() >= 2) {
            cir::InstId source_value = start.function.parameters[1].value.inst;
            cir::BlockId function_block = builder_.current_block();
            cir::BlockId object_block =
                begin_fragment_block("assign.memberwise.objects");
            cir::InstId this_value = builder_.lvalue_to_rvalue(
                current_this_place_, loc);
            cir::InstId destination_object = builder_.deref(this_value, loc);
            cir::InstId source_object = builder_.deref(source_value, loc);
            cir::Fragment assignments =
                finish_fragment_block(object_block, function_block);
            const cir::RecordFacts* published =
                file_.record_facts(decl.entity);
            if (published && published->kind == cir::RecordKind::Union) {
                cir::BlockId block = begin_fragment_block("assign.union");
                cir::InstId value =
                    builder_.lvalue_to_rvalue(source_object, loc);
                builder_.store(destination_object, value, loc);
                assignments = chain(
                    std::move(assignments),
                    finish_fragment_block(block, function_block), loc);
            } else if (published) {
                RecordLifecyclePlan lifecycle = record_lifecycle_plan(
                    *published,
                    is_move ? RecordLifecycleOperation::MoveAssign
                            : RecordLifecycleOperation::CopyAssign);
                for (const RecordLifecycleStep& step : lifecycle.steps) {
                    const cir::RecordFieldFact& field = step.field;
                    cir::BlockId block =
                        begin_fragment_block("assign.memberwise.field");
                    cir::InstId destination = builder_.field_addr(
                        destination_object, field.entity,
                        field.type.type, loc);
                    cir::InstId source_place = builder_.field_addr(
                        source_object, field.entity,
                        field.type.type, loc);

                    if (cir::TypeId member_array_leaf =
                            step.array_shape.leaf_type;
                        member_array_leaf.valid()) {
                        const cir::RecordMethodFact* leaf_assignment =
                            canonical_special_member(
                                file_, member_array_leaf,
                                is_move
                                    ? cir::SpecialMemberKind::MoveAssignment
                                    : cir::SpecialMemberKind::CopyAssignment,
                                is_move,
                                assignment_fact
                                    ? special_member_source_form(
                                          file_, *assignment_fact)
                                    : std::nullopt);
                        if (leaf_assignment &&
                            leaf_assignment->entity.valid() &&
                            !leaf_assignment->is_deleted &&
                            !leaf_assignment->is_trivial) {
                            cir::Fragment field_fragment =
                                finish_fragment_block(block, function_block);
                            bool transfer_error = false;
                            cir::Fragment loop = array_transfer_loop_fragment(
                                destination, source_place, field.type.type,
                                leaf_assignment->entity, /*assign=*/true,
                                is_move, loc, &transfer_error);
                            assignments = chain(std::move(assignments),
                                                std::move(field_fragment),
                                                loc);
                            assignments = chain(std::move(assignments),
                                                std::move(loop), loc);
                        } else {
                            cir::InstId value =
                                builder_.lvalue_to_rvalue(source_place, loc);
                            builder_.store(destination, value, loc);
                            assignments = chain(
                                std::move(assignments),
                                finish_fragment_block(block, function_block),
                                loc);
                        }
                        continue;
                    }
                    const cir::RecordMethodFact* member_assignment =
                        canonical_special_member(
                            file_, field.type.type,
                            is_move
                                ? cir::SpecialMemberKind::MoveAssignment
                                : cir::SpecialMemberKind::CopyAssignment,
                            is_move,
                            assignment_fact
                                ? special_member_source_form(
                                      file_, *assignment_fact)
                                : std::nullopt);
                    if (member_assignment &&
                        member_assignment->entity.valid() &&
                        !member_assignment->is_deleted) {
                        cir::Fragment field_fragment =
                            finish_fragment_block(block, function_block);
                        ExprResult callee;
                        callee.fragment = std::move(field_fragment);
                        callee.place = destination;
                        callee.entity = member_assignment->entity;
                        callee.type =
                            file_.entity(member_assignment->entity).type;
                        callee.name = "operator=";

                        callee.qualified_name = true;
                        callee.category = ValueCategory::FunctionDesignator;

                        ExprResult argument;
                        argument.place = source_place;
                        argument.type = field.type.type;
                        argument.category = is_move
                            ? ValueCategory::XValue
                            : ValueCategory::LValue;
                        std::vector<ExprResult> call_arguments;
                        call_arguments.push_back(std::move(argument));
                        ExprResult call = collect_call_expr(
                            std::move(callee), std::move(call_arguments), loc);
                        assignments = chain(
                            std::move(assignments),
                            std::move(call.fragment), loc);
                    } else {
                        cir::InstId value =
                            builder_.lvalue_to_rvalue(source_place, loc);
                        builder_.store(destination, value, loc);
                        assignments = chain(
                            std::move(assignments),
                            finish_fragment_block(block, function_block), loc);
                    }
                }
            }
            ExprResult returned;
            returned.place = destination_object;
            returned.type = decl.type;
            returned.category = ValueCategory::LValue;
            StmtResult return_stmt =
                collect_return_stmt(std::move(returned), loc);
            cir::Fragment body = chain(std::move(assignments),
                                       std::move(return_stmt.fragment), loc);
            finish_member_function(
                make_stmt_result(std::move(body), true,
                                 return_stmt.has_error),
                loc);
            file_.entity_mut(assignment).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        restore_function_context(std::move(saved));
    };
    synthesize_implicit_assignment(implicit_copy_assignment, false);
    synthesize_implicit_assignment(implicit_move_assignment, true);

    decl.is_definition = true;
    return decl;
}

Session::TagLookupResult Session::lookup_record_tag(std::string_view name,
                                                    cir::RecordKind kind,
                                                    TagLookupMode mode) const {
    TagLookupResult result;
    const cir::Binding* binding =
        lookup_tag_binding(name, mode == TagLookupMode::Visible);
    if (binding && !binding->entities.empty()) {
        result.binding = binding;
        result.entity = binding->entities.back();
        result.type = binding->type.type;
        result.facts = file_.record_facts(result.entity);
        result.found = result.entity.valid();
    } else {
        cir::ModuleAttachmentId module_attachment{};
        for (cir::DeclContextId context = current_decl_context();
             context.valid() && file_.valid(context);
             context = file_.decl_context(context).parent) {
            cir::EntityId owner = file_.decl_context(context).owner;
            if (owner.valid() && file_.valid(owner) &&
                file_.entity(owner).module_attachment.valid()) {
                module_attachment = file_.entity(owner).module_attachment;
                break;
            }
        }
        result.entity = hidden_friend_record_entity(
            name, current_decl_context(), module_attachment);
        if (!result.entity.valid()) {
            return result;
        }
        result.type = file_.entity(result.entity).type;
        result.facts = file_.record_facts(result.entity);
        result.found = true;
    }
    result.kind_mismatch =
        result.found &&
        (!file_.valid(result.entity) ||
         file_.entity(result.entity).kind != cir::EntityKind::Record ||
         !result.facts ||
         !record_kinds_agree(result.facts->kind, kind));
    return result;
}

RecordDeclResult Session::create_record_tag(cir::RecordKind kind,
                                            std::string tag,
                                            SrcLoc loc,
                                            bool bind_tag) {
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Record, tag, {}, {}, loc);
    cir::TypeId type = builder_.record_type(entity, std::string(cir::record_kind_name(kind)) + " " + tag);
    file_.entity_mut(entity).type = type;
    file_.entity_mut(entity).lexical_context = current_decl_context();
    file_.entity_mut(entity).semantic_context =
        file_.create_decl_context(cir::DeclContextKind::Record,
                                  current_decl_context(),
                                  entity,
                                  loc);

    bool local_declaration_context = false;
    for (cir::DeclContextId context = current_decl_context();
         context.valid() && file_.valid(context);
         context = file_.decl_context(context).parent) {
        cir::DeclContextKind context_kind = file_.decl_context(context).kind;
        if (context_kind == cir::DeclContextKind::Function ||
            context_kind == cir::DeclContextKind::Block) {
            local_declaration_context = true;
            break;
        }
        if (context_kind == cir::DeclContextKind::Namespace ||
            context_kind == cir::DeclContextKind::TranslationUnit) {
            break;
        }
    }
    if (lang_opts_.is_cxx_mode() && local_declaration_context &&
        current_function_.valid() && file_.valid(current_function_)) {
        cir::EntityId function = file_.function(current_function_).entity;
        if (function.valid() && file_.valid(function)) {
            cir::Entity& record = file_.entity_mut(entity);
            record.local_enclosing_function = function;
            record.local_source_name = file_.intern_name(tag);
            bool is_anonymous_record =
                tag.rfind("<anonymous-", 0) == 0 ||
                tag.rfind(".anonymous.", 0) == 0;
            record.local_name_kind = tag.rfind(".lambda.", 0) == 0
                ? cir::LocalNameComponentKind::Lambda
                : (is_anonymous_record
                       ? cir::LocalNameComponentKind::Anonymous
                       : cir::LocalNameComponentKind::SourceName);
            uint32_t ordinal = 0;
            uint32_t anonymous_ordinal = 0;
            for (cir::EntityId prior_id : file_.entity_ids()) {
                if (prior_id == entity || !file_.valid(prior_id)) {
                    continue;
                }
                const cir::Entity& prior = file_.entity(prior_id);
                if (record.local_name_kind ==
                        cir::LocalNameComponentKind::Anonymous &&
                    prior.kind == cir::EntityKind::Record &&
                    prior.local_enclosing_function == function &&
                    prior.local_name_kind ==
                        cir::LocalNameComponentKind::Anonymous) {
                    ++anonymous_ordinal;
                }
                if (prior.kind == cir::EntityKind::Record &&
                    prior.local_enclosing_function == function &&
                    prior.local_source_name == record.local_source_name &&
                    prior.local_name_kind == record.local_name_kind) {
                    ++ordinal;
                }
            }
            record.local_name_ordinal = ordinal;
            record.local_component_ordinal =
                record.local_name_kind == cir::LocalNameComponentKind::Lambda
                    ? static_cast<uint32_t>(lambda_closure_counter_)
                    : (record.local_name_kind ==
                               cir::LocalNameComponentKind::Anonymous
                           ? anonymous_ordinal
                           : ordinal);
            const cir::Entity& enclosing = file_.entity(function);
            bool mergeable =
                enclosing.linkage == cir::LinkageKind::LinkOnceODR ||
                enclosing.decl_flags.is_inline ||
                (file_.template_specialization(function) &&
                 !enclosing.is_explicit_template_specialization);
            record.linkage = mergeable ? cir::LinkageKind::LinkOnceODR
                                       : cir::LinkageKind::Internal;
            record.abi_identity = cir::AbiIdentityKind::Local;
        }
    }

    cir::RecordFacts facts;
    facts.entity = entity;
    facts.type = file_.type_ref(type);
    facts.kind = kind;
    facts.is_incomplete = true;
    file_.set_record_facts(entity, std::move(facts));
    if (bind_tag) {
        bind_entity(tag,
                    cir::LookupNamespace::Tag,
                    entity,
                    type,
                    true,
                    false,
                    false,
                    {},
                    loc);
        if (lang_opts_.is_cxx_mode() && !tag.empty()) {
            bind_entity(tag,
                        cir::LookupNamespace::Ordinary,
                        entity,
                        type,
                        true,
                        false,
                        false,
                        {},
                        loc);
        }
    }
    return RecordDeclResult{entity, type, false, false};
}

cir::TypeId Session::declare_enum_tag(std::string_view tag_view,
                                      bool is_scoped,
                                      cir::TypeRef fixed_underlying,
                                      SrcLoc loc) {
    std::string tag(tag_view);
    if (tag.empty()) {
        report_error("expected enum tag", loc);
        return file_.unknown_type();
    }

    const cir::Binding* binding = lookup_tag_binding(tag, true);
    if (binding && !binding->entities.empty()) {
        cir::EntityId entity = binding->entities.back();
        if (!file_.valid(entity) || file_.entity(entity).kind != cir::EntityKind::Enum) {
            report_error("tag '" + tag + "' was previously declared as a different kind", loc);
            return file_.unknown_type();
        }
        cir::TypeId existing_type = file_.entity(entity).type;
        const auto* payload = file_.valid(existing_type)
            ? std::get_if<cir::EnumTypePayload>(&file_.type_payload(existing_type))
            : nullptr;
        if (payload && payload->is_scoped != is_scoped) {
            report_error("enum declaration scopedness does not match previous declaration",
                         loc);
            return file_.unknown_type();
        }
        if (payload && fixed_underlying.valid() &&
            payload->underlying_type.valid() &&
            !types_compatible(payload->underlying_type, fixed_underlying)) {
            report_error("enum underlying type does not match previous declaration",
                         loc);
            return file_.unknown_type();
        }
        if (existing_type.valid()) {
            return existing_type;
        }
    }

    return create_enum_tag(std::move(tag),
                           loc,
                           true,
                           false,
                           fixed_underlying,
                           is_scoped,
                           is_scoped || fixed_underlying.valid());
}

cir::TypeRef Session::select_enum_underlying(
    cir::TypeRef fixed_underlying,
    const std::vector<EnumEnumeratorInput>& enumerators) {
    if (fixed_underlying.valid()) {
        return fixed_underlying;
    }

    bool fits_int = true;
    bool fits_uint = true;
    bool any_negative = false;
    int64_t next = 0;
    for (const EnumEnumeratorInput& enumerator : enumerators) {
        int64_t value = enumerator.value.value_or(next);
        next = value + 1;
        if (value < 0) {
            any_negative = true;
            fits_uint = false;
        }
        if (value < -2147483648LL || value > 2147483647LL) {
            fits_int = false;
        }
        if (value > 4294967295LL) {
            fits_uint = false;
        }
    }
    if (any_negative) {

        return type_ref(file_.builtin_type(fits_int
                                               ? cir::BuiltinTypeKind::Int
                                               : cir::BuiltinTypeKind::Long));
    }

    return type_ref(file_.builtin_type(fits_uint
                                           ? cir::BuiltinTypeKind::UInt
                                           : cir::BuiltinTypeKind::ULong));
}

cir::TypeId Session::create_enum_tag(std::string tag,
                                     SrcLoc loc,
                                     bool bind_tag,
                                     bool is_definition,
                                     cir::TypeRef underlying,
                                     bool is_scoped,
                                     bool has_fixed_underlying_type) {
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Enum, tag, {}, {}, loc);
    if (!underlying.valid()) {
        underlying = type_ref(builder_.int_type());
    }
    bool is_incomplete = !is_definition &&
                         !(lang_opts_.is_cxx_mode() &&
                           has_fixed_underlying_type);
    cir::TypeId type = builder_.enum_type(entity,
                                          enum_type_spelling(tag, is_scoped),
                                          underlying,
                                          is_scoped,
                                          is_incomplete,
                                          has_fixed_underlying_type);
    file_.entity_mut(entity).type = type;
    file_.entity_mut(entity).is_definition = is_definition;
    file_.entity_mut(entity).semantic_context =
        file_.create_decl_context(cir::DeclContextKind::Enum,
                                  current_decl_context(),
                                  entity,
                                  loc);

    if (bind_tag) {
        bind_entity(tag,
                    cir::LookupNamespace::Tag,
                    entity,
                    type,
                    true,
                    false,
                    is_definition,
                    {},
                    loc);
        if (lang_opts_.is_cxx_mode() && !tag.empty()) {
            bind_entity(tag,
                        cir::LookupNamespace::Ordinary,
                        entity,
                        type,
                        true,
                        false,
                        is_definition,
                        {},
                        loc);
        }
    }
    return type;
}

cir::EntityId Session::declare_enumerator(std::string_view name,
                                          int64_t value,
                                          cir::TypeId provisional_type,
                                          SrcLoc loc) {
    if (name.empty()) {
        return {};
    }

    cir::TypeId type;
    if (provisional_type.valid()) {
        type = provisional_type;
    } else if (value >= -2147483648LL && value <= 2147483647LL) {
        type = builder_.int_type();
    } else if (value >= 0 && value <= 4294967295LL) {
        type = file_.builtin_type(cir::BuiltinTypeKind::UInt);
    } else {
        type = file_.builtin_type(cir::BuiltinTypeKind::Long);
    }
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Enumerator,
                                               name,
                                               type,
                                               {},
                                               loc,
                                               cir::StorageDuration::None);
    file_.entity_mut(entity).has_constant_value = true;
    cir::IntegerTypeShape shape = cir::integer_shape_for_type(file_, type);
    file_.entity_mut(entity).constant_integer_value =
        cir::IntegerValue::from_signed(value, 64).cast(
            shape.bit_width, shape.is_unsigned);
    bind_entity(name,
                cir::LookupNamespace::Ordinary,
                entity,
                type,
                false,
                false,
                true,
                {},
                loc);
    return entity;
}

EnumDeclResult Session::define_enum(std::string_view tag_view,
                                    std::vector<EnumEnumeratorInput> enumerators,
                                    SrcLoc loc,
                                    cir::TypeRef fixed_underlying,
                                    bool is_packed,
                                    bool is_scoped) {
    const bool declaration_has_fixed_underlying_type =
        is_scoped || fixed_underlying.valid();
    if (is_packed && !fixed_underlying.valid() && !enumerators.empty()) {

        int64_t min_value = 0;
        int64_t max_value = 0;
        for (const EnumEnumeratorInput& input : enumerators) {
            int64_t v = input.value.value_or(0);
            min_value = std::min(min_value, v);
            max_value = std::max(max_value, v);
        }
        cir::BuiltinTypeKind kind;
        if (min_value >= 0) {
            kind = max_value <= 255 ? cir::BuiltinTypeKind::UChar
                 : max_value <= 65535 ? cir::BuiltinTypeKind::UShort
                                      : cir::BuiltinTypeKind::UInt;
        } else {
            kind = (min_value >= -128 && max_value <= 127)
                     ? cir::BuiltinTypeKind::SChar
                 : (min_value >= -32768 && max_value <= 32767)
                     ? cir::BuiltinTypeKind::Short
                     : cir::BuiltinTypeKind::Int;
        }
        fixed_underlying = file_.type_ref(file_.builtin_type(kind));
    }
    std::string tag(tag_view);
    bool anonymous = tag.empty();
    if (anonymous) {
        ++anonymous_record_counter_;
        tag = "<anonymous-enum." + std::to_string(anonymous_record_counter_) + ">";
    }

    cir::EntityId enum_entity{};
    cir::TypeId enum_type{};
    bool has_error = false;

    if (fixed_underlying.valid()) {
        for (const EnumEnumeratorInput& enumerator : enumerators) {
            if (enumerator.value.has_value() &&
                !enum_value_fits_underlying(file_,
                                            fixed_underlying,
                                            *enumerator.value)) {
                report_error(
                    "enumerator value is not representable in the fixed underlying type",
                    enumerator.loc);
                has_error = true;
            }
        }
    }

    const cir::Binding* binding = anonymous ? nullptr : lookup_tag_binding(tag, false);
    bool reused_declaration = false;
    if (binding && !binding->entities.empty()) {
        enum_entity = binding->entities.back();
        if (!file_.valid(enum_entity) || file_.entity(enum_entity).kind != cir::EntityKind::Enum) {
            report_error("tag '" + tag + "' was previously declared as a different kind", loc);
            has_error = true;
            enum_type = file_.unknown_type();
        } else {
            reused_declaration = true;
            if (file_.entity(enum_entity).is_definition) {
                report_error("redefinition of enum '" + tag + "'", loc);
                has_error = true;
            }
            enum_type = file_.entity(enum_entity).type;
            const auto* previous_payload =
                std::get_if<cir::EnumTypePayload>(
                    &file_.type_payload(enum_type));
            const bool has_fixed_underlying_type =
                declaration_has_fixed_underlying_type ||
                (previous_payload &&
                 previous_payload->has_fixed_underlying_type);
            cir::TypeRef underlying = select_enum_underlying(fixed_underlying, enumerators);
            cir::TypeId complete_type =
                builder_.enum_type(enum_entity,
                                   enum_type_spelling(tag, is_scoped),
                                   underlying,
                                   is_scoped,
                                   false,
                                   has_fixed_underlying_type);
            file_.entity_mut(enum_entity).type = complete_type;
            enum_type = complete_type;
            file_.entity_mut(enum_entity).is_definition = true;
        }
    } else {
        cir::TypeRef underlying = select_enum_underlying(fixed_underlying, enumerators);
        enum_type = create_enum_tag(tag,
                                    loc,
                                    !anonymous,
                                    true,
                                    underlying,
                                    is_scoped,
                                    declaration_has_fixed_underlying_type);
        const auto* enum_payload =
            std::get_if<cir::EnumTypePayload>(&file_.type_payload(enum_type));
        enum_entity = enum_payload ? enum_payload->entity : cir::EntityId{};
    }

    if (reused_declaration && !anonymous && enum_entity.valid() &&
        file_.valid(enum_entity)) {
        bind_entity(tag,
                    cir::LookupNamespace::Tag,
                    enum_entity,
                    enum_type,
                    true,
                    false,
                    true,
                    {},
                    loc);
        if (lang_opts_.is_cxx_mode()) {
            bind_entity(tag,
                        cir::LookupNamespace::Ordinary,
                        enum_entity,
                        enum_type,
                        true,
                        false,
                        true,
                        {},
                        loc);
        }
    }

    const bool fixed_enumerator_type =
        lang_opts_.is_cxx_mode() || fixed_underlying.valid();
    cir::TypeId c_underlying_type = builder_.int_type();
    if (!fixed_enumerator_type) {
        if (const auto* payload = std::get_if<cir::EnumTypePayload>(
                &file_.type_payload(enum_type));
            payload && payload->underlying_type.valid()) {
            c_underlying_type =
                file_.resolved_type(payload->underlying_type.type);
        }
    }
    int64_t next_value = 0;
    for (const EnumEnumeratorInput& enumerator : enumerators) {
        int64_t value = enumerator.value.value_or(next_value);
        next_value = value + 1;
        cir::TypeId enumerator_type =
            fixed_enumerator_type
                ? enum_type
                : ((value >= -2147483648LL && value <= 2147483647LL)
                       ? builder_.int_type()
                       : c_underlying_type);
        if (enumerator.name.empty()) {
            has_error = true;
            continue;
        }
        cir::EntityId entity_id = enumerator.entity;
        if (entity_id.valid() && file_.valid(entity_id)) {

            cir::Entity& entity = file_.entity_mut(entity_id);
            entity.parent = enum_entity;
            entity.type = enumerator_type;
            entity.has_constant_value = true;
            cir::IntegerTypeShape shape =
                cir::integer_shape_for_type(file_, enumerator_type);
            entity.constant_integer_value =
                cir::IntegerValue::from_signed(value, 64).cast(
                    shape.bit_width, shape.is_unsigned);
        } else {
            entity_id = builder_.add_entity(cir::EntityKind::Enumerator,
                                            enumerator.name,
                                            enumerator_type,
                                            enum_entity,
                                            enumerator.loc,
                                            cir::StorageDuration::None);
            file_.entity_mut(entity_id).has_constant_value = true;
            cir::IntegerTypeShape shape =
                cir::integer_shape_for_type(file_, enumerator_type);
            file_.entity_mut(entity_id).constant_integer_value =
                cir::IntegerValue::from_signed(value, 64).cast(
                    shape.bit_width, shape.is_unsigned);
            cir::DeclContextId enum_context =
                enum_entity.valid() && file_.valid(enum_entity)
                ? file_.entity(enum_entity).semantic_context
                : cir::DeclContextId{};
            bool bind_in_enum = lang_opts_.is_cxx_mode() && enum_context.valid();
            if (bind_in_enum) {
                enter_existing_context(enum_context, ScopeFlags::EnumScope);
            }
            bind_entity(enumerator.name,
                        cir::LookupNamespace::Ordinary,
                        entity_id,
                        enumerator_type,
                        false,
                        false,
                        true,
                        {},
                        enumerator.loc);
            if (bind_in_enum) {
                leave_scope();
            }
        }
        if (lang_opts_.is_cxx_mode() && !is_scoped) {
            bind_entity(enumerator.name,
                        cir::LookupNamespace::Ordinary,
                        entity_id,
                        enumerator_type,
                        false,
                        false,
                        true,
                        {},
                        enumerator.loc);
        }
    }

    return EnumDeclResult{enum_entity, enum_type, true, has_error};
}

std::string Session::anonymous_record_name(cir::RecordKind kind) {
    ++anonymous_record_counter_;
    return "<anonymous-" + std::string(cir::record_kind_name(kind)) + "." +
           std::to_string(anonymous_record_counter_) + ">";
}

std::optional<size_t> Session::size_of_type(cir::TypeId type, SrcLoc loc) {
    auto size_align = size_align_of_type(type, loc);
    return size_align ? std::optional<size_t>(size_align->first) : std::nullopt;
}

std::optional<size_t> Session::align_of_type(cir::TypeId type, SrcLoc loc) {
    auto size_align = size_align_of_type(type, loc);
    return size_align ? std::optional<size_t>(size_align->second) : std::nullopt;
}

std::optional<std::pair<size_t, size_t>> Session::size_align_of_type(cir::TypeId type_id,
                                                                     SrcLoc loc) {
    if (!file_.valid(type_id)) {
        report_error("invalid type in record layout", loc);
        return std::nullopt;
    }

    cir::TypeId completeness_type = file_.resolved_type(type_id);
    while (file_.valid(completeness_type) &&
           file_.type(completeness_type).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(completeness_type));
        completeness_type = array
            ? file_.resolved_type(array->element_type.type)
            : cir::TypeId{};
    }
    (void)require_complete_class_type(
        completeness_type, loc, cir::InstantiationDemandKind::CompleteClass);
    auto size_align = cir::size_align_of_type(file_, type_id);
    if (size_align) {
        return std::pair<size_t, size_t>{size_align->size_bytes,
                                         size_align->alignment_bytes};
    }
    if (is_dependent_type(type_id)) {

        return std::pair<size_t, size_t>{8, 8};
    }
    report_error("cannot lay out unsupported field type '" + file_.format_type(type_id) + "'", loc);
    return std::nullopt;
}
Session::RecordLayoutInfo Session::compute_record_layout(
    cir::RecordKind kind,
    bool is_packed,
    size_t requested_alignment,
    size_t pack_alignment,
    const std::vector<cir::RecordFieldFact>& input_fields,
    SrcLoc loc) {
    RecordLayoutInfo result;
    result.fields = input_fields;
    result.alignment = 1;
    if (result.fields.empty()) {
        result.alignment = std::max<size_t>(1, requested_alignment);

        result.size_bits =
            lang_opts_.is_cxx_mode() ? result.alignment * 8 : 0;
        return result;
    }

    const bool is_union = kind == cir::RecordKind::Union;
    const auto& policy = file_.abi_policy();
    const bool use_msvc_bitfields = policy.bitfield_abi == BitfieldABI::MSVC;
    const bool tight_packed_bitfields = !use_msvc_bitfields &&
                                        (is_packed || pack_alignment == 1);

    const bool msb_first_bitfields =
        !use_msvc_bitfields && policy.endianness == EndiannessKind::Big;
    auto to_target_bit_offset = [&](cir::RecordFieldFact& field) {
        if (field.bit_width_is_dependent) {
            return;
        }
        if (msb_first_bitfields &&
            field.storage_size >= field.bit_offset + field.bit_width) {
            field.bit_offset =
                field.storage_size - field.bit_offset - field.bit_width;
        }
    };

    auto field_size_align = [&](const cir::RecordFieldFact& field)
        -> std::pair<size_t, size_t> {
        if (const cir::ArrayTypePayload* array =
                incomplete_array_payload(file_, field.type.type)) {
            auto element_size_align = size_align_of_type(array->element_type.type, loc);
            if (!element_size_align) {
                result.has_error = true;
                return {0, 1};
            }
            size_t field_align = field.storage_alignment_override > 0
                ? field.storage_alignment_override
                : (field.forced_alignment > 0
                       ? field.forced_alignment
                       : element_size_align->second);
            field_align = std::max<size_t>(1, field_align);
            if (field.storage_alignment_override == 0 &&
                field.forced_alignment == 0 &&
                !is_packed &&
                pack_alignment > 0 &&
                field_align > pack_alignment) {
                field_align = pack_alignment;
            }
            if (is_packed &&
                field.storage_alignment_override == 0 &&
                field.forced_alignment == 0) {
                field_align = 1;
            }
            return {0, field_align};
        }
        auto size_align = size_align_of_type(field.type.type, loc);
        if (!size_align) {
            result.has_error = true;
            return {1, 1};
        }
        size_t field_size = field.storage_size_override > 0
            ? field.storage_size_override
            : size_align->first;
        size_t field_align = field.storage_alignment_override > 0
            ? field.storage_alignment_override
            : (field.forced_alignment > 0 ? field.forced_alignment : size_align->second);

        bool zero_sized_member =
            size_align->first == 0 && field.storage_size_override == 0;
        if (!zero_sized_member) {
            field_size = std::max<size_t>(1, field_size);
        }
        field_align = std::max<size_t>(1, field_align);
        if (field.storage_alignment_override == 0 &&
            field.forced_alignment == 0 &&
            !is_packed &&
            pack_alignment > 0 &&
            field_align > pack_alignment) {
            field_align = pack_alignment;
        }
        if (is_packed &&
            field.storage_alignment_override == 0 &&
            field.forced_alignment == 0) {
            field_align = 1;
        }
        return {field_size, field_align};
    };

    const bool supports_zero_size_subobjects =
        policy.cxx_abi == CxxAbiKind::Itanium;
    auto classify_subobject_size = [&](cir::RecordFieldFact& field) {
        field.is_potentially_overlapping =
            field.is_base_subobject || field.is_no_unique_address;
        field.subobject_size = cir::SubobjectSizeKind::NonZero;
        if (!supports_zero_size_subobjects ||
            !field.is_potentially_overlapping || field.is_bitfield) {
            return;
        }
        cir::TypeId type = file_.resolved_type(field.type.type);
        if (is_dependent_type(type)) {
            field.subobject_size = cir::SubobjectSizeKind::Dependent;
            return;
        }
        if (!file_.valid(type) ||
            file_.type(type).kind != cir::TypeKind::Record) {
            return;
        }
        const cir::RecordFacts* record = file_.record_facts_for_type(type);
        if (!record || record->is_empty == cir::ClassPropertyState::Unavailable ||
            record->is_empty == cir::ClassPropertyState::Dependent) {
            field.subobject_size = cir::SubobjectSizeKind::Dependent;
        } else if (record->is_empty == cir::ClassPropertyState::True) {
            field.subobject_size = cir::SubobjectSizeKind::Zero;
        }
    };
    for (cir::RecordFieldFact& field : result.fields) {
        classify_subobject_size(field);
    }

    using FootprintEntry = std::pair<cir::TypeId, size_t>;
    std::function<void(cir::TypeId, size_t, bool,
                       std::vector<FootprintEntry>&)>
        append_record_footprint;
    append_record_footprint = [&](cir::TypeId input,
                                  size_t base_offset,
                                  bool include_virtual_storage,
                                  std::vector<FootprintEntry>& footprint) {
        cir::TypeId type = file_.resolved_type(input);
        if (!file_.valid(type)) {
            return;
        }
        if (file_.type(type).kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(type));
            if (!array || !array->size.has_value()) {
                return;
            }
            auto element_layout = cir::size_align_of_type(
                file_, array->element_type.type);
            if (!element_layout) {
                return;
            }
            for (size_t index = 0; index < *array->size; ++index) {
                append_record_footprint(
                    array->element_type.type,
                    base_offset + index * element_layout->size_bytes,
                    include_virtual_storage,
                    footprint);
            }
            return;
        }
        if (file_.type(type).kind != cir::TypeKind::Record) {
            return;
        }
        footprint.emplace_back(type, base_offset);
        const cir::RecordFacts* record = file_.record_facts_for_type(type);
        if (!record || record->is_incomplete) {
            return;
        }
        for (const cir::RecordFieldFact& nested : record->fields) {
            if (nested.is_bitfield || nested.is_flexible_array_member ||
                (nested.is_virtual_base_storage &&
                 !include_virtual_storage)) {
                continue;
            }
            append_record_footprint(nested.type.type,
                                    base_offset + nested.offset,
                                    !nested.is_base_subobject,
                                    footprint);
        }
    };

    auto is_flexible_array_tail = [&](size_t index, const cir::RecordFieldFact& field) {
        return index + 1 == result.fields.size() && field.is_flexible_array_member;
    };

    if (is_union) {
        size_t max_size = 0;
        size_t max_align = 1;
        for (size_t index = 0; index < result.fields.size(); ++index) {
            cir::RecordFieldFact& field = result.fields[index];
            auto [field_size, field_align] = field_size_align(field);
            field.offset = 0;
            if (field.is_bitfield) {
                uint32_t type_storage_bits =
                    static_cast<uint32_t>(field_size * 8);
                uint32_t layout_bit_width =
                    field.bit_width_is_dependent
                        ? std::max<uint32_t>(1, type_storage_bits)
                        : field.bit_width;
                uint32_t storage_bits = bitfield_allocation_storage_bits(
                    type_storage_bits, layout_bit_width);
                field.bit_offset = 0;
                field.storage_size = storage_bits;
                field_size = use_msvc_bitfields
                    ? field_size
                    : std::max<size_t>(1, (layout_bit_width + 7) / 8);
            } else {
                field.bit_offset = 0;
                field.bit_width = 0;
                field.storage_size = 0;
            }
            if (field.subobject_size != cir::SubobjectSizeKind::Zero) {
                max_size = std::max(max_size, field_size);
            }
            max_align = std::max(max_align, field_align);
            if (is_flexible_array_tail(index, field)) {
                result.has_flexible_array_member = true;
                field.is_flexible_array_member = true;
            }
        }
        size_t final_align = is_packed ? 1 : max_align;
        if (requested_alignment > final_align) {
            final_align = requested_alignment;
        }
        size_t total_bytes = align_to(std::max<size_t>(1, max_size), final_align);
        result.size_bits = total_bytes * 8;
        result.alignment = std::max<size_t>(1, final_align);
        return result;
    }

    size_t current_bit = 0;
    size_t current_byte = 0;
    size_t object_extent = 0;
    size_t max_align = 1;
    uint32_t current_msvc_storage_bits = 0;
    uint32_t current_msvc_bit_offset = 0;
    size_t current_msvc_storage_byte = 0;
    std::vector<FootprintEntry> occupied_record_subobjects;

    auto footprint_conflicts = [&](const std::vector<FootprintEntry>& candidate) {
        for (const FootprintEntry& entry : candidate) {
            for (const FootprintEntry& occupied : occupied_record_subobjects) {
                if (entry.first == occupied.first &&
                    entry.second == occupied.second) {
                    return true;
                }
            }
        }
        return false;
    };

    for (size_t index = 0; index < result.fields.size(); ++index) {
        cir::RecordFieldFact& field = result.fields[index];
        auto [field_size, field_align] = field_size_align(field);
        if (is_flexible_array_tail(index, field)) {
            result.has_flexible_array_member = true;
            field.is_flexible_array_member = true;
            field_size = 0;
        }
        max_align = std::max(max_align, field_align);

        if (field.is_bitfield) {
            uint32_t type_storage_bits =
                static_cast<uint32_t>(field_size * 8);
            uint32_t layout_bit_width =
                field.bit_width_is_dependent
                    ? std::max<uint32_t>(1, type_storage_bits)
                    : field.bit_width;
            uint32_t storage_bits = bitfield_allocation_storage_bits(
                type_storage_bits, layout_bit_width);
            size_t unit_align = std::max<size_t>(1, field_align);
            if (layout_bit_width == 0) {
                if (use_msvc_bitfields && current_msvc_storage_bits > 0) {
                    current_byte =
                        current_msvc_storage_byte + (current_msvc_storage_bits / 8);
                    current_msvc_storage_bits = 0;
                    current_msvc_bit_offset = 0;
                }
                current_byte = align_to(std::max(current_byte, (current_bit + 7) / 8),
                                        unit_align);
                current_bit = current_byte * 8;
                field.offset = current_bit / 8;
                field.bit_offset = 0;
                field.storage_size = storage_bits;
                current_bit = align_to(current_bit, unit_align * 8);
                current_byte = current_bit / 8;
                continue;
            }

            if (use_msvc_bitfields) {
                bool fits = current_msvc_storage_bits == storage_bits &&
                            current_msvc_bit_offset + layout_bit_width <=
                                storage_bits;
                if (!fits) {
                    if (current_msvc_storage_bits > 0) {
                        current_byte =
                            current_msvc_storage_byte + (current_msvc_storage_bits / 8);
                    } else {
                        current_byte = std::max(current_byte, (current_bit + 7) / 8);
                    }
                    current_byte = align_to(current_byte, unit_align);
                    current_msvc_storage_byte = current_byte;
                    current_msvc_storage_bits = storage_bits;
                    current_msvc_bit_offset = 0;
                }
                field.offset = current_msvc_storage_byte;
                field.bit_offset = current_msvc_bit_offset;
                field.storage_size = storage_bits;
                current_msvc_bit_offset += layout_bit_width;
                current_bit = (current_msvc_storage_byte * 8) + current_msvc_bit_offset;
                continue;
            }

            if (tight_packed_bitfields) {
                field.offset = current_bit / 8;
                field.bit_offset = static_cast<uint32_t>(current_bit % 8);
                field.storage_size =
                    static_cast<uint32_t>(
                        ((field.bit_offset + layout_bit_width + 7) / 8) * 8);
                current_bit += layout_bit_width;
                current_byte = std::max(current_byte, (current_bit + 7) / 8);
                to_target_bit_offset(field);
                continue;
            }

            if (layout_bit_width > type_storage_bits) {
                current_bit = align_to(current_bit, unit_align * 8);
                field.offset = current_bit / 8;
                field.bit_offset = 0;
                field.storage_size = storage_bits;
                current_bit += layout_bit_width;
                current_byte = std::max(
                    current_byte,
                    field.offset + static_cast<size_t>(storage_bits / 8));
                if (use_msvc_bitfields) {
                    current_msvc_storage_bits = 0;
                    current_msvc_bit_offset = 0;
                }
                to_target_bit_offset(field);
                continue;
            }

            size_t unit_align_bits = std::max<size_t>(8, unit_align * 8);
            size_t unit_start = (current_bit / unit_align_bits) * unit_align_bits;
            size_t unit_end = unit_start + storage_bits;
            if (current_bit + layout_bit_width > unit_end) {
                current_bit = align_to(unit_end, unit_align_bits);
                unit_start = current_bit;
                unit_end = unit_start + storage_bits;
            }
            size_t storage_byte_offset = (current_bit / storage_bits) * (storage_bits / 8);
            field.offset = storage_byte_offset;
            field.bit_offset = static_cast<uint32_t>(current_bit % storage_bits);
            field.storage_size = storage_bits;
            current_bit += layout_bit_width;

            current_byte = std::max(current_byte, (current_bit + 7) / 8);
            to_target_bit_offset(field);
            continue;
        }

        if (use_msvc_bitfields && current_msvc_storage_bits > 0) {
            current_byte = current_msvc_storage_byte + (current_msvc_storage_bits / 8);
            current_msvc_storage_bits = 0;
            current_msvc_bit_offset = 0;
        }
        const size_t ordinary_cursor =
            std::max(current_byte, (current_bit + 7) / 8);
        const bool is_zero =
            field.subobject_size == cir::SubobjectSizeKind::Zero;
        size_t candidate = is_zero ? 0 : align_to(ordinary_cursor, field_align);
        bool tried_virtual_zero_at_origin =
            is_zero && field.is_virtual_base_storage;
        std::vector<FootprintEntry> candidate_footprint;
        while (true) {
            candidate_footprint.clear();
            append_record_footprint(field.type.type, candidate,
                                    !field.is_base_subobject,
                                    candidate_footprint);
            if (!footprint_conflicts(candidate_footprint)) {
                break;
            }
            if (tried_virtual_zero_at_origin) {
                candidate = align_to(ordinary_cursor, field_align);
                tried_virtual_zero_at_origin = false;
            } else {
                candidate += field_align;
            }
        }
        field.offset = candidate;
        field.bit_offset = 0;
        field.bit_width = 0;
        field.storage_size = 0;
        occupied_record_subobjects.insert(occupied_record_subobjects.end(),
                                          candidate_footprint.begin(),
                                          candidate_footprint.end());
        if (is_zero) {
            object_extent = std::max(object_extent, candidate + 1);
            continue;
        }
        current_byte = candidate + field_size;
        current_bit = current_byte * 8;
        object_extent = std::max(object_extent, current_byte);
    }

    if (use_msvc_bitfields && current_msvc_storage_bits > 0) {
        current_byte = current_msvc_storage_byte + (current_msvc_storage_bits / 8);
    } else {
        current_byte = std::max(current_byte, (current_bit + 7) / 8);
    }
    current_byte = std::max(current_byte, object_extent);
    size_t final_align = is_packed ? 1 : max_align;
    if (requested_alignment > final_align) {
        final_align = requested_alignment;
    }

    if (!lang_opts_.is_cxx_mode() && current_byte == 0) {
        result.size_bits = 0;
        result.alignment = std::max<size_t>(1, final_align);
        return result;
    }
    size_t size_bytes = align_to(std::max<size_t>(1, current_byte), final_align);
    result.size_bits = std::max<size_t>(8, size_bytes * 8);
    result.alignment = std::max<size_t>(1, final_align);
    return result;
}

const cir::RecordFieldFact* Session::lookup_field(cir::TypeId record_type,
                                                  std::string_view member_name) const {
    const cir::RecordFacts* facts = file_.record_facts_for_type(record_type);
    if (!facts || facts->is_incomplete) {
        return nullptr;
    }
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (!field.name.valid()) {
            continue;
        }
        if (file_.name(field.name) == member_name) {
            return &field;
        }
    }
    return nullptr;
}

const cir::RecordStaticDataMemberFact* Session::static_data_member_fact(
    cir::EntityId entity) const {
    if (!entity.valid() || !file_.valid(entity)) {
        return nullptr;
    }
    cir::EntityId owner = file_.entity(entity).parent;
    const cir::RecordFacts* facts = owner.valid() && file_.valid(owner)
        ? file_.record_facts(owner)
        : nullptr;
    if (!facts) {
        return nullptr;
    }
    for (const cir::RecordStaticDataMemberFact& member :
         facts->static_data_members) {
        if (member.entity == entity) {
            return &member;
        }
    }
    return nullptr;
}

Session::FieldPathLookupResult Session::lookup_field_path(cir::TypeId record_type,
                                                          std::string_view member_name) const {
    FieldPathLookupResult result;
    if (const cir::RecordFieldFact* direct = lookup_field(record_type, member_name)) {
        result.entities.push_back(direct->entity);
        result.type = direct->type.type;
        result.found = true;
        return result;
    }

    std::vector<std::vector<cir::EntityId>> matches;
    std::vector<cir::TypeId> match_types;
    auto search_record = [&](auto&& self,
                             cir::TypeId current_type,
                             std::vector<cir::EntityId>& path) -> void {
        const cir::RecordFacts* facts = file_.record_facts_for_type(current_type);
        if (!facts || facts->is_incomplete) {
            return;
        }

        for (const cir::RecordFieldFact& field : facts->fields) {
            if (field.name.valid() && file_.name(field.name) == member_name) {
                path.push_back(field.entity);
                matches.push_back(path);
                match_types.push_back(field.type.type);
                path.pop_back();
                continue;
            }
            if (!is_anonymous_record_member(file_, field) ||
                field.is_virtual_base_storage) {

                continue;
            }
            path.push_back(field.entity);
            self(self, field.type.type, path);
            path.pop_back();
        }
    };

    const cir::RecordFacts* facts = file_.record_facts_for_type(record_type);
    if (!facts || facts->is_incomplete) {
        return result;
    }
    std::vector<cir::EntityId> path;
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (!is_anonymous_record_member(file_, field)) {
            continue;
        }
        path.push_back(field.entity);
        search_record(search_record, field.type.type, path);
        path.pop_back();
    }

    if (matches.empty()) {
        return result;
    }
    result.found = true;
    if (matches.size() > 1) {
        result.ambiguous = true;
        return result;
    }
    result.entities = std::move(matches.front());
    result.type = match_types.front();
    return result;
}

cir::TypeId Session::structor_impl_type(cir::TypeId with_this_type) {

    cir::TypeId resolved = file_.resolved_type(with_this_type);
    const auto* payload =
        std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved));
    if (!payload) {
        return with_this_type;
    }

    cir::TypeRef return_type = payload->return_type;
    std::vector<cir::TypeRef> parameters = payload->parameters;
    bool is_variadic = payload->is_variadic;
    parameters.push_back(file_.type_ref(builder_.int_type()));
    parameters.push_back(file_.type_ref(builder_.pointer_type(
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void)))));
    return function_type(return_type, parameters, is_variadic, true);
}

cir::TypeId Session::member_function_type_with_this(cir::TypeId record_type,
                                                    cir::TypeId declared_type) {
    cir::TypeId resolved = file_.resolved_type(declared_type);
    const auto* payload =
        std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved));
    if (!payload) {
        return declared_type;
    }

    cir::TypeRef return_type = payload->return_type;
    std::vector<cir::TypeRef> declared_parameters = payload->parameters;
    bool is_variadic = payload->is_variadic;
    bool member_is_const = payload->member_is_const;
    bool member_is_volatile = payload->member_is_volatile;
    cir::FunctionRefQualifierKind member_ref_qualifier =
        payload->member_ref_qualifier;
    cir::FunctionExceptionSpec exception_spec = payload->exception_spec;
    payload = nullptr;

    cir::TypeRef this_pointee = file_.type_ref(record_type);
    if (member_is_const) {
        this_pointee.qualifiers |= cir::QualConst;
    }
    if (member_is_volatile) {
        this_pointee.qualifiers |= cir::QualVolatile;
    }
    std::vector<cir::TypeRef> parameters;
    parameters.reserve(declared_parameters.size() + 1);
    parameters.push_back(file_.type_ref(pointer_type(this_pointee)));
    parameters.insert(parameters.end(),
                      declared_parameters.begin(),
                      declared_parameters.end());
    return function_type(return_type, parameters, is_variadic, true,
                         member_is_const, std::move(exception_spec),
                         {}, member_ref_qualifier, member_is_volatile);
}

bool Session::validate_static_member_function_type(cir::TypeId declared_type,
                                                   SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(declared_type);
    const auto* function = file_.valid(resolved)
        ? std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved))
        : nullptr;
    if (!function) {
        return true;
    }

    bool valid = true;
    auto reject_qualifier = [&](std::string_view qualifier) {
        report_error("static member function cannot have '" +
                         std::string(qualifier) + "' qualifier",
                     loc);
        valid = false;
    };
    if (function->member_is_const) {
        reject_qualifier("const");
    }
    if (function->member_is_volatile) {
        reject_qualifier("volatile");
    }
    if (function->member_ref_qualifier ==
        cir::FunctionRefQualifierKind::LValue) {
        reject_qualifier("&");
    } else if (function->member_ref_qualifier ==
               cir::FunctionRefQualifierKind::RValue) {
        reject_qualifier("&&");
    }
    return valid;
}

cir::EntityId Session::create_member_template_specialization(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    cir::TypeId declared_type,
    SrcLoc loc,
    const DeclFlags* explicit_specialization_flags,
    const TemplateArgumentBindings* exact_bindings,
    bool defer_inherited_constructor_definition) {
    if (!info.entity.valid() || !file_.valid(info.entity) ||
        !declared_type.valid()) {
        return {};
    }

    const cir::Entity primary = file_.entity(info.entity);
    if (primary.kind != cir::EntityKind::Method &&
        primary.kind != cir::EntityKind::Constructor &&
        primary.kind != cir::EntityKind::Destructor) {
        return {};
    }
    cir::EntityId record_entity = primary.parent;
    if (!record_entity.valid() || !file_.valid(record_entity)) {
        return {};
    }
    const cir::RecordMethodFact* primary_fact =
        file_.method_fact(info.entity);
    const cir::RecordFacts* existing_facts =
        file_.record_facts(record_entity);
    if (!primary_fact || !existing_facts) {
        return {};
    }

    cir::TypeId entity_type = primary_fact->is_static
        ? declared_type
        : member_function_type_with_this(file_.entity(record_entity).type,
                                         declared_type);
    if ((primary.kind == cir::EntityKind::Constructor ||
         primary.kind == cir::EntityKind::Destructor) &&
        !existing_facts->virtual_bases.empty()) {
        entity_type = structor_impl_type(entity_type);
    }

    cir::DeclSemanticFlags specialization_flags =
        explicit_specialization_flags
            ? explicit_specialization_flags->to_cir()
            : primary.decl_flags;
    if (!explicit_specialization_flags) {
        specialization_flags.is_consteval =
            specialization_flags.is_consteval ||
            consteval_only_function_type_immediately_escalates(
                declared_type,
                specialization_flags.is_constexpr,
                primary.kind,
                /*instantiated_templated_entity=*/true);
    }

    std::string display = template_display_name(info, arguments);
    cir::EntityId specialization =
        builder_.add_entity(primary.kind,
                            display,
                            entity_type,
                            record_entity,
                            loc.isInvalid() ? primary.loc : loc,
                            cir::StorageDuration::None,
                            cir::MemorySpace::Default,
                            specialization_flags);
    cir::Entity& entity = file_.entity_mut(specialization);
    entity.is_definition = false;
    entity.is_static_member_function = primary_fact->is_static;
    entity.linkage = cir::LinkageKind::External;
    entity.lexical_context = primary.lexical_context;
    entity.semantic_context = primary.semantic_context;
    entity.attr_facts = primary.attr_facts;
    if (explicit_specialization_flags) {
        apply_attributes(specialization,
                         AttributeTarget::Function,
                         explicit_specialization_flags->attrs,
                         loc);
    }

    cir::RecordFacts facts = *existing_facts;
    cir::RecordMethodFact fact = *primary_fact;
    fact.entity = specialization;
    fact.type = file_.type_ref(declared_type);
    fact.is_consteval = specialization_flags.is_consteval;
    if (explicit_specialization_flags) {
        fact.is_function_template = false;
        fact.is_constexpr = explicit_specialization_flags->is_constexpr;
        fact.is_consteval = explicit_specialization_flags->is_consteval;
        fact.constraint_satisfaction =
            cir::ConstraintSatisfactionKind::Unconstrained;
        fact.associated_constraint_fingerprint = 0;
        fact.more_constrained_than.clear();
        fact.attributes = explicit_specialization_flags->attrs.attrs;
    }
    facts.methods.push_back(std::move(fact));
    file_.set_record_facts(record_entity, std::move(facts));

    remember_template_specialization(specialization,
                                     info,
                                     arguments,
                                     loc,
                                     0,
                                     nullptr,
                                     nullptr,
                                     exact_bindings);
    inherit_function_template_default_arguments(specialization, info);

    if (!defer_inherited_constructor_definition &&
        !define_inherited_constructor_template_specialization(
            specialization, loc)) {
        return {};
    }
    return specialization;
}

bool Session::define_inherited_constructor_template_specialization(
    cir::EntityId specialization,
    SrcLoc loc) {
    if (!specialization.valid() || !file_.valid(specialization)) {
        return false;
    }
    if (file_.entity(specialization).is_definition) {
        return true;
    }
    const cir::RecordMethodFact* specialization_fact =
        file_.method_fact(specialization);
    if (!specialization_fact ||
        !specialization_fact->inherited_constructor ||
        specialization_fact->is_deleted ||
        specialization_fact->inherited_constructor->routes.empty()) {
        return true;
    }

    cir::RecordMethodFact inherited = *specialization_fact;
    cir::EntityId record_entity = file_.entity(specialization).parent;
    const cir::RecordFacts* completed_owner =
        file_.record_facts(record_entity);
    const cir::InheritedConstructorRouteFact& route =
        inherited.inherited_constructor->routes.front();
    cir::TypeId target_type{};
    std::string target_name;
    if (completed_owner) {
        for (const cir::RecordBaseFact& base : completed_owner->bases) {
            if (base.record_entity == route.nominated_direct_base) {
                target_type = base.type.type;
                target_name = base.name.valid()
                    ? std::string(file_.name(base.name))
                    : std::string(file_.name(
                          file_.entity(base.record_entity).name));
                break;
            }
        }
        if (route.origin_subobject <
                completed_owner->virtual_subobjects.size() &&
            completed_owner->virtual_subobjects[route.origin_subobject]
                .is_virtual) {
            target_type = completed_owner
                ->virtual_subobjects[route.origin_subobject]
                .type.type;
            cir::EntityId origin_record =
                inherited.inherited_constructor->origin_record;
            if (origin_record.valid() && file_.valid(origin_record) &&
                file_.entity(origin_record).name.valid()) {
                target_name = std::string(
                    file_.name(file_.entity(origin_record).name));
            }
        }
    }
    const auto* declared_payload =
        std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(inherited.type.type)));
    if (!target_type.valid() || !declared_payload) {
        return false;
    }

    std::unique_ptr<BlockContextState> saved = save_function_context();
    std::vector<ParamInput> params;
    params.reserve(declared_payload->parameters.size());
    for (size_t i = 0; i < declared_payload->parameters.size(); ++i) {
        ParamInput param;
        param.name = ".inherited.template." + std::to_string(i);
        param.type = declared_payload->parameters[i];
        param.loc = loc;
        params.push_back(std::move(param));
    }
    FunctionDeclStart start =
        begin_member_function(specialization, params, loc, true);
    bool defined = !start.decl.has_error;
    if (defined) {
        MemberInitializerInput forward;
        forward.name = std::move(target_name);
        forward.base_type = target_type;
        forward.loc = loc;
        for (const ParamInput& param : params) {
            forward.arguments.push_back(
                inherited_constructor_forwarding_argument(param, loc));
        }
        std::vector<MemberInitializerInput> initializers;
        initializers.push_back(std::move(forward));
        enter_template_argument_access_exemption();
        StmtResult body = collect_constructor_initializers(
            std::move(initializers), loc);
        leave_template_argument_access_exemption();
        defined = !body.has_error;
        finish_member_function(std::move(body), loc);
        file_.entity_mut(specialization).linkage =
            cir::LinkageKind::LinkOnceODR;
    }
    restore_function_context(std::move(saved));
    return defined;
}

SrcLoc Session::record_method_owner_point_loc(cir::EntityId method) const {
    method = structor_impl_entity(method);
    if (!method.valid() || !file_.valid(method)) {
        return {};
    }
    cir::EntityId record_entity = file_.entity(method).parent;
    if (!record_entity.valid() || !file_.valid(record_entity)) {
        return file_.entity(method).loc;
    }
    if (const cir::TemplateSpecializationFact* spec =
            file_.template_specialization(record_entity)) {
        if (!spec->point_of_instantiation.isInvalid()) {
            return spec->point_of_instantiation;
        }
    }
    return file_.entity(record_entity).loc.isInvalid()
        ? file_.entity(method).loc
        : file_.entity(record_entity).loc;
}

uint64_t Session::record_method_owner_point_lookup_generation(
    cir::EntityId method) const {
    method = structor_impl_entity(method);
    if (method.valid() && file_.valid(method)) {
        cir::EntityId record_entity = file_.entity(method).parent;
        if (record_entity.valid() && file_.valid(record_entity)) {
            if (const cir::TemplateSpecializationFact* spec =
                    file_.template_specialization(record_entity)) {
                if (spec->point_lookup_generation != 0) {
                    return spec->point_lookup_generation;
                }
            }
        }
    }
    uint64_t generation = current_point_lookup_generation();
    return generation != 0 ? generation : lookup_generation_;
}

void Session::mark_record_method_required_at(cir::EntityId method,
                                             SrcLoc loc,
                                             uint64_t lookup_generation) {
    method = structor_impl_entity(method);
    if (!method.valid() || !file_.valid(method)) {
        return;
    }
    cir::EntityId record_entity = file_.entity(method).parent;
    if (!record_entity.valid() || !file_.valid(record_entity)) {
        return;
    }
    const cir::RecordFacts* facts = file_.record_facts(record_entity);
    if (!facts) {
        return;
    }
    cir::RecordFacts updated = *facts;
    for (cir::RecordMethodFact& fact : updated.methods) {
        if (fact.entity == method) {
            if (fact.first_required_lookup_generation == 0) {
                fact.first_required_loc =
                    loc.isInvalid() ? file_.entity(method).loc : loc;
                fact.first_required_lookup_generation = lookup_generation;
                if (fact.first_required_lookup_generation == 0) {
                    fact.first_required_lookup_generation =
                        current_point_lookup_generation();
                }
                if (fact.first_required_lookup_generation == 0) {
                    fact.first_required_lookup_generation = lookup_generation_;
                }
                file_.set_record_facts(record_entity, std::move(updated));
            }
            return;
        }
    }
}

cir::InstId Session::emit_construct_in_place(
    cir::InstId place,
    cir::EntityId constructor,
    const std::vector<cir::InstId>& args,
    SrcLoc loc) {
    mark_record_method_required(constructor, loc);
    return builder_.construct_in_place(place, constructor, args, loc);
}

cir::InstId Session::emit_destroy(cir::InstId place,
                                  cir::EntityId destructor,
                                  SrcLoc loc) {
    mark_record_method_required(destructor, loc);
    return builder_.destroy(place, destructor, loc);
}

cir::InstId Session::emit_structor_call(
    cir::EntityId structor,
    cir::TypeId result_type,
    const std::vector<cir::InstId>& args,
    SrcLoc loc) {
    mark_record_method_required(structor, loc);
    return builder_.call(structor, result_type, args, loc);
}

void Session::mark_record_method_required(cir::EntityId method, SrcLoc loc) {
    mark_record_method_required_at(method, loc, 0);
}

void Session::mark_record_vtable_methods_required(
    cir::EntityId record_entity) {
    if (!record_entity.valid() || !file_.valid(record_entity)) {
        return;
    }
    const cir::RecordFacts* facts = file_.record_facts(record_entity);
    if (!facts) {
        return;
    }
    std::vector<cir::VirtualTableSlotFact> slots =
        facts->primary_vtable_slot_facts;
    for (const cir::RecordFacts::SecondaryVtable& secondary :
         facts->secondary_vtables) {
        slots.insert(slots.end(), secondary.slot_facts.begin(),
                     secondary.slot_facts.end());
    }
    for (const cir::VirtualTableSlotFact& slot : slots) {
        if (!slot.runtime_callable || !slot.final_overrider.valid()) {
            continue;
        }
        const cir::RecordMethodFact* fact =
            file_.method_fact(slot.final_overrider);
        if (!fact || fact->is_pure || fact->is_consteval) {
            continue;
        }
        mark_record_method_required_at(
            slot.final_overrider,
            record_method_owner_point_loc(slot.final_overrider),
            record_method_owner_point_lookup_generation(
                slot.final_overrider));
    }
}

cir::Fragment Session::guard_on_structor_flag(cir::Fragment body,
                                              SrcLoc loc) {

    if (!current_structor_flag_.valid() || body.empty()) {
        return body;
    }
    auto merge_blocks = [](cir::Fragment& target, const cir::Fragment& source) {
        if (source.empty()) {
            return;
        }
        if (target.empty()) {
            target.entry = source.entry;
        }
        target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                             source.blocks.end());
        target.exit = source.exit;
    };
    cir::BlockId previous = builder_.current_block();
    cir::BlockId cond_block = begin_fragment_block("structor.guard");
    cir::InstId zero =
        builder_.integer_literal(0, builder_.int_type(), "0", loc);
    cir::InstId is_complete = builder_.binary(
        cir::BinaryOpKind::NotEqual, builder_.int_type(),
        current_structor_flag_, zero, loc);
    cir::Fragment fragment = finish_fragment_block(cond_block, previous);
    cir::BlockId continuation =
        builder_.create_detached_block("structor.done");
    builder_.cond_branch_from(fragment.exit, is_complete, body.entry,
                              continuation, {}, loc);
    merge_blocks(fragment, body);
    builder_.branch_from(body.exit, continuation, {}, loc);
    merge_blocks(fragment, builder_.block_fragment(continuation));
    fragment.exit = continuation;
    return fragment;
}

cir::Fragment Session::branch_on_structor_flag(cir::Fragment complete_body,
                                               cir::Fragment base_body,
                                               SrcLoc loc) {
    if (!current_structor_flag_.valid()) {
        return complete_body;
    }
    auto merge_blocks = [](cir::Fragment& target, const cir::Fragment& source) {
        if (source.empty()) {
            return;
        }
        if (target.empty()) {
            target.entry = source.entry;
        }
        target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                             source.blocks.end());
        target.exit = source.exit;
    };
    auto ensure_body = [&](cir::Fragment body) -> cir::Fragment {
        if (!body.empty()) {
            return body;
        }
        cir::BlockId block = builder_.create_detached_block("structor.arm");
        return builder_.block_fragment(block);
    };
    complete_body = ensure_body(std::move(complete_body));
    base_body = ensure_body(std::move(base_body));
    cir::BlockId previous = builder_.current_block();
    cir::BlockId cond_block = begin_fragment_block("structor.branch");
    cir::InstId zero =
        builder_.integer_literal(0, builder_.int_type(), "0", loc);
    cir::InstId is_complete = builder_.binary(
        cir::BinaryOpKind::NotEqual, builder_.int_type(),
        current_structor_flag_, zero, loc);
    cir::Fragment fragment = finish_fragment_block(cond_block, previous);
    cir::BlockId continuation =
        builder_.create_detached_block("structor.branch.done");
    builder_.cond_branch_from(fragment.exit, is_complete, complete_body.entry,
                              base_body.entry, {}, loc);
    merge_blocks(fragment, complete_body);
    builder_.branch_from(complete_body.exit, continuation, {}, loc);
    merge_blocks(fragment, base_body);
    builder_.branch_from(base_body.exit, continuation, {}, loc);
    merge_blocks(fragment, builder_.block_fragment(continuation));
    fragment.exit = continuation;
    return fragment;
}

Session::VttInfo Session::compute_vtt_info(const cir::RecordFacts& facts) const {
    VttInfo info;
    info.entry_count = 1;
    std::vector<const cir::RecordBaseFact*> direct;
    for (const cir::RecordBaseFact& base : facts.bases) {
        if (!base.is_virtual) {
            direct.push_back(&base);
        }
    }
    std::stable_sort(direct.begin(), direct.end(),
                     [](const cir::RecordBaseFact* a,
                        const cir::RecordBaseFact* b) {
                         return a->declaration_index < b->declaration_index;
                     });
    for (const cir::RecordBaseFact* base : direct) {
        const cir::RecordFacts* base_record =
            file_.record_facts_for_type(file_.resolved_type(base->type.type));
        if (!base_record || base_record->virtual_bases.empty()) {
            continue;
        }
        VttInfo sub = compute_vtt_info(*base_record);
        VttInfo::Slice slice;
        slice.record_entity = base->record_entity;
        slice.offset = base->non_virtual_offset;
        slice.start = info.entry_count;
        slice.count = sub.sub_count;
        info.base_slices.push_back(slice);
        info.entry_count += sub.sub_count;
    }
    info.sites_start = info.entry_count;
    for (const cir::RecordFacts::SecondaryVtable& secondary :
         facts.secondary_vtables) {
        if (!secondary.is_virtual) {
            continue;
        }
        info.sites.push_back({true, secondary.base_field,
                              secondary.storage_path,
                              secondary.base_offset_bytes,
                              secondary.address_point_bytes});
        ++info.entry_count;
    }
    for (const cir::RecordFacts::SecondaryVtable& secondary :
         facts.secondary_vtables) {
        if (secondary.is_virtual) {
            continue;
        }
        info.sites.push_back({false, secondary.base_field,
                              secondary.storage_path,
                              secondary.base_offset_bytes,
                              secondary.address_point_bytes});
        ++info.entry_count;
    }
    info.sub_count = info.entry_count;
    for (const cir::RecordFacts::VirtualBase& vbase : facts.virtual_bases) {
        const cir::RecordFacts* vbase_record =
            file_.record_facts_for_type(file_.resolved_type(vbase.type.type));
        if (!vbase_record || vbase_record->virtual_bases.empty()) {
            continue;
        }
        VttInfo sub = compute_vtt_info(*vbase_record);
        VttInfo::Slice slice;
        slice.record_entity = vbase.record_entity;
        slice.offset = vbase.storage_offset_bytes;
        slice.start = info.entry_count;
        slice.count = sub.sub_count;
        info.vbase_slices.push_back(slice);
        info.entry_count += sub.sub_count;
    }
    return info;
}

cir::EntityId Session::emit_construction_vtable(const cir::RecordFacts& complete,
                                                const cir::RecordFacts& base,
                                                size_t offset,
                                                SrcLoc loc) {
    std::string symbol = abi::itanium_construction_vtable_symbol(
        file_, complete.entity, base.entity, offset);
    if (symbol.empty() || !base.vtable_entity.valid()) {
        return {};
    }
    auto cached = collecting_pattern_ ? vtable_thunks_.end()
                                      : vtable_thunks_.find(symbol);
    if (cached != vtable_thunks_.end()) {
        return cached->second;
    }

    auto class_prefix_words = [&](cir::TypeId type) -> size_t {
        const cir::RecordFacts* record =
            file_.record_facts_for_type(file_.resolved_type(type));
        return record ? record->virtual_bases.size() : 0;
    };
    size_t total_words =
        base.virtual_bases.size() + 2 + base.vtable_slots.size();
    for (const cir::RecordFacts::SecondaryVtable& secondary :
         base.secondary_vtables) {
        total_words += class_prefix_words(secondary.base_type.type) + 2 +
                       secondary.slots.size();
    }
    cir::TypeId table_type = builder_.array_type(
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void)),
        total_words);
    cir::EntityId table_entity =
        builder_.add_entity(cir::EntityKind::Variable, symbol, table_type, {},
                            loc, cir::StorageDuration::Static);
    cir::Entity& table_record = file_.entity_mut(table_entity);
    table_record.is_definition = true;
    table_record.linkage = cir::LinkageKind::LinkOnceODR;
    table_record.is_extern_c = true;
    mark_generated_abi_entity(table_entity, complete.entity,
                              cir::GeneratedSymbolRole::ConstructionVTable);
    table_record.has_static_initializer = true;
    const size_t ptr = std::max<size_t>(
        1, (file_.target_info().pointer_width + 7) / 8);
    table_record.static_initializer_bytes.assign(total_words * ptr, 0);

    auto write_word = [&](size_t byte_offset, int64_t value) {
        abi::write_scalar_bits(
            file_.entity_mut(table_entity)
                    .static_initializer_bytes.data() + byte_offset,
            ptr, static_cast<uint64_t>(value), 0,
            file_.target_info().endianness);
    };
    auto add_reloc = [&](size_t byte_offset, cir::EntityId target) {
        if (target.valid()) {
            file_.entity_mut(table_entity)
                .static_initializer_relocations.push_back(
                    cir::StaticInitializerRelocation{byte_offset, target, 0});
        }
    };
    auto complete_storage = [&](cir::EntityId record_entity,
                                bool* found) -> size_t {
        for (const cir::RecordFacts::VirtualBase& vbase :
             complete.virtual_bases) {
            if (vbase.record_entity == record_entity) {
                if (found) {
                    *found = true;
                }
                return vbase.storage_offset_bytes;
            }
        }
        if (found) {
            *found = false;
        }
        return 0;
    };
    auto resolve = [&](const cir::VirtualTableSlotFact& plan,
                       size_t table_pos) -> cir::EntityId {
        if (!plan.runtime_callable || !plan.final_overrider.valid()) {
            return {};
        }
        cir::EntityId target = plan.final_overrider;
        cir::EntityId slot_declaration = plan.declaration.valid()
            ? plan.declaration
            : plan.final_overrider;
        const cir::RecordMethodFact* slot_fact = file_.method_fact(target);
        if (slot_fact && slot_fact->is_pure) {
            return runtime_function(
                "__cxa_pure_virtual",
                function_type(file_.type_ref(file_.builtin_type(
                                  cir::BuiltinTypeKind::Void)),
                              {}, false, true),
                loc);
        }
        bool owned_by_base = target.valid() && file_.valid(target) &&
                             file_.entity(target).parent == base.entity;
        if (plan.is_deleting_destructor) {
            target = synthesize_deleting_destructor(target, loc);
            slot_declaration =
                synthesize_deleting_destructor(slot_declaration, loc);
        } else if (target.valid() && file_.valid(target) &&
                   file_.entity(target).kind == cir::EntityKind::Destructor) {
            target = structor_complete_variant(target);
            slot_declaration = structor_complete_variant(slot_declaration);
        }
        cir::VirtualAdjustmentFact this_adjustment = plan.this_adjustment;
        if (owned_by_base) {
            int64_t delta = static_cast<int64_t>(offset) -
                            static_cast<int64_t>(table_pos);
            this_adjustment = {};
            if (delta != 0) {
                this_adjustment.kind =
                    cir::VirtualAdjustmentKind::NonVirtual;
                this_adjustment.static_offset_bytes = delta;
            }
        }
        if (this_adjustment.required() ||
            plan.result_adjustment.required()) {
            target = synthesize_vtable_thunk(
                target,
                slot_declaration,
                this_adjustment,
                plan.result_adjustment,
                loc);
        }
        return target;
    };

    size_t primary_ap = base.vtable_address_point;
    for (size_t i = 0; i < base.virtual_bases.size(); ++i) {
        bool found = false;
        size_t storage =
            complete_storage(base.virtual_bases[i].record_entity, &found);
        if (found) {
            write_word(primary_ap - 3 * ptr - ptr * i,
                       static_cast<int64_t>(storage) -
                           static_cast<int64_t>(offset));
        }
    }
    write_word(primary_ap - 2 * ptr, 0);
    add_reloc(primary_ap - ptr, base.typeinfo_entity);
    for (size_t i = 0; i < base.vtable_slots.size(); ++i) {
        cir::VirtualTableSlotFact plan =
            i < base.primary_vtable_slot_facts.size()
                ? base.primary_vtable_slot_facts[i]
                : cir::VirtualTableSlotFact{};
        if (!plan.final_overrider.valid()) {
            plan.final_overrider = base.vtable_slots[i];
            plan.declaration = base.vtable_slots[i];
        }
        cir::EntityId resolved = resolve(plan, offset);
        add_reloc(primary_ap + ptr * i, resolved);
    }
    for (const cir::RecordFacts::SecondaryVtable& secondary :
         base.secondary_vtables) {
        size_t table_pos = offset + secondary.base_offset_bytes;
        if (secondary.is_virtual) {
            for (const cir::RecordFacts::VirtualBase& vbase :
                 base.virtual_bases) {
                if (vbase.storage_field == secondary.base_field) {
                    bool found = false;
                    size_t storage =
                        complete_storage(vbase.record_entity, &found);
                    if (found) {
                        table_pos = storage;
                    }
                    break;
                }
            }
        }
        size_t ap = secondary.address_point_bytes;
        const cir::RecordFacts* table_class =
            file_.record_facts_for_type(
                file_.resolved_type(secondary.base_type.type));
        if (table_class) {
            for (size_t i = 0; i < table_class->virtual_bases.size(); ++i) {
                bool found = false;
                size_t storage = complete_storage(
                    table_class->virtual_bases[i].record_entity, &found);
                if (found) {
                    write_word(ap - 3 * ptr - ptr * i,
                               static_cast<int64_t>(storage) -
                                   static_cast<int64_t>(table_pos));
                }
            }
        }
        write_word(ap - 2 * ptr, static_cast<int64_t>(offset) -
                                     static_cast<int64_t>(table_pos));
        add_reloc(ap - ptr, base.typeinfo_entity);
        for (size_t i = 0; i < secondary.slots.size(); ++i) {
            cir::VirtualTableSlotFact plan =
                i < secondary.slot_facts.size()
                    ? secondary.slot_facts[i]
                    : cir::VirtualTableSlotFact{};
            if (!plan.final_overrider.valid()) {
                plan.final_overrider = secondary.slots[i];
                plan.declaration = secondary.slots[i];
            }
            cir::EntityId resolved = resolve(plan, table_pos);
            add_reloc(ap + ptr * i, resolved);
        }
    }
    if (!collecting_pattern_) {

        if (auto [thunk, inserted] =
                vtable_thunks_.emplace(symbol, table_entity);
            inserted) {
            track_speculative_rollback(
                [this, symbol] { vtable_thunks_.erase(symbol); });
        }
    }
    return table_entity;
}

void Session::emit_virtual_table_table(cir::RecordFacts& facts, SrcLoc loc) {
    if (facts.virtual_bases.empty() || !facts.vtable_entity.valid()) {
        return;
    }
    std::string symbol =
        abi::itanium_record_data_symbol(file_, facts.entity, "_ZTT");
    if (symbol.empty()) {
        return;
    }
    VttInfo info = compute_vtt_info(facts);
    cir::TypeId ztt_type = builder_.array_type(
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void)),
        info.entry_count);
    cir::EntityId ztt_entity =
        builder_.add_entity(cir::EntityKind::Variable, symbol, ztt_type, {},
                            loc, cir::StorageDuration::Static);
    cir::Entity& ztt_record = file_.entity_mut(ztt_entity);
    ztt_record.is_definition = true;
    ztt_record.linkage = cir::LinkageKind::LinkOnceODR;
    ztt_record.is_extern_c = true;
    mark_generated_abi_entity(ztt_entity, facts.entity,
                              cir::GeneratedSymbolRole::VTT);
    ztt_record.has_static_initializer = true;
    const size_t ptr = std::max<size_t>(
        1, (file_.target_info().pointer_width + 7) / 8);
    ztt_record.static_initializer_bytes.assign(info.entry_count * ptr, 0);
    auto entry = [&](size_t index, cir::EntityId group, size_t address_point) {
        if (group.valid()) {
            file_.entity_mut(ztt_entity)
                .static_initializer_relocations.push_back(
                    cir::StaticInitializerRelocation{
                        index * ptr, group,
                        static_cast<int64_t>(address_point)});
        }
    };
    entry(0, facts.vtable_entity, facts.vtable_address_point);

    auto fill = [&](auto&& self, const cir::RecordFacts& base, size_t offset,
                    size_t index) -> void {
        cir::EntityId ztc = emit_construction_vtable(facts, base, offset, loc);
        if (!ztc.valid()) {
            return;
        }
        VttInfo sub = compute_vtt_info(base);
        entry(index, ztc, base.vtable_address_point);
        for (const VttInfo::Slice& slice : sub.base_slices) {
            const cir::RecordFacts* deeper =
                file_.record_facts(slice.record_entity);
            if (deeper) {
                self(self, *deeper, offset + slice.offset,
                     index + slice.start);
            }
        }
        for (size_t k = 0; k < sub.sites.size(); ++k) {
            entry(index + sub.sites_start + k, ztc,
                  sub.sites[k].address_point);
        }
    };
    for (const VttInfo::Slice& slice : info.base_slices) {
        const cir::RecordFacts* base = file_.record_facts(slice.record_entity);
        if (base) {
            fill(fill, *base, slice.offset, slice.start);
        }
    }
    for (size_t k = 0; k < info.sites.size(); ++k) {
        entry(info.sites_start + k, facts.vtable_entity,
              info.sites[k].address_point);
    }
    for (const VttInfo::Slice& slice : info.vbase_slices) {
        const cir::RecordFacts* vbase =
            file_.record_facts(slice.record_entity);
        if (vbase) {
            fill(fill, *vbase, slice.offset, slice.start);
        }
    }
    facts.vtt_entity = ztt_entity;
}

cir::InstId Session::load_vtt_entry(size_t index, SrcLoc loc) {
    cir::TypeId usize = builder_.usize_type();
    cir::TypeId void_pointer =
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
    cir::InstId vtt_value =
        builder_.lvalue_to_rvalue(current_structor_vtt_place_, loc);
    cir::InstId raw = builder_.cast(usize, vtt_value, "value", loc);
    cir::InstId offset = builder_.integer_literal(
        static_cast<int64_t>(index * 8), usize, std::to_string(index * 8),
        loc);
    cir::InstId adjusted =
        builder_.binary(cir::BinaryOpKind::Add, usize, raw, offset, loc);
    cir::InstId pointer = builder_.cast(builder_.pointer_type(void_pointer),
                                        adjusted, "value", loc);
    cir::InstId place = builder_.deref(pointer, loc);
    return builder_.lvalue_to_rvalue(place, loc);
}

cir::InstId Session::vtt_slice_value(size_t index, SrcLoc loc) {
    cir::TypeId usize = builder_.usize_type();
    cir::TypeId vtt_type = builder_.pointer_type(builder_.pointer_type(
        file_.builtin_type(cir::BuiltinTypeKind::Void)));
    cir::InstId vtt_value =
        builder_.lvalue_to_rvalue(current_structor_vtt_place_, loc);
    cir::InstId raw = builder_.cast(usize, vtt_value, "value", loc);
    cir::InstId offset = builder_.integer_literal(
        static_cast<int64_t>(index * 8), usize, std::to_string(index * 8),
        loc);
    cir::InstId adjusted =
        builder_.binary(cir::BinaryOpKind::Add, usize, raw, offset, loc);
    return builder_.cast(vtt_type, adjusted, "value", loc);
}

cir::Fragment Session::vtt_vptr_store_fragment(SrcLoc loc) {
    cir::Fragment result;
    if (!current_member_record_.valid() || !current_this_place_.valid() ||
        !current_structor_vtt_place_.valid()) {
        return result;
    }
    const cir::RecordFacts* facts = file_.record_facts(current_member_record_);
    if (!facts || !facts->is_polymorphic) {
        return result;
    }
    VttInfo info = compute_vtt_info(*facts);
    cir::TypeId record_type = facts->type.type;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("ctor.vptr.vtt");

    std::vector<cir::EntityId> path;
    if (vptr_field_path(record_type, &path)) {
        cir::InstId this_value =
            builder_.lvalue_to_rvalue(current_this_place_, loc);
        cir::InstId place = builder_.deref(this_value, loc);
        for (cir::EntityId step : path) {
            place = builder_.field_addr(place, step,
                                        file_.entity(step).type, loc);
        }
        builder_.store(place, load_vtt_entry(0, loc), loc);
    }
    for (size_t k = 0; k < info.sites.size(); ++k) {
        const VttInfo::Site& site = info.sites[k];
        cir::InstId entry_value =
            load_vtt_entry(info.sites_start + k, loc);
        cir::InstId this_value =
            builder_.lvalue_to_rvalue(current_this_place_, loc);
        cir::InstId place = builder_.deref(this_value, loc);
        std::vector<cir::EntityId> steps;
        if (site.is_virtual) {
            place = emit_virtual_base_adjust(place, site.base_field, loc);
            if (!vptr_field_path(file_.entity(site.base_field).type, &steps)) {
                continue;
            }
        } else {
            steps = site.storage_path;
            if (!vptr_field_path(file_.entity(site.base_field).type, &steps)) {
                continue;
            }
        }
        for (cir::EntityId step : steps) {
            place = builder_.field_addr(place, step,
                                        file_.entity(step).type, loc);
        }
        builder_.store(place, entry_value, loc);
    }
    result = finish_fragment_block(block, previous);
    return result;
}

void Session::register_member_definition_default_arguments(
    cir::EntityId method_entity,
    const std::vector<ParamInput>& declared_params,
    SrcLoc loc) {
    bool has_new_default = false;
    for (const ParamInput& param : declared_params) {
        has_new_default = has_new_default ||
                          param.default_argument.has_value();
    }
    if (!has_new_default || !method_entity.valid() ||
        !file_.valid(method_entity)) {
        return;
    }

    const cir::Entity& method = file_.entity(method_entity);
    auto owning_record_is_templated_class = [&]() {
        cir::EntityId record_entity = method.parent;
        if (!record_entity.valid() || !file_.valid(record_entity)) {
            return false;
        }
        if (const TemplateInfo* info = template_info(record_entity)) {
            if (info->is_class_template) {
                return true;
            }
        }
        if (const cir::TemplateSpecializationFact* spec =
                file_.template_specialization(record_entity)) {
            if (spec->template_entity.valid()) {
                const TemplateInfo* info = template_info(spec->template_entity);
                return info && info->is_class_template;
            }
        }
        return false;
    };
    if (owning_record_is_templated_class()) {
        report_error("default arguments for members of class templates "
                     "must appear on the initial in-class declaration",
                     loc);
        return;
    }

    const cir::Binding* binding = nullptr;
    if (method.name.valid() && method.semantic_context.valid()) {
        binding = file_.lookup_callable_binding(method.semantic_context,
                                                file_.name(method.name),
                                                /*include_parents=*/false);
    }
    register_function_default_arguments(method_entity, declared_params,
                                        binding, loc);

    const cir::RecordMethodFact* fact = file_.method_fact(method_entity);
    const auto* payload = fact
        ? std::get_if<cir::FunctionTypePayload>(
              &file_.type_payload(file_.resolved_type(fact->type.type)))
        : nullptr;
    if (!payload) {
        return;
    }
    auto parameter_has_default = [&](size_t index) {
        return callable_default_argument(method_entity, index) != nullptr;
    };
    auto all_parameters_defaulted_from = [&](size_t start) {
        for (size_t i = start; i < payload->parameters.size(); ++i) {
            if (!parameter_has_default(i)) {
                return false;
            }
        }
        return true;
    };
    auto record_type = [&]() {
        cir::EntityId record_entity = method.parent;
        return record_entity.valid() && file_.valid(record_entity)
            ? file_.entity(record_entity).type
            : cir::TypeId{};
    };
    auto special_assignment_kind = [&](cir::TypeRef parameter)
        -> std::string_view {
        cir::TypeId expected = file_.resolved_type(record_type());
        cir::TypeId type = file_.resolved_type(parameter.type);
        if (!file_.valid(type) || !file_.valid(expected)) {
            return {};
        }
        cir::TypeKind kind = file_.type(type).kind;
        if (kind == cir::TypeKind::RValueReference) {
            cir::TypeRef referred = file_.reference_referred_ref(type);
            return file_.resolved_type(referred.type) == expected
                ? std::string_view("move assignment operator")
                : std::string_view();
        }
        if (kind == cir::TypeKind::LValueReference) {
            cir::TypeRef referred = file_.reference_referred_ref(type);
            return file_.resolved_type(referred.type) == expected
                ? std::string_view("copy assignment operator")
                : std::string_view();
        }
        return type == expected ? std::string_view("copy assignment operator")
                                : std::string_view();
    };

    if (method.kind != cir::EntityKind::Constructor) {
        if (method.kind == cir::EntityKind::Method &&
            fact && !fact->is_static &&
            method.name.valid() && file_.name(method.name) == "operator=" &&
            !payload->parameters.empty() &&
            all_parameters_defaulted_from(1)) {
            std::string_view kind =
                special_assignment_kind(payload->parameters.front());
            if (!kind.empty()) {
                report_error("out-of-line default arguments cannot make an "
                             "assignment operator a " +
                                 std::string(kind),
                             loc);
            }
        }
        return;
    }
    if (!payload->parameters.empty() &&
        all_parameters_defaulted_from(0)) {
        report_error("out-of-line default arguments cannot make a "
                     "constructor a default constructor",
                     loc);
        return;
    }
    if (payload->parameters.empty() ||
        !all_parameters_defaulted_from(1)) {
        return;
    }
    cir::TypeId first = file_.resolved_type(payload->parameters.front().type);
    if (!file_.valid(first)) {
        return;
    }
    cir::TypeKind first_kind = file_.type(first).kind;
    if (first_kind != cir::TypeKind::LValueReference &&
        first_kind != cir::TypeKind::RValueReference) {
        return;
    }
    cir::TypeRef referred = file_.reference_referred_ref(first);
    if (file_.resolved_type(referred.type) !=
        file_.resolved_type(record_type())) {
        return;
    }
    report_error(std::string("out-of-line default arguments cannot make a "
                             "constructor a ") +
                     (first_kind == cir::TypeKind::RValueReference
                          ? "move constructor"
                          : "copy constructor"),
                 loc);
}

FunctionDeclStart Session::begin_member_function(
    cir::EntityId method_entity,
    const std::vector<ParamInput>& declared_params,
    SrcLoc loc,
    bool suppress_noexcept_region) {
    FunctionDeclStart result;
    if (!file_.valid(method_entity)) {
        result.decl.has_error = true;
        return result;
    }
    current_prologue_ = {};
    function_labels_.clear();
    local_label_scopes_.clear();
    pending_orphan_label_blocks_.clear();
    vla_sp_slot_place_ = {};

    cir::EntityId record_entity;
    cir::TypeId method_type;
    cir::EntityKind method_kind;
    bool entity_is_static_member_function = false;
    {
        const cir::Entity& method = file_.entity(method_entity);
        record_entity = method.parent;
        method_type = method.type;
        method_kind = method.kind;
        entity_is_static_member_function =
            method.is_static_member_function;
        if (!record_entity.valid() &&
            method.kind == cir::EntityKind::Function &&
            method.semantic_context.valid() &&
            file_.valid(method.semantic_context) &&
            file_.decl_context(method.semantic_context).kind ==
                cir::DeclContextKind::Record) {
            record_entity =
                file_.decl_context(method.semantic_context).owner;
        }
    }
    diagnose_abstract_function_use(method_type,
                                   AbstractFunctionUse::Definition,
                                   loc);
    cir::TypeId record_type = file_.entity(record_entity).type;
    cir::DeclContextId record_context =
        file_.entity(record_entity).semantic_context;
    if (!record_context.valid()) {
        report_error("member function belongs to an incomplete class", loc);
        result.decl.has_error = true;
        return result;
    }

    enter_existing_context(record_context, ScopeFlags::RecordScope);

    cir::TypeId resolved_type = file_.resolved_type(method_type);
    const auto* payload =
        std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved_type));
    cir::TypeId result_type = payload && payload->return_type.valid()
        ? payload->return_type.type
        : file_.builtin_type(cir::BuiltinTypeKind::Void);

    file_.entity_mut(method_entity).is_definition = true;

    const cir::RecordMethodFact* fact = file_.method_fact(method_entity);
    bool is_static =
        entity_is_static_member_function ||
        method_kind == cir::EntityKind::Function ||
        (fact && fact->is_static);

    tstate().function_parameter_pack_scope_stack_.push_back(
        FunctionParameterPackScopeState{
            std::move(tstate().function_parameter_pack_names_),
            std::move(tstate().function_parameter_pack_elements_),
            std::move(tstate().function_parameter_pack_template_indices_)});
    tstate().function_parameter_pack_names_ = {};
    tstate().function_parameter_pack_elements_ = {};
    tstate().function_parameter_pack_template_indices_ = {};
    std::unordered_map<uint64_t, std::string> source_pack_names_by_entity;

    std::vector<std::pair<cir::EntityId, cir::TypeId>> param_entities;
    param_entities.reserve(declared_params.size() + 1);
    cir::EntityId this_entity{};

    bool this_is_const = payload && payload->member_is_const;
    bool this_is_volatile = payload && payload->member_is_volatile;
    if (!is_static) {

        cir::TypeRef this_pointee = file_.type_ref(record_type);
        if (this_is_const) {
            this_pointee.qualifiers |= cir::QualConst;
        }
        if (this_is_volatile) {
            this_pointee.qualifiers |= cir::QualVolatile;
        }
        cir::TypeId this_type = builder_.pointer_type(this_pointee);
        this_entity = builder_.add_entity(cir::EntityKind::Parameter,
                                          "this",
                                          this_type,
                                          method_entity,
                                          loc,
                                          cir::StorageDuration::Parameter);
        param_entities.emplace_back(this_entity, this_type);
    }
    for (const ParamInput& param : declared_params) {
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
        cir::EntityId entity = param.prototype_entity;
        if (entity.valid()) {
            file_.entity_mut(entity).parent = method_entity;
        } else {
            entity = builder_.add_entity(cir::EntityKind::Parameter,
                                         param.name,
                                         param.type.type,
                                         method_entity,
                                         param_loc,
                                         cir::StorageDuration::Parameter);
        }
        file_.entity_mut(entity).qualifiers = param.type.qualifiers;
        if (param.is_parameter_pack) {
            uint64_t entity_index = static_cast<uint64_t>(entity.index);
            journal_speculative_set_entry(
                "member function parameter pack identity",
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
        param_entities.emplace_back(entity, param.type.type);
    }

    bool vbase_structor = false;
    {
        if (method_kind == cir::EntityKind::Constructor ||
            method_kind == cir::EntityKind::Destructor) {
            const cir::RecordFacts* record_facts =
                file_.record_facts(record_entity);
            vbase_structor =
                record_facts && !record_facts->virtual_bases.empty();
        }
    }
    if (vbase_structor) {
        cir::TypeId flag_type = builder_.int_type();
        cir::EntityId flag_entity = builder_.add_entity(
            cir::EntityKind::Parameter, ".complete", flag_type, method_entity,
            loc, cir::StorageDuration::Parameter);
        param_entities.emplace_back(flag_entity, flag_type);
        cir::TypeId vtt_type = builder_.pointer_type(builder_.pointer_type(
            file_.builtin_type(cir::BuiltinTypeKind::Void)));
        cir::EntityId vtt_entity = builder_.add_entity(
            cir::EntityKind::Parameter, ".vtt", vtt_type, method_entity, loc,
            cir::StorageDuration::Parameter);
        param_entities.emplace_back(vtt_entity, vtt_type);
    }

    cir::FunctionStart fn =
        builder_.begin_function(method_entity, result_type, param_entities, loc);
    current_function_ = fn.function;
    current_result_type_ = result_type;
    nrvo_return_candidates_.clear();
    nrvo_has_incompatible_return_ = false;
    active_catch_handlers_ = 0;
    active_constructor_function_try_handlers_ = 0;
    coroutine_state_.reset();
    first_plain_return_loc_ = {};
    has_plain_return_ = false;
    enter_scope_impl(ScopeFlags::FunctionScope, method_entity, loc);
    if (!suppress_noexcept_region) {
        begin_noexcept_body_region(method_type, loc);
    }

    for (const cir::FunctionParameter& parameter : fn.parameters) {
        cir::EntityId param_entity = parameter.entity;
        cir::TypeId param_type = file_.entity(param_entity).type;
        SrcLoc param_loc = file_.entity(param_entity).loc;

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("param.place");
        cir::InstId param_place = builder_.local_place(param_entity, param_type, param_loc);
        builder_.store(param_place, parameter.value.inst, param_loc);
        cir::Fragment param_fragment = finish_fragment_block(block, previous);
        current_prologue_ = chain(std::move(current_prologue_),
                                  std::move(param_fragment),
                                  param_loc);

        if (file_.entity(param_entity).name.valid()) {
            bind_entity(file_.name(file_.entity(param_entity).name),
                        cir::LookupNamespace::Ordinary,
                        param_entity,
                        param_type,
                        false,
                        false,
                        true,
                        param_place,
                        param_loc);
        }
        if (this_entity.valid() && param_entity == this_entity) {
            current_this_place_ = param_place;
        }
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
    current_member_record_ = record_entity;
    if (is_static) {
        current_this_place_ = {};
    }

    current_structor_flag_ = {};
    current_structor_vtt_place_ = {};
    if (vbase_structor && fn.parameters.size() >= 2) {
        current_structor_flag_ =
            fn.parameters[fn.parameters.size() - 2].value.inst;
        cir::InstId vtt_param =
            fn.parameters[fn.parameters.size() - 1].value.inst;
        // The effective VTT: the class's own _ZTT for complete-object work,
        // the caller-provided sub-VTT otherwise (Itanium 2.6.3).
        const cir::RecordFacts* record_facts_ptr =
            file_.record_facts(record_entity);
        cir::TypeId vtt_type = builder_.pointer_type(builder_.pointer_type(
            file_.builtin_type(cir::BuiltinTypeKind::Void)));
        cir::BlockId eff_previous = builder_.current_block();
        cir::BlockId eff_block = begin_fragment_block("structor.vtt.eff");
        cir::EntityId eff_entity = builder_.add_entity(
            cir::EntityKind::Variable, ".vtt.eff", vtt_type, method_entity,
            loc, cir::StorageDuration::Automatic);
        cir::InstId eff_place =
            builder_.local_place(eff_entity, vtt_type, loc);
        cir::Fragment eff_fragment =
            finish_fragment_block(eff_block, eff_previous);
        current_structor_vtt_place_ = eff_place;

        cir::Fragment own_fragment;
        if (record_facts_ptr && record_facts_ptr->vtt_entity.valid()) {
            cir::BlockId own_previous = builder_.current_block();
            cir::BlockId own_block = begin_fragment_block("structor.vtt.own");
            cir::TypeId usize = builder_.usize_type();
            cir::InstId ztt_place =
                builder_.global_place(record_facts_ptr->vtt_entity, loc);
            cir::InstId ztt_address = builder_.addr_of(ztt_place, loc);
            cir::InstId own_value =
                builder_.cast(vtt_type, ztt_address, "value", loc);
            builder_.store(eff_place, own_value, loc);
            own_fragment = finish_fragment_block(own_block, own_previous);
        }
        cir::Fragment param_fragment_vtt;
        {
            cir::BlockId param_previous = builder_.current_block();
            cir::BlockId param_block =
                begin_fragment_block("structor.vtt.param");
            builder_.store(eff_place, vtt_param, loc);
            param_fragment_vtt =
                finish_fragment_block(param_block, param_previous);
        }
        eff_fragment = chain(
            std::move(eff_fragment),
            branch_on_structor_flag(std::move(own_fragment),
                                    std::move(param_fragment_vtt), loc),
            loc);
        current_prologue_ = chain(std::move(current_prologue_),
                                  std::move(eff_fragment), loc);
    }

    if (file_.entity(method_entity).kind == cir::EntityKind::Destructor) {
        StmtResult vptr_store = store_vptr_fragment(loc);
        if (current_structor_flag_.valid()) {
            vptr_store.fragment = branch_on_structor_flag(
                std::move(vptr_store.fragment),
                vtt_vptr_store_fragment(loc), loc);
        }
        current_prologue_ = chain(std::move(current_prologue_),
                                  std::move(vptr_store.fragment),
                                  loc);
        begin_destructor_lifecycle_region(loc);
    }

    result.decl.entity = method_entity;
    result.decl.type = method_type;
    result.function = fn;
    return result;
}

void Session::finish_member_function(StmtResult body, SrcLoc loc) {
    finish_function(std::move(body), loc);

    leave_scope();
    current_this_place_ = {};
    current_member_record_ = {};
}

Session::AccessContext Session::current_access_context() const {
    AccessContext context;
    context.exact = true;
    context.lexical_context = current_decl_context();

    cir::EntityId declaration_record{};
    for (cir::DeclContextId lexical = context.lexical_context;
         lexical.valid() && file_.valid(lexical);
         lexical = file_.decl_context(lexical).parent) {
        const cir::DeclContext& declaration = file_.decl_context(lexical);
        if (declaration.kind == cir::DeclContextKind::Record) {
            declaration_record = declaration.owner;
            break;
        }
        if (declaration.kind == cir::DeclContextKind::Function ||
            declaration.kind == cir::DeclContextKind::Block) {
            break;
        }
    }

    context.accessing_record = declaration_record.valid()
        ? declaration_record
        : current_member_record_;
    if (member_access_function_override_.valid()) {
        context.accessing_function = member_access_function_override_;
        context.declaring_entity = context.accessing_function;
    } else if (!declaration_record.valid() &&
               current_function_.valid() && file_.valid(current_function_)) {
        context.accessing_function = file_.function(current_function_).entity;
        context.declaring_entity = context.accessing_function;
    } else if (declaration_record.valid()) {
        context.declaring_entity = declaration_record;
    }
    if (!context.accessing_record.valid() &&
        context.accessing_function.valid() &&
        file_.valid(context.accessing_function)) {
        const cir::Entity& function =
            file_.entity(context.accessing_function);
        if (function.is_record_member) {
            context.accessing_record = function.declaring_record.valid()
                ? function.declaring_record
                : function.parent;
            if (!context.accessing_record.valid()) {
                context.accessing_record = enclosing_record_for_context(
                    function.semantic_context);
            }
        } else if (function.kind == cir::EntityKind::Function) {

            context.accessing_record = enclosing_record_for_context(
                function.lexical_context);
        }
    }
    // Compiler-generated initialization/cleanup functions are implementation
    // vehicles for their ABI owner, not independent source declarations.
    // [class.access.general] applies access to the declaration of the source
    // entity as a whole, so delayed constructor/destructor selection inside
    // one of these helpers must retain the owner's declaration context.
    if (!member_access_function_override_.valid() &&
        context.accessing_function.valid() &&
        file_.valid(context.accessing_function)) {
        const cir::Entity& function =
            file_.entity(context.accessing_function);
        if (function.abi_identity == cir::AbiIdentityKind::Generated &&
            function.abi_owner.valid() &&
            file_.valid(function.abi_owner)) {
            AccessContext owner =
                access_context_for_entity(function.abi_owner);
            context.declaring_entity = owner.declaring_entity;
            context.accessing_function = owner.accessing_function;
            if (!context.accessing_record.valid()) {
                context.accessing_record = owner.accessing_record;
            }
            context.lexical_context = owner.lexical_context;
        }
    }
    bool free_function_context = context.accessing_function.valid() &&
        file_.valid(context.accessing_function) &&
        file_.entity(context.accessing_function).kind ==
            cir::EntityKind::Function;
    if (!context.accessing_record.valid() && !free_function_context) {
        context.accessing_record = enclosing_record_for_context(
            context.lexical_context);
    }
    return context;
}

Session::AccessContext Session::access_context_for_entity(
    cir::EntityId entity) const {
    AccessContext context;
    context.exact = true;
    context.declaring_entity = entity;
    if (!entity.valid() || !file_.valid(entity)) {
        return current_access_context();
    }
    const cir::Entity& declaration = file_.entity(entity);
    context.lexical_context = declaration.lexical_context.valid()
        ? declaration.lexical_context
        : declaration.semantic_context;
    switch (declaration.kind) {
        case cir::EntityKind::Function:
        case cir::EntityKind::Method:
        case cir::EntityKind::Constructor:
        case cir::EntityKind::Destructor:
            context.accessing_function = entity;
            break;
        default:
            break;
    }
    if (declaration.kind == cir::EntityKind::Record) {
        context.accessing_record = entity;
    } else if (declaration.is_record_member &&
               declaration.declaring_record.valid()) {
        context.accessing_record = declaration.declaring_record;
    } else if (declaration.parent.valid() &&
               file_.valid(declaration.parent) &&
               file_.entity(declaration.parent).kind ==
                   cir::EntityKind::Record) {
        context.accessing_record = declaration.parent;
    }
    for (cir::DeclContextId scope = context.lexical_context;
         scope.valid() && file_.valid(scope);
         scope = file_.decl_context(scope).parent) {
        cir::EntityId owner = file_.decl_context(scope).owner;
        if (!owner.valid() || !file_.valid(owner)) {
            continue;
        }
        cir::EntityKind owner_kind = file_.entity(owner).kind;
        if (!context.accessing_function.valid() &&
            (owner_kind == cir::EntityKind::Function ||
             owner_kind == cir::EntityKind::Method ||
             owner_kind == cir::EntityKind::Constructor ||
             owner_kind == cir::EntityKind::Destructor)) {
            context.accessing_function = owner;
        }
        if (!context.accessing_record.valid() &&
            owner_kind == cir::EntityKind::Record) {
            context.accessing_record = owner;
        }
    }
    if (!context.accessing_record.valid()) {
        context.accessing_record = enclosing_record_for_context(
            context.lexical_context);
    }
    return context;
}

Session::AccessCaptureToken Session::begin_access_capture() {
    return begin_access_capture(AccessCaptureToken{});
}

Session::AccessCaptureToken Session::begin_access_capture(
    AccessCaptureToken prefix) {
    AccessCapture capture;
    if (prefix.valid()) {
        size_t prefix_index = static_cast<size_t>(prefix.index - 1);
        if (prefix_index < access_captures_.size() &&
            access_captures_[prefix_index].retained) {
            capture.obligations = access_captures_[prefix_index].obligations;
        }
    }
    capture.active = true;
    access_captures_.push_back(std::move(capture));
    uint32_t index = static_cast<uint32_t>(access_captures_.size() - 1);
    active_access_captures_.push_back(index);
    return AccessCaptureToken{index + 1};
}

void Session::suspend_access_capture(AccessCaptureToken capture) {
    if (!capture.valid()) {
        return;
    }
    uint32_t index = capture.index - 1;
    if (!active_access_captures_.empty() &&
        active_access_captures_.back() == index) {
        active_access_captures_.pop_back();
    }
    if (index < access_captures_.size()) {
        access_captures_[index].active = false;
    }
}

bool Session::capture_access_obligation(AccessObligation obligation) {

    if (active_access_captures_.empty() || current_function_.valid() ||
        in_default_argument_replay()) {
        return false;
    }
    uint32_t index = active_access_captures_.back();
    if (index >= access_captures_.size() ||
        !access_captures_[index].active) {
        return false;
    }
    if (!obligation.fixed_context) {
        obligation.captured_context = current_access_context();
    }
    auto& obligations = access_captures_[index].obligations;
    bool duplicate = std::any_of(
        obligations.begin(), obligations.end(),
        [&](const AccessObligation& existing) {
            return existing.kind == obligation.kind &&
                existing.member == obligation.member &&
                existing.access_owner == obligation.access_owner &&
                existing.declared_access == obligation.declared_access &&
                existing.declaring_class == obligation.declaring_class &&
                existing.derived_type == obligation.derived_type &&
                existing.base_type == obligation.base_type &&
                existing.designating_class == obligation.designating_class &&
                existing.object_class == obligation.object_class &&
                existing.fixed_context == obligation.fixed_context &&
                existing.loc.offset == obligation.loc.offset;
        });
    if (!duplicate) {
        obligations.push_back(std::move(obligation));
    }
    return true;
}

bool Session::finish_access_capture(AccessCaptureToken capture,
                                    cir::EntityId declaring_entity) {
    if (!capture.valid()) {
        return true;
    }
    uint32_t index = capture.index - 1;
    suspend_access_capture(capture);
    if (index >= access_captures_.size() ||
        !access_captures_[index].retained) {
        return true;
    }
    AccessContext context = access_context_for_entity(declaring_entity);
    bool allowed = true;
    std::unordered_set<uint32_t> failed_locations;
    for (const AccessObligation& obligation :
         access_captures_[index].obligations) {
        if (failed_locations.contains(obligation.loc.offset)) {
            continue;
        }
        if (!evaluate_access_obligation(obligation, context)) {
            allowed = false;
            failed_locations.insert(obligation.loc.offset);
        }
    }
    access_captures_[index].retained = false;
    access_captures_[index].obligations.clear();
    return allowed;
}

void Session::discard_access_capture(AccessCaptureToken capture) {
    if (!capture.valid()) {
        return;
    }
    uint32_t index = capture.index - 1;
    suspend_access_capture(capture);
    if (index < access_captures_.size()) {
        access_captures_[index].retained = false;
        access_captures_[index].obligations.clear();
    }
}

bool Session::check_member_access_in_context(
    cir::EntityId member,
    cir::RecordMemberAccess access,
    const AccessContext& context,
    SrcLoc loc,
    cir::EntityId access_owner,
    bool report) {
    cir::EntityId owner = access_owner;
    if (!owner.valid() && file_.valid(member)) {
        const cir::Entity& declaration = file_.entity(member);
        owner = declaration.declaring_record.valid()
            ? declaration.declaring_record
            : declaration.parent;
    }
    if (member_access_allowed_from(owner,
                                   access,
                                   context.accessing_record,
                                   context.accessing_function,
                                   !context.exact ||
                                       context.accessing_function.valid())) {
        return true;
    }
    if (!report) {
        return false;
    }
    std::string member_name = file_.valid(member) &&
                                      file_.entity(member).name.valid()
        ? std::string(file_.name(file_.entity(member).name))
        : std::string("<member>");
    std::string owner_name =
        owner.valid() && file_.valid(owner) && file_.entity(owner).name.valid()
            ? std::string(file_.name(file_.entity(owner).name))
            : std::string("<class>");
    report_error("'" + member_name + "' is a " +
                     (access == cir::RecordMemberAccess::Private ? "private"
                                                                 : "protected") +
                     " member of '" + owner_name + "'",
                 loc);
    return false;
}

bool Session::check_member_lookup_base_access_in_context(
    const std::vector<std::vector<AccessBaseStep>>& routes,
    cir::TypeId declaring_class,
    cir::TypeId derived_type,
    const AccessContext& context,
    SrcLoc loc,
    bool report) {
    if (routes.empty() ||
        std::any_of(routes.begin(), routes.end(),
                    [&](const std::vector<AccessBaseStep>& path) {
                        return std::all_of(
                            path.begin(), path.end(),
                            [&](const AccessBaseStep& step) {
                                return step.declared_access ==
                                           cir::RecordMemberAccess::Public ||
                                    member_access_allowed_from(
                                        step.derived_class,
                                        step.declared_access,
                                        context.accessing_record,
                                        context.accessing_function,
                                        !context.exact ||
                                            context.accessing_function.valid());
                            });
                    })) {
        return true;
    }
    if (!report) {
        return false;
    }
    report_error("cannot name member of inaccessible base class '" +
                     file_.format_type(declaring_class) + "' through '" +
                     file_.format_type(derived_type) + "'",
                 loc);
    return false;
}

bool Session::evaluate_access_obligation(
    const AccessObligation& obligation,
    const AccessContext& context,
    bool report) {
    switch (obligation.kind) {
        case AccessObligationKind::Member: {
            cir::EntityId owner = obligation.access_owner.valid()
                ? obligation.access_owner
                : (obligation.member.valid() && file_.valid(obligation.member)
                       ? file_.entity(obligation.member).parent
                       : cir::EntityId{});
            auto allowed_from = [&](const AccessContext& candidate) {
                if (member_access_allowed_from(
                    owner,
                    obligation.declared_access,
                    candidate.accessing_record,
                    candidate.accessing_function,
                    !candidate.exact ||
                        candidate.accessing_function.valid())) {
                    return true;
                }
                if (obligation.declared_access !=
                        cir::RecordMemberAccess::Protected ||
                    !obligation.designating_class.valid() ||
                    !owner.valid() || !file_.valid(owner)) {
                    return false;
                }
                cir::TypeId designating =
                    file_.resolved_type(obligation.designating_class);
                if (!file_.valid(designating) ||
                    file_.type(designating).kind != cir::TypeKind::Record) {
                    return false;
                }
                cir::TypeId owner_type =
                    file_.resolved_type(file_.entity(owner).type);
                if (designating != owner_type &&
                    !derived_to_base_path(designating, owner_type, nullptr)) {
                    return false;
                }
                cir::EntityId designating_record =
                    file_.record_entity(designating);
                return designating_record.valid() &&
                    member_access_allowed_from(
                        designating_record,
                        cir::RecordMemberAccess::Private,
                        candidate.accessing_record,
                        candidate.accessing_function,
                        !candidate.exact ||
                            candidate.accessing_function.valid());
            };
            const AccessContext& captured = obligation.captured_context;
            bool has_captured_context = captured.declaring_entity.valid() ||
                captured.accessing_record.valid() ||
                captured.accessing_function.valid() ||
                captured.lexical_context.valid() || captured.exact;
            if ((!obligation.fixed_context && allowed_from(context)) ||
                (has_captured_context && allowed_from(captured))) {
                return true;
            }
            return check_member_access_in_context(
                obligation.member, obligation.declared_access,
                obligation.fixed_context ? captured : context,
                obligation.loc, owner, report);
        }
        case AccessObligationKind::MemberLookupBase:
            return check_member_lookup_base_access_in_context(
                obligation.base_routes,
                obligation.declaring_class,
                obligation.derived_type,
                obligation.fixed_context ? obligation.captured_context
                                         : context,
                obligation.loc,
                report);
        case AccessObligationKind::BaseConversion:
            return check_base_path_access_in_context(
                obligation.storage_path,
                obligation.derived_type,
                obligation.base_type,
                context,
                obligation.loc);
    }
    return true;
}

bool Session::check_base_path_access_in_context(
    const std::vector<cir::EntityId>& path,
    cir::TypeId derived,
    cir::TypeId base,
    const AccessContext& context,
    SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode()) {
        return true;
    }

    auto vbase_route_accessible = [&](auto&& self,
                                      const cir::RecordFacts* record,
                                      cir::EntityId route_owner,
                                      cir::TypeId target) -> bool {
        if (!record) {
            return false;
        }
        for (const cir::RecordBaseFact& edge : record->bases) {
            if (edge.declared_access != cir::RecordMemberAccess::Public &&
                !(route_owner.valid() &&
                  member_access_allowed_from(route_owner,
                                             edge.declared_access,
                                             context.accessing_record,
                                             context.accessing_function,
                                             !context.exact ||
                                                 context.accessing_function
                                                     .valid()))) {
                continue;
            }
            cir::TypeId next = file_.resolved_type(edge.type.type);
            if (edge.is_virtual && next == target) {
                return true;
            }
            if (self(self, file_.record_facts_for_type(next),
                     edge.record_entity, target)) {
                return true;
            }
        }
        return false;
    };
    for (cir::EntityId step : path) {
        const cir::RecordFieldFact* field = file_.field_fact(step);
        if (!field || !field->is_base_subobject) {
            continue;
        }
        cir::EntityId owner = step.valid() && file_.valid(step)
            ? file_.entity(step).parent
            : cir::EntityId{};
        if (field->is_virtual_base_storage) {
            cir::TypeId vbase_type = file_.resolved_type(field->type.type);
            if (owner.valid() &&
                vbase_route_accessible(vbase_route_accessible,
                                       file_.record_facts_for_type(
                                           file_.entity(owner).type),
                                       owner, vbase_type)) {
                continue;
            }
            report_error("cannot convert '" + file_.format_type(derived) +
                             "' to inaccessible virtual base class '" +
                             file_.format_type(base) + "'",
                         loc);
            return false;
        }
        if (field->declared_access == cir::RecordMemberAccess::Public) {
            continue;
        }
        if (owner.valid() &&
            member_access_allowed_from(owner,
                                       field->declared_access,
                                       context.accessing_record,
                                       context.accessing_function,
                                       !context.exact ||
                                           context.accessing_function.valid())) {
            continue;
        }
        report_error(
            "cannot convert '" + file_.format_type(derived) + "' to " +
                (field->declared_access == cir::RecordMemberAccess::Private
                     ? "private"
                     : "protected") +
                " base class '" + file_.format_type(base) + "'",
            loc);
        return false;
    }
    return true;
}

bool Session::check_base_path_access(const std::vector<cir::EntityId>& path,
                                     cir::TypeId derived,
                                     cir::TypeId base,
                                     SrcLoc loc) {
    if (template_argument_access_exemption_depth_ != 0) {
        return true;
    }
    AccessObligation obligation;
    obligation.kind = AccessObligationKind::BaseConversion;
    obligation.storage_path = path;
    obligation.derived_type = derived;
    obligation.base_type = base;
    obligation.loc = loc;
    if (capture_access_obligation(obligation)) {
        return true;
    }
    return check_base_path_access_in_context(path, derived, base,
                                             current_access_context(), loc);
}

bool Session::protected_member_object_access_allowed(
    cir::EntityId member_owner,
    cir::TypeId object_type) {
    if (!lang_opts_.is_cxx_mode() ||
        template_argument_access_exemption_depth_ != 0) {
        return true;
    }
    cir::TypeId owner_type = member_owner.valid() && file_.valid(member_owner)
        ? file_.resolved_type(file_.entity(member_owner).type)
        : cir::TypeId{};
    if (!owner_type.valid()) {
        return true;
    }

    std::vector<cir::TypeId> candidates;
    std::vector<cir::TypeId> worklist{file_.resolved_type(object_type)};
    while (!worklist.empty()) {
        cir::TypeId current = worklist.back();
        worklist.pop_back();
        if (!current.valid() || !file_.valid(current) ||
            std::find(candidates.begin(), candidates.end(), current) !=
                candidates.end()) {
            continue;
        }
        candidates.push_back(current);
        const cir::RecordFacts* facts = file_.record_facts_for_type(current);
        if (!facts) {
            continue;
        }
        for (const cir::RecordBaseFact& edge : facts->bases) {
            worklist.push_back(file_.resolved_type(edge.type.type));
        }
        for (const cir::RecordFacts::VirtualBase& vbase :
             facts->virtual_bases) {
            worklist.push_back(file_.resolved_type(vbase.type.type));
        }
    }
    for (cir::TypeId candidate : candidates) {
        if (candidate != owner_type &&
            analyze_derived_to_base_path(candidate, owner_type).kind ==
                DerivedToBasePathKind::NotFound) {
            continue;
        }
        const cir::RecordFacts* facts = file_.record_facts_for_type(candidate);
        if (!facts || !facts->entity.valid()) {
            continue;
        }

        if (member_access_allowed(facts->entity,
                                  cir::RecordMemberAccess::Private)) {
            return true;
        }
    }
    return false;
}

Session::DerivedToBasePathResult Session::analyze_derived_to_base_path(
    cir::TypeId derived_type,
    cir::TypeId base_type) const {
    DerivedToBasePathResult result;
    cir::TypeId derived = file_.resolved_type(derived_type);
    cir::TypeId base = file_.resolved_type(base_type);
    if (!file_.valid(derived) || !file_.valid(base) || derived == base) {
        return result;
    }
    const cir::RecordFacts* facts = file_.record_facts_for_type(derived);
    if (!facts) {
        return result;
    }

    auto add_candidate = [&](const std::vector<cir::EntityId>& path) {
        if (result.kind == DerivedToBasePathKind::NotFound) {
            result.kind = DerivedToBasePathKind::Unique;
            result.path = path;
        } else {
            result.kind = DerivedToBasePathKind::Ambiguous;
            result.path.clear();
        }
    };

    auto collect_nonvirtual = [&](auto&& self,
                                  cir::TypeId current_type,
                                  std::vector<cir::EntityId>& path) -> void {
        if (result.kind == DerivedToBasePathKind::Ambiguous) {
            return;
        }
        const cir::RecordFacts* current =
            file_.record_facts_for_type(file_.resolved_type(current_type));
        if (!current) {
            return;
        }
        for (const cir::RecordFieldFact& field : current->fields) {
            if (!field.is_base_subobject || field.is_virtual_base_storage) {
                continue;
            }
            cir::TypeId field_type = file_.resolved_type(field.type.type);
            path.push_back(field.entity);
            if (field_type == base) {
                add_candidate(path);
            } else {
                self(self, field_type, path);
            }
            path.pop_back();
            if (result.kind == DerivedToBasePathKind::Ambiguous) {
                return;
            }
        }
    };

    std::vector<cir::EntityId> path;
    collect_nonvirtual(collect_nonvirtual, derived, path);
    if (result.kind == DerivedToBasePathKind::Ambiguous) {
        return result;
    }

    for (const cir::RecordFacts::VirtualBase& vbase : facts->virtual_bases) {
        cir::TypeId vbase_type = file_.resolved_type(vbase.type.type);
        path.assign(1, vbase.storage_field);
        if (vbase_type == base) {
            add_candidate(path);
        } else {
            collect_nonvirtual(collect_nonvirtual, vbase_type, path);
        }
        if (result.kind == DerivedToBasePathKind::Ambiguous) {
            return result;
        }
    }
    return result;
}

bool Session::derived_to_base_path(cir::TypeId derived_type,
                                   cir::TypeId base_type,
                                   std::vector<cir::EntityId>* path_out) const {
    DerivedToBasePathResult result =
        analyze_derived_to_base_path(derived_type, base_type);
    if (result.kind != DerivedToBasePathKind::Unique) {
        return false;
    }
    if (path_out) {
        *path_out = std::move(result.path);
    }
    return true;
}

uint32_t Session::base_declaration_index(
    const cir::RecordFacts& facts,
    const cir::RecordFieldFact& field) const {
    cir::EntityId field_record =
        file_.record_entity(file_.resolved_type(field.type.type));
    for (const cir::RecordBaseFact& base : facts.bases) {
        if (base.is_virtual == field.is_virtual_base_storage &&
            base.record_entity == field_record) {
            return base.declaration_index;
        }
    }
    return std::numeric_limits<uint32_t>::max();
}

void Session::add_pending_class_friend_type(cir::EntityId record,
                                            cir::TypeRef friend_type,
                                            bool is_pack_expansion,
                                            SrcLoc loc) {
    if (!record.valid() || !file_.valid(record) ||
        !friend_type.type.valid()) {
        return;
    }
    cir::RecordClassFriendGrant grant;
    grant.loc = loc;
    grant.is_pack_expansion = is_pack_expansion;
    cir::TypeId resolved = file_.resolved_type(friend_type.type);
    if (is_dependent_type(resolved)) {
        grant.kind = cir::RecordClassFriendGrantKind::DependentRecipe;
        grant.recipe_kind = cir::RecordClassFriendRecipeKind::DirectType;
        grant.type_pattern = friend_type;
    } else if (file_.valid(resolved) &&
               file_.type(resolved).kind == cir::TypeKind::Record) {
        grant.kind = cir::RecordClassFriendGrantKind::ExactRecord;
        grant.entity = file_.record_entity(resolved);
        if (!grant.entity.valid() || !file_.valid(grant.entity)) {
            return;
        }
    } else {

        return;
    }

    uint64_t key = static_cast<uint64_t>(record.index);
    auto& grants = tstate().pending_class_friends_[key];
    auto same_grant = [&](const cir::RecordClassFriendGrant& prior) {
        return prior.kind == grant.kind &&
               prior.recipe_kind == grant.recipe_kind &&
               prior.entity == grant.entity &&
               prior.type_pattern == grant.type_pattern &&
               prior.is_pack_expansion == grant.is_pack_expansion;
    };
    if (std::any_of(grants.begin(), grants.end(), same_grant)) {
        return;
    }
    grants.push_back(std::move(grant));
    track_speculative_rollback([this, key] {
        auto found = tstate().pending_class_friends_.find(key);
        if (found == tstate().pending_class_friends_.end()) {
            return;
        }
        if (!found->second.empty()) {
            found->second.pop_back();
        }
        if (found->second.empty()) {
            tstate().pending_class_friends_.erase(found);
        }
    });
}

void Session::add_pending_friend_class_template(cir::EntityId record,
                                                cir::EntityId template_entity) {
    if (!record.valid() || !template_entity.valid() ||
        !file_.valid(template_entity)) {
        return;
    }
    uint64_t key = static_cast<uint64_t>(record.index);
    auto& grants = tstate().pending_class_friends_[key];
    auto duplicate = std::find_if(
        grants.begin(), grants.end(),
        [&](const cir::RecordClassFriendGrant& grant) {
            return grant.kind ==
                       cir::RecordClassFriendGrantKind::PrimaryClassTemplate &&
                   grant.entity == template_entity;
        });
    if (duplicate != grants.end()) {
        return;
    }
    cir::RecordClassFriendGrant grant;
    grant.kind = cir::RecordClassFriendGrantKind::PrimaryClassTemplate;
    grant.entity = template_entity;
    grants.push_back(std::move(grant));
    track_speculative_rollback([this, key] {
        auto found = tstate().pending_class_friends_.find(key);
        if (found == tstate().pending_class_friends_.end()) {
            return;
        }
        if (!found->second.empty()) {
            found->second.pop_back();
        }
        if (found->second.empty()) {
            tstate().pending_class_friends_.erase(found);
        }
    });
}

void Session::add_pending_friend_function_template(
    cir::EntityId record,
    cir::EntityId template_entity) {
    if (!record.valid() || !template_entity.valid() ||
        !file_.valid(template_entity)) {
        return;
    }
    const TemplateInfo* info = template_info(template_entity);
    if (!info || info->is_class_template || info->is_alias_template ||
        info->is_variable_template || info->is_concept ||
        file_.entity(template_entity).kind != cir::EntityKind::Function) {
        return;
    }

    uint64_t key = static_cast<uint64_t>(record.index);
    auto& grants = tstate().pending_function_friends_[key];
    if (std::any_of(
            grants.begin(), grants.end(),
            [template_entity](const cir::RecordFunctionFriendGrant& grant) {
                return grant.kind ==
                           cir::RecordFunctionFriendGrantKind::
                               PrimaryFunctionTemplate &&
                       grant.entity == template_entity;
            })) {
        return;
    }
    cir::RecordFunctionFriendGrant grant;
    grant.kind =
        cir::RecordFunctionFriendGrantKind::PrimaryFunctionTemplate;
    grant.entity = template_entity;
    grant.name = file_.entity(template_entity).name;
    grant.type_pattern = file_.type_ref(info->pattern_type);
    grants.push_back(std::move(grant));
    track_speculative_rollback([this, key, template_entity] {
        auto found = tstate().pending_function_friends_.find(key);
        if (found == tstate().pending_function_friends_.end()) {
            return;
        }
        auto grant = std::find_if(
            found->second.begin(), found->second.end(),
            [template_entity](const cir::RecordFunctionFriendGrant& candidate) {
                return candidate.kind ==
                           cir::RecordFunctionFriendGrantKind::
                               PrimaryFunctionTemplate &&
                       candidate.entity == template_entity;
            });
        if (grant != found->second.end()) {
            found->second.erase(grant);
        }
        if (found->second.empty()) {
            tstate().pending_function_friends_.erase(found);
        }
    });
}

void Session::add_pending_friend_function_template_specialization(
    cir::EntityId record,
    cir::EntityId template_entity,
    std::vector<TemplateArgument> arguments,
    cir::TypeId function_type) {
    if (!record.valid() || !template_entity.valid() ||
        !file_.valid(template_entity) || !function_type.valid()) {
        return;
    }
    const TemplateInfo* info = template_info(template_entity);
    if (!info || info->is_class_template || info->is_alias_template ||
        info->is_variable_template || info->is_concept ||
        file_.entity(template_entity).kind != cir::EntityKind::Function) {
        return;
    }

    uint64_t key = static_cast<uint64_t>(record.index);
    cir::RecordFunctionFriendGrant grant;
    grant.kind = cir::RecordFunctionFriendGrantKind::
        FunctionTemplateSpecialization;
    grant.entity = template_entity;
    grant.name = file_.entity(template_entity).name;
    grant.arguments = std::move(arguments);
    grant.type_pattern = file_.type_ref(function_type);
    auto& grants = tstate().pending_function_friends_[key];
    std::string grant_key = template_memo_key(template_entity,
                                             grant.arguments);
    if (std::any_of(
            grants.begin(),
            grants.end(),
            [&](const cir::RecordFunctionFriendGrant& prior) {
                return prior.kind ==
                           cir::RecordFunctionFriendGrantKind::
                               FunctionTemplateSpecialization &&
                       prior.entity == template_entity &&
                       template_memo_key(prior.entity,
                                         prior.arguments) == grant_key;
            })) {
        return;
    }
    grants.push_back(std::move(grant));
    track_speculative_rollback([this, key, template_entity, grant_key] {
        auto found = tstate().pending_function_friends_.find(key);
        if (found == tstate().pending_function_friends_.end()) {
            return;
        }
        auto grant = std::find_if(
            found->second.begin(),
            found->second.end(),
            [&](const cir::RecordFunctionFriendGrant& prior) {
                return prior.kind ==
                           cir::RecordFunctionFriendGrantKind::
                               FunctionTemplateSpecialization &&
                       prior.entity == template_entity &&
                       template_memo_key(prior.entity,
                                         prior.arguments) == grant_key;
            });
        if (grant != found->second.end()) {
            found->second.erase(grant);
        }
        if (found->second.empty()) {
            tstate().pending_function_friends_.erase(found);
        }
    });
}

void Session::add_pending_dependent_member_friend_type(
    cir::EntityId record,
    cir::TypeRef friend_type,
    const std::vector<TemplateParameter>& parameters,
    SrcLoc loc) {
    if (!record.valid() || !file_.valid(record) || !friend_type.type.valid()) {
        return;
    }
    cir::TypeId type = file_.resolved_type(friend_type.type);
    if (!file_.valid(type) ||
        file_.type(type).kind != cir::TypeKind::DependentName) {
        return;
    }
    const auto& dependent =
        std::get<cir::DependentNameTypePayload>(file_.type_payload(type));
    if (!dependent.member_name.valid() ||
        !dependent.qualifier_type.type.valid()) {
        return;
    }
    cir::TypeId qualifier =
        file_.resolved_type(dependent.qualifier_type.type);
    if (!file_.valid(qualifier) ||
        file_.type(qualifier).kind != cir::TypeKind::Record) {
        return;
    }
    cir::EntityId qualifier_record = file_.record_entity(qualifier);
    const cir::TemplateSpecializationFact* qualifier_fact =
        qualifier_record.valid() ? file_.template_specialization(qualifier_record)
                                 : nullptr;
    const TemplateInfo* qualifier_template =
        qualifier_fact && qualifier_fact->template_entity.valid()
            ? template_info(qualifier_fact->template_entity)
            : nullptr;
    if (!qualifier_template || !qualifier_template->is_class_template) {
        report_error(
            "dependent member friend declaration qualifier must name a class template specialization",
            loc);
        return;
    }

    cir::RecordClassFriendGrant grant;
    grant.kind = cir::RecordClassFriendGrantKind::DependentRecipe;
    grant.recipe_kind =
        cir::RecordClassFriendRecipeKind::MemberOfClassTemplate;
    grant.type_pattern = cir::TypeRef{
        qualifier,
        dependent.qualifier_type.qualifiers,
        dependent.qualifier_type.memory_space};
    grant.member_name = dependent.member_name;
    grant.loc = loc;
    for (const TemplateParameter& parameter : parameters) {
        if (parameter.is_parameter_pack) {
            report_error(
                "template parameter packs in dependent member friend type declarations are not supported yet",
                parameter.loc.isInvalid() ? loc : parameter.loc);
            return;
        }
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                grant.required_type_params.push_back(parameter.index);
                break;
            case TemplateParameterKind::NonType:
                grant.required_value_params.push_back(parameter.index);
                break;
            case TemplateParameterKind::Template:
                grant.required_template_params.push_back(parameter.index);
                break;
        }
    }
    if (!dependent_member_friend_parameters_deducible_from_qualifier(
            grant.type_pattern,
            grant.required_type_params,
            grant.required_value_params,
            grant.required_template_params)) {
        report_error(
            "template parameters of a dependent member friend declaration shall be deducible from its class template-id",
            loc);
        return;
    }

    uint64_t key = static_cast<uint64_t>(record.index);
    tstate().pending_class_friends_[key].push_back(std::move(grant));
    track_speculative_rollback([this, key] {
        auto found = tstate().pending_class_friends_.find(key);
        if (found == tstate().pending_class_friends_.end()) {
            return;
        }
        if (!found->second.empty()) {
            found->second.pop_back();
        }
        if (found->second.empty()) {
            tstate().pending_class_friends_.erase(found);
        }
    });
}

void Session::add_pending_dependent_member_friend_function(
    cir::EntityId record,
    cir::TypeRef qualifier_pattern,
    std::string_view name,
    cir::TypeRef function_type_pattern,
    const std::vector<TemplateParameter>& parameters,
    SrcLoc loc) {
    if (!record.valid() || !file_.valid(record) || name.empty() ||
        !qualifier_pattern.type.valid() || !function_type_pattern.type.valid()) {
        return;
    }
    cir::TypeId qualifier = file_.resolved_type(qualifier_pattern.type);
    if (!file_.valid(qualifier) ||
        file_.type(qualifier).kind != cir::TypeKind::Record) {
        report_error(
            "dependent member friend declaration qualifier must name a class template specialization",
            loc);
        return;
    }
    cir::EntityId qualifier_record = file_.record_entity(qualifier);
    const cir::TemplateSpecializationFact* qualifier_fact =
        qualifier_record.valid() ? file_.template_specialization(qualifier_record)
                                 : nullptr;
    const TemplateInfo* qualifier_template =
        qualifier_fact && qualifier_fact->template_entity.valid()
            ? template_info(qualifier_fact->template_entity)
            : nullptr;
    if (!qualifier_template || !qualifier_template->is_class_template) {
        report_error(
            "dependent member friend declaration qualifier must name a class template specialization",
            loc);
        return;
    }
    cir::TypeId function_type = file_.resolved_type(function_type_pattern.type);
    if (!file_.valid(function_type) ||
        file_.type(function_type).kind != cir::TypeKind::Function) {
        report_error(
            "dependent member friend function declaration must name a function",
            loc);
        return;
    }

    cir::RecordFunctionFriendGrant grant;
    grant.kind =
        cir::RecordFunctionFriendGrantKind::DependentMemberFunction;
    grant.qualifier_pattern = cir::TypeRef{
        qualifier,
        qualifier_pattern.qualifiers,
        qualifier_pattern.memory_space};
    grant.member_name = file_.intern_name(name);
    grant.type_pattern = cir::TypeRef{
        function_type,
        function_type_pattern.qualifiers,
        function_type_pattern.memory_space};
    grant.loc = loc;
    for (const TemplateParameter& parameter : parameters) {
        if (parameter.is_parameter_pack) {
            report_error(
                "template parameter packs in dependent member friend function declarations are not supported yet",
                parameter.loc.isInvalid() ? loc : parameter.loc);
            return;
        }
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                grant.required_type_params.push_back(parameter.index);
                break;
            case TemplateParameterKind::NonType:
                grant.required_value_params.push_back(parameter.index);
                break;
            case TemplateParameterKind::Template:
                grant.required_template_params.push_back(parameter.index);
                break;
        }
    }
    if (!dependent_member_friend_parameters_deducible_from_qualifier(
            grant.qualifier_pattern,
            grant.required_type_params,
            grant.required_value_params,
            grant.required_template_params)) {
        report_error(
            "template parameters of a dependent member friend declaration shall be deducible from its class template-id",
            loc);
        return;
    }

    uint64_t key = static_cast<uint64_t>(record.index);
    tstate().pending_function_friends_[key].push_back(std::move(grant));
    track_speculative_rollback([this, key] {
        auto found = tstate().pending_function_friends_.find(key);
        if (found == tstate().pending_function_friends_.end()) {
            return;
        }
        if (!found->second.empty()) {
            found->second.pop_back();
        }
        if (found->second.empty()) {
            tstate().pending_function_friends_.erase(found);
        }
    });
}

void Session::add_pending_dependent_member_friend_function_template(
    cir::EntityId record,
    cir::TypeRef qualifier_pattern,
    std::string_view name,
    cir::TypeRef function_type_pattern,
    const std::vector<TemplateParameter>& friend_parameters,
    const std::vector<TemplateParameter>& member_template_parameters,
    SrcLoc loc) {
    if (!record.valid() || !file_.valid(record) || name.empty() ||
        !qualifier_pattern.type.valid() || !function_type_pattern.type.valid()) {
        return;
    }
    cir::TypeId qualifier = file_.resolved_type(qualifier_pattern.type);
    if (!file_.valid(qualifier) ||
        file_.type(qualifier).kind != cir::TypeKind::Record) {
        report_error(
            "dependent member friend declaration qualifier must name a class template specialization",
            loc);
        return;
    }
    cir::EntityId qualifier_record = file_.record_entity(qualifier);
    const cir::TemplateSpecializationFact* qualifier_fact =
        qualifier_record.valid() ? file_.template_specialization(qualifier_record)
                                 : nullptr;
    const TemplateInfo* qualifier_template =
        qualifier_fact && qualifier_fact->template_entity.valid()
            ? template_info(qualifier_fact->template_entity)
            : nullptr;
    if (!qualifier_template || !qualifier_template->is_class_template) {
        report_error(
            "dependent member friend declaration qualifier must name a class template specialization",
            loc);
        return;
    }
    cir::TypeId function_type = file_.resolved_type(function_type_pattern.type);
    if (!file_.valid(function_type) ||
        file_.type(function_type).kind != cir::TypeKind::Function) {
        report_error(
            "dependent member friend function template declaration must name a function",
            loc);
        return;
    }

    cir::RecordFunctionFriendGrant grant;
    grant.kind = cir::RecordFunctionFriendGrantKind::
        DependentMemberFunctionTemplate;
    grant.qualifier_pattern = cir::TypeRef{
        qualifier,
        qualifier_pattern.qualifiers,
        qualifier_pattern.memory_space};
    grant.member_name = file_.intern_name(name);
    grant.type_pattern = cir::TypeRef{
        function_type,
        function_type_pattern.qualifiers,
        function_type_pattern.memory_space};
    grant.loc = loc;
    grant.member_template_parameters =
        template_parameter_patterns_from(member_template_parameters);
    for (const TemplateParameter& parameter : friend_parameters) {
        if (parameter.is_parameter_pack) {
            report_error(
                "template parameter packs in dependent member friend function template declarations are not supported yet",
                parameter.loc.isInvalid() ? loc : parameter.loc);
            return;
        }
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                grant.required_type_params.push_back(parameter.index);
                break;
            case TemplateParameterKind::NonType:
                grant.required_value_params.push_back(parameter.index);
                break;
            case TemplateParameterKind::Template:
                grant.required_template_params.push_back(parameter.index);
                break;
        }
    }
    for (const TemplateParameter& parameter : member_template_parameters) {
        if (parameter.is_parameter_pack) {
            report_error(
                "template parameter packs in dependent member friend function template declarations are not supported yet",
                parameter.loc.isInvalid() ? loc : parameter.loc);
            return;
        }
    }
    if (!dependent_member_friend_parameters_deducible_from_qualifier(
            grant.qualifier_pattern,
            grant.required_type_params,
            grant.required_value_params,
            grant.required_template_params)) {
        report_error(
            "template parameters of a dependent member friend declaration shall be deducible from its class template-id",
            loc);
        return;
    }

    uint64_t key = static_cast<uint64_t>(record.index);
    tstate().pending_function_friends_[key].push_back(
        std::move(grant));
    track_speculative_rollback([this, key] {
        auto found = tstate().pending_function_friends_.find(key);
        if (found == tstate().pending_function_friends_.end()) {
            return;
        }
        if (!found->second.empty()) {
            found->second.pop_back();
        }
        if (found->second.empty()) {
            tstate().pending_function_friends_.erase(found);
        }
    });
}

cir::EntityId Session::friend_function_entity(
    std::string_view name,
    cir::TypeId type,
    cir::DeclContextId context,
    cir::ModuleAttachmentId module_attachment,
    cir::EntityId signature_owner) const {
    if (name.empty() || !type.valid() || !context.valid()) {
        return {};
    }
    cir::TypeRef requested{file_.resolved_type(type),
                           cir::QualNone,
                           cir::MemorySpace::Default};
    auto declaration_corresponds = [&](cir::TypeRef candidate) {
        cir::TypeId candidate_type = file_.resolved_type(candidate.type);
        if (!function_signatures_match(requested.type, candidate_type)) {
            return false;
        }
        const auto* requested_function =
            std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(requested.type));
        const auto* candidate_function =
            std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(candidate_type));
        return requested_function && candidate_function &&
               types_compatible(requested_function->return_type,
                                candidate_function->return_type);
    };
    for (const cir::RecordFunctionFriendGrant& grant :
         tstate().friend_function_identities_) {
        if (grant.kind !=
                cir::RecordFunctionFriendGrantKind::ExactFunction ||
            grant.context != context ||
            grant.module_attachment != module_attachment ||
            grant.signature_owner != signature_owner ||
            !grant.entity.valid() ||
            !file_.valid(grant.entity) || !grant.name.valid() ||
            file_.name(grant.name) != name) {
            continue;
        }
        if (declaration_corresponds(grant.type_pattern)) {
            return grant.entity;
        }
    }
    const cir::DeclContext& declaration_context = file_.decl_context(context);
    if (declaration_context.kind == cir::DeclContextKind::Record &&
        declaration_context.owner.valid() &&
        file_.valid(declaration_context.owner)) {
        if (const cir::RecordFacts* facts =
                file_.record_facts(declaration_context.owner)) {
            for (const cir::RecordMethodFact& method : facts->methods) {
                if (!method.name.valid() || file_.name(method.name) != name ||
                    !method.entity.valid() || !file_.valid(method.entity)) {
                    continue;
                }
                if (declaration_corresponds(method.type)) {
                    return method.entity;
                }
            }
        }
    }
    const cir::Binding* binding =
        file_.lookup_ordinary_binding(context, name, false);
    if (binding && file_.binding_is_callable(*binding)) {
        for (cir::EntityId entity : binding->entities) {
            if (!entity.valid() || !file_.valid(entity) ||
                file_.entity(entity).kind != cir::EntityKind::Function) {
                continue;
            }
            cir::TypeRef candidate{file_.resolved_type(file_.entity(entity).type),
                                   cir::QualNone,
                                   cir::MemorySpace::Default};
            if (declaration_corresponds(candidate)) {
                return entity;
            }
        }
    }
    return {};
}

cir::EntityId Session::add_pending_friend_function(
    cir::EntityId record,
    std::string_view name,
    cir::TypeId type,
    cir::DeclContextId context,
    SrcLoc loc,
    cir::EntityId signature_owner,
    bool require_existing,
    cir::OperatorFunctionIdentity operator_function) {
    if (!record.valid() || name.empty() || !type.valid() ||
        !context.valid()) {
        return {};
    }
    cir::ModuleAttachmentId module_attachment{};
    if (file_.valid(record)) {
        module_attachment = file_.entity(record).module_attachment;
    }
    cir::EntityId entity = friend_function_entity(
        name, type, context, module_attachment, signature_owner);
    bool created_hidden_entity = !entity.valid();
    if (created_hidden_entity && require_existing) {
        report_error(
            "friend declaration in a local class must match a declaration in the innermost enclosing non-class scope",
            loc);
        return {};
    }
    if (!created_hidden_entity) {
        if (const cir::RecordMethodFact* method = file_.method_fact(entity)) {
            check_member_access_from(entity,
                                     method->declared_access,
                                     record,
                                     {},
                                     loc);
        }
    }
    if (created_hidden_entity) {
        entity = builder_.add_entity(cir::EntityKind::Function,
                                     name,
                                     type,
                                     {},
                                     loc);
        file_.entity_mut(entity).is_definition = false;
        file_.entity_mut(entity).linkage = cir::LinkageKind::External;
        file_.entity_mut(entity).is_extern_c = in_extern_c_linkage();
        file_.entity_mut(entity).lexical_context = current_decl_context();
        file_.entity_mut(entity).semantic_context = context;
        file_.entity_mut(entity).module_attachment = module_attachment;
    }
    if (operator_function.valid()) {
        file_.entity_mut(entity).operator_function = operator_function;
    }

    uint64_t key = static_cast<uint64_t>(record.index);
    cir::RecordFunctionFriendGrant grant;
    grant.kind = cir::RecordFunctionFriendGrantKind::ExactFunction;
    grant.name = file_.intern_name(name);
    grant.context = context;
    grant.module_attachment = module_attachment;
    grant.signature_owner = signature_owner;
    grant.type_pattern = file_.type_ref(type);
    grant.entity = entity;
    grant.loc = loc;
    auto& pending = tstate().pending_function_friends_[key];
    bool inserted_pending_grant = std::none_of(
            pending.begin(), pending.end(),
            [entity](const cir::RecordFunctionFriendGrant& prior) {
                return prior.kind ==
                           cir::RecordFunctionFriendGrantKind::ExactFunction &&
                       prior.entity == entity;
            });
    if (inserted_pending_grant) {
        pending.push_back(grant);
    }
    bool inserted_friend_identity =
        std::none_of(tstate().friend_function_identities_.begin(),
                     tstate().friend_function_identities_.end(),
                     [entity](const cir::RecordFunctionFriendGrant& prior) {
                         return prior.entity == entity;
                     });
    if (inserted_friend_identity) {
        tstate().friend_function_identities_.push_back(grant);
    }
    track_speculative_rollback([this, key, entity, inserted_pending_grant,
                                inserted_friend_identity] {
        auto found = tstate().pending_function_friends_.find(key);
        if (inserted_pending_grant &&
            found != tstate().pending_function_friends_.end()) {
            std::erase_if(
                found->second,
                [entity](const cir::RecordFunctionFriendGrant& grant) {
                    return grant.kind ==
                               cir::RecordFunctionFriendGrantKind::
                                   ExactFunction &&
                           grant.entity == entity;
                });
            if (found->second.empty()) {
                tstate().pending_function_friends_.erase(found);
            }
        }
        if (inserted_friend_identity) {
            auto identity = std::find_if(
                tstate().friend_function_identities_.begin(),
                tstate().friend_function_identities_.end(),
                [entity](const cir::RecordFunctionFriendGrant& grant) {
                    return grant.entity == entity;
                });
            if (identity != tstate().friend_function_identities_.end()) {
                tstate().friend_function_identities_.erase(identity);
            }
        }
    });
    return entity;
}

bool Session::dependent_member_friend_type_matches(
    cir::EntityId record,
    const cir::RecordClassFriendGrant& grant) const {
    if (!record.valid() || !file_.valid(record) ||
        !grant.type_pattern.type.valid()) {
        return false;
    }
    const cir::Entity& nested = file_.entity(record);
    if (!nested.name.valid() || nested.name != grant.member_name) {
        return false;
    }

    cir::EntityId enclosing{};
    if (nested.parent.valid() && file_.valid(nested.parent) &&
        file_.entity(nested.parent).kind == cir::EntityKind::Record) {
        enclosing = nested.parent;
    } else if (nested.semantic_context.valid()) {
        cir::DeclContextId parent_context =
            file_.decl_context(nested.semantic_context).parent;
        if (parent_context.valid()) {
            cir::EntityId owner = file_.decl_context(parent_context).owner;
            if (owner.valid() && file_.valid(owner) &&
                file_.entity(owner).kind == cir::EntityKind::Record) {
                enclosing = owner;
            }
        }
    }
    if (!enclosing.valid()) {
        return false;
    }
    PatternBindings bindings;
    return dependent_member_friend_qualifier_matches(
               enclosing,
               grant.type_pattern,
               bindings) &&
           dependent_member_friend_parameters_deduced(
               grant.required_type_params,
               grant.required_value_params,
               grant.required_template_params,
               bindings);
}

bool Session::dependent_member_friend_function_matches(
    cir::EntityId function,
    const cir::RecordFunctionFriendGrant& grant) const {
    if (!function.valid() || !file_.valid(function) ||
        !grant.qualifier_pattern.type.valid() ||
        !grant.type_pattern.type.valid()) {
        return false;
    }
    const cir::Entity& entity = file_.entity(function);
    if (!entity.name.valid() || entity.name != grant.member_name ||
        !entity.parent.valid() || !file_.valid(entity.parent) ||
        file_.entity(entity.parent).kind != cir::EntityKind::Record ||
        !entity.type.valid()) {
        return false;
    }

    PatternBindings bindings;
    if (!dependent_member_friend_qualifier_matches(entity.parent,
                                                   grant.qualifier_pattern,
                                                   bindings) ||
        !dependent_member_friend_parameters_deduced(
            grant.required_type_params,
            grant.required_value_params,
            grant.required_template_params,
            bindings)) {
        return false;
    }

    PatternBindings function_bindings = bindings;
    return unify_type_pattern(grant.type_pattern.type,
                              entity.type,
                              function_bindings);
}

bool Session::dependent_member_friend_function_template_matches(
    cir::EntityId function,
    const cir::RecordFunctionFriendGrant& grant) const {
    if (!function.valid() || !file_.valid(function) ||
        !grant.qualifier_pattern.type.valid() ||
        !grant.type_pattern.type.valid()) {
        return false;
    }

    cir::EntityId template_entity = function;
    if (const cir::TemplateSpecializationFact* fact =
            file_.template_specialization(function);
        fact && fact->template_entity.valid()) {
        template_entity = fact->template_entity;
    }
    const TemplateInfo* info = template_info(template_entity);
    if (!info && template_entity == function) {
        info = validating_template_info();
    }
    if (!info || !info->entity.valid() || !file_.valid(info->entity) ||
        !info->pattern_type.valid()) {
        return false;
    }

    const cir::Entity& entity = file_.entity(info->entity);
    if (!entity.name.valid() || entity.name != grant.member_name ||
        !entity.parent.valid() || !file_.valid(entity.parent) ||
        file_.entity(entity.parent).kind != cir::EntityKind::Record) {
        return false;
    }

    PatternBindings bindings;
    if (!dependent_member_friend_qualifier_matches(entity.parent,
                                                   grant.qualifier_pattern,
                                                   bindings) ||
        !dependent_member_friend_parameters_deduced(
            grant.required_type_params,
            grant.required_value_params,
            grant.required_template_params,
            bindings) ||
        !dependent_member_friend_template_parameter_lists_match(
            grant.member_template_parameters,
            info->parameters,
            bindings)) {
        return false;
    }

    std::vector<std::pair<cir::TypeId, cir::TypeId>> inner_type_params;
    inner_type_params.reserve(grant.member_template_parameters.size());
    for (size_t i = 0; i < grant.member_template_parameters.size() &&
                       i < info->parameters.size();
         ++i) {
        const cir::TemplateParameterPattern& pattern =
            grant.member_template_parameters[i];
        const TemplateParameter& actual = info->parameters[i];
        if (pattern.kind == cir::TemplateParameterPatternKind::Type &&
            actual.kind == TemplateParameterKind::Type &&
            pattern.type_param_type.valid() &&
            actual.type_param_type.valid()) {
            inner_type_params.push_back(
                {pattern.type_param_type, actual.type_param_type});
        }
    }
    return dependent_member_friend_template_type_corresponds(
        grant.type_pattern.type,
        info->pattern_type,
        bindings,
        inner_type_params,
        DependentTypeCorrespondenceMode::MatchPattern);
}

bool Session::member_access_allowed(cir::EntityId member_owner,
                                    cir::RecordMemberAccess access) const {
    AccessContext context = current_access_context();
    return member_access_allowed_from(member_owner, access,
                                      context.accessing_record,
                                      context.accessing_function);
}

bool Session::member_access_allowed_from(
    cir::EntityId member_owner,
    cir::RecordMemberAccess access,
    cir::EntityId accessing_record,
    cir::EntityId accessing_function,
    bool infer_active_template_function) const {
    if (access == cir::RecordMemberAccess::Public || !member_owner.valid()) {
        return true;
    }
    if (!accessing_record.valid() && accessing_function.valid() &&
        file_.valid(accessing_function)) {
        cir::EntityId parent = file_.entity(accessing_function).parent;
        if (parent.valid() && file_.valid(parent) &&
            file_.entity(parent).kind == cir::EntityKind::Record) {
            accessing_record = parent;
        }
    }
    auto enclosing_record = [&](cir::EntityId record) {
        if (!record.valid() || !file_.valid(record)) {
            return cir::EntityId{};
        }
        cir::DeclContextId context = file_.entity(record).semantic_context;
        if (!context.valid() || !file_.valid(context)) {
            return cir::EntityId{};
        }
        for (cir::DeclContextId parent = file_.decl_context(context).parent;
             parent.valid() && file_.valid(parent);
             parent = file_.decl_context(parent).parent) {
            const cir::DeclContext& parent_context =
                file_.decl_context(parent);
            if (parent_context.kind == cir::DeclContextKind::Record &&
                parent_context.owner.valid()) {
                return parent_context.owner;
            }
        }
        return cir::EntityId{};
    };

    if (const cir::RecordFacts* owner_facts = file_.record_facts(member_owner);
        owner_facts) {
        auto exact_records_correspond = [&](cir::EntityId lhs,
                                            cir::EntityId rhs) {
            if (!lhs.valid() || !rhs.valid() || !file_.valid(lhs) ||
                !file_.valid(rhs)) {
                return false;
            }
            if (lhs == rhs) {
                return true;
            }
            cir::EntityId lhs_template{};
            cir::EntityId rhs_template{};
            std::vector<TemplateArgument> lhs_arguments;
            std::vector<TemplateArgument> rhs_arguments;
            return class_template_arguments_for_record(lhs,
                                                       &lhs_template,
                                                       &lhs_arguments) &&
                   class_template_arguments_for_record(rhs,
                                                       &rhs_template,
                                                       &rhs_arguments) && [&] {
                       if (!lhs_template.valid() ||
                           lhs_template != rhs_template) {
                           return false;
                       }

                       for (const auto& frame :
                            tstate().current_instantiation_frames_) {
                           if (frame.memo_key.empty() &&
                               frame.record == rhs) {
                               return true;
                           }
                       }
                       return lhs_arguments.size() == rhs_arguments.size() &&
                           std::equal(
                               lhs_arguments.begin(),
                               lhs_arguments.end(),
                               rhs_arguments.begin(),
                               [&](const TemplateArgument& lhs_argument,
                                   const TemplateArgument& rhs_argument) {
                                   return template_arguments_equivalent(
                                       lhs_argument, rhs_argument);
                               });
                   }();
        };
        auto class_friend = [&](cir::EntityId entity) {
            if (!entity.valid() || !file_.valid(entity)) {
                return false;
            }
            for (const cir::RecordClassFriendGrant& grant :
                 owner_facts->class_friends) {
                switch (grant.kind) {
                    case cir::RecordClassFriendGrantKind::ExactRecord:
                        if (exact_records_correspond(grant.entity, entity)) {
                            return true;
                        }
                        break;
                    case cir::RecordClassFriendGrantKind::PrimaryClassTemplate:
                        if (grant.entity.valid() &&
                            class_template_entity_for_record(entity) ==
                                grant.entity) {
                            return true;
                        }
                        break;
                    case cir::RecordClassFriendGrantKind::DependentRecipe:
                        if (grant.recipe_kind ==
                                cir::RecordClassFriendRecipeKind::
                                    MemberOfClassTemplate &&
                            dependent_member_friend_type_matches(entity,
                                                                 grant)) {
                            return true;
                        }
                        break;
                }
            }
            return false;
        };
        auto function_template_friend = [&]() {
            if (std::none_of(
                    owner_facts->function_friends.begin(),
                    owner_facts->function_friends.end(),
                    [](const cir::RecordFunctionFriendGrant& grant) {
                        return grant.kind ==
                            cir::RecordFunctionFriendGrantKind::
                                PrimaryFunctionTemplate;
                    })) {
                return false;
            }
            cir::EntityId template_entity{};
            if (accessing_function.valid() &&
                file_.valid(accessing_function)) {
                if (const cir::TemplateSpecializationFact* fact =
                        file_.template_specialization(accessing_function);
                    fact && fact->template_entity.valid()) {
                    template_entity = fact->template_entity;
                } else if (const TemplateInfo* info =
                               template_info(accessing_function);
                           info && !info->is_class_template &&
                           !info->is_alias_template &&
                           !info->is_variable_template &&
                           file_.entity(accessing_function).kind ==
                               cir::EntityKind::Function) {
                    template_entity = accessing_function;
                }
            }
            if (!template_entity.valid() && infer_active_template_function) {
                for (auto frame = tstate().current_instantiation_frames_.rbegin();
                     frame != tstate().current_instantiation_frames_.rend();
                     ++frame) {
                    cir::EntityId active = frame->template_entity;
                    if (!active.valid() || !file_.valid(active)) {
                        continue;
                    }
                    const TemplateInfo* info = template_info(active);
                    if (!info || info->is_class_template ||
                        info->is_alias_template || info->is_variable_template ||
                        file_.entity(active).kind !=
                            cir::EntityKind::Function) {
                        continue;
                    }
                    template_entity = active;
                    break;
                }
            }
            if (!template_entity.valid() && infer_active_template_function) {
                for (auto it = active_instantiations_.rbegin();
                     it != active_instantiations_.rend();
                     ++it) {
                    cir::EntityId active{
                        static_cast<uint32_t>(it->template_entity_index)};
                    if (!active.valid() || !file_.valid(active)) {
                        continue;
                    }
                    const TemplateInfo* info = template_info(active);
                    if (!info || info->is_class_template ||
                        info->is_alias_template || info->is_variable_template ||
                        file_.entity(active).kind !=
                            cir::EntityKind::Function) {
                        continue;
                    }
                    template_entity = active;
                    break;
                }
            }
            return template_entity.valid() &&
                   std::any_of(
                       owner_facts->function_friends.begin(),
                       owner_facts->function_friends.end(),
                       [template_entity](
                           const cir::RecordFunctionFriendGrant& grant) {
                           return grant.kind ==
                                      cir::RecordFunctionFriendGrantKind::
                                          PrimaryFunctionTemplate &&
                                  grant.entity == template_entity;
                       });
        };
        auto function_template_specialization_friend = [&]() {
            if (!accessing_function.valid() ||
                std::none_of(
                    owner_facts->function_friends.begin(),
                    owner_facts->function_friends.end(),
                    [](const cir::RecordFunctionFriendGrant& grant) {
                        return grant.kind ==
                            cir::RecordFunctionFriendGrantKind::
                                FunctionTemplateSpecialization;
                    })) {
                return false;
            }
            if (!file_.valid(accessing_function)) {
                return false;
            }
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(accessing_function);
            if (!fact || !fact->template_entity.valid()) {
                return false;
            }
            const cir::Entity& entity = file_.entity(accessing_function);
            cir::TypeRef current_type{
                file_.resolved_type(entity.type),
                cir::QualNone,
                cir::MemorySpace::Default};
            std::string current_key =
                template_memo_key(fact->template_entity,
                                  fact->argument_bindings);
            for (const cir::RecordFunctionFriendGrant& grant :
                 owner_facts->function_friends) {
                if (grant.kind ==
                        cir::RecordFunctionFriendGrantKind::
                            FunctionTemplateSpecialization &&
                    grant.entity == fact->template_entity &&
                    template_memo_key(grant.entity,
                                      grant.arguments) == current_key &&
                    types_compatible(current_type, grant.type_pattern)) {
                    return true;
                }
            }
            return false;
        };
        for (cir::EntityId record = accessing_record;
             record.valid() && file_.valid(record);
             record = enclosing_record(record)) {
            if (class_friend(record)) {
                return true;
            }
        }
        if (function_template_friend()) {
            return true;
        }
        if (function_template_specialization_friend()) {
            return true;
        }
        if (accessing_function.valid()) {
            for (const cir::RecordFunctionFriendGrant& grant :
                 owner_facts->function_friends) {
                if (grant.kind ==
                        cir::RecordFunctionFriendGrantKind::
                            DependentMemberFunction &&
                    dependent_member_friend_function_matches(
                        accessing_function, grant)) {
                    return true;
                }
            }
        }
        if (accessing_function.valid()) {
            for (const cir::RecordFunctionFriendGrant& grant :
                 owner_facts->function_friends) {
                if (grant.kind ==
                        cir::RecordFunctionFriendGrantKind::
                            DependentMemberFunctionTemplate &&
                    dependent_member_friend_function_template_matches(
                        accessing_function, grant)) {
                    return true;
                }
            }
        }
        if (accessing_function.valid()) {
            if (std::any_of(
                    owner_facts->function_friends.begin(),
                    owner_facts->function_friends.end(),
                    [accessing_function](
                        const cir::RecordFunctionFriendGrant& grant) {
                        return grant.kind ==
                                   cir::RecordFunctionFriendGrantKind::
                                       ExactFunction &&
                               accessing_function == grant.entity;
                    })) {
                return true;
            }
        }
    }
    if (!accessing_record.valid()) {
        return false;
    }

    for (cir::EntityId record = accessing_record;
         record.valid() && file_.valid(record);) {
        if (record == member_owner) {
            return true;
        }
        record = enclosing_record(record);
    }
    if (access == cir::RecordMemberAccess::Protected) {

        cir::TypeId owner_type = file_.entity(member_owner).type;
        if (derived_to_base_path(file_.entity(accessing_record).type,
                                 owner_type, nullptr)) {
            return true;
        }

        cir::DeclContextId accessing_context =
            file_.entity(accessing_record).semantic_context;
        for (ScopeId scope = current_scope_;
             scope != InvalidScopeId && scope < scopes_.size();
             scope = scopes_[scope].parent) {
            if (scopes_[scope].context != accessing_context) {
                continue;
            }
            for (const RecordBaseInput& base :
                 scopes_[scope].pending_bases) {
                if (base.is_dependent) {
                    continue;
                }
                cir::TypeId base_type = file_.resolved_type(base.type);
                if (base_type == file_.resolved_type(owner_type) ||
                    derived_to_base_path(base_type, owner_type, nullptr)) {
                    return true;
                }
            }
            break;
        }
        return false;
    }
    return false;
}

bool Session::check_member_access_from(cir::EntityId member,
                                       cir::RecordMemberAccess access,
                                       cir::EntityId accessing_record,
                                       cir::EntityId accessing_function,
                                       SrcLoc loc) {
    cir::EntityId owner{};
    if (file_.valid(member)) {
        const cir::Entity& declaration = file_.entity(member);
        owner = declaration.declaring_record.valid()
            ? declaration.declaring_record
            : declaration.parent;
    }
    AccessContext context;
    context.accessing_record = accessing_record;
    context.accessing_function = accessing_function;
    return check_member_access_in_context(member, access, context, loc, owner);
}

bool Session::exact_class_friend_access_depends_on_current_instantiation(
    cir::EntityId member_owner) const {
    if (!current_member_record_.valid()) {
        return false;
    }
    cir::EntityId current_template =
        class_template_entity_for_record(current_member_record_);
    const cir::RecordFacts* owner_facts = file_.record_facts(member_owner);
    return current_template.valid() && owner_facts &&
        std::any_of(
            owner_facts->class_friends.begin(),
            owner_facts->class_friends.end(),
            [&](const cir::RecordClassFriendGrant& grant) {
                return grant.kind ==
                           cir::RecordClassFriendGrantKind::ExactRecord &&
                    class_template_entity_for_record(grant.entity) ==
                        current_template;
            });
}

void Session::check_member_access(cir::EntityId member,
                                  cir::RecordMemberAccess access,
                                  SrcLoc loc) {
    if (template_argument_access_exemption_depth_ != 0) {
        return;
    }
    if (access != cir::RecordMemberAccess::Public && collecting_pattern_ &&
        current_member_record_.valid()) {
        cir::EntityId owner{};
        if (file_.valid(member)) {
            const cir::Entity& declaration = file_.entity(member);
            owner = declaration.declaring_record.valid()
                ? declaration.declaring_record
                : declaration.parent;
        }
        if (exact_class_friend_access_depends_on_current_instantiation(owner)) {

            mark_pattern_unusable();
        }
    }
    AccessObligation obligation;
    obligation.kind = AccessObligationKind::Member;
    obligation.member = member;
    if (member.valid() && file_.valid(member)) {
        const cir::Entity& declaration = file_.entity(member);
        obligation.access_owner = declaration.declaring_record.valid()
            ? declaration.declaring_record
            : declaration.parent;
    }
    obligation.declared_access = access;
    obligation.loc = loc;
    if (capture_access_obligation(std::move(obligation))) {
        return;
    }
    (void)check_member_access_in_context(member, access,
                                         current_access_context(), loc);
}

bool Session::record_has_user_constructor(cir::TypeId type) const {
    const cir::RecordFacts* facts =
        file_.record_facts_for_type(file_.resolved_type(type));

    return facts && (facts->definition_data.has_user_declared_constructor ||
                     facts->definition_data.has_inherited_constructor ||
                     facts->is_lambda_closure);
}

bool Session::record_needs_construction(cir::TypeId type) const {

    const cir::RecordFacts* facts =
        file_.record_facts_for_type(file_.resolved_type(type));
    if (!facts) {
        return false;
    }
    if (facts->definition_data.has_user_declared_constructor ||
        facts->definition_data.has_inherited_constructor) {
        return true;
    }
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (method.special_member_kind ==
                cir::SpecialMemberKind::DefaultConstructor &&
            method.is_eligible && !method.is_deleted && !method.is_trivial) {
            return true;
        }
    }
    return false;
}

bool Session::record_requires_default_constructor_selection(
    cir::TypeId type) const {
    if (record_needs_construction(type)) {
        return true;
    }
    const cir::RecordFacts* facts =
        file_.record_facts_for_type(file_.resolved_type(type));
    if (!facts) {
        return false;
    }
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (method.special_member_kind ==
                cir::SpecialMemberKind::DefaultConstructor &&
            method.constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Unsatisfied &&
            method.constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Invalid &&
            method.is_deleted) {
            return true;
        }
    }
    return false;
}

ExprResult Session::inherited_constructor_forwarding_argument(
    const ParamInput& parameter,
    SrcLoc loc) {
    ExprResult argument = lookup_name(parameter.name, loc, false);
    cir::TypeId parameter_type = file_.resolved_type(parameter.type.type);
    if (!file_.valid(parameter_type)) {
        return argument;
    }
    cir::TypeKind kind = file_.type(parameter_type).kind;
    if (kind == cir::TypeKind::LValueReference) {
        return argument;
    }

    cir::TypeId forwarding_type = kind == cir::TypeKind::RValueReference
        ? parameter.type.type
        : reference_type(parameter.type, cir::ReferenceKind::RValue);
    return collect_cast_expr(forwarding_type, std::move(argument), loc);
}

cir::EntityId Session::synthesize_inherited_variadic_call_constructor(
    cir::EntityId constructor,
    const std::vector<cir::TypeRef>& argument_types,
    SrcLoc loc) {
    const cir::RecordMethodFact* selected = file_.method_fact(constructor);
    if (!selected || !selected->inherited_constructor ||
        selected->inherited_constructor->routes.empty() ||
        !file_.valid(constructor)) {
        return {};
    }
    cir::EntityId owner = file_.entity(constructor).parent;
    const cir::RecordFacts* owner_facts = file_.record_facts(owner);
    if (!owner_facts) {
        return {};
    }
    cir::InheritedConstructorFact inherited_identity =
        *selected->inherited_constructor;

    std::string cache_key = std::to_string(constructor.index);
    for (cir::TypeRef type : argument_types) {
        cache_key += ":" + std::to_string(type.type.index) + "/" +
            std::to_string(type.qualifiers) + "/" +
            std::to_string(static_cast<unsigned>(type.memory_space));
    }
    auto cached = inherited_variadic_call_constructors_.find(cache_key);
    if (cached != inherited_variadic_call_constructors_.end()) {
        return cached->second;
    }

    const cir::InheritedConstructorRouteFact& route =
        selected->inherited_constructor->routes.front();
    cir::TypeId target_type{};
    std::string target_name;
    for (const cir::RecordBaseFact& base : owner_facts->bases) {
        if (base.record_entity != route.nominated_direct_base) {
            continue;
        }
        target_type = base.type.type;
        target_name = base.name.valid()
            ? std::string(file_.name(base.name))
            : std::string(file_.name(
                  file_.entity(base.record_entity).name));
        break;
    }
    if (route.origin_subobject < owner_facts->virtual_subobjects.size() &&
        owner_facts->virtual_subobjects[route.origin_subobject].is_virtual) {
        target_type =
            owner_facts->virtual_subobjects[route.origin_subobject].type.type;
        cir::EntityId origin_record = inherited_identity.origin_record;
        if (origin_record.valid() && file_.valid(origin_record) &&
            file_.entity(origin_record).name.valid()) {
            target_name = std::string(
                file_.name(file_.entity(origin_record).name));
        }
    }
    if (!target_type.valid() || target_name.empty()) {
        return {};
    }

    cir::TypeRef void_type =
        file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::Void));
    cir::TypeId declared_type =
        function_type(void_type, argument_types, false, true);
    cir::TypeId entity_type = member_function_type_with_this(
        owner_facts->type.type, declared_type);
    bool has_virtual_bases = !owner_facts->virtual_bases.empty();
    if (has_virtual_bases) {
        entity_type = structor_impl_type(entity_type);
    }

    std::string constructor_name = selected->name.valid()
        ? std::string(file_.name(selected->name))
        : std::string(file_.name(file_.entity(owner).name));
    cir::EntityId thunk = builder_.add_entity(
        cir::EntityKind::Constructor, constructor_name, entity_type, owner,
        loc, cir::StorageDuration::None);
    cir::Entity& thunk_entity = file_.entity_mut(thunk);
    thunk_entity.is_definition = false;
    thunk_entity.linkage = cir::LinkageKind::LinkOnceODR;
    thunk_entity.decl_flags.is_inline = true;
    thunk_entity.lexical_context = file_.entity(owner).semantic_context;
    thunk_entity.semantic_context = file_.entity(owner).semantic_context;
    record_member_declaration(thunk, owner, selected->declared_access, loc);

    cir::RecordFacts updated = *owner_facts;
    cir::RecordMethodFact thunk_fact = *selected;
    thunk_fact.entity = thunk;
    thunk_fact.type = file_.type_ref(declared_type);
    thunk_fact.is_eligible = false;
    thunk_fact.is_function_template = false;
    thunk_fact.first_required_loc = {};
    thunk_fact.first_required_lookup_generation = 0;
    updated.methods.push_back(std::move(thunk_fact));
    file_.set_record_facts(owner, std::move(updated));

    if (has_virtual_bases) {
        cir::EntityId origin_record = inherited_identity.origin_record;
        (void)synthesize_structor_variant(thunk, true, loc, origin_record);
        (void)synthesize_structor_variant(thunk, false, loc, origin_record);
    }

    std::unique_ptr<BlockContextState> saved = save_function_context();
    std::vector<ParamInput> params;
    params.reserve(argument_types.size());
    for (size_t index = 0; index < argument_types.size(); ++index) {
        ParamInput param;
        param.name = ".inherited.variadic." + std::to_string(index);
        param.type = argument_types[index];
        param.loc = loc;
        params.push_back(std::move(param));
    }
    FunctionDeclStart start = begin_member_function(thunk, params, loc, true);
    bool defined = !start.decl.has_error;
    if (defined) {
        MemberInitializerInput forward;
        forward.name = std::move(target_name);
        forward.base_type = target_type;
        forward.loc = loc;
        for (const ParamInput& param : params) {
            forward.arguments.push_back(
                inherited_constructor_forwarding_argument(param, loc));
        }
        std::vector<MemberInitializerInput> initializers;
        initializers.push_back(std::move(forward));
        enter_template_argument_access_exemption();
        StmtResult body = collect_constructor_initializers(
            std::move(initializers), loc);
        leave_template_argument_access_exemption();
        finish_member_function(std::move(body), loc);
        file_.entity_mut(thunk).linkage = cir::LinkageKind::LinkOnceODR;
    }
    restore_function_context(std::move(saved));
    if (!defined) {
        return {};
    }

    inherited_variadic_call_constructors_.emplace(cache_key, thunk);
    track_speculative_rollback([this, cache_key] {
        inherited_variadic_call_constructors_.erase(cache_key);
    });
    return thunk;
}

Session::ConstructorCallMaterialization
Session::materialize_constructor_call(cir::TypeId record_type,
                                      std::vector<ExprResult> arguments,
                                      SrcLoc loc,
                                      ConstructorInitializationKind init_kind) {
    ConstructorCallMaterialization result;
    bool ambiguous = false;
    cir::EntityId constructor =
        select_constructor(record_type, arguments, &ambiguous, loc,
                           init_kind);
    result.ambiguous = ambiguous;
    if (!constructor.valid()) {
        return result;
    }
    if (init_kind == ConstructorInitializationKind::CopyList) {
        const cir::RecordMethodFact* fact = file_.method_fact(constructor);
        if (fact && fact->is_explicit) {
            report_error(
                "explicit constructor selected in copy-list-initialization",
                loc);
            result.constructor = constructor;
            result.has_error = true;
            return result;
        }
    }
    return materialize_selected_constructor_call(
        constructor, std::move(arguments), loc,
        init_kind == ConstructorInitializationKind::Direct
            ? record_type
            : cir::TypeId{});
}

Session::ConstructorCallMaterialization
Session::materialize_selected_constructor_call(cir::EntityId constructor,
                                               std::vector<ExprResult> arguments,
                                               SrcLoc loc,
                                               cir::TypeId direct_constructor_target) {
    ConstructorCallMaterialization result;
    result.constructor = constructor;
    if (!constructor.valid() || !file_.valid(constructor)) {
        result.has_error = true;
        return result;
    }
    auto constructor_owner_name = [&]() {
        cir::EntityId owner = file_.entity(constructor).parent;
        if (owner.valid() && file_.valid(owner) &&
            file_.entity(owner).type.valid()) {
            return file_.format_type(file_.entity(owner).type);
        }
        return std::string("<class>");
    };

    const cir::RecordMethodFact* fact = file_.method_fact(constructor);
    std::vector<cir::TypeRef> parameter_types;
    bool is_variadic = false;
    bool is_inherited_variadic = false;
    if (fact) {
        cir::EntityId access_constructor = constructor;
        const cir::RecordMethodFact* access_fact = fact;
        if (fact->inherited_constructor &&
            fact->inherited_constructor->origin_constructor.valid()) {
            access_constructor =
                fact->inherited_constructor->origin_constructor;
            if (const cir::RecordMethodFact* origin =
                    file_.method_fact(access_constructor)) {
                access_fact = origin;
            }
        }
        check_member_access(access_constructor,
                            access_fact->declared_access, loc);
        if (fact->is_deleted) {
            report_error("call to deleted constructor of '" +
                             constructor_owner_name() + "'",
                         loc);
            result.has_error = true;
            return result;
        }
        if (const auto* payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(fact->type.type)))) {
            parameter_types = payload->parameters;
            is_variadic = payload->is_variadic;
            is_inherited_variadic = is_variadic &&
                fact->inherited_constructor.has_value();
        }
    }

    std::vector<bool> braced_argument;
    if (arguments.size() == 1 && arguments.front().init_list &&
        arguments.front().category == ValueCategory::InitList &&
        !constructor_initializer_list_element_type(constructor).has_value()) {
        std::shared_ptr<InitListValue> list = arguments.front().init_list;
        std::vector<ExprResult> clauses;
        clauses.reserve(list->elements.size());
        braced_argument.reserve(list->elements.size());
        for (InitElementInput& element : list->elements) {
            if (!element.designators.empty()) {
                report_error(
                    "designated initializer cannot select a constructor",
                    element.loc);
                result.has_error = true;
            }
            clauses.push_back(std::move(element.value));
            braced_argument.push_back(list->syntax == InitListSyntax::Braced);
        }
        arguments = std::move(clauses);
    } else {
        braced_argument.assign(arguments.size(), false);
    }

    while (arguments.size() < parameter_types.size()) {
        size_t parameter_index = arguments.size();
        if (!callable_default_argument(constructor, parameter_index)) {
            break;
        }
        if (!default_argument_replay_callback_) {
            report_error("cannot materialize constructor default argument",
                         loc);
            result.has_error = true;
            break;
        }
        ExprResult default_argument =
            default_argument_replay_callback_(constructor,
                                              parameter_index,
                                              loc);
        result.has_error = result.has_error || default_argument.has_error;
        arguments.push_back(std::move(default_argument));
        braced_argument.push_back(false);
    }
    if (arguments.size() < parameter_types.size()) {
        report_error("selected constructor for '" +
                         constructor_owner_name() +
                         "' is missing default argument facts",
                     loc);
        result.has_error = true;
        return result;
    }
    if (!is_variadic && arguments.size() > parameter_types.size()) {
        report_error("selected constructor for '" +
                         constructor_owner_name() +
                         "' received too many arguments",
                     loc);
        result.has_error = true;
        return result;
    }

    result.argument_values.reserve(arguments.size());
    std::vector<cir::TypeRef> materialized_argument_types;
    materialized_argument_types.reserve(arguments.size());
    for (size_t i = 0; i < arguments.size(); ++i) {
        cir::TypeId target = i < parameter_types.size()
            ? parameter_types[i].type
            : cir::TypeId{};
        if (i < braced_argument.size() && braced_argument[i] &&
            target.valid()) {
            arguments[i].has_error =
                diagnose_braced_narrowing(target, arguments[i], loc) ||
                arguments[i].has_error;
        }
        ExprResult converted;
        if (target.valid()) {
            cir::TypeId resolved_target = file_.resolved_type(target);
            const cir::RecordFacts* target_record =
                file_.record_facts_for_type(resolved_target);
            if (target_record && target_record->is_non_trivial_for_calls &&
                !is_reference_type(target)) {
                converted = materialize_constructor_parameter_argument(
                    std::move(arguments[i]), resolved_target, loc);
                result.has_error = result.has_error || converted.has_error;
                result.argument_fragment =
                    chain(std::move(result.argument_fragment),
                          std::move(converted.fragment), loc);
                result.argument_values.push_back(converted.value);
                materialized_argument_types.push_back(parameter_types[i]);
                continue;
            }
            bool handled_direct_constructor_reference = false;
            if (direct_constructor_target.valid() &&
                arguments.size() == 1 && i == 0 &&
                file_.valid(resolved_target) &&
                (file_.type(resolved_target).kind ==
                     cir::TypeKind::LValueReference ||
                 file_.type(resolved_target).kind ==
                     cir::TypeKind::RValueReference)) {
                cir::TypeRef referred =
                    file_.reference_referred_ref(resolved_target);
                cir::TypeId referred_type =
                    file_.resolved_type(referred.type);
                cir::TypeId source_type =
                    file_.resolved_type(arguments[i].type);
                bool matching_target =
                    referred_type ==
                    file_.resolved_type(direct_constructor_target);
                bool class_source =
                    file_.valid(source_type) &&
                    file_.type(source_type).kind ==
                        cir::TypeKind::Record;
                if (matching_target && class_source &&
                    source_type != referred_type) {
                    if (arguments[i].category == ValueCategory::PrValue &&
                        arguments[i].value.valid()) {
                        MemberAccessBase materialized_source =
                            collect_member_access_base(
                                std::move(arguments[i]),
                                /*is_arrow=*/false, loc);
                        arguments[i] =
                            std::move(materialized_source.base_place);
                    }
                    UserConversionSequence sequence =
                        resolve_initialization_user_conversion(
                            arguments[i], referred_type,
                            UserConversionContext::
                                DirectConstructorReference,
                            loc);
                    if (sequence.kind ==
                        UserConversionSequence::Kind::Ambiguous) {
                        report_error(
                            "conversion from '" +
                                file_.format_type(arguments[i].type) +
                                "' to '" +
                                file_.format_type(referred_type) +
                                "' is ambiguous",
                            loc);
                        report_overload_ambiguity_notes(
                            sequence.ambiguity, loc);
                        converted = std::move(arguments[i]);
                        converted.has_error = true;
                        converted.value = {};
                        handled_direct_constructor_reference = true;
                    } else if (
                        sequence.kind ==
                            UserConversionSequence::Kind::
                                ConversionFunction ||
                        sequence.kind ==
                            UserConversionSequence::Kind::Constructor) {
                        ExprResult object =
                            apply_user_conversion_sequence(
                                std::move(arguments[i]), referred_type,
                                sequence, loc);
                        converted = convert_to(std::move(object), target,
                                               UseContext::Init, loc);
                        handled_direct_constructor_reference = true;
                    }
                }
            }
            if (!handled_direct_constructor_reference) {
                converted = convert_to(std::move(arguments[i]), target,
                                       UseContext::Init, loc);
            }
        } else {
            converted = require_value(std::move(arguments[i]),
                                      UseContext::RValue, loc);
            converted = apply_default_argument_promotion(
                std::move(converted), loc);
        }
        result.has_error = result.has_error || converted.has_error;
        result.argument_fragment =
            chain(std::move(result.argument_fragment),
                  std::move(converted.fragment), loc);
        result.argument_values.push_back(converted.value);
        materialized_argument_types.push_back(
            target.valid() ? parameter_types[i]
                           : file_.type_ref(converted.type));
    }
    if (!result.has_error && is_inherited_variadic &&
        materialized_argument_types.size() > parameter_types.size()) {
        cir::EntityId thunk =
            synthesize_inherited_variadic_call_constructor(
                constructor, materialized_argument_types, loc);
        if (!thunk.valid()) {
            report_error("cannot materialize inherited variadic constructor",
                         loc);
            result.has_error = true;
        } else {
            result.constructor = thunk;
        }
    }
    if (!result.has_error) {
        // A selected virtual-base constructor specialization can still have a
        // lazily deferred body. Publish its stable complete/base ABI entry
        // points before callers capture one in ConstructInPlace;
        // materializing the body later cannot retarget an instruction that
        // already names the hidden complete-object/VTT implementation.
        ensure_structor_variants(result.constructor, loc);
    }
    return result;
}

ExprResult Session::materialize_constructor_parameter_argument(
    ExprResult argument,
    cir::TypeId parameter_type,
    SrcLoc loc) {
    cir::TypeId resolved_parameter = file_.resolved_type(parameter_type);

    if (argument.category == ValueCategory::PrValue &&
        file_.resolved_type(argument.type) == resolved_parameter) {
        cir::EntityId result_object = temporary_entity_of_value(argument.value);
        if (result_object.valid() && file_.valid(result_object) &&
            file_.entity(result_object).storage_duration ==
                cir::StorageDuration::Temporary) {
            file_.entity_mut(result_object).is_parameter_argument_object = true;
            return argument;
        }
    }

    ConstructorInitializationKind init_kind =
        argument.init_list && argument.category == ValueCategory::InitList
            ? ConstructorInitializationKind::CopyList
            : ConstructorInitializationKind::Copy;
    std::vector<ExprResult> initializer;
    initializer.push_back(std::move(argument));
    ConstructorCallMaterialization materialized =
        materialize_constructor_call(resolved_parameter,
                                     std::move(initializer), loc, init_kind);

    ExprResult result;
    result.type = resolved_parameter;
    result.category = ValueCategory::PrValue;
    result.has_error = materialized.has_error ||
        !materialized.constructor.valid();
    result.fragment = std::move(materialized.argument_fragment);
    if (!materialized.constructor.valid()) {
        report_error("cannot initialize non-trivial constructor parameter of type '" +
                         file_.format_type(resolved_parameter) + "'",
                     loc);
        return result;
    }

    cir::BlockId place_previous = builder_.current_block();
    cir::BlockId place_block =
        begin_fragment_block("ctor.call.arg.temp");
    cir::EntityId temp = builder_.add_entity(
        cir::EntityKind::Variable, ".ctor.arg.temp", resolved_parameter, {},
        loc, cir::StorageDuration::Temporary);
    cir::Entity& temp_record = file_.entity_mut(temp);
    temp_record.is_definition = true;
    temp_record.is_parameter_argument_object = true;
    cir::InstId place = builder_.local_place(temp, resolved_parameter, loc);
    cir::Fragment place_fragment =
        finish_fragment_block(place_block, place_previous);
    result.fragment = chain(std::move(result.fragment),
                            std::move(place_fragment), loc);

    if (!materialized.has_error) {
        cir::BlockId construct_previous = builder_.current_block();
        cir::BlockId construct_block =
            begin_fragment_block("ctor.call.arg.construct");
        emit_construct_in_place(
            place, structor_complete_variant(materialized.constructor),
            materialized.argument_values, loc);
        cir::Fragment construct_fragment =
            finish_fragment_block(construct_block, construct_previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(construct_fragment), loc);
        register_destructor_cleanup(
            temp, resolved_parameter, loc,
            /*full_expression_temporary=*/true);
    }

    cir::BlockId load_previous = builder_.current_block();
    cir::BlockId load_block =
        begin_fragment_block("ctor.call.arg.load");
    result.value = builder_.lvalue_to_rvalue(place, loc);
    cir::Fragment load_fragment =
        finish_fragment_block(load_block, load_previous);
    result.fragment = chain(std::move(result.fragment),
                            std::move(load_fragment), loc);
    return result;
}

cir::EntityId Session::record_copy_constructor(cir::TypeId type) const {
    const cir::RecordMethodFact* method = canonical_special_member(
        file_, type, cir::SpecialMemberKind::CopyConstructor);
    return method && method->is_eligible && !method->is_deleted
        ? method->entity
        : cir::EntityId{};
}

cir::EntityId Session::record_move_constructor(cir::TypeId type) const {
    const cir::RecordMethodFact* method = canonical_special_member(
        file_, type, cir::SpecialMemberKind::MoveConstructor);
    return method && method->is_eligible && !method->is_deleted
        ? method->entity
        : cir::EntityId{};
}

cir::EntityId Session::corresponding_record_method(
    cir::DeclContextId context,
    std::string_view name,
    cir::TypeRef type,
    bool ignore_exception_spec) const {
    const cir::Binding* binding = file_.lookup_callable_binding(
        context, name, /*include_parents=*/false);
    if (!binding) {
        return {};
    }

    std::vector<const cir::RecordMethodFact*> matches;
    for (cir::EntityId candidate : binding->entities) {
        if (template_info(candidate)) {
            continue;
        }
        const cir::RecordMethodFact* fact = file_.method_fact(candidate);
        PatternBindings bindings;
        if (!fact ||
            !unify_type_pattern(fact->type.type,
                                type.type,
                                bindings,
                                ignore_exception_spec
                                    ? TypePatternExceptionMatch::
                                          IgnoreAtCurrentFunction
                                    : TypePatternExceptionMatch::Exact)) {
            continue;
        }
        if (fact->special_member_kind == cir::SpecialMemberKind::Destructor) {
            if (fact->is_selected_destructor) {
                return candidate;
            }
            continue;
        }
        matches.push_back(fact);
    }
    if (matches.size() == 1) {

        return matches.front()->entity;
    }

    std::vector<const cir::RecordMethodFact*> viable;
    for (const cir::RecordMethodFact* fact : matches) {
        if (fact->constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Unsatisfied &&
            fact->constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Invalid) {
            viable.push_back(fact);
        }
    }
    std::vector<const cir::RecordMethodFact*> maximal;
    for (const cir::RecordMethodFact* candidate : viable) {
        bool dominated = false;
        for (const cir::RecordMethodFact* other : viable) {
            if (candidate == other) {
                continue;
            }
            if (std::find(other->more_constrained_than.begin(),
                          other->more_constrained_than.end(),
                          candidate->associated_constraint_fingerprint) !=
                other->more_constrained_than.end()) {
                dominated = true;
                break;
            }
        }
        if (!dominated) {
            maximal.push_back(candidate);
        }
    }
    return maximal.size() == 1 ? maximal.front()->entity : cir::EntityId{};
}

cir::EntityId Session::record_destructor(cir::TypeId type) const {
    const cir::RecordMethodFact* method = selected_record_destructor(type);
    return method && method->entity.valid() && !method->is_deleted &&
                   !method->is_trivial
        ? method->entity
        : cir::EntityId{};
}

const cir::RecordMethodFact* Session::selected_record_destructor(
    cir::TypeId type) const {
    return canonical_special_member(file_, type,
                                    cir::SpecialMemberKind::Destructor);
}

bool Session::validate_potentially_invoked_destructor(cir::TypeId type,
                                                       SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(type);

    if (cir::TypeId leaf = array_class_element_leaf(resolved); leaf.valid()) {
        resolved = leaf;
    }
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Record) {
        return true;
    }
    const cir::RecordMethodFact* method =
        selected_record_destructor(resolved);
    if (!method || !method->entity.valid() ||
        !file_.valid(method->entity)) {

        return true;
    }
    std::string type_name = file_.format_type(resolved);
    if (method->is_deleted) {
        report_error("potentially invoked destructor of '" + type_name +
                         "' is deleted",
                     loc);
        return false;
    }
    cir::EntityId owner = file_.entity(method->entity).parent;
    if (!member_access_allowed(owner, method->declared_access)) {
        check_member_access(method->entity, method->declared_access, loc);
        return false;
    }
    if (!method->is_trivial) {
        mark_record_method_required(method->entity, loc);
    }
    return true;
}

cir::EntityId Session::temporary_entity_of_value(cir::InstId value) const {
    if (!value.valid() || !file_.valid(value)) {
        return {};
    }
    const cir::Inst& load = file_.inst(value);
    if (load.kind != cir::InstKind::LValueToRValue) {
        return {};
    }
    std::vector<cir::ValueRef> places = file_.value_operands(load.operands);
    if (places.empty() || !places.front().valid() ||
        !file_.valid(places.front().inst)) {
        return {};
    }
    const cir::Inst& place = file_.inst(places.front().inst);
    if (place.kind != cir::InstKind::LocalPlace) {
        return {};
    }
    std::vector<cir::Operand> operands = file_.operands(place.operands);
    if (operands.empty()) {
        return {};
    }
    const cir::EntityId* entity =
        std::get_if<cir::EntityId>(&operands.front().data);
    return entity ? *entity : cir::EntityId{};
}

cir::LifetimeId Session::lifetime_for_entity(cir::EntityId entity) const {
    if (!entity.valid()) {
        return {};
    }
    for (auto obligation = lifetime_obligations_.rbegin();
         obligation != lifetime_obligations_.rend(); ++obligation) {
        if (obligation->entity == entity &&
            obligation->owner != LifetimeOwnerKind::Retired) {
            return obligation->id;
        }
    }
    return {};
}

cir::LifetimeId Session::temporary_lifetime_of_value(cir::InstId value) const {
    return lifetime_for_entity(temporary_entity_of_value(value));
}

bool Session::adopt_materialized_object_storage(
    const ExprResult& source,
    cir::InstId destination_place,
    cir::EntityId destination_entity) {
    if ((!destination_place.valid() || !file_.valid(destination_place)) &&
        (!destination_entity.valid() || !file_.valid(destination_entity))) {
        return false;
    }
    if (!destination_entity.valid()) {
        const cir::Inst& destination = file_.inst(destination_place);
        if (destination.kind == cir::InstKind::LocalPlace ||
            destination.kind == cir::InstKind::GlobalPlace) {
            std::vector<cir::Operand> operands =
                file_.operands(destination.operands);
            if (!operands.empty()) {
                if (const auto* entity =
                        std::get_if<cir::EntityId>(&operands.front().data)) {
                    destination_entity = *entity;
                }
            }
        }
    }

    std::vector<cir::EntityId> sources;
    for (cir::LifetimeId lifetime : source.materialized_lifetimes) {
        if (!lifetime.valid() ||
            lifetime.index >= lifetime_obligations_.size()) {
            continue;
        }
        const LifetimeObligation& obligation =
            lifetime_obligations_[lifetime.index];
        if (obligation.id == lifetime && obligation.entity.valid() &&
            std::find(sources.begin(), sources.end(), obligation.entity) ==
                sources.end()) {
            sources.push_back(obligation.entity);
        }
    }
    if (sources.empty()) {
        if (cir::EntityId entity = temporary_entity_of_value(source.value);
            entity.valid()) {
            sources.push_back(entity);
        }
    }

    bool adopted = false;
    for (cir::EntityId source_entity : sources) {
        if (!file_.valid(source_entity) ||
            source_entity == destination_entity) {
            continue;
        }
        cir::Entity& entity = file_.entity_mut(source_entity);
        entity.is_function_result_object = false;
        if (destination_entity.valid()) {
            entity.object_storage_alias = destination_entity;
            entity.object_storage_alias_place = {};
        } else {
            entity.object_storage_alias = {};
            entity.object_storage_alias_place = destination_place;
        }
        adopted = true;
    }
    return adopted;
}

bool Session::adopt_materialized_result_storage(const ExprResult& source) {
    std::vector<cir::EntityId> sources;
    for (cir::LifetimeId lifetime : source.materialized_lifetimes) {
        if (!lifetime.valid() ||
            lifetime.index >= lifetime_obligations_.size()) {
            continue;
        }
        const LifetimeObligation& obligation =
            lifetime_obligations_[lifetime.index];
        if (obligation.id == lifetime && obligation.entity.valid()) {
            sources.push_back(obligation.entity);
        }
    }
    if (sources.empty()) {
        if (cir::EntityId entity = temporary_entity_of_value(source.value);
            entity.valid()) {
            sources.push_back(entity);
        }
    }
    bool adopted = false;
    for (cir::EntityId entity_id : sources) {
        if (!file_.valid(entity_id)) {
            continue;
        }
        cir::Entity& entity = file_.entity_mut(entity_id);
        entity.object_storage_alias = {};
        entity.object_storage_alias_place = {};
        entity.is_function_result_object = true;
        adopted = true;
    }
    return adopted;
}

bool Session::transfer_lifetime(cir::LifetimeId lifetime,
                                LifetimeOwnerKind owner,
                                uint64_t owner_id) {
    if (!lifetime.valid() || lifetime.index >= lifetime_obligations_.size()) {
        return false;
    }
    LifetimeObligation& obligation = lifetime_obligations_[lifetime.index];
    if (obligation.id != lifetime ||
        obligation.owner == LifetimeOwnerKind::Retired) {
        return false;
    }

    obligation.owner = owner;
    obligation.owner_id = owner_id;
    bool keep_normal_record = owner == LifetimeOwnerKind::LexicalScope ||
                              owner == LifetimeOwnerKind::FullExpression ||
                              owner == LifetimeOwnerKind::ConstructorRollback;
    for (CleanupScope& scope : cleanup_scopes_) {
        for (auto record = scope.records.begin();
             record != scope.records.end();) {
            if (record->lifetime != lifetime) {
                ++record;
                continue;
            }
            if (keep_normal_record) {
                record->owner = owner;
                record->owner_id = owner_id;
                ++record;
            } else {
                record = scope.records.erase(record);
            }
        }
    }

    if (keep_normal_record) {
        return true;
    }

    for (EhCleanupStep& step : eh_cleanup_steps_) {
        if (step.lifetime != lifetime || !step.destroy_inst.valid()) {
            continue;
        }
        if (file_.valid(step.code_block)) {
            std::vector<cir::InstId>& instructions =
                file_.block_mut(step.code_block).instructions;
            auto inst = std::find(instructions.begin(), instructions.end(),
                                  step.destroy_inst);
            if (inst != instructions.end()) {
                instructions.erase(inst);
            }
        }
        step.destroy_inst = {};
        break;
    }
    return true;
}

bool Session::retire_lifetime(cir::LifetimeId lifetime) {
    if (!transfer_lifetime(lifetime, LifetimeOwnerKind::Retired)) {
        return false;
    }
    LifetimeObligation& obligation = lifetime_obligations_[lifetime.index];
    obligation.owner = LifetimeOwnerKind::Retired;
    obligation.owner_id = 0;
    return true;
}

bool Session::remove_destructor_cleanup(cir::EntityId entity) {
    return retire_lifetime(lifetime_for_entity(entity));
}

cir::LifetimeId Session::register_destructor_cleanup(
    cir::EntityId entity,
    cir::TypeId type,
    SrcLoc loc,
    bool full_expression_temporary) {
    if (!lang_opts_.is_cxx_mode()) {
        return {};
    }
    if (!validate_potentially_invoked_destructor(type, loc) ||
        cleanup_scopes_.empty()) {
        return {};
    }
    if (!entity.valid() ||
        (file_.entity(entity).storage_duration != cir::StorageDuration::Automatic &&
         file_.entity(entity).storage_duration != cir::StorageDuration::Temporary)) {
        return {};
    }

    cir::TypeId array_leaf = array_class_element_leaf(type);
    if (array_leaf.valid() &&
        !validate_potentially_invoked_destructor(array_leaf, loc)) {
        return {};
    }
    cir::EntityId cleanup_function{};
    cir::EntityId unwind_cleanup_function{};
    if (array_leaf.valid()) {
        cleanup_function = array_destroy_helper(type, loc);
        unwind_cleanup_function = array_destroy_helper(
            type, loc, ArrayDestructionMode::UnwindCleanup);
    } else {
        cir::EntityId destructor = record_destructor(type);
        if (destructor.valid()) {
            cleanup_function = structor_complete_variant(destructor);
            unwind_cleanup_function = cleanup_function;
        }
    }
    return register_cleanup_with_function(entity, type, loc,
                                          full_expression_temporary,
                                          cleanup_function,
                                          unwind_cleanup_function,
                                          array_leaf.valid());
}

cir::LifetimeId Session::register_cleanup_with_function(
    cir::EntityId entity,
    cir::TypeId type,
    SrcLoc loc,
    bool full_expression_temporary,
    cir::EntityId cleanup_function,
    cir::EntityId unwind_cleanup_function,
    bool call_with_address) {
    LifetimeOwnerKind owner = LifetimeOwnerKind::LexicalScope;
    uint64_t owner_id = 0;
    if (full_expression_temporary) {
        owner = LifetimeOwnerKind::FullExpression;
        if (!active_lifetime_boundaries_.empty()) {
            owner_id = active_lifetime_boundaries_.back();
        }
    }
    cir::LifetimeId lifetime{
        static_cast<uint32_t>(lifetime_obligations_.size()),
        next_lifetime_generation_++};
    lifetime_obligations_.push_back(LifetimeObligation{
        lifetime, entity, type, cleanup_function, loc, owner, owner_id,
        cleanup_function.valid()});
    if (!cleanup_function.valid()) {
        return lifetime;
    }

    if (!builder_.current_function().valid()) {
        cleanup_scopes_.back().records.push_back(
            CleanupRecord{lifetime, entity, type, cleanup_function,
                          loc, owner, owner_id, {}});
        return lifetime;
    }
    cir::BlockId saved_target = builder_.current_unwind_target();
    cleanup_scopes_.back().records.push_back(
        CleanupRecord{lifetime, entity, type, cleanup_function,
                      loc, owner, owner_id, saved_target});
    cir::BlockId previous = builder_.current_block();
    cir::BlockId pad = builder_.create_block("cleanup.lpad");
    cir::BlockId action = builder_.create_block("cleanup.act");

    builder_.set_block_unwind_target(pad, {});
    builder_.set_block_unwind_target(action, {});
    builder_.switch_to_block(pad);
    cir::EhLandingPadPayload pad_payload;
    pad_payload.is_cleanup = true;
    cir::InstId landing_pad =
        builder_.eh_landing_pad(std::move(pad_payload), loc);
    cir::InstId selector = builder_.eh_selector(landing_pad, loc);
    builder_.branch(action, {landing_pad, selector}, loc);
    cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
    cir::InstId exn_param =
        builder_.add_block_parameter(action, void_ptr, "exn", loc);
    cir::InstId sel_param =
        builder_.add_block_parameter(action, builder_.int_type(), "sel", loc);
    builder_.switch_to_block(action);
    cir::InstId place = builder_.local_place(entity, type, loc);
    cir::InstId destroy_inst;
    if (call_with_address) {
        cir::InstId address = builder_.addr_of(place, loc);
        destroy_inst = builder_.call(unwind_cleanup_function,
                                     file_.builtin_type(
                                         cir::BuiltinTypeKind::Void),
                                     {address}, loc);
    } else {
        destroy_inst = emit_destroy(place, cleanup_function, loc);
    }
    emit_unwind_continue(action, exn_param, sel_param, saved_target, loc);
    builder_.switch_to_block(previous);

    eh_pads_in_flight_.push_back(landing_pad);
    track_speculative_rollback([this]() {
        if (!eh_pads_in_flight_.empty()) {
            eh_pads_in_flight_.pop_back();
        }
    });
    eh_code_targets_[pad.index] = action;
    track_speculative_rollback([this, pad_index = pad.index]() {
        eh_code_targets_.erase(pad_index);
    });
    eh_cleanup_steps_.push_back(
        EhCleanupStep{lifetime, entity, landing_pad, pad, action, destroy_inst});
    track_speculative_rollback([this]() {
        if (!eh_cleanup_steps_.empty()) {
            eh_cleanup_steps_.pop_back();
        }
    });
    builder_.set_current_unwind_target(pad);
    return lifetime;
}

void Session::install_subobject_rollback(
    const RecordLifecycleStep& step,
    SrcLoc loc,
    const std::function<cir::InstId(SrcLoc)>& action_place) {
    if (!builder_.current_function().valid()) {
        return;
    }
    const cir::RecordFieldFact& field = step.field;
    cir::TypeId subobject_type = file_.resolved_type(field.type.type);
    cir::TypeId array_leaf = step.array_shape.leaf_type;
    cir::EntityId cleanup_function;
    if (array_leaf.valid()) {
        cleanup_function = record_destructor(array_leaf);
    } else {
        cir::EntityId destructor = record_destructor(subobject_type);
        if (destructor.valid()) {
            cleanup_function = field.is_base_subobject
                ? structor_base_variant(destructor)
                : structor_complete_variant(destructor);
        }
    }
    if (!cleanup_function.valid()) {
        return;
    }

    cir::LifetimeId lifetime{
        static_cast<uint32_t>(lifetime_obligations_.size()),
        next_lifetime_generation_++};
    lifetime_obligations_.push_back(LifetimeObligation{
        lifetime, field.entity, subobject_type, cleanup_function, loc,
        LifetimeOwnerKind::ConstructorRollback,
        static_cast<uint64_t>(current_function_.index), true});

    cir::BlockId saved_target = builder_.current_unwind_target();
    cir::BlockId previous = builder_.current_block();
    builder_.set_current_unwind_target({});
    cir::BlockId pad = builder_.create_block("ctor.subobject.lpad");
    cir::BlockId action = builder_.create_block("ctor.subobject.act");
    builder_.set_block_unwind_target(pad, {});
    builder_.set_block_unwind_target(action, {});
    builder_.switch_to_block(pad);
    cir::EhLandingPadPayload pad_payload;
    pad_payload.is_cleanup = true;
    cir::InstId landing_pad =
        builder_.eh_landing_pad(std::move(pad_payload), loc);
    cir::InstId selector = builder_.eh_selector(landing_pad, loc);
    builder_.branch(action, {landing_pad, selector}, loc);
    cir::TypeId void_type = builder_.void_type();
    cir::InstId exn_param = builder_.add_block_parameter(
        action, builder_.pointer_type(void_type), "exn", loc);
    cir::InstId sel_param = builder_.add_block_parameter(
        action, builder_.int_type(), "sel", loc);
    builder_.switch_to_block(action);

    cir::BlockId destroy_block = action;
    cir::BlockId continue_block = action;
    if (step.complete_object_only && current_structor_flag_.valid()) {
        destroy_block = builder_.create_block("ctor.vbase.rollback");
        continue_block = builder_.create_block("ctor.rollback.continue");
        builder_.set_block_unwind_target(destroy_block, {});
        builder_.set_block_unwind_target(continue_block, {});
        cir::InstId zero = builder_.integer_literal(
            0, builder_.int_type(), "0", loc);
        cir::InstId is_complete = builder_.binary(
            cir::BinaryOpKind::NotEqual, builder_.int_type(),
            current_structor_flag_, zero, loc);
        builder_.cond_branch_from(action, is_complete, destroy_block,
                                  continue_block, {}, loc);
        builder_.switch_to_block(destroy_block);
    }

    cir::InstId place = action_place(loc);
    cir::InstId destroy_inst;
    cir::BlockId destroy_exit = destroy_block;
    if (array_leaf.valid()) {
        cir::Fragment array_destroy = array_destroy_loop_fragment(
            place, subobject_type, {}, loc,
            ArrayDestructionMode::UnwindCleanup);
        builder_.attach_fragment_to_function(builder_.current_function(),
                                             array_destroy);
        builder_.branch(array_destroy.entry, {}, loc);
        destroy_exit = array_destroy.exit;
    } else {
        bool vtt_call = false;
        if (field.is_base_subobject &&
            current_structor_vtt_place_.valid()) {
            const cir::RecordFacts* subobject_facts =
                file_.record_facts_for_type(subobject_type);
            if (subobject_facts && !subobject_facts->virtual_bases.empty()) {
                const cir::RecordFacts* own_facts =
                    file_.record_facts(current_member_record_);
                cir::EntityId subobject_record =
                    file_.record_entity(subobject_type);
                if (own_facts) {
                    VttInfo info = compute_vtt_info(*own_facts);
                    const auto& slices = field.is_virtual_base_storage
                        ? info.vbase_slices
                        : info.base_slices;
                    for (const VttInfo::Slice& slice : slices) {
                        if (slice.record_entity != subobject_record) {
                            continue;
                        }
                        cir::InstId saved_vtt = current_structor_vtt_place_;
                        current_structor_vtt_place_ =
                            rematerialize_entity_place(saved_vtt, loc);
                        cir::InstId slice_value =
                            vtt_slice_value(slice.start, loc);
                        current_structor_vtt_place_ = saved_vtt;
                        destroy_inst = emit_structor_call(
                            cleanup_function, void_type,
                            {builder_.addr_of(place, loc), slice_value}, loc);
                        vtt_call = true;
                        break;
                    }
                }
            }
        }
        if (!vtt_call) {
            destroy_inst = emit_destroy(place, cleanup_function, loc);
        }
    }
    cir::BlockId unwind_continue_block = destroy_exit;
    if (destroy_block != continue_block) {
        builder_.branch_from(destroy_exit, continue_block, {}, loc);
        unwind_continue_block = continue_block;
    }
    emit_unwind_continue(unwind_continue_block, exn_param, sel_param,
                         saved_target, loc);
    builder_.switch_to_block(previous);

    eh_pads_in_flight_.push_back(landing_pad);
    track_speculative_rollback([this]() {
        if (!eh_pads_in_flight_.empty()) {
            eh_pads_in_flight_.pop_back();
        }
    });
    eh_code_targets_[pad.index] = action;
    track_speculative_rollback([this, pad_index = pad.index]() {
        eh_code_targets_.erase(pad_index);
    });
    eh_cleanup_steps_.push_back(EhCleanupStep{
        lifetime, field.entity, landing_pad, pad, destroy_block,
        destroy_inst});
    track_speculative_rollback([this]() {
        if (!eh_cleanup_steps_.empty()) {
            eh_cleanup_steps_.pop_back();
        }
    });
    builder_.set_current_unwind_target(pad);
}

Session::ClassArrayShape Session::class_array_shape(cir::TypeId type) const {
    ClassArrayShape shape;
    cir::TypeId current = file_.resolved_type(type);
    shape.array_type = current;
    uint64_t total = 1;
    while (file_.valid(current) &&
           file_.type(current).kind == cir::TypeKind::Array) {
        const auto* payload = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(current));
        if (!payload || !payload->size.has_value()) {
            shape.dependent = payload && payload->size_expr_is_dependent;
            return shape;
        }
        if (payload->size_expr_is_dependent) {
            shape.dependent = true;
            return shape;
        }
        uint64_t extent = static_cast<uint64_t>(*payload->size);
        shape.extents.push_back(extent);
        if (extent != 0 &&
            total > std::numeric_limits<uint64_t>::max() / extent) {
            shape.extent_overflow = true;
            return shape;
        }
        total *= extent;
        current = file_.resolved_type(payload->element_type.type);
    }
    if (shape.extents.empty() || !file_.valid(current) ||
        file_.type(current).kind != cir::TypeKind::Record ||
        !file_.record_facts_for_type(current)) {
        return shape;
    }
    shape.leaf_type = current;
    shape.total_leaf_count = total;
    return shape;
}

cir::TypeId Session::array_class_element_leaf(cir::TypeId type) const {
    return class_array_shape(type).leaf_type;
}

Session::RecordLifecyclePlan Session::record_lifecycle_plan(
    const cir::RecordFacts& facts,
    RecordLifecycleOperation operation) const {
    RecordLifecyclePlan plan;
    plan.operation = operation;
    if (facts.kind == cir::RecordKind::Union) {

        return plan;
    }

    auto append = [&](const cir::RecordFieldFact& field) {
        if (field.name.valid() && file_.name(field.name) == ".vptr") {
            return;
        }

        if (field.is_flexible_array_member) {
            return;
        }

        if (operation == RecordLifecycleOperation::Destroy &&
            field.is_anonymous_union_object) {
            return;
        }
        RecordLifecycleStep step;
        step.field = field;
        step.array_shape = class_array_shape(field.type.type);
        step.complete_object_only = field.is_virtual_base_storage &&
            operation != RecordLifecycleOperation::CopyAssign &&
            operation != RecordLifecycleOperation::MoveAssign;
        plan.steps.push_back(std::move(step));
    };

    if (operation == RecordLifecycleOperation::CopyAssign ||
        operation == RecordLifecycleOperation::MoveAssign) {
        std::vector<const cir::RecordFieldFact*> bases;
        for (const cir::RecordFieldFact& field : facts.fields) {
            if (field.is_base_subobject) {
                bases.push_back(&field);
            }
        }
        std::stable_sort(
            bases.begin(), bases.end(),
            [&](const cir::RecordFieldFact* lhs,
                const cir::RecordFieldFact* rhs) {
                return base_declaration_index(facts, *lhs) <
                    base_declaration_index(facts, *rhs);
            });
        for (const cir::RecordFieldFact* base : bases) {
            append(*base);
        }
        for (const cir::RecordFieldFact& field : facts.fields) {
            if (!field.is_base_subobject) {
                append(field);
            }
        }
        return plan;
    }

    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_virtual_base_storage) {
            append(field);
        }
    }
    std::vector<const cir::RecordFieldFact*> direct_bases;
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (field.is_base_subobject && !field.is_virtual_base_storage) {
            direct_bases.push_back(&field);
        }
    }
    std::stable_sort(
        direct_bases.begin(), direct_bases.end(),
        [&](const cir::RecordFieldFact* lhs,
            const cir::RecordFieldFact* rhs) {
            return base_declaration_index(facts, *lhs) <
                base_declaration_index(facts, *rhs);
        });
    for (const cir::RecordFieldFact* base : direct_bases) {
        append(*base);
    }
    for (const cir::RecordFieldFact& field : facts.fields) {
        if (!field.is_base_subobject) {
            append(field);
        }
    }

    if (operation == RecordLifecycleOperation::Destroy) {
        std::reverse(plan.steps.begin(), plan.steps.end());
    }
    return plan;
}

cir::InstId Session::flatten_array_place(cir::InstId array_place,
                                         cir::TypeId array_type,
                                         cir::TypeId leaf,
                                         size_t total,
                                         SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(array_type);
    const auto* payload =
        std::get_if<cir::ArrayTypePayload>(&file_.type_payload(resolved));
    if (payload &&
        file_.resolved_type(payload->element_type.type) == leaf) {
        return array_place;
    }
    cir::TypeId flat = this->array_type(file_.type_ref(leaf), total);
    cir::InstId address = builder_.addr_of(array_place, loc);
    cir::InstId flat_pointer =
        builder_.cast(builder_.pointer_type(flat), address, "value", loc);
    return builder_.deref(flat_pointer, loc);
}

cir::Fragment Session::array_destroy_loop_fragment(cir::InstId array_place,
                                                   cir::TypeId array_type,
                                                   cir::InstId count_value,
                                                   SrcLoc loc,
                                                   ArrayDestructionMode mode,
                                                   const std::function<
                                                       cir::InstId(SrcLoc)>*
                                                       action_place) {
    cir::Fragment fragment;
    cir::TypeId resolved = file_.resolved_type(array_type);
    ClassArrayShape shape = class_array_shape(resolved);
    cir::TypeId leaf = shape.leaf_type;
    uint64_t total = shape.total_leaf_count;
    if (!shape.valid()) {
        return fragment;
    }
    cir::EntityId destructor = record_destructor(leaf);
    if (!destructor.valid()) {
        return fragment;
    }
    ArrayLifecyclePlan plan;
    plan.shape = shape;
    plan.operation = ArrayLifecycleOperation::Destroy;
    plan.element_function = destructor;
    plan.first_leaf = 0;
    plan.past_last_leaf = total;
    plan.track_progress = count_value.valid() ||
        mode == ArrayDestructionMode::Normal;
    if (!plan.valid()) {
        return fragment;
    }
    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved_block = builder_.current_block();
    cir::BlockId saved_target = builder_.current_unwind_target();
    cir::EntityId progress_entity;
    cir::BlockId element_pad;

    if (mode == ArrayDestructionMode::Normal &&
        builder_.current_function().valid()) {
        cir::EntityId progress = builder_.add_entity(
            cir::EntityKind::Variable,
            ".array.destroy.remaining." +
                std::to_string(compound_literal_counter_++),
            usize, {}, loc, cir::StorageDuration::Automatic,
            cir::MemorySpace::Default, {});
        file_.entity_mut(progress).is_definition = true;
        progress_entity = progress;

        builder_.set_current_unwind_target({});
        element_pad = builder_.create_block("array.dtor.lpad");
        cir::BlockId action = builder_.create_block("array.dtor.act");
        builder_.set_block_unwind_target(element_pad, {});
        builder_.set_block_unwind_target(action, {});
        builder_.switch_to_block(element_pad);
        cir::EhLandingPadPayload payload;
        payload.is_cleanup = true;
        cir::InstId landing_pad =
            builder_.eh_landing_pad(std::move(payload), loc);
        cir::InstId selector = builder_.eh_selector(landing_pad, loc);
        builder_.branch(action, {landing_pad, selector}, loc);
        cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
        cir::InstId exn_param = builder_.add_block_parameter(
            action, void_ptr, "exn", loc);
        cir::InstId sel_param = builder_.add_block_parameter(
            action, builder_.int_type(), "sel", loc);
        builder_.switch_to_block(action);
        cir::InstId action_progress =
            builder_.local_place(progress, usize, loc);
        cir::InstId remaining =
            builder_.lvalue_to_rvalue(action_progress, loc);
        cir::InstId action_array = action_place && *action_place
            ? (*action_place)(loc)
            : rematerialize_entity_place(array_place, loc);
        cir::Fragment remaining_destroy = array_destroy_loop_fragment(
            action_array, resolved, remaining, loc,
            ArrayDestructionMode::UnwindCleanup);
        builder_.attach_fragment_to_function(builder_.current_function(),
                                             remaining_destroy);
        builder_.branch(remaining_destroy.entry, {}, loc);
        emit_unwind_continue(remaining_destroy.exit, exn_param, sel_param,
                             saved_target, loc);

        eh_pads_in_flight_.push_back(landing_pad);
        track_speculative_rollback([this]() {
            if (!eh_pads_in_flight_.empty()) {
                eh_pads_in_flight_.pop_back();
            }
        });
        eh_code_targets_[element_pad.index] = action;
        track_speculative_rollback(
            [this, pad_index = element_pad.index]() {
                eh_code_targets_.erase(pad_index);
            });
        builder_.set_current_unwind_target(element_pad);
    }

    cir::BlockId entry = builder_.create_detached_block("array.dtor.entry");
    cir::BlockId head = builder_.create_detached_block("array.dtor.head");
    cir::BlockId body = builder_.create_detached_block("array.dtor.body");
    cir::BlockId done = builder_.create_detached_block("array.dtor.done");
    cir::InstId index = builder_.add_block_parameter(head, usize, "idx", loc);

    builder_.switch_to_block(entry);
    cir::InstId flat_place =
        flatten_array_place(array_place, resolved, leaf, total, loc);
    cir::InstId count = count_value.valid()
        ? count_value
        : builder_.integer_literal(static_cast<int64_t>(total), usize, {},
                                   loc);
    builder_.branch(head, {count}, loc);

    builder_.switch_to_block(head);
    cir::InstId zero = builder_.integer_literal(0, usize, {}, loc);
    cir::InstId at_begin = builder_.binary(cir::BinaryOpKind::Equal,
                                           builder_.int_type(), index, zero,
                                           loc);
    builder_.cond_branch_from(head, at_begin, done, body, {}, loc);

    builder_.switch_to_block(body);
    cir::InstId one = builder_.integer_literal(1, usize, {}, loc);
    cir::InstId previous_index =
        builder_.binary(cir::BinaryOpKind::Sub, usize, index, one, loc);
    if (progress_entity.valid()) {

        cir::InstId body_progress =
            builder_.local_place(progress_entity, usize, loc);
        builder_.store(body_progress, previous_index, loc);
    }
    cir::InstId element_place =
        builder_.array_element_place(flat_place, previous_index, loc);
    emit_destroy(element_place, structor_complete_variant(destructor), loc);
    builder_.branch(head, {previous_index}, loc);

    fragment.blocks = {entry, head, body, done};
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;
    if (element_pad.valid()) {
        builder_.set_block_unwind_target(done, saved_target);
    }
    builder_.set_current_unwind_target(saved_target);
    builder_.switch_to_block(saved_block);
    return fragment;
}

cir::InstId Session::rematerialize_entity_place(cir::InstId place,
                                                SrcLoc loc) {
    if (!place.valid() || !file_.valid(place)) {
        return place;
    }
    const cir::Inst& inst = file_.inst(place);
    if (inst.kind != cir::InstKind::LocalPlace &&
        inst.kind != cir::InstKind::GlobalPlace) {
        return place;
    }
    std::vector<cir::Operand> operands = file_.operands(inst.operands);
    if (operands.empty()) {
        return place;
    }
    const cir::EntityId* entity =
        std::get_if<cir::EntityId>(&operands.front().data);
    if (!entity || !entity->valid()) {
        return place;
    }
    return inst.kind == cir::InstKind::LocalPlace
        ? builder_.local_place(*entity, file_.entity(*entity).type, loc)
        : builder_.global_place(*entity, loc);
}

cir::InstId Session::begin_array_construct_unwind(
    cir::InstId array_place,
    cir::TypeId array_type,
    cir::TypeId leaf,
    cir::BlockId saved_target,
    SrcLoc loc,
    const std::function<cir::InstId(SrcLoc)>* action_place_builder) {

    cir::EntityId leaf_destructor = record_destructor(leaf);
    if (!leaf_destructor.valid() || !builder_.current_function().valid()) {
        return {};
    }
    cir::TypeId resolved = file_.resolved_type(array_type);
    cir::TypeId usize = builder_.usize_type();
    cir::EntityId progress = builder_.add_entity(
        cir::EntityKind::Variable,
        ".array.progress." + std::to_string(compound_literal_counter_++),
        usize, {}, loc, cir::StorageDuration::Automatic,
        cir::MemorySpace::Default, {});
    file_.entity_mut(progress).is_definition = true;

    builder_.set_current_unwind_target({});
    cir::BlockId pad = builder_.create_block("array.ctor.lpad");
    cir::BlockId action = builder_.create_block("array.ctor.act");
    cir::BlockId pad_previous = builder_.current_block();
    builder_.switch_to_block(pad);
    cir::EhLandingPadPayload pad_payload;
    pad_payload.is_cleanup = true;
    cir::InstId landing_pad =
        builder_.eh_landing_pad(std::move(pad_payload), loc);
    cir::InstId selector = builder_.eh_selector(landing_pad, loc);
    builder_.branch(action, {landing_pad, selector}, loc);
    cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
    cir::InstId exn_param =
        builder_.add_block_parameter(action, void_ptr, "exn", loc);
    cir::InstId sel_param =
        builder_.add_block_parameter(action, builder_.int_type(), "sel", loc);
    builder_.switch_to_block(action);
    cir::InstId progress_place = builder_.local_place(progress, usize, loc);
    cir::InstId constructed = builder_.lvalue_to_rvalue(progress_place, loc);

    cir::InstId action_place = action_place_builder && *action_place_builder
        ? (*action_place_builder)(loc)
        : rematerialize_entity_place(array_place, loc);
    cir::Fragment unwind_destroy =
        array_destroy_loop_fragment(
            action_place, resolved, constructed, loc,
            ArrayDestructionMode::UnwindCleanup);
    builder_.attach_fragment_to_function(builder_.current_function(),
                                         unwind_destroy);
    builder_.branch(unwind_destroy.entry, {}, loc);
    emit_unwind_continue(unwind_destroy.exit, exn_param, sel_param,
                         saved_target, loc);
    builder_.switch_to_block(pad_previous);

    eh_pads_in_flight_.push_back(landing_pad);
    track_speculative_rollback([this]() {
        if (!eh_pads_in_flight_.empty()) {
            eh_pads_in_flight_.pop_back();
        }
    });
    eh_code_targets_[pad.index] = action;
    track_speculative_rollback([this, pad_index = pad.index]() {
        eh_code_targets_.erase(pad_index);
    });
    builder_.set_current_unwind_target(pad);
    return progress_place;
}

cir::Fragment Session::array_construct_loop_fragment(
    cir::InstId array_place,
    cir::TypeId array_type,
    uint64_t first_leaf,
    uint64_t past_last_leaf,
    SrcLoc loc,
    bool* had_error,
    const std::function<cir::InstId(SrcLoc)>* action_place,
    cir::InstId shared_progress_place) {
    cir::Fragment fragment;
    cir::TypeId resolved = file_.resolved_type(array_type);
    ClassArrayShape shape = class_array_shape(resolved);
    cir::TypeId leaf = shape.leaf_type;
    uint64_t total = shape.total_leaf_count;
    ArrayLifecyclePlan plan;
    plan.shape = shape;
    plan.operation = ArrayLifecycleOperation::DefaultConstruct;
    plan.first_leaf = first_leaf;
    plan.past_last_leaf = past_last_leaf;
    plan.track_progress = record_destructor(leaf).valid();
    if (!plan.valid()) {
        return fragment;
    }
    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved_block = builder_.current_block();

    cir::BlockId saved_target = builder_.current_unwind_target();
    cir::InstId progress_place = shared_progress_place.valid()
        ? shared_progress_place
        : begin_array_construct_unwind(
              array_place, resolved, leaf, saved_target, loc, action_place);

    cir::BlockId entry = builder_.create_detached_block("array.ctor.entry");
    cir::BlockId head = builder_.create_detached_block("array.ctor.head");
    cir::BlockId done = builder_.create_detached_block("array.ctor.done");
    cir::InstId index = builder_.add_block_parameter(head, usize, "idx", loc);

    builder_.switch_to_block(entry);
    cir::InstId flat_place =
        flatten_array_place(array_place, resolved, leaf, total, loc);
    cir::InstId first = builder_.integer_literal(
        static_cast<int64_t>(first_leaf), usize, {}, loc);
    if (progress_place.valid()) {
        builder_.store(rematerialize_entity_place(progress_place, loc),
                       first, loc);
    }
    builder_.branch(head, {first}, loc);

    builder_.switch_to_block(head);
    cir::InstId extent = builder_.integer_literal(
        static_cast<int64_t>(past_last_leaf), usize, {}, loc);
    cir::InstId at_end = builder_.binary(cir::BinaryOpKind::Equal,
                                         builder_.int_type(), index, extent,
                                         loc);

    cir::BlockId body = builder_.create_detached_block("array.ctor.body");
    builder_.cond_branch_from(head, at_end, done, body, {}, loc);

    builder_.switch_to_block(body);
    if (progress_place.valid()) {
        builder_.store(rematerialize_entity_place(progress_place, loc),
                       index, loc);
    }
    cir::InstId element_place =
        builder_.array_element_place(flat_place, index, loc);
    cir::Fragment body_fragment = builder_.block_fragment(body);
    ConstructorCallMaterialization materialized =
        materialize_constructor_call(leaf, {}, loc);
    if (!materialized.constructor.valid()) {
        report_error("no matching default constructor for array elements "
                     "of '" + file_.format_type(leaf) + "'",
                     loc);
        if (had_error) {
            *had_error = true;
        }
    } else {
        if (had_error) {
            *had_error = *had_error || materialized.has_error;
        }
        body_fragment = chain(std::move(body_fragment),
                              std::move(materialized.argument_fragment),
                              loc);
        cir::BlockId construct_previous = builder_.current_block();
        cir::BlockId construct = begin_fragment_block("array.ctor.elem");
        emit_construct_in_place(
            element_place,
            structor_complete_variant(materialized.constructor),
            materialized.argument_values, loc);
        body_fragment = chain(
            std::move(body_fragment),
            finish_fragment_block(construct, construct_previous), loc);
    }
    builder_.switch_to_block(body_fragment.exit);
    cir::InstId one = builder_.integer_literal(1, usize, {}, loc);
    cir::InstId next_index =
        builder_.binary(cir::BinaryOpKind::Add, usize, index, one, loc);
    builder_.branch(head, {next_index}, loc);

    fragment.blocks = {entry, head};
    fragment.blocks.insert(fragment.blocks.end(),
                           body_fragment.blocks.begin(),
                           body_fragment.blocks.end());
    fragment.blocks.push_back(done);
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;

    if (progress_place.valid() && !shared_progress_place.valid()) {
        builder_.set_current_unwind_target(saved_target);

        builder_.set_block_unwind_target(done, saved_target);
    }
    builder_.switch_to_block(saved_block);
    return fragment;
}

cir::Fragment Session::array_transfer_loop_fragment(
    cir::InstId destination_place,
    cir::InstId source_place,
    cir::TypeId array_type,
    cir::EntityId element_function,
    bool assign,
    bool is_move,
    SrcLoc loc,
    bool* had_error,
    const std::function<cir::InstId(SrcLoc)>* action_place) {
    cir::Fragment fragment;
    cir::TypeId resolved = file_.resolved_type(array_type);
    ClassArrayShape shape = class_array_shape(resolved);
    cir::TypeId leaf = shape.leaf_type;
    uint64_t total = shape.total_leaf_count;
    ArrayLifecyclePlan plan;
    plan.shape = shape;
    plan.operation = assign
        ? (is_move ? ArrayLifecycleOperation::MoveAssign
                   : ArrayLifecycleOperation::CopyAssign)
        : (is_move ? ArrayLifecycleOperation::MoveConstruct
                   : ArrayLifecycleOperation::CopyConstruct);
    plan.element_function = element_function;
    plan.first_leaf = 0;
    plan.past_last_leaf = total;
    plan.track_progress = !assign && record_destructor(leaf).valid();
    if (!plan.valid() || !plan.element_function.valid()) {
        return fragment;
    }
    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved_block = builder_.current_block();

    cir::BlockId saved_target = builder_.current_unwind_target();
    cir::InstId progress_place = assign
        ? cir::InstId{}
        : begin_array_construct_unwind(destination_place, resolved, leaf,
                                       saved_target, loc, action_place);

    cir::BlockId entry = builder_.create_detached_block("array.xfer.entry");
    cir::BlockId head = builder_.create_detached_block("array.xfer.head");
    cir::BlockId done = builder_.create_detached_block("array.xfer.done");
    cir::InstId index = builder_.add_block_parameter(head, usize, "idx", loc);

    builder_.switch_to_block(entry);
    cir::InstId flat_destination =
        flatten_array_place(destination_place, resolved, leaf, total, loc);
    cir::InstId flat_source =
        flatten_array_place(source_place, resolved, leaf, total, loc);
    cir::InstId first = builder_.integer_literal(0, usize, {}, loc);
    if (progress_place.valid()) {
        builder_.store(rematerialize_entity_place(progress_place, loc),
                       first, loc);
    }
    builder_.branch(head, {first}, loc);

    builder_.switch_to_block(head);
    cir::InstId extent = builder_.integer_literal(
        static_cast<int64_t>(total), usize, {}, loc);
    cir::InstId at_end = builder_.binary(cir::BinaryOpKind::Equal,
                                         builder_.int_type(), index, extent,
                                         loc);
    cir::BlockId body = builder_.create_detached_block("array.xfer.body");
    builder_.cond_branch_from(head, at_end, done, body, {}, loc);

    builder_.switch_to_block(body);
    if (progress_place.valid()) {
        builder_.store(rematerialize_entity_place(progress_place, loc),
                       index, loc);
    }
    cir::InstId destination_element =
        builder_.array_element_place(flat_destination, index, loc);
    cir::InstId source_element =
        builder_.array_element_place(flat_source, index, loc);
    cir::Fragment body_fragment = builder_.block_fragment(body);
    if (assign) {

        ExprResult callee;
        callee.place = destination_element;
        callee.entity = element_function;
        callee.type = file_.entity(element_function).type;
        callee.name = "operator=";
        callee.qualified_name = true;
        callee.category = ValueCategory::FunctionDesignator;
        ExprResult argument;
        argument.place = source_element;
        argument.type = leaf;
        argument.category =
            is_move ? ValueCategory::XValue : ValueCategory::LValue;
        std::vector<ExprResult> call_arguments;
        call_arguments.push_back(std::move(argument));
        ExprResult call =
            collect_call_expr(std::move(callee), std::move(call_arguments),
                              loc);
        if (had_error) {
            *had_error = *had_error || call.has_error;
        }
        body_fragment =
            chain(std::move(body_fragment), std::move(call.fragment), loc);
    } else {
        cir::BlockId construct_previous = builder_.current_block();
        cir::BlockId construct = begin_fragment_block("array.xfer.elem");
        cir::InstId source_address = builder_.addr_of(source_element, loc);
        emit_construct_in_place(destination_element,
                                structor_complete_variant(element_function),
                                {source_address}, loc);
        body_fragment = chain(
            std::move(body_fragment),
            finish_fragment_block(construct, construct_previous), loc);
    }
    builder_.switch_to_block(body_fragment.exit);
    cir::InstId one = builder_.integer_literal(1, usize, {}, loc);
    cir::InstId next_index =
        builder_.binary(cir::BinaryOpKind::Add, usize, index, one, loc);
    builder_.branch(head, {next_index}, loc);

    fragment.blocks = {entry, head};
    fragment.blocks.insert(fragment.blocks.end(),
                           body_fragment.blocks.begin(),
                           body_fragment.blocks.end());
    fragment.blocks.push_back(done);
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;

    if (progress_place.valid()) {
        builder_.set_current_unwind_target(saved_target);
        builder_.set_block_unwind_target(done, saved_target);
    }
    builder_.switch_to_block(saved_block);
    return fragment;
}

cir::EntityId Session::array_destroy_helper(cir::TypeId array_type,
                                            SrcLoc loc,
                                            ArrayDestructionMode mode) {
    cir::TypeId resolved = file_.resolved_type(array_type);
    if (!file_.valid(resolved)) {
        return {};
    }
    uint64_t key = (static_cast<uint64_t>(resolved.index) << 1) |
        (mode == ArrayDestructionMode::UnwindCleanup ? 1ull : 0ull);
    if (!collecting_pattern_) {
        auto found = array_destroy_helpers_.find(key);
        if (found != array_destroy_helpers_.end()) {
            return found->second;
        }
    }
    cir::TypeId leaf = array_class_element_leaf(resolved);
    if (!leaf.valid() || !record_destructor(leaf).valid()) {
        return {};
    }
    std::string symbol = abi::itanium_type_data_symbol(
        file_, file_.type_ref(resolved),
        mode == ArrayDestructionMode::Normal
            ? "__aburi_array_dtor_"
            : "__aburi_array_dtor_unwind_");
    if (symbol.empty()) {
        return {};
    }
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId pointer_type = builder_.pointer_type(resolved);
    cir::TypeId helper_type =
        function_type(file_.type_ref(void_type),
                      {file_.type_ref(pointer_type)}, false, true);
    std::vector<ParamInput> params;
    ParamInput param;
    param.name = ".array";
    param.type = file_.type_ref(pointer_type);
    param.loc = loc;
    params.push_back(std::move(param));

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags flags;
    FunctionDeclStart helper = begin_function_type(
        symbol, helper_type, file_.type_ref(void_type), params, loc, flags);
    file_.entity_mut(helper.decl.entity).is_extern_c = true;
    file_.entity_mut(helper.decl.entity).linkage = cir::LinkageKind::LinkOnceODR;
    mark_generated_abi_entity(helper.decl.entity,
                              file_.record_entity(file_.resolved_type(leaf)),
                              cir::GeneratedSymbolRole::ArrayCleanup);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId entry = begin_fragment_block("array.dtor.helper");
    cir::InstId pointer = helper.function.parameters.front().value.inst;
    cir::InstId place = builder_.deref(pointer, loc);
    cir::Fragment body = finish_fragment_block(entry, previous);
    std::function<cir::InstId(SrcLoc)> action_place =
        [this, pointer](SrcLoc action_loc) {
            return builder_.deref(pointer, action_loc);
        };
    cir::Fragment destroy = array_destroy_loop_fragment(
        place, resolved, {}, loc, mode,
        mode == ArrayDestructionMode::Normal ? &action_place : nullptr);
    body = chain(std::move(body), std::move(destroy), loc);
    builder_.switch_to_block(body.exit);
    builder_.return_void(loc);
    builder_.switch_to_block(previous);
    finish_function(make_stmt_result(std::move(body), true, false), loc);
    restore_function_context(std::move(saved));

    array_destroy_helpers_[key] = helper.decl.entity;
    track_speculative_rollback([this, key]() {
        array_destroy_helpers_.erase(key);
    });
    return helper.decl.entity;
}

bool Session::diagnose_abstract_instantiation(cir::TypeId type, SrcLoc loc) {
    cir::TypeId object_type = file_.resolved_type(type);
    while (file_.valid(object_type) &&
           file_.type(object_type).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(object_type));
        if (!array) {
            break;
        }
        object_type = file_.resolved_type(array->element_type.type);
    }
    const cir::RecordFacts* facts =
        file_.record_facts_for_type(object_type);
    if (facts && facts->is_abstract) {
        report_error("cannot create an object of abstract class type '" +
                         file_.format_type(object_type) + "'",
                     loc);
        return true;
    }
    return false;
}

bool Session::diagnose_abstract_function_use(cir::TypeId function_type,
                                             AbstractFunctionUse use,
                                             SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode()) {
        return false;
    }

    cir::TypeId resolved = file_.resolved_type(function_type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Function) {
        return false;
    }
    const auto* function =
        std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved));
    if (!function) {
        return false;
    }

    bool diagnosed = false;
    auto diagnose_type = [&](cir::TypeRef type, std::string_view role) {
        cir::TypeId object_type = file_.resolved_type(type.type);
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(object_type);
        if (!facts || !facts->is_abstract) {
            return;
        }

        std::string action = use == AbstractFunctionUse::Definition
            ? "function definition cannot have "
            : "function call cannot use ";
        report_error(action + std::string(role) + " of abstract class type '" +
                         file_.format_type(type.type) + "'",
                     loc);
        diagnosed = true;
    };

    if (use == AbstractFunctionUse::Definition) {
        diagnose_type(function->return_type, "a return type");
    }
    for (cir::TypeRef parameter : function->parameters) {
        diagnose_type(parameter, "a parameter");
    }
    return diagnosed;
}

void Session::diagnose_abstract_call_result_materialization(ExprResult& expr,
                                                            SrcLoc loc) {
    if (!expr.unmaterialized_abstract_call_result) {
        return;
    }
    report_error("function call cannot use a return type of abstract class type '" +
                     file_.format_type(expr.type) + "'",
                 expr.abstract_call_loc.isInvalid() ? loc
                                                    : expr.abstract_call_loc);
    expr.unmaterialized_abstract_call_result = false;
    expr.has_error = true;
}

DeclResult Session::construct_global_variable(DeclResult started,
                                              std::vector<ExprResult> arguments,
                                              SrcLoc loc,
                                              ConstructorInitializationKind init_kind,
                                              bool value_initialize,
                                              std::optional<ExprResult> initializer) {

    bool published_constant = started.entity.valid() &&
        file_.valid(started.entity) &&
        file_.entity(started.entity).constant_state.valid();
    if (!published_constant && !initializer.has_value()) {
        published_constant = try_publish_constant_construction(
            started, arguments, init_kind, value_initialize, loc);
    }
    bool needs_constant_cleanup =
        record_destructor(started.type).valid() ||
        array_class_element_leaf(started.type).valid();
    if (published_constant && !needs_constant_cleanup) {
        started.fragment = {};
        return started;
    }
    if (!published_constant && started.entity.valid() &&
        file_.valid(started.entity) &&
        file_.entity(started.entity).decl_flags.is_constinit) {
        report_error("constinit variable does not have a constant initializer",
                     loc);
        started.has_error = true;
        return started;
    }

    uint32_t index = ++global_init_counter_;
    const cir::Entity& object = file_.entity(started.entity);
    bool mergeable = object.linkage == cir::LinkageKind::LinkOnceODR ||
                     object.decl_flags.is_inline;
    std::string object_symbol =
        abi::itanium_linkage_name(file_, started.entity);
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId init_type =
        function_type(file_.type_ref(void_type), {}, false, true);

    cir::EntityId cleanup_entity{};
    cir::TypeId void_pointer = builder_.pointer_type(void_type);
    cir::TypeId cleanup_type = function_type(
        file_.type_ref(void_type), {file_.type_ref(void_pointer)}, false, true);
    cir::TypeId global_array_leaf = array_class_element_leaf(started.type);
    cir::EntityId destructor =
        global_array_leaf.valid() ? cir::EntityId{}
                                  : record_destructor(started.type);
    cir::EntityId global_array_helper = global_array_leaf.valid()
        ? array_destroy_helper(started.type, loc)
        : cir::EntityId{};
    if (destructor.valid() || global_array_helper.valid()) {
        std::unique_ptr<BlockContextState> saved = save_function_context();
        DeclFlags cleanup_flags;
        cleanup_flags.is_static = true;
        ParamInput object_param;
        object_param.name = ".object";
        object_param.type = file_.type_ref(void_pointer);
        object_param.loc = loc;
        std::string cleanup_name = mergeable
            ? generated_owner_helper_name(file_, started.entity,
                                          "__aburi_cxx_global_cleanup_", index)
            : "__cxx_global_var_cleanup." + std::to_string(index);
        FunctionDeclStart cleanup = begin_function_type(
            cleanup_name, cleanup_type,
            file_.type_ref(void_type), {object_param}, loc, cleanup_flags);
        if (mergeable) {
            file_.entity_mut(cleanup.decl.entity).is_extern_c = true;
            file_.entity_mut(cleanup.decl.entity).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("global.cleanup");
        cir::InstId object = cleanup.function.parameters.front().value.inst;
        cir::InstId typed_pointer = builder_.cast(
            builder_.pointer_type(started.type), object, "value", loc);
        cir::InstId place = builder_.deref(typed_pointer, loc);
        if (global_array_helper.valid()) {
            cir::InstId address = builder_.addr_of(place, loc);
            builder_.call(global_array_helper, void_type, {address}, loc);
            builder_.return_void(loc);
            cir::Fragment body = finish_fragment_block(block, previous);
            finish_function(make_stmt_result(std::move(body), true, false),
                            loc);
        } else {
            emit_destroy(place, structor_complete_variant(destructor), loc);
            builder_.return_void(loc);
            cir::Fragment body = finish_fragment_block(block, previous);
            finish_function(make_stmt_result(std::move(body), true, false),
                            loc);
        }
        restore_function_context(std::move(saved));
        cleanup_entity = cleanup.decl.entity;
        mark_generated_abi_entity(cleanup_entity, started.entity,
                                  cir::GeneratedSymbolRole::StaticCleanup);
    }

    cir::EntityId guard_entity{};
    if (mergeable) {
        std::string encoding;
        if (object_symbol.starts_with("_Z")) {
            encoding = object_symbol.substr(2);
        } else {
            std::string_view source_name =
                file_.entity(started.entity).name.valid()
                    ? file_.name(file_.entity(started.entity).name)
                    : std::string_view("object");
            encoding = std::to_string(source_name.size()) +
                       std::string(source_name);
        }
        std::string guard_symbol = "_ZGV" + encoding;
        cir::TypeId guard_type =
            file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
        guard_entity = builder_.add_entity(
            cir::EntityKind::Variable, guard_symbol, guard_type, {}, loc,
            cir::StorageDuration::Static);
        cir::Entity& guard = file_.entity_mut(guard_entity);
        guard.is_definition = true;
        guard.linkage = cir::LinkageKind::LinkOnceODR;
        guard.has_static_initializer = true;
        guard.static_initializer_bytes.assign(8, 0);
        guard.attr_facts.asm_label = guard_symbol;
        mark_generated_abi_entity(guard_entity, started.entity,
                                  cir::GeneratedSymbolRole::Guard);
    }

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags init_flags;
    init_flags.is_static = true;
    std::string init_name = mergeable
        ? generated_owner_helper_name(file_, started.entity,
                                      "__aburi_cxx_global_init_", index)
        : "__cxx_global_var_init." + std::to_string(index);
    FunctionDeclStart init = begin_function_type(
        init_name, init_type,
        file_.type_ref(void_type), {}, loc, init_flags);
    if (mergeable) {
        file_.entity_mut(init.decl.entity).is_extern_c = true;
        file_.entity_mut(init.decl.entity).linkage =
            cir::LinkageKind::LinkOnceODR;
    }
    mark_generated_abi_entity(init.decl.entity, started.entity,
                              cir::GeneratedSymbolRole::StaticInitializer);

    global_init_functions_.push_back(init.decl.entity);

    cir::Fragment guarded_prefix;
    cir::BlockId guarded_acquire{};
    cir::BlockId guarded_init_entry{};
    cir::BlockId guarded_continuation{};
    cir::BlockId saved_unwind_target = builder_.current_unwind_target();
    if (guard_entity.valid()) {
        cir::BlockId guard_previous = builder_.current_block();
        cir::BlockId guard_block = begin_fragment_block("inline.guard");
        cir::InstId guard_place = builder_.global_place(guard_entity, loc);
        cir::TypeId byte_type = builder_.char_type();
        cir::InstId guard_address = builder_.addr_of(guard_place, loc);
        cir::InstId byte_pointer = builder_.cast(
            builder_.pointer_type(byte_type), guard_address, "value", loc);
        cir::InstId byte_place = builder_.deref(byte_pointer, loc);
        cir::InstId guard_value =
            builder_.lvalue_to_rvalue(byte_place, loc);
        cir::InstId zero =
            builder_.integer_literal(0, byte_type, "0", loc);
        cir::InstId needs_init = builder_.binary(
            cir::BinaryOpKind::Equal, builder_.int_type(), guard_value, zero,
            loc);
        guarded_prefix = finish_fragment_block(guard_block, guard_previous);
        guarded_acquire =
            builder_.create_detached_block("inline.acquire");
        guarded_init_entry =
            builder_.create_detached_block("inline.init");
        guarded_continuation =
            builder_.create_detached_block("inline.done");
        builder_.cond_branch_from(guarded_prefix.exit, needs_init,
                                  guarded_acquire,
                                  guarded_continuation, {}, loc);

        cir::TypeId guard_type = file_.entity(guard_entity).type;
        cir::TypeId guard_pointer = builder_.pointer_type(guard_type);
        builder_.switch_to_block(guarded_acquire);
        cir::EntityId acquire_fn = runtime_function(
            "__cxa_guard_acquire",
            function_type(file_.type_ref(builder_.int_type()),
                          {file_.type_ref(guard_pointer)}, false, true),
            loc);
        cir::InstId acquired = builder_.call(
            acquire_fn, builder_.int_type(),
            {builder_.addr_of(builder_.global_place(guard_entity, loc), loc)},
            loc);
        cir::InstId int_zero =
            builder_.integer_literal(0, builder_.int_type(), "0", loc);
        cir::InstId won = builder_.binary(
            cir::BinaryOpKind::NotEqual, builder_.int_type(), acquired,
            int_zero, loc);
        builder_.cond_branch_from(guarded_acquire, won, guarded_init_entry,
                                  guarded_continuation, {}, loc);

        cir::BlockId abort_previous = builder_.current_block();
        builder_.set_current_unwind_target({});
        cir::BlockId abort_pad =
            builder_.create_block("inline.init.lpad");
        cir::BlockId abort_action =
            builder_.create_block("inline.guard.abort");
        builder_.set_block_unwind_target(abort_pad, {});
        builder_.set_block_unwind_target(abort_action, {});
        builder_.switch_to_block(abort_pad);
        cir::EhLandingPadPayload payload;
        payload.is_cleanup = true;
        cir::InstId landing_pad =
            builder_.eh_landing_pad(std::move(payload), loc);
        cir::InstId selector = builder_.eh_selector(landing_pad, loc);
        builder_.branch(abort_action, {landing_pad, selector}, loc);
        cir::InstId exn = builder_.add_block_parameter(
            abort_action, void_pointer, "exn", loc);
        cir::InstId sel = builder_.add_block_parameter(
            abort_action, builder_.int_type(), "sel", loc);
        builder_.switch_to_block(abort_action);
        cir::EntityId abort_fn = runtime_function(
            "__cxa_guard_abort",
            function_type(file_.type_ref(void_type),
                          {file_.type_ref(guard_pointer)}, false, true),
            loc);
        builder_.call(
            abort_fn, void_type,
            {builder_.addr_of(builder_.global_place(guard_entity, loc), loc)},
            loc);
        emit_unwind_continue(abort_action, exn, sel, saved_unwind_target, loc);
        builder_.switch_to_block(abort_previous);
        eh_pads_in_flight_.push_back(landing_pad);
        track_speculative_rollback([this]() {
            if (!eh_pads_in_flight_.empty()) {
                eh_pads_in_flight_.pop_back();
            }
        });
        eh_code_targets_[abort_pad.index] = abort_action;
        track_speculative_rollback([this, pad_index = abort_pad.index]() {
            eh_code_targets_.erase(pad_index);
        });
        builder_.set_current_unwind_target(abort_pad);
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("global.init");
    cir::InstId place = builder_.global_place(started.entity, loc);
    cir::Fragment place_fragment = finish_fragment_block(block, previous);

    DeclResult constructed = started;
    constructed.place = place;
    constructed.fragment = {};
    if (published_constant) {
        constructed.fragment = {};
    } else if (initializer.has_value()) {
        bool initializer_error = initializer->has_error;
        constructed.fragment = emit_initializer_for_place(
            place, started.type, std::move(*initializer), loc);
        constructed.has_error = constructed.has_error || initializer_error;
    } else {
        constructed = construct_variable(std::move(constructed),
                                         std::move(arguments), loc, init_kind,
                                         value_initialize);
    }
    cir::Fragment body =
        chain(std::move(place_fragment), std::move(constructed.fragment), loc);

    if (cleanup_entity.valid()) {
        cir::BlockId exit_previous = builder_.current_block();
        cir::BlockId exit_block = begin_fragment_block("global.cxa_atexit");
        cir::TypeId cleanup_pointer = builder_.pointer_type(cleanup_type);
        cir::EntityId atexit_fn = runtime_function(
            "__cxa_atexit",
            function_type(file_.type_ref(builder_.int_type()),
                          {file_.type_ref(cleanup_pointer),
                           file_.type_ref(void_pointer),
                           file_.type_ref(void_pointer)},
                          false, true),
            loc);
        cir::InstId cleanup_address =
            builder_.function_to_pointer(cleanup_entity, loc);
        cir::InstId object_address = builder_.cast(
            void_pointer, builder_.addr_of(place, loc), "value", loc);
        cir::EntityId dso = extern_runtime_global("__dso_handle", loc);
        cir::InstId dso_address = builder_.cast(
            void_pointer,
            builder_.addr_of(builder_.global_place(dso, loc), loc),
            "value", loc);
        builder_.call(atexit_fn, builder_.int_type(),
                      {cleanup_address, object_address, dso_address}, loc);
        cir::Fragment atexit_fragment =
            finish_fragment_block(exit_block, exit_previous);
        body = chain(std::move(body), std::move(atexit_fragment), loc);
    }
    if (guard_entity.valid()) {
        cir::BlockId release_previous = builder_.current_block();
        cir::BlockId release_block =
            begin_fragment_block("inline.release");
        cir::TypeId guard_pointer =
            builder_.pointer_type(file_.entity(guard_entity).type);
        cir::EntityId release_fn = runtime_function(
            "__cxa_guard_release",
            function_type(file_.type_ref(void_type),
                          {file_.type_ref(guard_pointer)}, false, true),
            loc);
        builder_.call(
            release_fn, void_type,
            {builder_.addr_of(builder_.global_place(guard_entity, loc), loc)},
            loc);
        body = chain(std::move(body),
                     finish_fragment_block(release_block, release_previous),
                     loc);
        builder_.set_current_unwind_target(saved_unwind_target);

        auto merge_blocks = [](cir::Fragment& target,
                               const cir::Fragment& source) {
            if (source.empty()) {
                return;
            }
            if (target.empty()) {
                target.entry = source.entry;
            }
            target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                                 source.blocks.end());
            target.exit = source.exit;
        };
        cir::Fragment guarded = std::move(guarded_prefix);
        merge_blocks(guarded, builder_.block_fragment(guarded_acquire));
        merge_blocks(guarded, builder_.block_fragment(guarded_init_entry));
        builder_.branch_from(guarded_init_entry, body.entry, {}, loc);
        merge_blocks(guarded, body);
        builder_.branch_from(body.exit, guarded_continuation, {}, loc);
        merge_blocks(guarded,
                     builder_.block_fragment(guarded_continuation));
        guarded.exit = guarded_continuation;
        body = std::move(guarded);
    }
    finish_function(make_stmt_result(std::move(body)), loc);
    restore_function_context(std::move(saved));

    if (cleanup_entity.valid()) {
        cir::LifetimeId lifetime{
            static_cast<uint32_t>(lifetime_obligations_.size()),
            next_lifetime_generation_++};
        lifetime_obligations_.push_back(LifetimeObligation{
            lifetime, started.entity, started.type, cleanup_entity, loc,
            LifetimeOwnerKind::StaticExit,
            static_cast<uint64_t>(started.entity.index), true});
    }

    started.has_error = started.has_error || constructed.has_error;
    started.fragment = {};
    return started;
}

DeclResult Session::initialize_global_variable(DeclResult started,
                                               ExprResult initializer,
                                               SrcLoc loc,
                                               ConstructorInitializationKind
                                                   init_kind) {

    started.has_error = started.has_error || initializer.has_error;
    uint32_t index = ++global_init_counter_;
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId init_type =
        function_type(file_.type_ref(void_type), {}, false, true);

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags init_flags;
    init_flags.is_static = true;
    FunctionDeclStart init = begin_function_type(
        "__cxx_global_var_init." + std::to_string(index), init_type,
        file_.type_ref(void_type), {}, loc, init_flags);
    mark_generated_abi_entity(init.decl.entity, started.entity,
                              cir::GeneratedSymbolRole::StaticInitializer);
    global_init_functions_.push_back(init.decl.entity);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("global.init.place");
    cir::InstId place = builder_.global_place(started.entity, loc);
    cir::Fragment place_fragment = finish_fragment_block(block, previous);
    cir::Fragment initializer_fragment;
    if (initializer.category == ValueCategory::InitList &&
        initializer_list_element_type(started.type).has_value()) {
        ExprResult value = materialize_list_initialization(
            std::move(initializer), started.type, UseContext::Init, loc,
            cir::StorageDuration::Static);
        started.has_error = started.has_error || value.has_error;
        initializer_fragment = std::move(value.fragment);
        if (!value.has_error && value.value.valid()) {
            cir::BlockId store_previous = builder_.current_block();
            cir::BlockId store_block =
                begin_fragment_block("global.initializer_list.store");
            builder_.store(place, value.value, loc);
            initializer_fragment = chain(
                std::move(initializer_fragment),
                finish_fragment_block(store_block, store_previous), loc);
        }
        for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
            transfer_lifetime(lifetime, LifetimeOwnerKind::StaticExit,
                              started.entity.index);
        }
    } else {
        initializer_fragment = emit_initializer_for_place(
            place, started.type, std::move(initializer), loc,
            init_kind == ConstructorInitializationKind::Direct
                ? UseContext::DirectInit
                : UseContext::Init);
    }
    cir::Fragment body = chain(std::move(place_fragment),
                               std::move(initializer_fragment), loc);
    finish_function(make_stmt_result(std::move(body)), loc);
    restore_function_context(std::move(saved));

    started.fragment = {};
    return started;
}

void Session::finish_global_initialization(SrcLoc loc) {

    std::vector<cir::EntityId> local_inits;
    local_inits.reserve(global_init_functions_.size());
    for (cir::EntityId init : global_init_functions_) {
        const cir::Entity& init_entity = file_.entity(init);
        bool imported = init_entity.origin_unit.valid() &&
            init_entity.origin_unit != module_state_.unit &&
            file_.has_imported_definition(init) &&
            init_entity.linkage != cir::LinkageKind::LinkOnceODR;
        if (!imported) {
            local_inits.push_back(init);
        }
    }
    global_init_functions_ = std::move(local_inits);
    if (global_init_functions_.empty()) {
        return;
    }
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId init_type =
        function_type(file_.type_ref(void_type), {}, false, true);
    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags flags;
    flags.is_static = true;
    FunctionDeclStart fn = begin_function_type("_GLOBAL__sub_I_a.cpp",
                                               init_type,
                                               file_.type_ref(void_type),
                                               {}, loc, flags);
    mark_generated_abi_entity(fn.decl.entity, {},
                              cir::GeneratedSymbolRole::StaticInitializer);
    file_.entity_mut(fn.decl.entity).attr_facts.constructor_priority = 65535;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("global.sub_i");
    for (cir::EntityId init : global_init_functions_) {
        builder_.call(init, void_type, {}, loc);
    }
    builder_.return_void(loc);
    cir::Fragment body = finish_fragment_block(block, previous);
    finish_function(make_stmt_result(std::move(body), true, false), loc);
    restore_function_context(std::move(saved));
    global_init_functions_.clear();
}

DeclResult Session::construct_local_static(DeclResult started,
                                           std::vector<ExprResult> arguments,
                                           SrcLoc loc,
                                           ConstructorInitializationKind init_kind,
                                           bool value_initialize,
                                           std::optional<ExprResult> initializer) {

    uint32_t index = ++global_init_counter_;
    const cir::Entity& object = file_.entity(started.entity);
    bool mergeable = false;
    if (object.local_enclosing_function.valid() &&
        file_.valid(object.local_enclosing_function)) {
        const cir::Entity& function =
            file_.entity(object.local_enclosing_function);
        mergeable = function.linkage == cir::LinkageKind::LinkOnceODR ||
            function.decl_flags.is_inline ||
            (file_.template_specialization(object.local_enclosing_function) &&
             !function.is_explicit_template_specialization);
    }
    cir::TypeId guard_type = builder_.usize_type();
    std::string entity_name = object.name.valid()
        ? std::string(file_.name(object.name))
        : std::string("static");
    std::string object_symbol = abi::itanium_linkage_name(file_, started.entity);
    std::string guard_symbol;
    if (mergeable && object_symbol.starts_with("_Z")) {
        guard_symbol = "_ZGV" + object_symbol.substr(2);
    } else {
        guard_symbol = ".static.guard." + std::to_string(index) + "." +
                       entity_name;
    }
    cir::EntityId guard_entity = builder_.add_entity(
        cir::EntityKind::Variable, guard_symbol,
        guard_type, {}, loc, cir::StorageDuration::Static);
    cir::Entity& guard_record = file_.entity_mut(guard_entity);
    guard_record.is_definition = true;
    guard_record.linkage = mergeable ? cir::LinkageKind::LinkOnceODR
                                     : cir::LinkageKind::Internal;
    guard_record.has_static_initializer = true;
    guard_record.static_initializer_bytes.assign(8, 0);
    if (mergeable) {
        guard_record.attr_facts.asm_label = guard_symbol;
    }
    mark_generated_abi_entity(guard_entity, started.entity,
                              cir::GeneratedSymbolRole::Guard);

    cir::EntityId cleanup_entity{};
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId void_pointer = builder_.pointer_type(void_type);
    cir::TypeId cleanup_type = function_type(
        file_.type_ref(void_type), {file_.type_ref(void_pointer)}, false, true);
    cir::TypeId static_array_leaf = array_class_element_leaf(started.type);
    cir::EntityId destructor =
        static_array_leaf.valid() ? cir::EntityId{}
                                  : record_destructor(started.type);
    cir::EntityId static_array_helper = static_array_leaf.valid()
        ? array_destroy_helper(started.type, loc)
        : cir::EntityId{};
    if (destructor.valid() || static_array_helper.valid()) {
        std::unique_ptr<BlockContextState> saved = save_function_context();
        DeclFlags cleanup_flags;
        cleanup_flags.is_static = true;
        ParamInput object_param;
        object_param.name = ".object";
        object_param.type = file_.type_ref(void_pointer);
        object_param.loc = loc;
        std::string cleanup_name = mergeable
            ? generated_owner_helper_name(file_, started.entity,
                                          "__aburi_cxx_static_cleanup_", index)
            : "__cxx_static_cleanup." + std::to_string(index);
        FunctionDeclStart cleanup = begin_function_type(
            cleanup_name, cleanup_type,
            file_.type_ref(void_type), {object_param}, loc, cleanup_flags);
        if (mergeable) {
            file_.entity_mut(cleanup.decl.entity).is_extern_c = true;
            file_.entity_mut(cleanup.decl.entity).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("static.cleanup");
        cir::InstId object = cleanup.function.parameters.front().value.inst;
        cir::InstId typed_pointer = builder_.cast(
            builder_.pointer_type(started.type), object, "value", loc);
        cir::InstId place = builder_.deref(typed_pointer, loc);
        if (static_array_helper.valid()) {
            cir::InstId address = builder_.addr_of(place, loc);
            builder_.call(static_array_helper, void_type, {address}, loc);
        } else {
            emit_destroy(place, structor_complete_variant(destructor), loc);
        }
        builder_.return_void(loc);
        cir::Fragment body = finish_fragment_block(block, previous);
        finish_function(make_stmt_result(std::move(body), true, false), loc);
        restore_function_context(std::move(saved));
        cleanup_entity = cleanup.decl.entity;
        mark_generated_abi_entity(cleanup_entity, started.entity,
                                  cir::GeneratedSymbolRole::StaticCleanup);
    }

    cir::Fragment fragment = adopt_or_create_fragment_entry(
        std::move(started.fragment), "static.guard");
    cir::BlockId previous = builder_.current_block();
    builder_.switch_to_block(fragment.exit);
    cir::InstId guard_place = builder_.global_place(guard_entity, loc);

    cir::TypeId byte_type = builder_.char_type();
    cir::InstId guard_address = builder_.addr_of(guard_place, loc);
    cir::InstId byte_pointer = builder_.cast(
        builder_.pointer_type(byte_type), guard_address, "value", loc);
    cir::InstId byte_place = builder_.deref(byte_pointer, loc);
    cir::InstId guard_value = builder_.lvalue_to_rvalue(byte_place, loc);
    cir::InstId zero = builder_.integer_literal(0, byte_type, "0", loc);
    cir::InstId needs_init = builder_.binary(
        cir::BinaryOpKind::Equal, builder_.int_type(), guard_value, zero, loc);
    cir::BlockId acquire_block = builder_.create_detached_block("static.acquire");
    cir::BlockId init_empty = builder_.create_detached_block("static.init");
    cir::BlockId continuation = builder_.create_detached_block("static.done");
    builder_.cond_branch_from(fragment.exit, needs_init, acquire_block,
                              continuation, {}, loc);

    cir::TypeId guard_pointer_type = builder_.pointer_type(guard_type);
    builder_.switch_to_block(acquire_block);
    cir::EntityId acquire_fn = runtime_function(
        "__cxa_guard_acquire",
        function_type(file_.type_ref(builder_.int_type()),
                      {file_.type_ref(guard_pointer_type)}, false, true),
        loc);
    cir::InstId acquire_address = builder_.addr_of(guard_place, loc);
    cir::InstId acquired = builder_.call(acquire_fn, builder_.int_type(),
                                         {acquire_address}, loc);
    cir::InstId int_zero =
        builder_.integer_literal(0, builder_.int_type(), "0", loc);
    cir::InstId won_init = builder_.binary(cir::BinaryOpKind::NotEqual,
                                           builder_.int_type(), acquired,
                                           int_zero, loc);
    builder_.cond_branch_from(acquire_block, won_init, init_empty,
                              continuation, {}, loc);

    cir::BlockId saved_unwind_target = builder_.current_unwind_target();
    cir::BlockId abort_previous = builder_.current_block();
    builder_.set_current_unwind_target({});
    cir::BlockId abort_pad = builder_.create_block("static.init.lpad");
    cir::BlockId abort_action = builder_.create_block("static.guard.abort");
    builder_.set_block_unwind_target(abort_pad, {});
    builder_.set_block_unwind_target(abort_action, {});
    builder_.switch_to_block(abort_pad);
    cir::EhLandingPadPayload abort_payload;
    abort_payload.is_cleanup = true;
    cir::InstId abort_landing_pad =
        builder_.eh_landing_pad(std::move(abort_payload), loc);
    cir::InstId abort_selector =
        builder_.eh_selector(abort_landing_pad, loc);
    builder_.branch(abort_action, {abort_landing_pad, abort_selector}, loc);
    cir::InstId abort_exn = builder_.add_block_parameter(
        abort_action, void_pointer, "exn", loc);
    cir::InstId abort_sel = builder_.add_block_parameter(
        abort_action, builder_.int_type(), "sel", loc);
    builder_.switch_to_block(abort_action);
    cir::EntityId abort_fn = runtime_function(
        "__cxa_guard_abort",
        function_type(file_.type_ref(void_type),
                      {file_.type_ref(guard_pointer_type)}, false, true),
        loc);
    cir::InstId abort_guard_place =
        builder_.global_place(guard_entity, loc);
    builder_.call(abort_fn, void_type,
                  {builder_.addr_of(abort_guard_place, loc)}, loc);
    emit_unwind_continue(abort_action, abort_exn, abort_sel,
                         saved_unwind_target, loc);
    builder_.switch_to_block(abort_previous);
    eh_pads_in_flight_.push_back(abort_landing_pad);
    track_speculative_rollback([this]() {
        if (!eh_pads_in_flight_.empty()) {
            eh_pads_in_flight_.pop_back();
        }
    });
    eh_code_targets_[abort_pad.index] = abort_action;
    track_speculative_rollback([this, pad_index = abort_pad.index]() {
        eh_code_targets_.erase(pad_index);
    });
    builder_.set_current_unwind_target(abort_pad);

    cir::BlockId work_previous = builder_.current_block();
    cir::BlockId work_block = begin_fragment_block("static.init.work");
    cir::InstId object_place = builder_.global_place(started.entity, loc);
    cir::Fragment work_fragment =
        finish_fragment_block(work_block, work_previous);

    DeclResult constructed = started;
    constructed.place = object_place;
    constructed.fragment = {};
    if (initializer.has_value()) {
        bool initializer_error = initializer->has_error;
        if (initializer->category == ValueCategory::InitList &&
            initializer_list_element_type(started.type).has_value()) {
            ExprResult value = materialize_list_initialization(
                std::move(*initializer), started.type, UseContext::Init, loc,
                cir::StorageDuration::Static);
            constructed.has_error =
                constructed.has_error || initializer_error || value.has_error;
            constructed.fragment = std::move(value.fragment);
            if (!value.has_error && value.value.valid()) {
                cir::BlockId store_previous = builder_.current_block();
                cir::BlockId store_block = begin_fragment_block(
                    "static.initializer_list.store");
                builder_.store(object_place, value.value, loc);
                constructed.fragment = chain(
                    std::move(constructed.fragment),
                    finish_fragment_block(store_block, store_previous), loc);
            }
            for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
                transfer_lifetime(lifetime, LifetimeOwnerKind::StaticExit,
                                  started.entity.index);
            }
        } else {
            constructed.fragment = emit_initializer_for_place(
                object_place, started.type, std::move(*initializer), loc,
                init_kind == ConstructorInitializationKind::Direct
                    ? UseContext::DirectInit
                    : UseContext::Init);
            constructed.has_error =
                constructed.has_error || initializer_error;
        }
    } else {
        constructed = construct_variable(std::move(constructed),
                                         std::move(arguments), loc, init_kind,
                                         value_initialize);
    }
    cir::Fragment init_fragment = chain(std::move(work_fragment),
                                        std::move(constructed.fragment), loc);
    if (cleanup_entity.valid()) {
        cir::BlockId atexit_previous = builder_.current_block();
        cir::BlockId atexit_block =
            begin_fragment_block("static.cxa_atexit");
        cir::TypeId cleanup_pointer_type =
            builder_.pointer_type(cleanup_type);
        cir::EntityId atexit_fn = runtime_function(
            "__cxa_atexit",
            function_type(file_.type_ref(builder_.int_type()),
                          {file_.type_ref(cleanup_pointer_type),
                           file_.type_ref(void_pointer),
                           file_.type_ref(void_pointer)},
                          false, true),
            loc);
        cir::InstId cleanup_pointer =
            builder_.function_to_pointer(cleanup_entity, loc);
        cir::InstId object_address = builder_.cast(
            void_pointer, builder_.addr_of(object_place, loc), "value", loc);
        cir::EntityId dso = extern_runtime_global("__dso_handle", loc);
        cir::InstId dso_address = builder_.cast(
            void_pointer,
            builder_.addr_of(builder_.global_place(dso, loc), loc),
            "value", loc);
        builder_.call(atexit_fn, builder_.int_type(),
                      {cleanup_pointer, object_address, dso_address}, loc);
        cir::Fragment atexit_fragment =
            finish_fragment_block(atexit_block, atexit_previous);
        init_fragment = chain(std::move(init_fragment),
                              std::move(atexit_fragment), loc);
    }
    {
        cir::BlockId release_previous = builder_.current_block();
        cir::BlockId release_block = begin_fragment_block("static.release");
        cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
        cir::EntityId release_fn = runtime_function(
            "__cxa_guard_release",
            function_type(file_.type_ref(void_type),
                          {file_.type_ref(guard_pointer_type)}, false, true),
            loc);
        cir::InstId release_address = builder_.addr_of(guard_place, loc);
        builder_.call(release_fn, void_type, {release_address}, loc);
        cir::Fragment release_fragment =
            finish_fragment_block(release_block, release_previous);
        init_fragment = chain(std::move(init_fragment),
                              std::move(release_fragment), loc);
    }
    builder_.set_current_unwind_target(saved_unwind_target);

    auto merge_blocks = [](cir::Fragment& target, const cir::Fragment& source) {
        if (source.empty()) {
            return;
        }
        if (target.empty()) {
            target.entry = source.entry;
        }
        target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                             source.blocks.end());
        target.exit = source.exit;
    };
    merge_blocks(fragment, builder_.block_fragment(acquire_block));
    merge_blocks(fragment, builder_.block_fragment(init_empty));
    builder_.branch_from(init_empty, init_fragment.entry, {}, loc);
    merge_blocks(fragment, init_fragment);
    builder_.branch_from(init_fragment.exit, continuation, {}, loc);
    merge_blocks(fragment, builder_.block_fragment(continuation));
    fragment.exit = continuation;
    builder_.switch_to_block(previous);

    started.has_error = started.has_error || constructed.has_error;
    started.fragment = std::move(fragment);
    if (cleanup_entity.valid()) {
        cir::LifetimeId lifetime{
            static_cast<uint32_t>(lifetime_obligations_.size()),
            next_lifetime_generation_++};
        lifetime_obligations_.push_back(LifetimeObligation{
            lifetime, started.entity, started.type, cleanup_entity, loc,
            LifetimeOwnerKind::StaticExit,
            static_cast<uint64_t>(started.entity.index), true});
    }
    return started;
}

DeclResult Session::construct_thread_variable(
    DeclResult started,
    std::vector<ExprResult> arguments,
    SrcLoc loc,
    ConstructorInitializationKind init_kind,
    bool value_initialize,
    std::optional<ExprResult> initializer) {
    uint32_t index = ++global_init_counter_;
    const cir::Entity& object = file_.entity(started.entity);
    bool mergeable = object.linkage == cir::LinkageKind::LinkOnceODR;
    if (!mergeable && object.local_enclosing_function.valid() &&
        file_.valid(object.local_enclosing_function)) {
        const cir::Entity& function =
            file_.entity(object.local_enclosing_function);
        mergeable = function.linkage == cir::LinkageKind::LinkOnceODR ||
            function.decl_flags.is_inline ||
            (file_.template_specialization(object.local_enclosing_function) &&
             !function.is_explicit_template_specialization);
    }
    cir::TypeId void_type = builder_.void_type();
    cir::TypeId void_pointer = builder_.pointer_type(void_type);
    cir::TypeId byte_type = builder_.char_type();

    std::string object_symbol = abi::itanium_linkage_name(file_, started.entity);
    std::string source_name = object.name.valid()
        ? std::string(file_.name(object.name))
        : std::string("object");
    std::string encoding;
    if (object_symbol.starts_with("_Z")) {
        encoding = object_symbol.substr(2);
    } else {
        encoding = std::to_string(source_name.size()) + source_name;
    }
    std::string guard_symbol = mergeable
        ? "_ZGV" + encoding
        : ".tls.guard." + std::to_string(index) + "." + source_name;
    cir::EntityId guard_entity = builder_.add_entity(
        cir::EntityKind::Variable, guard_symbol, byte_type, {}, loc,
        cir::StorageDuration::Thread);
    cir::Entity& guard = file_.entity_mut(guard_entity);
    guard.is_definition = true;
    guard.linkage = mergeable ? cir::LinkageKind::LinkOnceODR
                              : cir::LinkageKind::Internal;
    guard.has_static_initializer = true;
    guard.static_initializer_bytes.assign(1, 0);
    mark_generated_abi_entity(guard_entity, started.entity,
                              cir::GeneratedSymbolRole::Guard);
    if (mergeable) {
        guard.attr_facts.asm_label = guard_symbol;
    }

    cir::TypeId cleanup_type = function_type(
        file_.type_ref(void_type), {file_.type_ref(void_pointer)}, false, true);
    cir::EntityId cleanup_entity{};
    cir::TypeId array_leaf = array_class_element_leaf(started.type);
    cir::EntityId destructor =
        array_leaf.valid() ? cir::EntityId{} : record_destructor(started.type);
    cir::EntityId array_helper = array_leaf.valid()
        ? array_destroy_helper(started.type, loc)
        : cir::EntityId{};
    if (destructor.valid() || array_helper.valid()) {
        std::unique_ptr<BlockContextState> saved = save_function_context();
        DeclFlags flags;
        flags.is_static = true;
        ParamInput object_param;
        object_param.name = ".object";
        object_param.type = file_.type_ref(void_pointer);
        object_param.loc = loc;
        std::string cleanup_name = mergeable
            ? generated_owner_helper_name(file_, started.entity,
                                          "__aburi_cxx_thread_cleanup_", index)
            : "__cxx_thread_cleanup." + std::to_string(index);
        FunctionDeclStart cleanup = begin_function_type(
            cleanup_name, cleanup_type,
            file_.type_ref(void_type), {object_param}, loc, flags);
        if (mergeable) {
            file_.entity_mut(cleanup.decl.entity).is_extern_c = true;
            file_.entity_mut(cleanup.decl.entity).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("thread.cleanup");
        cir::InstId erased = cleanup.function.parameters.front().value.inst;
        cir::InstId typed = builder_.cast(
            builder_.pointer_type(started.type), erased, "value", loc);
        cir::InstId place = builder_.deref(typed, loc);
        if (array_helper.valid()) {
            builder_.call(array_helper, void_type,
                          {builder_.addr_of(place, loc)}, loc);
        } else {
            emit_destroy(place, structor_complete_variant(destructor), loc);
        }
        builder_.return_void(loc);
        cir::Fragment cleanup_body = finish_fragment_block(block, previous);
        finish_function(
            make_stmt_result(std::move(cleanup_body), true, false), loc);
        restore_function_context(std::move(saved));
        cleanup_entity = cleanup.decl.entity;
        mark_generated_abi_entity(cleanup_entity, started.entity,
                                  cir::GeneratedSymbolRole::ThreadCleanup);
    }

    if (!is_namespace_scope_static_entity(started.entity)) {

        cir::Fragment fragment = adopt_or_create_fragment_entry(
            std::move(started.fragment), "thread.local.guard");
        cir::BlockId previous = builder_.current_block();
        builder_.switch_to_block(fragment.exit);
        cir::InstId guard_place = builder_.global_place(guard_entity, loc);
        cir::InstId guard_value =
            builder_.lvalue_to_rvalue(guard_place, loc);
        cir::InstId zero = builder_.integer_literal(0, byte_type, "0", loc);
        cir::InstId needs_init = builder_.binary(
            cir::BinaryOpKind::Equal, builder_.int_type(), guard_value, zero,
            loc);
        cir::BlockId init_entry =
            builder_.create_detached_block("thread.local.init");
        cir::BlockId continuation =
            builder_.create_detached_block("thread.local.done");
        builder_.cond_branch_from(fragment.exit, needs_init, init_entry,
                                  continuation, {}, loc);

        cir::BlockId work_previous = builder_.current_block();
        cir::BlockId work_block =
            begin_fragment_block("thread.local.init.work");
        cir::InstId object_place =
            builder_.global_place(started.entity, loc);
        cir::Fragment work = finish_fragment_block(work_block, work_previous);
        DeclResult constructed = started;
        constructed.place = object_place;
        constructed.fragment = {};
        if (initializer.has_value()) {
            if (initializer->entity.valid() &&
                file_.valid(initializer->entity) &&
                file_.entity(initializer->entity).storage_duration ==
                    cir::StorageDuration::Thread) {
                work = chain(
                    std::move(work),
                    ensure_thread_initialized(initializer->entity, loc), loc);
            }
            bool initializer_error = initializer->has_error;
            cir::Fragment initializer_fragment;
            if (initializer->category == ValueCategory::InitList &&
                initializer_list_element_type(started.type).has_value()) {
                ExprResult value = materialize_list_initialization(
                    std::move(*initializer), started.type, UseContext::Init,
                    loc, cir::StorageDuration::Thread);
                constructed.has_error = constructed.has_error ||
                    initializer_error || value.has_error;
                initializer_fragment = std::move(value.fragment);
                if (!value.has_error && value.value.valid()) {
                    cir::BlockId store_previous = builder_.current_block();
                    cir::BlockId store_block = begin_fragment_block(
                        "thread.local.initializer_list.store");
                    builder_.store(object_place, value.value, loc);
                    initializer_fragment = chain(
                        std::move(initializer_fragment),
                        finish_fragment_block(store_block, store_previous),
                        loc);
                }
                for (cir::LifetimeId lifetime :
                     value.materialized_lifetimes) {
                    transfer_lifetime(lifetime,
                                      LifetimeOwnerKind::ThreadExit,
                                      started.entity.index);
                }
            } else {
                initializer_fragment = emit_initializer_for_place(
                    object_place, started.type, std::move(*initializer), loc,
                    init_kind == ConstructorInitializationKind::Direct
                        ? UseContext::DirectInit
                        : UseContext::Init);
                constructed.has_error =
                    constructed.has_error || initializer_error;
            }
            work = chain(std::move(work),
                         std::move(initializer_fragment), loc);
        } else {
            constructed = construct_variable(
                std::move(constructed), std::move(arguments), loc, init_kind,
                value_initialize);
            work = chain(std::move(work),
                         std::move(constructed.fragment), loc);
        }
        if (cleanup_entity.valid()) {
            cir::BlockId registration_previous = builder_.current_block();
            cir::BlockId registration_block =
                begin_fragment_block("thread.local.cxa_atexit");
            cir::TypeId cleanup_pointer = builder_.pointer_type(cleanup_type);
            cir::EntityId atexit_fn = runtime_function(
                "__cxa_thread_atexit",
                function_type(file_.type_ref(builder_.int_type()),
                              {file_.type_ref(cleanup_pointer),
                               file_.type_ref(void_pointer),
                               file_.type_ref(void_pointer)},
                              false, true),
                loc);
            cir::EntityId dso = extern_runtime_global("__dso_handle", loc);
            cir::InstId dso_address = builder_.cast(
                void_pointer,
                builder_.addr_of(builder_.global_place(dso, loc), loc),
                "value", loc);
            builder_.call(
                atexit_fn, builder_.int_type(),
                {builder_.function_to_pointer(cleanup_entity, loc),
                 builder_.cast(void_pointer,
                               builder_.addr_of(object_place, loc), "value",
                               loc),
                 dso_address},
                loc);
            work = chain(
                std::move(work),
                finish_fragment_block(registration_block,
                                      registration_previous),
                loc);
        }
        {
            cir::BlockId set_previous = builder_.current_block();
            cir::BlockId set_block =
                begin_fragment_block("thread.local.guard.set");
            cir::InstId one =
                builder_.integer_literal(1, byte_type, "1", loc);
            builder_.store(builder_.global_place(guard_entity, loc), one, loc);
            work = chain(std::move(work),
                         finish_fragment_block(set_block, set_previous), loc);
        }

        auto merge_blocks = [](cir::Fragment& target,
                               const cir::Fragment& source) {
            if (source.empty()) {
                return;
            }
            if (target.empty()) {
                target.entry = source.entry;
            }
            target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                                 source.blocks.end());
            target.exit = source.exit;
        };
        merge_blocks(fragment, builder_.block_fragment(init_entry));
        builder_.branch_from(init_entry, work.entry, {}, loc);
        merge_blocks(fragment, work);
        builder_.branch_from(work.exit, continuation, {}, loc);
        merge_blocks(fragment, builder_.block_fragment(continuation));
        fragment.exit = continuation;
        builder_.switch_to_block(previous);

        if (cleanup_entity.valid()) {
            cir::LifetimeId lifetime{
                static_cast<uint32_t>(lifetime_obligations_.size()),
                next_lifetime_generation_++};
            lifetime_obligations_.push_back(LifetimeObligation{
                lifetime, started.entity, started.type, cleanup_entity, loc,
                LifetimeOwnerKind::ThreadExit,
                static_cast<uint64_t>(started.entity.index), true});
        }
        started.has_error = started.has_error || constructed.has_error;
        started.fragment = std::move(fragment);
        return started;
    }

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags flags;
    flags.is_static = true;
    cir::TypeId init_type =
        function_type(file_.type_ref(void_type), {}, false, true);
    std::string init_name = mergeable
        ? generated_owner_helper_name(file_, started.entity,
                                      "__aburi_cxx_thread_init_", index)
        : "__cxx_thread_var_init." + std::to_string(index);
    FunctionDeclStart init = begin_function_type(
        init_name, init_type,
        file_.type_ref(void_type), {}, loc, flags);
    if (mergeable) {
        file_.entity_mut(init.decl.entity).is_extern_c = true;
    }
    file_.entity_mut(init.decl.entity).linkage =
        mergeable ? cir::LinkageKind::LinkOnceODR
                  : cir::LinkageKind::Internal;
    mark_generated_abi_entity(init.decl.entity, started.entity,
                              cir::GeneratedSymbolRole::ThreadInitializer);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId guard_block = begin_fragment_block("thread.guard");
    cir::InstId guard_place = builder_.global_place(guard_entity, loc);
    cir::InstId guard_value = builder_.lvalue_to_rvalue(guard_place, loc);
    cir::InstId zero = builder_.integer_literal(0, byte_type, "0", loc);
    cir::InstId needs_init = builder_.binary(
        cir::BinaryOpKind::Equal, builder_.int_type(), guard_value, zero, loc);
    cir::Fragment body = finish_fragment_block(guard_block, previous);
    cir::BlockId init_entry =
        builder_.create_detached_block("thread.init");
    cir::BlockId continuation =
        builder_.create_detached_block("thread.done");
    builder_.cond_branch_from(body.exit, needs_init, init_entry,
                              continuation, {}, loc);

    cir::BlockId work_previous = builder_.current_block();
    cir::BlockId work_block = begin_fragment_block("thread.init.work");
    cir::InstId object_place = builder_.global_place(started.entity, loc);
    cir::Fragment work = finish_fragment_block(work_block, work_previous);
    DeclResult constructed = started;
    constructed.place = object_place;
    constructed.fragment = {};
    if (initializer.has_value()) {
        if (initializer->entity.valid() &&
            file_.valid(initializer->entity) &&
            file_.entity(initializer->entity).storage_duration ==
                cir::StorageDuration::Thread) {
            work = chain(
                std::move(work),
                ensure_thread_initialized(initializer->entity, loc), loc);
        }
        bool initializer_error = initializer->has_error;
        cir::Fragment initializer_fragment;
        if (initializer->category == ValueCategory::InitList &&
            initializer_list_element_type(started.type).has_value()) {
            ExprResult value = materialize_list_initialization(
                std::move(*initializer), started.type, UseContext::Init, loc,
                cir::StorageDuration::Thread);
            constructed.has_error = constructed.has_error ||
                initializer_error || value.has_error;
            initializer_fragment = std::move(value.fragment);
            if (!value.has_error && value.value.valid()) {
                cir::BlockId store_previous = builder_.current_block();
                cir::BlockId store_block = begin_fragment_block(
                    "thread.initializer_list.store");
                builder_.store(object_place, value.value, loc);
                initializer_fragment = chain(
                    std::move(initializer_fragment),
                    finish_fragment_block(store_block, store_previous), loc);
            }
            for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
                transfer_lifetime(lifetime, LifetimeOwnerKind::ThreadExit,
                                  started.entity.index);
            }
        } else {
            initializer_fragment = emit_initializer_for_place(
                object_place, started.type, std::move(*initializer), loc,
                init_kind == ConstructorInitializationKind::Direct
                    ? UseContext::DirectInit
                    : UseContext::Init);
            constructed.has_error =
                constructed.has_error || initializer_error;
        }
        work = chain(std::move(work), std::move(initializer_fragment), loc);
    } else {
        constructed = construct_variable(std::move(constructed),
                                         std::move(arguments), loc, init_kind,
                                         value_initialize);
        work = chain(std::move(work), std::move(constructed.fragment), loc);
    }

    if (cleanup_entity.valid()) {
        cir::BlockId registration_previous = builder_.current_block();
        cir::BlockId registration_block =
            begin_fragment_block("thread.cxa_atexit");
        cir::TypeId cleanup_pointer = builder_.pointer_type(cleanup_type);
        cir::EntityId atexit_fn = runtime_function(
            "__cxa_thread_atexit",
            function_type(file_.type_ref(builder_.int_type()),
                          {file_.type_ref(cleanup_pointer),
                           file_.type_ref(void_pointer),
                           file_.type_ref(void_pointer)},
                          false, true),
            loc);
        cir::EntityId dso = extern_runtime_global("__dso_handle", loc);
        cir::InstId dso_address = builder_.cast(
            void_pointer,
            builder_.addr_of(builder_.global_place(dso, loc), loc),
            "value", loc);
        builder_.call(
            atexit_fn, builder_.int_type(),
            {builder_.function_to_pointer(cleanup_entity, loc),
             builder_.cast(void_pointer,
                           builder_.addr_of(object_place, loc), "value", loc),
             dso_address},
            loc);
        work = chain(
            std::move(work),
            finish_fragment_block(registration_block,
                                  registration_previous),
            loc);
    }
    {
        cir::BlockId set_previous = builder_.current_block();
        cir::BlockId set_block = begin_fragment_block("thread.guard.set");
        cir::InstId one = builder_.integer_literal(1, byte_type, "1", loc);
        builder_.store(builder_.global_place(guard_entity, loc), one, loc);
        work = chain(std::move(work),
                     finish_fragment_block(set_block, set_previous), loc);
    }

    auto merge_blocks = [](cir::Fragment& target,
                           const cir::Fragment& source) {
        if (source.empty()) {
            return;
        }
        if (target.empty()) {
            target.entry = source.entry;
        }
        target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                             source.blocks.end());
        target.exit = source.exit;
    };
    merge_blocks(body, builder_.block_fragment(init_entry));
    builder_.branch_from(init_entry, work.entry, {}, loc);
    merge_blocks(body, work);
    builder_.branch_from(work.exit, continuation, {}, loc);
    merge_blocks(body, builder_.block_fragment(continuation));
    body.exit = continuation;
    finish_function(make_stmt_result(std::move(body)), loc);
    restore_function_context(std::move(saved));

    uint64_t key = static_cast<uint64_t>(started.entity.index);
    thread_init_functions_[key] = init.decl.entity;
    track_speculative_rollback([this, key]() {
        thread_init_functions_.erase(key);
    });
    if (cleanup_entity.valid()) {
        cir::LifetimeId lifetime{
            static_cast<uint32_t>(lifetime_obligations_.size()),
            next_lifetime_generation_++};
        lifetime_obligations_.push_back(LifetimeObligation{
            lifetime, started.entity, started.type, cleanup_entity, loc,
            LifetimeOwnerKind::ThreadExit,
            static_cast<uint64_t>(started.entity.index), true});
    }

    started.has_error = started.has_error || constructed.has_error;
    started.fragment = ensure_thread_initialized(started.entity, loc);
    return started;
}

cir::Fragment Session::ensure_thread_initialized(cir::EntityId entity,
                                                  SrcLoc loc) {
    cir::Fragment fragment;
    auto found = thread_init_functions_.find(
        static_cast<uint64_t>(entity.index));
    if (found == thread_init_functions_.end() ||
        !builder_.current_function().valid()) {
        return fragment;
    }
    if (current_function_.valid() && file_.valid(current_function_) &&
        file_.function(current_function_).entity == found->second) {
        return fragment;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("thread.ensure_init");
    builder_.call(found->second, builder_.void_type(), {}, loc);
    return finish_fragment_block(block, previous);
}

DeclResult Session::construct_variable(DeclResult started,
                                       std::vector<ExprResult> arguments,
                                       SrcLoc loc,
                                       ConstructorInitializationKind init_kind,
                                       bool value_initialize,
                                       bool full_expression_temporary) {
    if (diagnose_abstract_instantiation(started.type, loc)) {
        started.has_error = true;
        return started;
    }
    if (!started.place.valid()) {
        if (is_namespace_scope_static_entity(started.entity)) {
            if (file_.entity(started.entity).storage_duration ==
                cir::StorageDuration::Thread) {
                return construct_thread_variable(
                    std::move(started), std::move(arguments), loc,
                    init_kind, value_initialize);
            }
            return construct_global_variable(std::move(started),
                                             std::move(arguments), loc,
                                             init_kind, value_initialize);
        }
        if (started.entity.valid() && file_.valid(started.entity) &&
            file_.entity(started.entity).storage_duration ==
                cir::StorageDuration::Static) {
            return construct_local_static(std::move(started),
                                          std::move(arguments), loc,
                                          init_kind, value_initialize);
        }
        if (started.entity.valid() && file_.valid(started.entity) &&
            file_.entity(started.entity).storage_duration ==
                cir::StorageDuration::Thread) {
            return construct_thread_variable(
                std::move(started), std::move(arguments), loc, init_kind,
                value_initialize);
        }
        report_error("constructed objects need automatic storage here",
                     loc);
        started.has_error = true;
        return started;
    }

    if (cir::TypeId array_leaf = array_class_element_leaf(started.type);
        array_leaf.valid()) {
        if (!arguments.empty()) {
            report_error("array of '" + file_.format_type(array_leaf) +
                             "' cannot take constructor arguments",
                         loc);
            started.has_error = true;
            return started;
        }
        if (record_requires_default_constructor_selection(array_leaf)) {
            bool construct_error = false;
            ClassArrayShape shape = class_array_shape(started.type);
            cir::Fragment construct = array_construct_loop_fragment(
                started.place, file_.resolved_type(started.type), 0,
                shape.total_leaf_count, loc, &construct_error);
            started.fragment =
                chain(std::move(started.fragment), std::move(construct), loc);
            started.has_error = started.has_error || construct_error;
        }
        register_destructor_cleanup(started.entity, started.type, loc,
                                    full_expression_temporary);
        return started;
    }

    cir::EntityId selected_conversion_constructor;
    if (lang_opts_.is_cxx_mode() &&
        init_kind == ConstructorInitializationKind::Copy &&
        arguments.size() == 1) {
        cir::TypeId source_resolved =
            file_.resolved_type(arguments.front().type);
        cir::TypeId target_resolved = file_.resolved_type(started.type);
        if (file_.valid(source_resolved) && file_.valid(target_resolved) &&
            file_.type(source_resolved).kind == cir::TypeKind::Record &&
            source_resolved != target_resolved) {
            if (arguments.front().category == ValueCategory::PrValue &&
                arguments.front().value.valid()) {
                MemberAccessBase materialized_source =
                    collect_member_access_base(std::move(arguments.front()),
                                               /*is_arrow=*/false,
                                               loc);
                arguments.front() = std::move(materialized_source.base_place);
            }
            UserConversionSequence sequence =
                resolve_initialization_user_conversion(
                    arguments.front(), started.type,
                    UserConversionContext::CopyInitialization, loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_error("conversion from '" +
                                 file_.format_type(arguments.front().type) +
                                 "' to '" + file_.format_type(started.type) +
                                 "' is ambiguous",
                             loc);
                report_overload_ambiguity_notes(sequence.ambiguity, loc);
                started.has_error = true;
                return started;
            }
            if (sequence.kind ==
                UserConversionSequence::Kind::ConversionFunction) {
                arguments.front() = apply_user_conversion_sequence(
                    std::move(arguments.front()), started.type, sequence,
                    loc);
                started.has_error =
                    started.has_error || arguments.front().has_error;
            } else if (sequence.kind ==
                       UserConversionSequence::Kind::Constructor) {
                selected_conversion_constructor = sequence.callable;
            }
        }
    }
    size_t provided_argument_count = arguments.size();
    bool dependent_pattern_construction =
        collecting_pattern_ &&
        (is_dependent_type(started.type) ||
         std::any_of(arguments.begin(), arguments.end(),
                     [&](const ExprResult& argument) {
                         return expr_is_dependent(argument) ||
                             expr_is_value_dependent(argument);
                     }));
    ConstructorCallMaterialization materialized =
        selected_conversion_constructor.valid()
            ? materialize_selected_constructor_call(
                  selected_conversion_constructor, std::move(arguments), loc)
            : materialize_constructor_call(started.type,
                                           std::move(arguments), loc,
                                           init_kind);
    if (!materialized.constructor.valid()) {
        if (dependent_pattern_construction) {

            mark_pattern_unusable();
            return started;
        }
        report_error(std::string(materialized.ambiguous
                                     ? "ambiguous constructor call for '"
                                     : "no matching constructor for '") +
                         file_.format_type(started.type) + "' taking " +
                         std::to_string(provided_argument_count) +
                         " argument(s)",
                     loc);
        started.has_error = true;
        return started;
    }
    started.has_error = started.has_error || materialized.has_error;
    const cir::RecordMethodFact* constructor_fact =
        file_.method_fact(materialized.constructor);
    bool needs_value_zero = value_initialize && constructor_fact &&
        !constructor_fact->is_user_provided &&
        started.entity.valid() && file_.valid(started.entity) &&
        file_.entity(started.entity).storage_duration ==
            cir::StorageDuration::Automatic;
    if (needs_value_zero) {
        started.fragment = chain(
            std::move(started.fragment),
            emit_zero_initializer(started.place, started.type, loc),
            loc);
    }
    started.fragment =
        chain(std::move(started.fragment),
              std::move(materialized.argument_fragment), loc);
    if (materialized.has_error) {
        return started;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("local.construct");
    emit_construct_in_place(started.place,
                            structor_complete_variant(materialized.constructor),
                            materialized.argument_values, loc);
    cir::Fragment construct_fragment = finish_fragment_block(block, previous);
    started.fragment =
        chain(std::move(started.fragment), std::move(construct_fragment), loc);

    if (file_.entity(materialized.constructor).decl_flags.is_consteval) {

        cir::BlockId load_previous = builder_.current_block();
        cir::BlockId load_block =
            begin_fragment_block("local.construct.immediate.load");
        cir::InstId value = builder_.lvalue_to_rvalue(started.place, loc);
        cir::Fragment load_fragment =
            finish_fragment_block(load_block, load_previous);
        ExprResult object;
        object.fragment = chain(std::move(started.fragment),
                                std::move(load_fragment), loc);
        object.value = value;
        object.type = started.type;
        object.category = ValueCategory::PrValue;
        object.has_error = started.has_error;
        object = fold_immediate_constructor_invocation(
            std::move(object), started.place, materialized.constructor, loc);
        started.fragment = std::move(object.fragment);
    }

    register_destructor_cleanup(started.entity, started.type, loc,
                                full_expression_temporary);
    return started;
}

DeclResult Session::default_construct_if_needed(DeclResult started, SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode() || !started.entity.valid() ||
        !file_.valid(started.entity)) {
        return started;
    }
    const cir::Entity& entity = file_.entity(started.entity);
    if (!entity.is_definition) {
        return started;
    }

    const bool is_static =
        entity.storage_duration == cir::StorageDuration::Static ||
        entity.storage_duration == cir::StorageDuration::Thread;
    if (entity.storage_duration != cir::StorageDuration::Automatic &&
        !is_static) {
        return started;
    }
    cir::TypeId resolved = file_.resolved_type(started.type);

    if (cir::TypeId leaf = array_class_element_leaf(resolved); leaf.valid()) {
        if (diagnose_abstract_instantiation(resolved, loc)) {
            started.has_error = true;
            return started;
        }
        if (is_static) {
            if (!record_requires_default_constructor_selection(leaf) &&
                !record_destructor(leaf).valid()) {
                return started;
            }
            started.place = {};
            return construct_variable(std::move(started), {}, loc);
        }
        if (!started.place.valid()) {
            return started;
        }
        if (record_requires_default_constructor_selection(leaf)) {
            bool construct_error = false;
            ClassArrayShape shape = class_array_shape(resolved);
            cir::Fragment construct = array_construct_loop_fragment(
                started.place, resolved, 0, shape.total_leaf_count, loc,
                &construct_error);
            started.fragment =
                chain(std::move(started.fragment), std::move(construct), loc);
            started.has_error = started.has_error || construct_error;
        }
        register_destructor_cleanup(started.entity, started.type, loc);
        return started;
    }
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Record) {
        return started;
    }
    if (diagnose_abstract_instantiation(resolved, loc)) {
        started.has_error = true;
        return started;
    }
    if (is_static) {
        if (!record_requires_default_constructor_selection(resolved)) {
            return started;
        }
        started.place = {};
        return construct_variable(std::move(started), {}, loc);
    }
    if (record_requires_default_constructor_selection(resolved)) {
        return construct_variable(std::move(started), {}, loc);
    }
    register_destructor_cleanup(started.entity, started.type, loc);
    return started;
}

StmtResult Session::collect_member_initializer(std::string_view member_name,
                                               std::vector<ExprResult> arguments,
                                               SrcLoc loc) {
    StmtResult result;
    if (!current_this_place_.valid() || !current_member_record_.valid()) {
        report_error("member initializers require a constructor", loc);
        result.has_error = true;
        return result;
    }
    const cir::RecordFacts* facts = file_.record_facts(current_member_record_);
    const cir::RecordFieldFact* field = nullptr;
    if (facts) {
        for (const cir::RecordFieldFact& candidate : facts->fields) {
            if (candidate.name.valid() &&
                file_.name(candidate.name) == member_name) {
                field = &candidate;
                break;
            }
        }
    }
    if (!field) {
        report_error("class has no member named '" + std::string(member_name) +
                         "' to initialize",
                     loc);
        result.has_error = true;
        return result;
    }

    cir::TypeId field_type = field->type.type;
    cir::EntityId field_entity = field->entity;
    cir::TypeRef field_ref = field->type;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("ctor.member");
    cir::InstId this_value = builder_.lvalue_to_rvalue(current_this_place_, loc);
    cir::InstId object_place = builder_.deref(this_value, loc);
    cir::InstId member_place =
        builder_.field_addr(object_place, field_entity, field_type, loc);
    cir::Fragment place_fragment = finish_fragment_block(block, previous);

    cir::TypeId resolved_field = file_.resolved_type(field_type);
    bool member_is_class =
        file_.valid(resolved_field) &&
        file_.type(resolved_field).kind == cir::TypeKind::Record &&
        (record_needs_construction(resolved_field) ||
         (arguments.empty() &&
          record_requires_default_constructor_selection(resolved_field)));

    if (member_is_class) {
        ConstructorCallMaterialization materialized =
            materialize_constructor_call(resolved_field,
                                         std::move(arguments),
                                         loc);
        if (!materialized.constructor.valid()) {
            report_error(std::string(materialized.ambiguous
                                         ? "ambiguous constructor for member '"
                                         : "no matching constructor for member '") +
                             std::string(member_name) + "'",
                         loc);
            result.has_error = true;
            return result;
        }
        result.has_error = result.has_error || materialized.has_error;
        result.fragment = chain(std::move(place_fragment),
                                std::move(materialized.argument_fragment),
                                loc);
        if (materialized.has_error) {
            result.falls_through = true;
            return result;
        }
        cir::BlockId construct_previous = builder_.current_block();
        cir::BlockId construct_block = begin_fragment_block("ctor.member.construct");
        emit_construct_in_place(member_place,
                                structor_complete_variant(materialized.constructor),
                                materialized.argument_values, loc);
        cir::Fragment construct_fragment =
            finish_fragment_block(construct_block, construct_previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(construct_fragment),
                                loc);
        result.falls_through = true;
        return result;
    }

    if (arguments.size() != 1) {
        report_error("member initializer for '" + std::string(member_name) +
                         "' expects one value",
                     loc);
        result.has_error = true;
        return result;
    }
    ExprResult value =
        convert_to(std::move(arguments.front()), field_type, UseContext::Init, loc);
    result.has_error = result.has_error || value.has_error;
    result.fragment = chain(std::move(place_fragment), std::move(value.fragment), loc);

    if (value.value.valid()) {
        cir::BlockId store_previous = builder_.current_block();
        cir::BlockId store_block = begin_fragment_block("ctor.member.store");
        builder_.store(member_place, value.value, loc);
        cir::Fragment store_fragment = finish_fragment_block(store_block, store_previous);
        result.fragment = chain(std::move(result.fragment), std::move(store_fragment), loc);
    }
    result.falls_through = true;
    (void)field_ref;
    return result;
}

ExprResult Session::collect_functional_cast(cir::TypeId type,
                                            std::vector<ExprResult> arguments,
                                            SrcLoc loc,
                                            InitListSyntax syntax,
                                            bool allow_explicit) {
    bool dependent_target = type.valid() &&
        (is_dependent_type(type) ||
         type_contains_dependent_alias_specialization(type));
    bool dependent_argument = false;
    for (const ExprResult& argument : arguments) {
        dependent_argument =
            dependent_argument || expr_is_value_dependent(argument);
    }
    if (dependent_target || dependent_argument) {
        if (arguments.size() == 1) {
            ExprResult operand = std::move(arguments.front());
            if (dependent_target) {

                return make_deferred_conversion_expr(
                    std::move(operand), type, loc);
            }
            return make_deferred_conversion_expr(std::move(operand), type,
                                                 loc);
        }
        ExprResult combined;
        for (ExprResult& argument : arguments) {
            combined.fragment = chain(std::move(combined.fragment),
                                      std::move(argument.fragment), loc);
            combined.has_error = combined.has_error || argument.has_error;
            combined.value_dependent = combined.value_dependent ||
                expr_is_value_dependent(argument);
            combined.references_template_value_parameter =
                combined.references_template_value_parameter ||
                argument.references_template_value_parameter;
        }
        if (dependent_target) {

            return make_deferred_typed_expr(
                std::move(combined), type, ValueCategory::PrValue, loc);
        }
        return make_deferred_conversion_expr(std::move(combined), type, loc);
    }
    cir::TypeId resolved = file_.resolved_type(type);
    bool is_record = file_.valid(resolved) &&
                     file_.type(resolved).kind == cir::TypeKind::Record;
    if (is_record && !require_complete_class_type(
                         resolved, loc,
                         cir::InstantiationDemandKind::CompleteClass)) {
        report_error("functional cast requires a complete class type", loc);
        ExprResult result;
        for (ExprResult& argument : arguments) {
            result.fragment = chain(std::move(result.fragment),
                                    std::move(argument.fragment), loc);
            result.has_error = result.has_error || argument.has_error;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.incomplete.cast");
        cir::InstId error = builder_.error(
            "cannot create an object of incomplete class type", loc);
        error = builder_.cast(type, error, "error", loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(error_fragment), loc);
        result.value = error;
        result.type = type;
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    }
    if (is_record && diagnose_abstract_instantiation(resolved, loc)) {
        ExprResult result;
        for (ExprResult& argument : arguments) {
            result.fragment = chain(std::move(result.fragment),
                                    std::move(argument.fragment), loc);
            result.has_error = result.has_error || argument.has_error;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.abstract.cast");
        cir::InstId error = builder_.error(
            "cannot create an object of abstract class type", loc);
        error = builder_.cast(type, error, "error", loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(error_fragment), loc);
        result.value = error;
        result.type = type;
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    }
    const bool is_scalar = is_scalar_type(resolved);
    const bool is_void = is_void_type(resolved);
    const bool is_enum = file_.valid(resolved) &&
        file_.type(resolved).kind == cir::TypeKind::Enum;
    if (is_enum && syntax == InitListSyntax::Braced &&
        arguments.size() == 1 &&
        arguments.front().category == ValueCategory::InitList) {
        return materialize_list_initialization(std::move(arguments.front()),
                                               type,
                                               UseContext::DirectInit,
                                               loc);
    }
    const bool braced_empty_list =
        syntax == InitListSyntax::Braced &&
        arguments.size() == 1 &&
        arguments.front().category == ValueCategory::InitList &&
        arguments.front().init_list &&
        arguments.front().init_list->elements.empty();
    if (is_void &&
        ((syntax == InitListSyntax::Parenthesized && arguments.empty()) ||
         braced_empty_list)) {

        return make_void_prvalue();
    }
    const bool value_initialization = is_record &&
        ((syntax == InitListSyntax::Parenthesized && arguments.empty()) ||
         braced_empty_list);
    bool copy_or_move_initialization = false;
    if (is_record && syntax == InitListSyntax::Parenthesized &&
        arguments.size() == 1 &&
        arguments.front().category != ValueCategory::InitList) {
        cir::TypeId source = file_.resolved_type(arguments.front().type);
        copy_or_move_initialization =
            source == resolved ||
            (file_.valid(source) &&
             file_.type(source).kind == cir::TypeKind::Record &&
             analyze_derived_to_base_path(source, resolved).kind !=
                 DerivedToBasePathKind::NotFound);
    }
    const bool implicit_value_initialization =
        value_initialization && !record_has_user_constructor(resolved) &&
        !(syntax == InitListSyntax::Braced && is_aggregate_type(resolved));
    if (is_scalar && syntax == InitListSyntax::Braced &&
        arguments.size() == 1 &&
        arguments.front().category == ValueCategory::InitList) {
        return collect_initialized_prvalue(type,
                                           std::move(arguments.front()),
                                           loc);
    }
    if (is_scalar && syntax == InitListSyntax::Parenthesized &&
        arguments.empty()) {
        ExprResult initializer =
            collect_init_list_expr({}, loc, InitListSyntax::Parenthesized);
        return collect_initialized_prvalue(type,
                                           std::move(initializer),
                                           loc);
    }
    if (is_record && !implicit_value_initialization &&
        !copy_or_move_initialization &&
        !record_has_user_constructor(resolved) &&
        is_aggregate_type(resolved)) {
        if (syntax == InitListSyntax::Braced && arguments.size() == 1 &&
            arguments.front().category == ValueCategory::InitList) {
            return collect_initialized_prvalue(type,
                                               std::move(arguments.front()),
                                               loc);
        }
        if (syntax == InitListSyntax::Parenthesized) {
            std::vector<InitElementInput> elements;
            elements.reserve(arguments.size());
            for (ExprResult& argument : arguments) {
                InitElementInput element;
                element.value = std::move(argument);
                element.loc = loc;
                elements.push_back(std::move(element));
            }
            ExprResult initializer =
                collect_init_list_expr(std::move(elements),
                                       loc,
                                       InitListSyntax::Parenthesized);
            return collect_initialized_prvalue(type,
                                               std::move(initializer),
                                               loc);
        }
    }
    if (is_record &&
        (record_has_user_constructor(resolved) ||
         implicit_value_initialization ||
         copy_or_move_initialization)) {
        std::string temp_name =
            ".ctor.tmp." + std::to_string(compound_literal_counter_++);
        cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                                 temp_name,
                                                 type,
                                                 {},
                                                 loc,
                                                 cir::StorageDuration::Automatic,
                                                 cir::MemorySpace::Default,
                                                 {});
        file_.entity_mut(temp).is_definition = true;

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.temp.place");
        cir::InstId place = builder_.local_place(temp, type, loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);

        bool requires_constructor = copy_or_move_initialization ||
            !implicit_value_initialization ||
            record_requires_default_constructor_selection(resolved);
        if (implicit_value_initialization && !requires_constructor) {
            cir::BlockId zero_previous = builder_.current_block();
            cir::BlockId zero_block = begin_fragment_block("expr.temp.zero");
            builder_.zero_object(place, loc);
            cir::Fragment zero_fragment =
                finish_fragment_block(zero_block, zero_previous);
            fragment = chain(std::move(fragment),
                             std::move(zero_fragment), loc);
        }

        DeclResult constructed;
        constructed.entity = temp;
        constructed.type = type;
        constructed.place = place;
        constructed.fragment = std::move(fragment);
        if (requires_constructor) {
            ConstructorInitializationKind constructor_kind =
                allow_explicit
                    ? ConstructorInitializationKind::Direct
                    : (syntax == InitListSyntax::Braced
                           ? ConstructorInitializationKind::CopyList
                           : ConstructorInitializationKind::Copy);
            constructed = construct_variable(std::move(constructed),
                                             std::move(arguments),
                                             loc,
                                             constructor_kind,
                                             value_initialization,
                                             /*full_expression_temporary=*/true);
        } else {
            register_destructor_cleanup(
                temp, type, loc, /*full_expression_temporary=*/true);
        }

        cir::BlockId load_previous = builder_.current_block();
        cir::BlockId load_block = begin_fragment_block("expr.temp.load");
        cir::InstId value = builder_.lvalue_to_rvalue(place, loc);
        cir::Fragment load_fragment =
            finish_fragment_block(load_block, load_previous);

        ExprResult result;
        result.fragment = chain(std::move(constructed.fragment),
                                std::move(load_fragment),
                                loc);
        result.value = value;
        result.type = type;
        result.category = ValueCategory::PrValue;
        if (cir::LifetimeId lifetime = lifetime_for_entity(temp);
            lifetime.valid()) {
            result.materialized_lifetimes.push_back(lifetime);
        }
        result.has_error = constructed.has_error;
        return result;
    }
    if (arguments.size() == 1) {

        if (!is_record && syntax == InitListSyntax::Parenthesized) {
            return collect_cast_expr(type, std::move(arguments.front()), loc);
        }
        return convert_to(std::move(arguments.front()), type, UseContext::Init, loc);
    }
    ExprResult result;
    report_error("functional cast to '" + file_.format_type(type) +
                     "' expects one value",
                 loc);
    result.has_error = true;
    result.type = type;
    result.category = ValueCategory::PrValue;
    return result;
}

cir::EntityId Session::runtime_function(std::string_view symbol,
                                        cir::TypeId function_type,
                                        SrcLoc loc) {
    auto found = runtime_functions_.find(std::string(symbol));
    if (found != runtime_functions_.end()) {

        if (found->second.valid() && file_.valid(found->second)) {
            return found->second;
        }
        runtime_functions_.erase(found);
    }
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Function,
                                               symbol,
                                               function_type,
                                               {},
                                               loc);
    file_.entity_mut(entity).is_definition = false;
    file_.entity_mut(entity).linkage = cir::LinkageKind::External;

    file_.entity_mut(entity).is_template_pattern = false;
    // The symbol is already an ABI-level name; never re-mangle it.
    file_.entity_mut(entity).is_extern_c = true;
    runtime_functions_.emplace(std::string(symbol), entity);
    return entity;
}

namespace {

const cir::FunctionTypePayload* allocation_function_payload(
    const cir::File& file,
    cir::EntityId entity) {
    if (!entity.valid() || !file.valid(entity)) {
        return nullptr;
    }
    cir::TypeId type = file.resolved_type(file.entity(entity).type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Function) {
        return nullptr;
    }
    return std::get_if<cir::FunctionTypePayload>(&file.type_payload(type));
}

cir::TypeId allocation_leaf_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    while (file.valid(type) && file.type(type).kind == cir::TypeKind::Array) {
        const auto* array =
            std::get_if<cir::ArrayTypePayload>(&file.type_payload(type));
        if (!array) {
            return {};
        }
        type = file.resolved_type(array->element_type.type);
    }
    return type;
}

bool allocation_entity_has_name(const cir::File& file,
                                cir::EntityId entity,
                                std::string_view name) {
    return entity.valid() && file.valid(entity) &&
        file.entity(entity).name.valid() &&
        file.name(file.entity(entity).name) == name;
}

std::string size_t_itanium_code(const TargetInfo& target) {
    if (target.pointer_width <= 32) {
        return "j";
    }
    if (target.long_width >= 64) {
        return "m";
    }
    return "y";
}

cir::TypeId allocation_size_type(const cir::File& file) {
    cir::File& mutable_file = const_cast<cir::File&>(file);
    const TargetInfo& target = file.target_info();
    if (target.pointer_width <= 32) {
        return mutable_file.builtin_type(cir::BuiltinTypeKind::UInt);
    }
    if (target.long_width >= target.pointer_width) {
        return mutable_file.builtin_type(cir::BuiltinTypeKind::ULong);
    }
    return mutable_file.builtin_type(cir::BuiltinTypeKind::ULongLong);
}

cir::TypeId language_size_type(const cir::File& file) {
    cir::File& mutable_file = const_cast<cir::File&>(file);
    return mutable_file.builtin_type(cir::BuiltinTypeKind::USize);
}

} // namespace

std::optional<cir::AllocationFunctionForm>
Session::classify_allocation_function(cir::EntityId entity,
                                      bool is_array) const {
    auto implicit = implicit_allocation_forms_.find(
        static_cast<uint64_t>(entity.index));
    if (implicit != implicit_allocation_forms_.end()) {
        cir::AllocationFunctionForm form = implicit->second;
        if (form.is_array == is_array) {
            return form;
        }
        return std::nullopt;
    }
    std::string_view expected = is_array ? "operatornew[]" : "operatornew";
    if (!allocation_entity_has_name(file_, entity, expected)) {
        return std::nullopt;
    }
    const cir::FunctionTypePayload* payload =
        allocation_function_payload(file_, entity);
    if (!payload || payload->parameters.empty()) {
        return std::nullopt;
    }
    cir::TypeId result = file_.resolved_type(payload->return_type.type);
    bool accepts_size =
        types_compatible(payload->parameters.front(),
                         file_.type_ref(allocation_size_type(file_))) ||
        types_compatible(payload->parameters.front(),
                         file_.type_ref(language_size_type(file_)));
    if (!file_.valid(result) ||
        file_.type(result).kind != cir::TypeKind::Pointer ||
        !is_void_type(file_.pointer_pointee_type(result)) ||
        !accepts_size) {
        return std::nullopt;
    }
    auto standard_named_type = [&](cir::TypeId type,
                                   std::string_view terminal) {
        type = file_.resolved_type(type);
        cir::EntityId named;
        if (file_.valid(type) && file_.type(type).kind == cir::TypeKind::Enum) {
            const auto* item =
                std::get_if<cir::EnumTypePayload>(&file_.type_payload(type));
            named = item ? item->entity : cir::EntityId{};
        } else if (file_.valid(type) &&
                   file_.type(type).kind == cir::TypeKind::Record) {
            named = file_.record_entity(type);
        }
        if (!named.valid() || !file_.valid(named) ||
            !file_.entity(named).name.valid() ||
            file_.name(file_.entity(named).name) != terminal) {
            return false;
        }
        cir::DeclContextId context = file_.entity(named).semantic_context;
        if (context.valid() && file_.valid(context) &&
            file_.decl_context(context).owner == named) {
            context = file_.decl_context(context).parent;
        }
        if (!context.valid() || !file_.valid(context)) {
            return false;
        }
        cir::EntityId owner = file_.decl_context(context).owner;
        return owner.valid() && file_.valid(owner) &&
            file_.entity(owner).kind == cir::EntityKind::Namespace &&
            file_.entity(owner).name.valid() &&
            file_.name(file_.entity(owner).name) == "std";
    };

    cir::AllocationFunctionForm form;
    form.is_array = is_array;
    size_t next = 1;
    if (payload->parameters.size() > next &&
        standard_named_type(payload->parameters[next].type,
                            "align_val_t")) {
        form.is_aligned = true;
        ++next;
    }
    form.is_placement = payload->parameters.size() != next;
    if (form.is_placement && !form.is_aligned &&
        payload->parameters.size() == 2) {
        cir::TypeId second =
            file_.resolved_type(payload->parameters[1].type);
        form.is_nonallocating = file_.valid(second) &&
            file_.type(second).kind == cir::TypeKind::Pointer &&
            is_void_type(file_.pointer_pointee_type(second)) &&
            file_.entity(entity).kind == cir::EntityKind::Function;
    }
    form.is_nonthrowing =
        payload->exception_spec.kind ==
        cir::FunctionExceptionSpecKind::NonThrowing;
    return form;
}

std::optional<cir::DeallocationFunctionForm>
Session::classify_deallocation_function(cir::EntityId entity,
                                        bool is_array) const {
    auto implicit = implicit_deallocation_forms_.find(
        static_cast<uint64_t>(entity.index));
    if (implicit != implicit_deallocation_forms_.end()) {
        cir::DeallocationFunctionForm form = implicit->second;
        if (form.is_array == is_array) {
            return form;
        }
        return std::nullopt;
    }
    std::string_view expected =
        is_array ? "operatordelete[]" : "operatordelete";
    if (!allocation_entity_has_name(file_, entity, expected)) {
        return std::nullopt;
    }
    const cir::FunctionTypePayload* payload =
        allocation_function_payload(file_, entity);
    if (!payload || payload->parameters.empty() ||
        !is_void_type(payload->return_type.type)) {
        return std::nullopt;
    }
    auto standard_named_type = [&](cir::TypeId type,
                                   std::string_view terminal) {
        type = file_.resolved_type(type);
        cir::EntityId named;
        if (file_.valid(type) && file_.type(type).kind == cir::TypeKind::Enum) {
            const auto* item =
                std::get_if<cir::EnumTypePayload>(&file_.type_payload(type));
            named = item ? item->entity : cir::EntityId{};
        } else if (file_.valid(type) &&
                   file_.type(type).kind == cir::TypeKind::Record) {
            named = file_.record_entity(type);
        }
        if (!named.valid() || !file_.valid(named) ||
            !file_.entity(named).name.valid() ||
            file_.name(file_.entity(named).name) != terminal) {
            return false;
        }
        cir::DeclContextId context = file_.entity(named).semantic_context;
        if (context.valid() && file_.valid(context) &&
            file_.decl_context(context).owner == named) {
            context = file_.decl_context(context).parent;
        }
        if (!context.valid() || !file_.valid(context)) {
            return false;
        }
        cir::EntityId owner = file_.decl_context(context).owner;
        return owner.valid() && file_.valid(owner) &&
            file_.entity(owner).kind == cir::EntityKind::Namespace &&
            file_.entity(owner).name.valid() &&
            file_.name(file_.entity(owner).name) == "std";
    };

    cir::DeallocationFunctionForm form;
    form.is_array = is_array;
    cir::TypeId first =
        file_.resolved_type(payload->parameters.front().type);
    if (!file_.valid(first) ||
        file_.type(first).kind != cir::TypeKind::Pointer) {
        return std::nullopt;
    }
    size_t next = 1;
    if (!is_array && payload->parameters.size() > next &&
        standard_named_type(payload->parameters[next].type,
                            "destroying_delete_t")) {
        form.is_destroying = true;
        cir::EntityId owner = file_.entity(entity).parent;
        cir::TypeId pointee = file_.resolved_type(
            file_.pointer_pointee_type(first));
        if (!owner.valid() || !file_.valid(owner) ||
            file_.entity(owner).kind != cir::EntityKind::Record ||
            pointee != file_.resolved_type(file_.entity(owner).type)) {
            return std::nullopt;
        }
        ++next;
    } else if (!is_void_type(file_.pointer_pointee_type(first))) {
        return std::nullopt;
    }
    if (payload->parameters.size() > next &&
        (types_compatible(payload->parameters[next],
                          file_.type_ref(allocation_size_type(file_))) ||
         types_compatible(payload->parameters[next],
                          file_.type_ref(language_size_type(file_))))) {
        form.is_sized = true;
        ++next;
    }
    if (payload->parameters.size() > next &&
        standard_named_type(payload->parameters[next].type,
                            "align_val_t")) {
        form.is_aligned = true;
        ++next;
    }
    form.is_placement = payload->parameters.size() != next ||
        template_info(entity) != nullptr;
    return form;
}

cir::EntityId Session::implicit_allocation_operator(bool is_array,
                                                    bool aligned,
                                                    SrcLoc loc) {
    std::string key = std::string(is_array ? "new[]" : "new") +
        (aligned ? ".aligned" : ".plain");
    auto found = implicit_allocation_functions_.find(key);
    if (found != implicit_allocation_functions_.end() &&
        found->second.valid() && file_.valid(found->second)) {
        return found->second;
    }
    cir::TypeId void_type = builder_.void_type();
    cir::TypeId void_pointer = builder_.pointer_type(void_type);
    std::vector<cir::TypeRef> parameters{
        file_.type_ref(allocation_size_type(file_))};
    if (aligned) {

        parameters.push_back(file_.type_ref(allocation_size_type(file_)));
    }
    std::string symbol = is_array ? "_Zna" : "_Znw";
    symbol += size_t_itanium_code(file_.target_info());
    if (aligned) {
        symbol += "St11align_val_t";
    }
    cir::EntityId entity = runtime_function(
        symbol,
        function_type(file_.type_ref(void_pointer), parameters, false, true),
        loc);
    cir::AllocationFunctionForm form;
    form.is_array = is_array;
    form.is_aligned = aligned;
    implicit_allocation_forms_[static_cast<uint64_t>(entity.index)] = form;
    implicit_allocation_functions_[key] = entity;
    return entity;
}

cir::EntityId Session::implicit_deallocation_operator(bool is_array,
                                                      bool sized,
                                                      bool aligned,
                                                      SrcLoc loc) {
    std::string key = std::string(is_array ? "delete[]" : "delete") +
        (sized ? ".sized" : ".plain") +
        (aligned ? ".aligned" : ".unaligned");
    auto found = implicit_allocation_functions_.find(key);
    if (found != implicit_allocation_functions_.end() &&
        found->second.valid() && file_.valid(found->second)) {
        return found->second;
    }
    cir::TypeId void_type = builder_.void_type();
    cir::TypeId void_pointer = builder_.pointer_type(void_type);
    std::vector<cir::TypeRef> parameters{file_.type_ref(void_pointer)};
    if (sized) {
        parameters.push_back(file_.type_ref(allocation_size_type(file_)));
    }
    if (aligned) {
        parameters.push_back(file_.type_ref(allocation_size_type(file_)));
    }
    std::string symbol = is_array ? "_ZdaPv" : "_ZdlPv";
    if (sized) {
        symbol += size_t_itanium_code(file_.target_info());
    }
    if (aligned) {
        symbol += "St11align_val_t";
    }
    cir::EntityId entity = runtime_function(
        symbol,
        function_type(file_.type_ref(void_type), parameters, false, true,
                      false,
                      cir::FunctionExceptionSpecKind::NonThrowing),
        loc);
    cir::DeallocationFunctionForm form;
    form.is_array = is_array;
    form.is_sized = sized;
    form.is_aligned = aligned;
    implicit_deallocation_forms_[static_cast<uint64_t>(entity.index)] = form;
    implicit_allocation_functions_[key] = entity;
    return entity;
}

std::vector<cir::EntityId> Session::expand_function_template_candidates(
    const std::vector<cir::EntityId>& candidates,
    const std::vector<ExprResult>& arguments,
    SrcLoc loc) {
    if (!tstate().function_template_instantiation_callback_) {
        return candidates;
    }
    std::vector<cir::EntityId> expanded;
    for (cir::EntityId candidate : candidates) {
        const TemplateInfo* info = template_info(candidate);
        if (!info) {
            expanded.push_back(candidate);
            continue;
        }
        if (info->is_class_template || info->is_alias_template ||
            info->is_variable_template || info->is_concept) {
            continue;
        }
        std::vector<TemplateArgument> deduced;
        TemplateArgumentBindings deduced_bindings;
        if (!deduce_template_arguments(*info,
                                       arguments,
                                       deduced,
                                       nullptr,
                                       nullptr,
                                       &deduced_bindings)) {
            continue;
        }
        cir::EntityId specialization =
            tstate().function_template_instantiation_callback_(
                *info, deduced_bindings, loc);
        if (specialization.valid()) {
            expanded.push_back(specialization);
        }
    }
    return expanded;
}

Session::AllocationSelection Session::select_allocation_function(
    cir::TypeId allocated_object_type,
    bool is_array,
    bool force_global,
    const std::vector<ExprResult>& arguments,
    SrcLoc loc,
    bool diagnose) {
    AllocationSelection result;
    std::string_view name = is_array ? "operatornew[]" : "operatornew";
    cir::TypeId leaf = allocation_leaf_type(file_, allocated_object_type);
    std::vector<cir::EntityId> candidates;
    std::vector<MemberLookupDeclaration> declarations;
    bool class_lookup = false;
    if (!force_global && file_.valid(leaf) &&
        file_.type(leaf).kind == cir::TypeKind::Record) {
        MemberLookupResult lookup = lookup_member_name(leaf, name);
        if (lookup.ambiguous) {
            if (diagnose) {
                report_error("allocation function lookup for '" +
                                 std::string(name) + "' is ambiguous",
                             loc);
            }
            return result;
        }
        class_lookup = lookup.found_name;
        if (class_lookup) {
            for (const MemberLookupDeclaration& declaration :
                 lookup.declarations) {
                candidates.push_back(declaration.entity);
                declarations.push_back(declaration);
            }
        }
    }
    if (!class_lookup) {
        if (const cir::Binding* binding = file_.lookup_callable_binding(
                translation_unit_context_, name,
                /*include_parents=*/false)) {
            candidates = binding->entities;
        }
    }

    std::vector<ExprResult> base_arguments;
    base_arguments.reserve(arguments.size() + 1);
    ExprResult size_argument;
    size_argument.type = allocation_size_type(file_);
    size_argument.category = ValueCategory::PrValue;
    base_arguments.push_back(std::move(size_argument));
    for (const ExprResult& argument : arguments) {
        ExprResult view;
        view.value = argument.value;
        view.place = argument.place;
        view.type = argument.type;
        view.category = argument.category;
        base_arguments.push_back(std::move(view));
    }

    std::optional<size_t> alignment = align_of_type(leaf, loc);
    bool extended = alignment.has_value() &&
        *alignment > file_.target_info().default_new_alignment_bytes;
    auto attempt = [&](bool aligned) -> AllocationSelection {
        std::vector<ExprResult> attempt_arguments;
        attempt_arguments.reserve(base_arguments.size() + (aligned ? 1 : 0));
        attempt_arguments.push_back(base_arguments.front());
        std::vector<cir::EntityId> form_candidates;
        cir::TypeId align_type{};
        for (cir::EntityId candidate : candidates) {
            std::optional<cir::AllocationFunctionForm> form =
                classify_allocation_function(candidate, is_array);
            if (!form || form->is_aligned != aligned) {
                continue;
            }
            form_candidates.push_back(candidate);
            if (aligned && !align_type.valid()) {
                const cir::FunctionTypePayload* payload =
                    allocation_function_payload(file_, candidate);
                if (payload && payload->parameters.size() > 1) {
                    align_type = payload->parameters[1].type;
                }
            }
        }
        if (aligned) {
            ExprResult align_argument;
            align_argument.type = align_type.valid()
                ? align_type
                : allocation_size_type(file_);
            align_argument.category = ValueCategory::PrValue;
            attempt_arguments.push_back(std::move(align_argument));
        }
        attempt_arguments.insert(attempt_arguments.end(),
                                 base_arguments.begin() + 1,
                                 base_arguments.end());
        form_candidates = expand_function_template_candidates(
            form_candidates, attempt_arguments, loc);
        bool has_implicit_signature = std::any_of(
            form_candidates.begin(), form_candidates.end(),
            [&](cir::EntityId candidate) {
                std::optional<cir::AllocationFunctionForm> form =
                    classify_allocation_function(candidate, is_array);
                return form && !form->is_placement &&
                    form->is_aligned == aligned;
            });
        if (!class_lookup && !has_implicit_signature && arguments.empty()) {
            form_candidates.push_back(
                implicit_allocation_operator(is_array, aligned, loc));
        }
        bool ambiguous = false;
        OverloadAmbiguityInfo ambiguity_info;
        cir::EntityId selected = select_overload(
            form_candidates, attempt_arguments,
            /*member_object_leading=*/false, &ambiguous, {},
            &ambiguity_info);
        if (!selected.valid()) {
            if (ambiguous && diagnose) {
                report_error("call to '" + std::string(name) +
                                 "' is ambiguous",
                             loc);
                report_overload_ambiguity_notes(ambiguity_info, loc);
            }
            return {};
        }
        AllocationSelection selected_result;
        selected_result.entity = selected;
        selected_result.form =
            *classify_allocation_function(selected, is_array);
        auto declaration = std::find_if(
            declarations.begin(), declarations.end(),
            [&](const MemberLookupDeclaration& item) {
                return item.entity == selected;
            });
        if (declaration != declarations.end()) {
            if (diagnose) {
                (void)check_member_lookup_access(*declaration, loc, leaf);
                (void)check_member_lookup_base_access(*declaration, leaf, loc);
            }
            selected_result.member_access_owner = declaration->access_owner;
            selected_result.member_access = declaration->declared_access;
        }
        if (const cir::RecordMethodFact* method = file_.method_fact(selected);
            method && method->is_deleted) {
            if (diagnose) {
                report_error("selected allocation function is deleted", loc);
            }
            return {};
        }
        return selected_result;
    };

    result = attempt(extended);
    if (!result.valid()) {
        result = attempt(!extended);
    }
    if (!result.valid() && diagnose) {
        report_error("no matching function for call to '" +
                         std::string(name) + "'",
                     loc);
    }
    return result;
}

Session::DeallocationSelection Session::select_deallocation_function(
    cir::TypeId deleted_object_type,
    bool is_array,
    bool force_global,
    bool placement_matching,
    const AllocationSelection* allocation,
    const std::vector<ExprResult>& placement_arguments,
    SrcLoc loc,
    bool diagnose,
    bool check_access) {
    DeallocationSelection result;
    std::string_view name =
        is_array ? "operatordelete[]" : "operatordelete";
    cir::TypeId leaf = allocation_leaf_type(file_, deleted_object_type);
    std::vector<cir::EntityId> candidates;
    std::vector<MemberLookupDeclaration> declarations;
    bool class_lookup = false;
    if (!force_global && file_.valid(leaf) &&
        file_.type(leaf).kind == cir::TypeKind::Record) {
        MemberLookupResult lookup = lookup_member_name(leaf, name);
        if (lookup.ambiguous) {
            if (diagnose) {
                report_error("deallocation function lookup for '" +
                                 std::string(name) + "' is ambiguous",
                             loc);
            }
            return result;
        }
        class_lookup = lookup.found_name;
        if (class_lookup) {
            for (const MemberLookupDeclaration& declaration :
                 lookup.declarations) {
                candidates.push_back(declaration.entity);
                declarations.push_back(declaration);
            }
        }
    }
    if (!class_lookup) {
        if (const cir::Binding* binding = file_.lookup_callable_binding(
                translation_unit_context_, name,
                /*include_parents=*/false)) {
            candidates = binding->entities;
        }
    }

    if (placement_matching) {
        if (!allocation || !allocation->valid()) {
            return result;
        }
        std::vector<ExprResult> deduction_arguments;
        ExprResult pointer_argument;
        pointer_argument.type = builder_.pointer_type(builder_.void_type());
        pointer_argument.category = ValueCategory::PrValue;
        deduction_arguments.push_back(std::move(pointer_argument));
        for (const ExprResult& argument : placement_arguments) {
            ExprResult view;
            view.value = argument.value;
            view.place = argument.place;
            view.type = argument.type;
            view.category = argument.category;
            deduction_arguments.push_back(std::move(view));
        }
        candidates = expand_function_template_candidates(
            candidates, deduction_arguments, loc);
        const cir::FunctionTypePayload* allocated =
            allocation_function_payload(file_, allocation->entity);
        std::vector<cir::EntityId> matches;
        for (cir::EntityId candidate : candidates) {
            const cir::FunctionTypePayload* deallocated =
                allocation_function_payload(file_, candidate);
            if (!allocated || !deallocated ||
                allocated->parameters.size() !=
                    deallocated->parameters.size()) {
                continue;
            }
            bool same = true;
            for (size_t i = 1; i < allocated->parameters.size(); ++i) {
                same = same && types_compatible(allocated->parameters[i],
                                                deallocated->parameters[i]);
            }
            if (same) {
                matches.push_back(candidate);
            }
        }
        if (matches.size() != 1) {
            return result;
        }
        result.entity = matches.front();
        result.form = *classify_deallocation_function(result.entity, is_array);
        if (!result.form.is_placement) {
            if (diagnose) {
                report_error("placement allocation selected a usual "
                             "deallocation function",
                             loc);
            }
            return {};
        }
    } else {
        std::vector<cir::EntityId> usual;
        for (cir::EntityId candidate : candidates) {
            std::optional<cir::DeallocationFunctionForm> form =
                classify_deallocation_function(candidate, is_array);
            if (form && !form->is_placement) {
                usual.push_back(candidate);
            }
        }
        if (!class_lookup) {
            auto add_implicit = [&](bool sized, bool aligned) {
                bool exists = std::any_of(
                    usual.begin(), usual.end(), [&](cir::EntityId candidate) {
                        auto form = classify_deallocation_function(candidate,
                                                                   is_array);
                        return form && form->is_sized == sized &&
                            form->is_aligned == aligned &&
                            !form->is_destroying;
                    });
                if (!exists) {
                    usual.push_back(implicit_deallocation_operator(
                        is_array, sized, aligned, loc));
                }
            };
            add_implicit(false, false);
            add_implicit(true, false);
            add_implicit(false, true);
            add_implicit(true, true);
        }
        bool has_destroying = std::any_of(
            usual.begin(), usual.end(), [&](cir::EntityId candidate) {
                auto form = classify_deallocation_function(candidate,
                                                           is_array);
                return form && form->is_destroying;
            });
        if (has_destroying) {
            std::erase_if(usual, [&](cir::EntityId candidate) {
                auto form = classify_deallocation_function(candidate,
                                                           is_array);
                return !form || !form->is_destroying;
            });
        }
        std::optional<size_t> alignment = align_of_type(leaf, loc);
        bool extended = alignment.has_value() &&
            *alignment > file_.target_info().default_new_alignment_bytes;
        bool has_preferred_alignment = std::any_of(
            usual.begin(), usual.end(), [&](cir::EntityId candidate) {
                auto form = classify_deallocation_function(candidate,
                                                           is_array);
                return form && form->is_aligned == extended;
            });
        if (has_preferred_alignment) {
            std::erase_if(usual, [&](cir::EntityId candidate) {
                auto form = classify_deallocation_function(candidate,
                                                           is_array);
                return !form || form->is_aligned != extended;
            });
        }
        if (usual.size() > 1) {
            bool require_sized_array = false;
            if (is_array) {
                cir::EntityId destructor = record_destructor(leaf);
                const cir::RecordMethodFact* fact =
                    file_.method_fact(destructor);
                require_sized_array = fact && !fact->is_trivial;
            }
            bool choose_sized = require_sized_array;

            if (class_lookup) {
                choose_sized = false;
            }
            bool has_preferred_size = std::any_of(
                usual.begin(), usual.end(), [&](cir::EntityId candidate) {
                    auto form = classify_deallocation_function(candidate,
                                                               is_array);
                    return form && form->is_sized == choose_sized;
                });
            if (has_preferred_size) {
                std::erase_if(usual, [&](cir::EntityId candidate) {
                    auto form = classify_deallocation_function(candidate,
                                                               is_array);
                    return !form || form->is_sized != choose_sized;
                });
            }
        }
        if (usual.size() != 1) {
            if (diagnose) {
                report_error(usual.empty()
                                 ? "no usual deallocation function found"
                                 : "deallocation function selection is ambiguous",
                             loc);
            }
            return result;
        }
        result.entity = usual.front();
        result.form = *classify_deallocation_function(result.entity, is_array);
    }

    auto declaration = std::find_if(
        declarations.begin(), declarations.end(),
        [&](const MemberLookupDeclaration& item) {
            return item.entity == result.entity;
        });
    if (declaration != declarations.end()) {
        if (check_access) {
            (void)check_member_lookup_access(*declaration, loc, leaf);
            (void)check_member_lookup_base_access(*declaration, leaf, loc);
        }
        result.member_access_owner = declaration->access_owner;
        result.member_access = declaration->declared_access;
    }
    if (const cir::RecordMethodFact* method = file_.method_fact(result.entity);
        method && method->is_deleted) {
        if (diagnose) {
            report_error("selected deallocation function is deleted", loc);
        }
        return {};
    }
    return result;
}

cir::InstId Session::emit_deallocation_call(
    const DeallocationSelection& selection,
    cir::InstId pointer,
    cir::TypeId object_type,
    SrcLoc loc,
    cir::InstId explicit_size,
    const std::vector<cir::InstId>& placement_arguments) {
    if (!selection.valid()) {
        return {};
    }
    const cir::FunctionTypePayload* payload =
        allocation_function_payload(file_, selection.entity);
    if (!payload || payload->parameters.empty()) {
        return {};
    }
    std::vector<cir::InstId> arguments;
    cir::TypeId first_type = payload->parameters.front().type;
    cir::InstId first = pointer;
    if (!type_equal(file_.inst(first).result_type, first_type)) {
        first = builder_.cast(first_type, first, "conversion", loc);
    }
    arguments.push_back(first);
    if (selection.form.is_placement) {
        arguments.insert(arguments.end(), placement_arguments.begin(),
                         placement_arguments.end());
        return builder_.call(selection.entity, builder_.void_type(),
                             arguments, loc);
    }
    size_t parameter = 1;
    if (selection.form.is_destroying) {
        cir::TypeId tag_type = payload->parameters[parameter++].type;
        cir::InstId tag;
        cir::TypeId resolved_tag = file_.resolved_type(tag_type);
        if (file_.valid(resolved_tag) &&
            file_.type(resolved_tag).kind == cir::TypeKind::Record) {
            cir::EntityId temporary = builder_.add_entity(
                cir::EntityKind::Variable,
                ".destroying.delete.tag." +
                    std::to_string(compound_literal_counter_++),
                tag_type, {}, loc, cir::StorageDuration::Automatic);
            file_.entity_mut(temporary).is_definition = true;
            cir::InstId place = builder_.local_place(temporary, tag_type, loc);
            builder_.zero_object(place, loc);
            tag = builder_.lvalue_to_rvalue(place, loc);
        } else {
            tag = builder_.integer_literal(
                0, builder_.usize_type(), "0", loc);
            if (!type_equal(tag_type, builder_.usize_type())) {
                tag = builder_.cast(tag_type, tag, "conversion", loc);
            }
        }
        arguments.push_back(tag);
    }
    if (selection.form.is_sized) {
        cir::InstId size = explicit_size;
        if (!size.valid()) {
            size = builder_.integer_literal(
                static_cast<int64_t>(
                    size_of_type(object_type, loc).value_or(0)),
                builder_.usize_type(), {}, loc);
        }
        cir::TypeId parameter_type = payload->parameters[parameter++].type;
        if (!type_equal(file_.inst(size).result_type, parameter_type)) {
            size = builder_.cast(parameter_type, size, "conversion", loc);
        }
        arguments.push_back(size);
    }
    if (selection.form.is_aligned) {
        cir::InstId alignment = builder_.integer_literal(
            static_cast<int64_t>(
                align_of_type(object_type, loc).value_or(1)),
            builder_.usize_type(), {}, loc);
        cir::TypeId parameter_type = payload->parameters[parameter++].type;
        if (!type_equal(file_.inst(alignment).result_type, parameter_type)) {
            alignment = builder_.cast(parameter_type, alignment,
                                      "conversion", loc);
        }
        arguments.push_back(alignment);
    }
    return builder_.call(selection.entity, builder_.void_type(), arguments,
                         loc);
}

cir::Fragment Session::dynamic_array_construct_fragment(
    cir::InstId leaf_pointer,
    cir::TypeId leaf_type,
    cir::InstId first,
    cir::InstId count,
    cir::InstId progress_place,
    SrcLoc loc,
    bool* had_error) {
    cir::Fragment fragment;
    ConstructorCallMaterialization materialized =
        materialize_constructor_call(leaf_type, {}, loc);
    if (!materialized.constructor.valid()) {
        report_error("no matching default constructor for array elements of '" +
                         file_.format_type(leaf_type) + "'",
                     loc);
        if (had_error) {
            *had_error = true;
        }
        return fragment;
    }
    if (had_error) {
        *had_error = *had_error || materialized.has_error;
    }
    if (materialized.has_error) {
        return fragment;
    }

    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved_block = builder_.current_block();
    cir::BlockId entry = builder_.create_detached_block("new.array.ctor.entry");
    cir::BlockId head = builder_.create_detached_block("new.array.ctor.head");
    cir::BlockId body = builder_.create_detached_block("new.array.ctor.body");
    cir::BlockId done = builder_.create_detached_block("new.array.ctor.done");
    cir::InstId index = builder_.add_block_parameter(head, usize, "idx", loc);

    builder_.switch_to_block(entry);
    if (progress_place.valid()) {
        builder_.store(rematerialize_entity_place(progress_place, loc), first,
                       loc);
    }
    builder_.branch(head, {first}, loc);

    builder_.switch_to_block(head);
    cir::InstId at_end = builder_.binary(cir::BinaryOpKind::Equal,
                                         builder_.int_type(), index, count,
                                         loc);
    builder_.cond_branch_from(head, at_end, done, body, {}, loc);

    builder_.switch_to_block(body);
    cir::InstId element = builder_.array_element_place(leaf_pointer, index,
                                                       loc);
    emit_construct_in_place(
        element, structor_complete_variant(materialized.constructor),
        materialized.argument_values, loc);
    cir::InstId one = builder_.integer_literal(1, usize, "1", loc);
    cir::InstId next = builder_.binary(cir::BinaryOpKind::Add, usize, index,
                                       one, loc);
    if (progress_place.valid()) {

        builder_.store(rematerialize_entity_place(progress_place, loc), next,
                       loc);
    }
    builder_.branch(head, {next}, loc);

    fragment.blocks = {entry, head, body, done};
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;
    builder_.switch_to_block(saved_block);
    return chain(std::move(materialized.argument_fragment),
                 std::move(fragment), loc);
}

cir::Fragment Session::dynamic_array_zero_fragment(cir::InstId leaf_pointer,
                                                   cir::TypeId leaf_type,
                                                   cir::InstId first,
                                                   cir::InstId count,
                                                   SrcLoc loc) {
    (void)leaf_type;
    cir::Fragment fragment;
    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved_block = builder_.current_block();
    cir::BlockId entry = builder_.create_detached_block("new.array.zero.entry");
    cir::BlockId head = builder_.create_detached_block("new.array.zero.head");
    cir::BlockId body = builder_.create_detached_block("new.array.zero.body");
    cir::BlockId done = builder_.create_detached_block("new.array.zero.done");
    cir::InstId index = builder_.add_block_parameter(head, usize, "idx", loc);

    builder_.switch_to_block(entry);
    builder_.branch(head, {first}, loc);
    builder_.switch_to_block(head);
    cir::InstId at_end = builder_.binary(cir::BinaryOpKind::Equal,
                                         builder_.int_type(), index, count,
                                         loc);
    builder_.cond_branch_from(head, at_end, done, body, {}, loc);
    builder_.switch_to_block(body);
    builder_.zero_object(builder_.array_element_place(leaf_pointer, index,
                                                      loc),
                         loc);
    cir::InstId one = builder_.integer_literal(1, usize, "1", loc);
    cir::InstId next = builder_.binary(cir::BinaryOpKind::Add, usize, index,
                                       one, loc);
    builder_.branch(head, {next}, loc);

    fragment.blocks = {entry, head, body, done};
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;
    builder_.switch_to_block(saved_block);
    return fragment;
}

cir::Fragment Session::dynamic_array_destroy_fragment(cir::InstId leaf_pointer,
                                                      cir::TypeId leaf_type,
                                                      cir::InstId count,
                                                      cir::InstId progress_place,
                                                      SrcLoc loc) {
    cir::Fragment fragment;
    cir::EntityId destructor = record_destructor(leaf_type);
    if (!destructor.valid()) {
        return fragment;
    }
    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved_block = builder_.current_block();
    cir::BlockId entry = builder_.create_detached_block("delete.array.entry");
    cir::BlockId head = builder_.create_detached_block("delete.array.head");
    cir::BlockId body = builder_.create_detached_block("delete.array.body");
    cir::BlockId done = builder_.create_detached_block("delete.array.done");
    cir::InstId index = builder_.add_block_parameter(head, usize, "idx", loc);

    builder_.switch_to_block(entry);
    builder_.branch(head, {count}, loc);
    builder_.switch_to_block(head);
    cir::InstId zero = builder_.integer_literal(0, usize, "0", loc);
    cir::InstId at_begin = builder_.binary(cir::BinaryOpKind::Equal,
                                           builder_.int_type(), index, zero,
                                           loc);
    builder_.cond_branch_from(head, at_begin, done, body, {}, loc);
    builder_.switch_to_block(body);
    cir::InstId one = builder_.integer_literal(1, usize, "1", loc);
    cir::InstId previous = builder_.binary(cir::BinaryOpKind::Sub, usize,
                                           index, one, loc);
    if (progress_place.valid()) {
        builder_.store(rematerialize_entity_place(progress_place, loc),
                       previous, loc);
    }
    cir::InstId element = builder_.array_element_place(leaf_pointer, previous,
                                                       loc);
    emit_destroy(element, structor_complete_variant(destructor), loc);
    builder_.branch(head, {previous}, loc);

    fragment.blocks = {entry, head, body, done};
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;
    builder_.switch_to_block(saved_block);
    return fragment;
}

ExprResult Session::collect_array_new_expr(NewExpressionInput input,
                                           SrcLoc loc) {
    ExprResult result;
    cir::TypeId array_type = file_.resolved_type(input.allocated_type);
    const auto* outer = file_.valid(array_type) &&
            file_.type(array_type).kind == cir::TypeKind::Array
        ? std::get_if<cir::ArrayTypePayload>(&file_.type_payload(array_type))
        : nullptr;
    if (!outer) {
        report_error("array new-expression requires an array type", loc);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }

    cir::TypeId element_type = file_.resolved_type(outer->element_type.type);
    cir::TypeId leaf_type = allocation_leaf_type(file_, element_type);
    (void)require_complete_class_type(
        leaf_type, loc, cir::InstantiationDemandKind::CompleteClass);
    if (!file_.valid(leaf_type) || is_void_type(leaf_type)) {
        report_error("cannot allocate an array of incomplete element type",
                     loc);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    if (diagnose_abstract_instantiation(leaf_type, loc)) {
        result.has_error = true;
    }

    uint64_t inner_count = 1;
    cir::TypeId nested = element_type;
    while (file_.valid(nested) &&
           file_.type(nested).kind == cir::TypeKind::Array) {
        const auto* payload = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(nested));
        if (!payload || !payload->size.has_value() ||
            payload->size_expr_is_dependent) {
            report_error("trailing new array bounds must be constant",
                         loc);
            result.has_error = true;
            break;
        }
        uint64_t extent = static_cast<uint64_t>(*payload->size);
        if (extent != 0 &&
            inner_count > std::numeric_limits<uint64_t>::max() / extent) {
            report_error("new array bound is too large", loc);
            result.has_error = true;
            break;
        }
        inner_count *= extent;
        nested = file_.resolved_type(payload->element_type.type);
    }

    std::vector<ExprResult> clauses;
    if (input.initializer_is_braced &&
        input.initializer_arguments.size() == 1 &&
        input.initializer_arguments.front().init_list) {
        std::shared_ptr<InitListValue> list =
            input.initializer_arguments.front().init_list;
        clauses.reserve(list->elements.size());
        for (InitElementInput& element : list->elements) {
            if (!element.designators.empty()) {
                report_error("designated initializers are not permitted in "
                             "a new array initializer",
                             element.loc);
                result.has_error = true;
            }
            clauses.push_back(std::move(element.value));
        }
    } else if (input.initializer_is_parenthesized) {
        clauses = std::move(input.initializer_arguments);
    }

    std::optional<uint64_t> constant_outer_count;
    if (outer->size.has_value()) {
        constant_outer_count = static_cast<uint64_t>(*outer->size);
    } else if (outer->size_kind == cir::ArraySizeKind::Incomplete) {
        if (!input.initializer_is_braced) {
            report_error("array bound is required without a braced "
                         "initializer",
                         loc);
            result.has_error = true;
            constant_outer_count = 0;
        } else {
            constant_outer_count = static_cast<uint64_t>(clauses.size());
        }
    }
    if (constant_outer_count.has_value() &&
        clauses.size() > *constant_outer_count) {
        report_error("too many initializers for new array", loc);
        result.has_error = true;
    }
    std::optional<size_t> leaf_size = size_of_type(leaf_type, loc);
    std::optional<size_t> leaf_alignment = align_of_type(leaf_type, loc);
    if (!leaf_size.has_value() || *leaf_size == 0 ||
        !leaf_alignment.has_value()) {
        report_error("cannot allocate an array of incomplete element type",
                     loc);
        result.has_error = true;
    }

    AllocationSelection allocation = select_allocation_function(
        leaf_type, /*is_array=*/true, input.force_global,
        input.placement_arguments, loc);
    cir::TypeId object_pointer =
        builder_.pointer_type(file_.type_ref(element_type));
    if (!allocation.valid() || !leaf_size.has_value() ||
        !leaf_alignment.has_value()) {
        result.has_error = true;
        result.type = object_pointer;
        result.category = ValueCategory::PrValue;
        return result;
    }
    DeallocationSelection failure_deallocation =
        select_deallocation_function(
            leaf_type, /*is_array=*/true, input.force_global,
            allocation.form.is_placement, &allocation,
            input.placement_arguments, loc,
            /*diagnose=*/true, /*check_access=*/true);
    DeallocationSelection ordinary_deallocation =
        select_deallocation_function(
            leaf_type, /*is_array=*/true, /*force_global=*/false,
            /*placement_matching=*/false, nullptr, {}, loc,
            /*diagnose=*/false, /*check_access=*/false);

    cir::EntityId leaf_destructor = record_destructor(leaf_type);
    bool cookie_required = !allocation.form.is_nonallocating &&
        (leaf_destructor.valid() ||
         (ordinary_deallocation.valid() &&
          ordinary_deallocation.form.is_sized));
    size_t size_type_bytes =
        static_cast<size_t>(file_.target_info().pointer_width / 8);
    abi::ArrayAllocationLayout layout =
        abi::itanium_array_allocation_layout(
            size_type_bytes, *leaf_alignment, cookie_required);

    cir::TypeId usize = builder_.usize_type();
    cir::TypeId allocation_size = allocation_size_type(file_);
    cir::TypeId void_pointer = builder_.pointer_type(builder_.void_type());
    cir::TypeId leaf_pointer_type =
        builder_.pointer_type(file_.type_ref(leaf_type));

    cir::BlockId size_previous = builder_.current_block();
    cir::BlockId size_block = begin_fragment_block("expr.new.array.size");
    cir::InstId outer_count;
    if (constant_outer_count.has_value()) {
        outer_count = builder_.integer_literal(
            static_cast<int64_t>(*constant_outer_count), usize,
            std::to_string(*constant_outer_count), loc);
    } else {
        outer_count = input.runtime_outer_bound;
        if (!outer_count.valid()) {
            outer_count = builder_.integer_literal(0, usize, "0", loc);
            result.has_error = true;
        } else if (!type_equal(file_.inst(outer_count).result_type, usize)) {
            outer_count = builder_.cast(usize, outer_count, "conversion", loc);
        }
    }
    cir::InstId inner = builder_.integer_literal(
        static_cast<int64_t>(inner_count), usize,
        std::to_string(inner_count), loc);
    cir::InstId total_count = builder_.binary(cir::BinaryOpKind::Mul, usize,
                                              outer_count, inner, loc);
    cir::InstId element_bytes = builder_.integer_literal(
        static_cast<int64_t>(*leaf_size), usize,
        std::to_string(*leaf_size), loc);
    cir::InstId payload_bytes = builder_.binary(cir::BinaryOpKind::Mul, usize,
                                                total_count, element_bytes,
                                                loc);
    cir::InstId prefix_bytes = builder_.integer_literal(
        static_cast<int64_t>(layout.prefix_bytes), usize,
        std::to_string(layout.prefix_bytes), loc);
    cir::InstId allocation_bytes = builder_.binary(
        cir::BinaryOpKind::Add, usize, payload_bytes, prefix_bytes, loc);
    cir::InstId call_size = allocation_bytes;
    if (!type_equal(allocation_size, usize)) {
        call_size = builder_.cast(allocation_size, allocation_bytes,
                                  "conversion", loc);
    }
    cir::Fragment size_fragment =
        finish_fragment_block(size_block, size_previous);

    std::vector<ExprResult> allocation_arguments;
    ExprResult size_argument;
    size_argument.type = allocation_size;
    size_argument.value = call_size;
    size_argument.category = ValueCategory::PrValue;
    size_argument.fragment = std::move(size_fragment);
    allocation_arguments.push_back(std::move(size_argument));
    const cir::FunctionTypePayload* allocation_type =
        allocation_function_payload(file_, allocation.entity);
    if (allocation.form.is_aligned) {
        ExprResult alignment_argument;
        alignment_argument.type = allocation_type &&
                allocation_type->parameters.size() > 1
            ? allocation_type->parameters[1].type
            : allocation_size;
        alignment_argument.category = ValueCategory::PrValue;
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.new.array.alignment");
        cir::InstId value = builder_.integer_literal(
            static_cast<int64_t>(*leaf_alignment), usize, {}, loc);
        if (!type_equal(alignment_argument.type, usize)) {
            value = builder_.cast(alignment_argument.type, value,
                                  "conversion", loc);
        }
        alignment_argument.value = value;
        alignment_argument.fragment = finish_fragment_block(block, previous);
        allocation_arguments.push_back(std::move(alignment_argument));
    }
    for (ExprResult& placement : input.placement_arguments) {
        allocation_arguments.push_back(std::move(placement));
    }
    ExprResult callee;
    callee.entity = allocation.entity;
    callee.type = file_.entity(allocation.entity).type;
    callee.name = "operatornew[]";
    callee.category = ValueCategory::FunctionDesignator;
    ExprResult allocation_call = collect_call_expr(
        std::move(callee), std::move(allocation_arguments), loc);
    result.has_error = result.has_error || allocation_call.has_error;

    cir::EntityId raw_entity;
    cir::EntityId count_entity;
    cir::EntityId size_entity;
    cir::EntityId progress_entity;
    std::vector<cir::EntityId> placement_entities;
    cir::BlockId cast_previous = builder_.current_block();
    cir::BlockId cast_block = begin_fragment_block("expr.new.array.raw");
    if (failure_deallocation.valid() &&
        builder_.current_function().valid()) {
        auto make_saved = [&](std::string name, cir::TypeId type,
                              cir::InstId value) {
            cir::EntityId entity = builder_.add_entity(
                cir::EntityKind::Variable, std::move(name), type, {}, loc,
                cir::StorageDuration::Automatic);
            file_.entity_mut(entity).is_definition = true;
            builder_.store(builder_.local_place(entity, type, loc), value,
                           loc);
            return entity;
        };
        raw_entity = make_saved(
            ".new.array.raw." +
                std::to_string(compound_literal_counter_++),
            void_pointer, allocation_call.value);
        count_entity = make_saved(
            ".new.array.count." +
                std::to_string(compound_literal_counter_++),
            usize, total_count);
        size_entity = make_saved(
            ".new.array.size." +
                std::to_string(compound_literal_counter_++),
            usize, allocation_bytes);
        if (leaf_destructor.valid()) {
            progress_entity = builder_.add_entity(
                cir::EntityKind::Variable,
                ".new.array.progress." +
                    std::to_string(compound_literal_counter_++),
                usize, {}, loc, cir::StorageDuration::Automatic);
            file_.entity_mut(progress_entity).is_definition = true;
            builder_.store(builder_.local_place(progress_entity, usize, loc),
                           builder_.integer_literal(0, usize, "0", loc), loc);
        }
        if (failure_deallocation.form.is_placement) {
            std::vector<cir::Operand> call_operands =
                file_.operands(file_.inst(allocation_call.value).operands);
            size_t first_placement = allocation.form.is_aligned ? 3 : 2;
            for (size_t i = first_placement;
                 i < call_operands.size(); ++i) {
                const auto* value =
                    std::get_if<cir::ValueRef>(&call_operands[i].data);
                if (!value || !value->valid()) {
                    continue;
                }
                cir::TypeId type = file_.inst(value->inst).result_type;
                placement_entities.push_back(make_saved(
                    ".new.array.place." +
                        std::to_string(compound_literal_counter_++),
                    type, value->inst));
            }
        }
    }
    cir::Fragment cast_fragment =
        finish_fragment_block(cast_block, cast_previous);
    cir::Fragment fragment = chain(std::move(input.bound_fragment),
                                   std::move(allocation_call.fragment), loc);
    fragment = chain(std::move(fragment), std::move(cast_fragment), loc);

    cir::BlockId saved_unwind = builder_.current_unwind_target();
    cir::BlockId cleanup_pad;
    std::vector<cir::BlockId> cleanup_blocks;
    if (raw_entity.valid()) {
        cir::BlockId cleanup_previous = builder_.current_block();
        builder_.set_current_unwind_target({});
        cleanup_pad =
            builder_.create_detached_block("new.array.cleanup.lpad");
        cir::BlockId action =
            builder_.create_detached_block("new.array.cleanup.act");
        cleanup_blocks = {cleanup_pad, action};
        builder_.set_block_unwind_target(cleanup_pad, {});
        builder_.set_block_unwind_target(action, {});
        builder_.switch_to_block(cleanup_pad);
        cir::EhLandingPadPayload payload;
        payload.is_cleanup = true;
        cir::InstId landing_pad = builder_.eh_landing_pad(std::move(payload),
                                                          loc);
        cir::InstId selector = builder_.eh_selector(landing_pad, loc);
        builder_.branch(action, {landing_pad, selector}, loc);
        cir::InstId exn = builder_.add_block_parameter(
            action, void_pointer, "exn", loc);
        cir::InstId sel = builder_.add_block_parameter(
            action, builder_.int_type(), "sel", loc);
        builder_.switch_to_block(action);
        cir::InstId raw = builder_.lvalue_to_rvalue(
            builder_.local_place(raw_entity, void_pointer, loc), loc);
        cir::BlockId cleanup_exit = action;
        if (leaf_destructor.valid() && progress_entity.valid()) {
            cir::InstId raw_number = builder_.cast(usize, raw, "value", loc);
            cir::InstId prefix = builder_.integer_literal(
                static_cast<int64_t>(layout.prefix_bytes), usize, {}, loc);
            cir::InstId data_number = builder_.binary(
                cir::BinaryOpKind::Add, usize, raw_number, prefix, loc);
            cir::InstId leaf_pointer = builder_.cast(
                leaf_pointer_type, data_number, "value", loc);
            cir::InstId constructed = builder_.lvalue_to_rvalue(
                builder_.local_place(progress_entity, usize, loc), loc);
            cir::Fragment destroy = dynamic_array_destroy_fragment(
                leaf_pointer, leaf_type, constructed, {}, loc);
            if (!destroy.empty()) {
                cleanup_blocks.insert(cleanup_blocks.end(),
                                      destroy.blocks.begin(),
                                      destroy.blocks.end());
                builder_.branch(destroy.entry, {}, loc);
                cleanup_exit = destroy.exit;
            }
        }
        builder_.switch_to_block(cleanup_exit);
        std::vector<cir::InstId> placement_values;
        for (cir::EntityId entity : placement_entities) {
            placement_values.push_back(builder_.lvalue_to_rvalue(
                builder_.local_place(entity, file_.entity(entity).type, loc),
                loc));
        }
        cir::InstId explicit_size;
        if (failure_deallocation.form.is_sized) {
            explicit_size = builder_.lvalue_to_rvalue(
                builder_.local_place(size_entity, usize, loc), loc);
        }
        emit_deallocation_call(failure_deallocation, raw, leaf_type, loc,
                               explicit_size, placement_values);
        emit_unwind_continue(cleanup_exit, exn, sel, saved_unwind, loc);
        eh_pads_in_flight_.push_back(landing_pad);
        track_speculative_rollback([this]() {
            if (!eh_pads_in_flight_.empty()) {
                eh_pads_in_flight_.pop_back();
            }
        });
        eh_code_targets_[cleanup_pad.index] = action;
        track_speculative_rollback(
            [this, index = cleanup_pad.index]() {
                eh_code_targets_.erase(index);
            });
        builder_.switch_to_block(cleanup_previous);
        builder_.set_current_unwind_target(cleanup_pad);
        for (const ExprResult& clause : clauses) {
            for (cir::BlockId block : clause.fragment.blocks) {
                if (file_.block(block).unwind_target == saved_unwind) {
                    builder_.set_block_unwind_target(block, cleanup_pad);
                }
            }
        }
    }

    cir::BlockId nonnull = builder_.create_detached_block(
        "new.array.nonnull");
    cir::BlockId null_block;
    bool null_check = allocation.form.is_nonthrowing &&
        !allocation.form.is_nonallocating;
    if (null_check) {
        null_block = builder_.create_detached_block("new.array.null");
    }
    cir::BlockId done = builder_.create_detached_block("new.array.done");
    cir::InstId result_value = builder_.add_block_parameter(
        done, object_pointer, "new.array.result", loc);

    cir::BlockId block_previous = builder_.current_block();
    builder_.switch_to_block(nonnull);
    cir::InstId raw_number = builder_.cast(
        usize, allocation_call.value, "value", loc);
    cir::InstId data_number = raw_number;
    if (layout.prefix_bytes != 0) {
        data_number = builder_.binary(
            cir::BinaryOpKind::Add, usize, raw_number,
            builder_.integer_literal(
                static_cast<int64_t>(layout.prefix_bytes), usize, {}, loc),
            loc);
    }
    cir::InstId typed = builder_.cast(object_pointer, data_number, "value",
                                      loc);
    cir::InstId leaf_pointer = builder_.cast(
        leaf_pointer_type, data_number, "value", loc);
    if (layout.has_cookie) {
        cir::InstId cookie_number = builder_.binary(
            cir::BinaryOpKind::Add, usize, raw_number,
            builder_.integer_literal(
                static_cast<int64_t>(layout.cookie_offset_from_allocation),
                usize, {}, loc),
            loc);
        cir::InstId cookie_pointer = builder_.cast(
            builder_.pointer_type(file_.type_ref(allocation_size)),
            cookie_number, "value", loc);
        cir::InstId cookie_value = total_count;
        if (!type_equal(allocation_size, usize)) {
            cookie_value = builder_.cast(allocation_size, total_count,
                                         "conversion", loc);
        }
        builder_.store(builder_.deref(cookie_pointer, loc), cookie_value, loc);
    }
    cir::Fragment init_fragment;
    bool value_initialize_tail = input.initializer_present;
    cir::InstId initialized_count = builder_.integer_literal(
        0, usize, "0", loc);
    bool needs_constructor = record_needs_construction(leaf_type) ||
        record_requires_default_constructor_selection(leaf_type);

    if (!clauses.empty()) {
        for (size_t index = 0; index < clauses.size(); ++index) {
            cir::BlockId place_previous = builder_.current_block();
            cir::BlockId place_block = begin_fragment_block(
                "new.array.init.element");
            cir::InstId index_value = builder_.integer_literal(
                static_cast<int64_t>(index), usize,
                std::to_string(index), loc);
            cir::InstId element = builder_.array_element_place(
                typed, index_value, loc);
            cir::Fragment place_fragment =
                finish_fragment_block(place_block, place_previous);
            init_fragment = chain(std::move(init_fragment),
                                  std::move(place_fragment), loc);
            init_fragment = chain(
                std::move(init_fragment),
                emit_initializer_for_place(
                    element, element_type, std::move(clauses[index]), loc),
                loc);
            if (progress_entity.valid()) {
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block(
                    "new.array.init.progress");
                uint64_t completed =
                    static_cast<uint64_t>(index + 1) * inner_count;
                builder_.store(
                    builder_.local_place(progress_entity, usize, loc),
                    builder_.integer_literal(
                        static_cast<int64_t>(completed), usize, {}, loc),
                    loc);
                init_fragment = chain(
                    std::move(init_fragment),
                    finish_fragment_block(block, previous), loc);
            }
        }
        uint64_t initialized =
            static_cast<uint64_t>(clauses.size()) * inner_count;
        initialized_count = builder_.integer_literal(
            static_cast<int64_t>(initialized), usize,
            std::to_string(initialized), loc);
    }

    bool known_complete_initializer = constant_outer_count.has_value() &&
        clauses.size() == *constant_outer_count;
    if (needs_constructor && !known_complete_initializer) {
        init_fragment = chain(
            std::move(init_fragment),
            dynamic_array_construct_fragment(
                leaf_pointer, leaf_type, initialized_count, total_count,
                progress_entity.valid()
                    ? builder_.local_place(progress_entity, usize, loc)
                    : cir::InstId{},
                loc, &result.has_error),
            loc);
    } else if (!needs_constructor && value_initialize_tail &&
               !known_complete_initializer) {
        init_fragment = chain(
            std::move(init_fragment),
            dynamic_array_zero_fragment(leaf_pointer, leaf_type,
                                        initialized_count, total_count, loc),
            loc);
    }

    if (init_fragment.empty()) {
        builder_.branch(done, {typed}, loc);
    } else {
        builder_.branch(init_fragment.entry, {}, loc);
        builder_.branch_from(init_fragment.exit, done, {typed}, loc);
    }
    if (null_check) {
        builder_.switch_to_block(null_block);
        cir::InstId null_value = builder_.cast(
            object_pointer,
            builder_.integer_literal(0, usize, "0", loc), "nullptr", loc);
        builder_.branch(done, {null_value}, loc);
    }

    builder_.switch_to_block(fragment.exit);
    if (null_check) {
        cir::InstId null_void = builder_.cast(
            void_pointer,
            builder_.integer_literal(0, usize, "0", loc), "nullptr", loc);
        cir::InstId is_nonnull = builder_.binary(
            cir::BinaryOpKind::NotEqual, builder_.int_type(),
            allocation_call.value, null_void, loc);
        builder_.cond_branch_from(fragment.exit, is_nonnull, nonnull,
                                  null_block, {}, loc);
    } else {
        builder_.branch_from(fragment.exit, nonnull, {}, loc);
    }
    fragment.blocks.push_back(nonnull);
    fragment.blocks.insert(fragment.blocks.end(), init_fragment.blocks.begin(),
                           init_fragment.blocks.end());
    if (null_block.valid()) {
        fragment.blocks.push_back(null_block);
    }
    fragment.blocks.push_back(done);
    fragment.blocks.insert(fragment.blocks.end(), cleanup_blocks.begin(),
                           cleanup_blocks.end());
    fragment.exit = done;
    fragment.falls_through = true;
    builder_.switch_to_block(block_previous);
    builder_.set_current_unwind_target(saved_unwind);

    result.fragment = std::move(fragment);
    result.value = result_value;
    result.type = object_pointer;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::collect_new_expr(cir::TypeId type,
                                     std::vector<ExprResult> arguments,
                                     SrcLoc loc) {
    NewExpressionInput input;
    input.allocated_type = type;
    input.initializer_present = !arguments.empty();
    input.initializer_arguments = std::move(arguments);
    return collect_new_expr(std::move(input), loc);
}

ExprResult Session::collect_new_expr(NewExpressionInput input, SrcLoc loc) {
    cir::TypeId type = input.allocated_type;
    std::vector<ExprResult> arguments =
        std::move(input.initializer_arguments);
    if (in_template_definition()) {
        bool dependent_target = type.valid() && is_dependent_type(type);
        bool dependent_argument = false;
        for (const ExprResult& argument : input.placement_arguments) {
            dependent_argument =
                dependent_argument || expr_is_dependent(argument);
        }
        for (const ExprResult& argument : arguments) {
            dependent_argument =
                dependent_argument || expr_is_dependent(argument);
        }
        if (dependent_target || dependent_argument) {
            ExprResult combined;
            combined.fragment = std::move(input.bound_fragment);
            for (ExprResult& argument : input.placement_arguments) {
                combined.fragment = chain(std::move(combined.fragment),
                                          std::move(argument.fragment), loc);
                combined.has_error = combined.has_error || argument.has_error;
            }
            for (ExprResult& argument : arguments) {
                combined.fragment = chain(std::move(combined.fragment),
                                          std::move(argument.fragment), loc);
                combined.has_error = combined.has_error || argument.has_error;
            }
            if (dependent_target) {
                return make_dependent_expr(std::move(combined), loc);
            }
            cir::TypeId pointee = type;
            cir::TypeId resolved_type = file_.resolved_type(type);
            if (input.is_array && file_.valid(resolved_type) &&
                file_.type(resolved_type).kind == cir::TypeKind::Array) {
                const auto* array = std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(resolved_type));
                if (array) {
                    pointee = array->element_type.type;
                }
            }
            cir::TypeId pointer_type =
                builder_.pointer_type(file_.type_ref(pointee));
            return make_deferred_typed_expr(std::move(combined), pointer_type,
                                            ValueCategory::PrValue, loc);
        }
    }
    if (input.is_array) {
        input.initializer_arguments = std::move(arguments);
        return collect_array_new_expr(std::move(input), loc);
    }
    ExprResult result;
    cir::TypeId resolved = file_.resolved_type(type);
    (void)require_complete_class_type(
        resolved, loc, cir::InstantiationDemandKind::CompleteClass);
    if (diagnose_abstract_instantiation(resolved, loc)) {
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    std::optional<size_t> size = size_of_type(resolved, loc);
    if (!size.has_value() || *size == 0) {
        report_error("cannot allocate an incomplete type", loc);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    cir::TypeId usize = allocation_size_type(file_);
    cir::TypeId void_pointer =
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
    cir::TypeId object_pointer = builder_.pointer_type(file_.type_ref(type));
    AllocationSelection allocation = select_allocation_function(
        resolved, /*is_array=*/false, input.force_global,
        input.placement_arguments, loc);
    if (!allocation.valid()) {
        result.has_error = true;
        result.type = object_pointer;
        result.category = ValueCategory::PrValue;
        return result;
    }
    DeallocationSelection failure_deallocation =
        select_deallocation_function(
            resolved, /*is_array=*/false, input.force_global,
            allocation.form.is_placement, &allocation,
            input.placement_arguments, loc,
            /*diagnose=*/true, /*check_access=*/true);

    std::vector<ExprResult> allocation_arguments;
    ExprResult size_argument;
    size_argument.type = usize;
    size_argument.category = ValueCategory::PrValue;
    cir::BlockId size_previous = builder_.current_block();
    cir::BlockId size_block = begin_fragment_block("expr.new.size");
    size_argument.value = builder_.integer_literal(
        static_cast<int64_t>(*size), usize, std::to_string(*size), loc);
    size_argument.fragment = finish_fragment_block(size_block, size_previous);
    allocation_arguments.push_back(std::move(size_argument));
    const cir::FunctionTypePayload* allocation_type =
        allocation_function_payload(file_, allocation.entity);
    if (allocation.form.is_aligned) {
        ExprResult alignment_argument;
        alignment_argument.type = allocation_type &&
                allocation_type->parameters.size() > 1
            ? allocation_type->parameters[1].type
            : usize;
        alignment_argument.category = ValueCategory::PrValue;
        cir::BlockId alignment_previous = builder_.current_block();
        cir::BlockId alignment_block =
            begin_fragment_block("expr.new.alignment");
        cir::InstId alignment_value = builder_.integer_literal(
            static_cast<int64_t>(*align_of_type(resolved, loc)), usize,
            {}, loc);
        if (!type_equal(alignment_argument.type, usize)) {
            alignment_value = builder_.cast(alignment_argument.type,
                                            alignment_value,
                                            "conversion", loc);
        }
        alignment_argument.value = alignment_value;
        alignment_argument.fragment =
            finish_fragment_block(alignment_block, alignment_previous);
        allocation_arguments.push_back(std::move(alignment_argument));
    }
    for (ExprResult& placement : input.placement_arguments) {
        allocation_arguments.push_back(std::move(placement));
    }
    ExprResult callee;
    callee.entity = allocation.entity;
    callee.type = file_.entity(allocation.entity).type;
    callee.name = allocation_entity_has_name(file_, allocation.entity,
                                             "operatornew")
        ? "operatornew"
        : "operatornew[]";
    callee.category = ValueCategory::FunctionDesignator;
    ExprResult allocation_call = collect_call_expr(
        std::move(callee), std::move(allocation_arguments), loc);
    result.has_error = result.has_error || allocation_call.has_error;
    cir::BlockId cast_previous = builder_.current_block();
    cir::BlockId cast_block = begin_fragment_block("expr.new.cast");
    cir::InstId typed = builder_.cast(object_pointer,
                                      allocation_call.value,
                                      "value", loc);
    cir::EntityId raw_cleanup_entity;
    std::vector<cir::EntityId> placement_cleanup_entities;
    if (failure_deallocation.valid() &&
        builder_.current_function().valid()) {
        raw_cleanup_entity = builder_.add_entity(
            cir::EntityKind::Variable,
            ".new.raw." + std::to_string(compound_literal_counter_++),
            void_pointer, {}, loc, cir::StorageDuration::Automatic);
        file_.entity_mut(raw_cleanup_entity).is_definition = true;
        cir::InstId raw_place = builder_.local_place(
            raw_cleanup_entity, void_pointer, loc);
        builder_.store(raw_place, allocation_call.value, loc);

        if (failure_deallocation.form.is_placement &&
            allocation_call.value.valid()) {
            std::vector<cir::Operand> call_operands =
                file_.operands(file_.inst(allocation_call.value).operands);

            for (size_t i = 2; i < call_operands.size(); ++i) {
                const auto* value_ref =
                    std::get_if<cir::ValueRef>(&call_operands[i].data);
                if (!value_ref || !value_ref->valid()) {
                    continue;
                }
                cir::TypeId value_type =
                    file_.inst(value_ref->inst).result_type;
                cir::EntityId saved = builder_.add_entity(
                    cir::EntityKind::Variable,
                    ".new.place." +
                        std::to_string(compound_literal_counter_++),
                    value_type, {}, loc, cir::StorageDuration::Automatic);
                file_.entity_mut(saved).is_definition = true;
                builder_.store(builder_.local_place(saved, value_type, loc),
                               value_ref->inst, loc);
                placement_cleanup_entities.push_back(saved);
            }
        }
    }
    cir::Fragment cast_fragment =
        finish_fragment_block(cast_block, cast_previous);
    cir::Fragment fragment = chain(std::move(input.bound_fragment),
                                   std::move(allocation_call.fragment), loc);
    fragment = chain(std::move(fragment), std::move(cast_fragment), loc);

    cir::BlockId saved_new_unwind_target = builder_.current_unwind_target();
    cir::BlockId new_cleanup_pad;
    std::vector<cir::BlockId> new_cleanup_blocks;
    if (raw_cleanup_entity.valid()) {
        builder_.set_current_unwind_target({});
        new_cleanup_pad = builder_.create_detached_block("new.cleanup.lpad");
        cir::BlockId action =
            builder_.create_detached_block("new.cleanup.act");
        new_cleanup_blocks = {new_cleanup_pad, action};
        builder_.set_block_unwind_target(new_cleanup_pad, {});
        builder_.set_block_unwind_target(action, {});
        builder_.switch_to_block(new_cleanup_pad);
        cir::EhLandingPadPayload pad_payload;
        pad_payload.is_cleanup = true;
        cir::InstId landing_pad =
            builder_.eh_landing_pad(std::move(pad_payload), loc);
        cir::InstId selector = builder_.eh_selector(landing_pad, loc);
        builder_.branch(action, {landing_pad, selector}, loc);
        cir::InstId exn = builder_.add_block_parameter(
            action, void_pointer, "exn", loc);
        cir::InstId sel = builder_.add_block_parameter(
            action, builder_.int_type(), "sel", loc);
        builder_.switch_to_block(action);
        cir::InstId raw = builder_.lvalue_to_rvalue(
            builder_.local_place(raw_cleanup_entity, void_pointer, loc), loc);
        std::vector<cir::InstId> placement_values;
        for (cir::EntityId saved : placement_cleanup_entities) {
            placement_values.push_back(builder_.lvalue_to_rvalue(
                builder_.local_place(saved, file_.entity(saved).type, loc),
                loc));
        }
        emit_deallocation_call(failure_deallocation, raw, resolved, loc, {},
                               placement_values);
        emit_unwind_continue(action, exn, sel, saved_new_unwind_target, loc);
        eh_pads_in_flight_.push_back(landing_pad);
        track_speculative_rollback([this]() {
            if (!eh_pads_in_flight_.empty()) {
                eh_pads_in_flight_.pop_back();
            }
        });
        eh_code_targets_[new_cleanup_pad.index] = action;
        track_speculative_rollback(
            [this, index = new_cleanup_pad.index]() {
                eh_code_targets_.erase(index);
            });
        builder_.set_current_unwind_target(new_cleanup_pad);
        auto reparent_initializer_fragment = [&](const cir::Fragment& value) {
            for (cir::BlockId block : value.blocks) {
                if (file_.block(block).unwind_target ==
                    saved_new_unwind_target) {
                    builder_.set_block_unwind_target(block,
                                                     new_cleanup_pad);
                }
            }
        };
        for (const ExprResult& argument : arguments) {
            reparent_initializer_fragment(argument.fragment);
        }
    }

    cir::Fragment initialization;
    bool empty_braced_list = arguments.size() == 1 &&
        arguments.front().init_list &&
        arguments.front().init_list->elements.empty();
    bool aggregate_copy_or_move = false;
    if (arguments.size() == 1 && arguments.front().type.valid()) {
        cir::TypeId source = file_.resolved_type(arguments.front().type);
        aggregate_copy_or_move =
            file_.valid(source) &&
            file_.type(source).kind == cir::TypeKind::Record &&
            (source == resolved ||
             analyze_derived_to_base_path(source, resolved).kind !=
                 DerivedToBasePathKind::NotFound);
    }
    const bool parenthesized_aggregate =
        lang_opts_.is_cxx20_or_later() &&
        input.initializer_is_parenthesized &&
        is_aggregate_type(resolved) &&
        !record_has_user_constructor(resolved) &&
        !aggregate_copy_or_move;
    bool braced_aggregate_copy_or_move = false;
    if (input.initializer_is_braced &&
        arguments.size() == 1 &&
        arguments.front().init_list &&
        arguments.front().init_list->elements.size() == 1 &&
        arguments.front().init_list->elements.front().designators.empty()) {
        cir::TypeId source = file_.resolved_type(
            arguments.front().init_list->elements.front().value.type);
        braced_aggregate_copy_or_move =
            file_.valid(source) &&
            file_.type(source).kind == cir::TypeKind::Record &&
            (source == resolved ||
             analyze_derived_to_base_path(source, resolved).kind !=
                 DerivedToBasePathKind::NotFound);
    }
    const bool braced_aggregate =
        input.initializer_is_braced &&
        arguments.size() == 1 &&
        arguments.front().init_list &&
        is_aggregate_type(resolved) &&
        !record_has_user_constructor(resolved) &&
        !braced_aggregate_copy_or_move;
    bool needs_constructor = braced_aggregate_copy_or_move ||
        record_needs_construction(resolved) ||
        ((arguments.empty() || empty_braced_list) &&
         record_requires_default_constructor_selection(resolved));
    auto initialize_aggregate_at_allocation =
        [&](ExprResult initializer) {
            cir::BlockId place_previous = builder_.current_block();
            cir::BlockId place_block =
                begin_fragment_block("expr.new.aggregate.place");
            cir::InstId object_place = builder_.deref(typed, loc);
            cir::Fragment place_fragment =
                finish_fragment_block(place_block, place_previous);
            return chain(
                std::move(place_fragment),
                emit_initializer_for_place(
                    object_place, type, std::move(initializer), loc,
                    UseContext::DirectInit),
                loc);
        };
    if (parenthesized_aggregate) {
        std::vector<InitElementInput> elements;
        elements.reserve(arguments.size());
        for (ExprResult& argument : arguments) {
            InitElementInput element;
            element.value = std::move(argument);
            element.loc = loc;
            elements.push_back(std::move(element));
        }
        ExprResult initializer = collect_init_list_expr(
            std::move(elements), loc, InitListSyntax::Parenthesized);
        initialization = initialize_aggregate_at_allocation(
            std::move(initializer));
    } else if (braced_aggregate) {
        initialization = initialize_aggregate_at_allocation(
            std::move(arguments.front()));
    } else if (needs_constructor) {
        ConstructorCallMaterialization materialized =
            materialize_constructor_call(resolved,
                                         std::move(arguments),
                                         loc);
        if (!materialized.constructor.valid()) {
            report_error(std::string(materialized.ambiguous
                                         ? "ambiguous constructor for 'new "
                                         : "no matching constructor for 'new ") +
                             file_.format_type(type) + "'",
                         loc);
            result.has_error = true;
        } else {
            result.has_error = result.has_error || materialized.has_error;
            initialization = chain(
                std::move(initialization),
                std::move(materialized.argument_fragment), loc);
            if (materialized.has_error) {
                result.type = object_pointer;
                result.value = typed;
                result.category = ValueCategory::PrValue;
                result.fragment = chain(std::move(fragment),
                                        std::move(initialization), loc);
                if (new_cleanup_pad.valid()) {
                    builder_.set_current_unwind_target(
                        saved_new_unwind_target);
                }
                return result;
            }
            cir::BlockId construct_previous = builder_.current_block();
            cir::BlockId construct_block = begin_fragment_block("expr.new.construct");
            cir::InstId object_place = builder_.deref(typed, loc);
            emit_construct_in_place(object_place,
                                    structor_complete_variant(materialized.constructor),
                                    materialized.argument_values, loc);
            cir::Fragment construct_fragment =
                finish_fragment_block(construct_block, construct_previous);
            initialization = chain(std::move(initialization),
                                   std::move(construct_fragment), loc);
        }
    } else if (arguments.size() == 1) {
        ExprResult converted = convert_to(std::move(arguments.front()),
                                          type,
                                          UseContext::Init,
                                          loc);
        result.has_error = result.has_error || converted.has_error;
        cir::BlockId store_previous = builder_.current_block();
        cir::BlockId store_block = begin_fragment_block("expr.new.init");
        cir::InstId object_place = builder_.deref(typed, loc);
        builder_.store(object_place, converted.value, loc);
        cir::Fragment store_fragment =
            finish_fragment_block(store_block, store_previous);
        initialization = chain(std::move(initialization),
                               std::move(converted.fragment), loc);
        initialization = chain(std::move(initialization),
                               std::move(store_fragment), loc);
    } else if (arguments.size() > 1) {
        report_error("new initializer with multiple arguments requires a class with a matching constructor",
                     loc);
        result.has_error = true;
    }

    cir::InstId expression_value = typed;
    bool null_check = allocation.form.is_nonthrowing &&
        !allocation.form.is_nonallocating && !initialization.empty();
    if (null_check) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId null_block =
            builder_.create_detached_block("new.null");
        cir::BlockId done = builder_.create_detached_block("new.done");
        expression_value = builder_.add_block_parameter(
            done, object_pointer, "new.result", loc);
        builder_.switch_to_block(fragment.exit);
        cir::InstId null_value = builder_.cast(
            void_pointer,
            builder_.integer_literal(0, builder_.usize_type(), "0", loc),
            "nullptr", loc);
        cir::InstId is_nonnull = builder_.binary(
            cir::BinaryOpKind::NotEqual, builder_.int_type(),
            allocation_call.value, null_value, loc);
        builder_.cond_branch_from(fragment.exit, is_nonnull,
                                  initialization.entry, null_block, {}, loc);
        builder_.branch_from(initialization.exit, done, {typed}, loc);
        builder_.branch_from(null_block, done, {typed}, loc);
        fragment.blocks.insert(fragment.blocks.end(),
                               initialization.blocks.begin(),
                               initialization.blocks.end());
        fragment.blocks.push_back(null_block);
        fragment.blocks.push_back(done);
        fragment.exit = done;
        fragment.falls_through = true;
        builder_.switch_to_block(previous);
    } else {
        fragment = chain(std::move(fragment), std::move(initialization), loc);
    }
    fragment.blocks.insert(fragment.blocks.end(), new_cleanup_blocks.begin(),
                           new_cleanup_blocks.end());

    result.fragment = std::move(fragment);
    result.value = expression_value;
    result.type = object_pointer;
    result.category = ValueCategory::PrValue;
    if (new_cleanup_pad.valid()) {
        builder_.set_current_unwind_target(saved_new_unwind_target);
    }
    return result;
}

ExprResult Session::collect_delete_expr(ExprResult pointer, SrcLoc loc) {
    DeleteExpressionInput input;
    input.pointer = std::move(pointer);
    return collect_delete_expr(std::move(input), loc);
}

ExprResult Session::collect_delete_expr(DeleteExpressionInput input,
                                        SrcLoc loc) {
    ExprResult pointer = std::move(input.pointer);
    if (expr_is_dependent(pointer)) {
        if (pointer.template_value_expr.valid()) {
            pointer.template_value_expr.canonical_id = {};
            cir::TemplateValueExprNode node;
            node.kind = cir::TemplateValueExprKind::Unary;
            node.op = input.is_array
                ? cir::TemplateValueExprOp::DeleteArray
                : cir::TemplateValueExprOp::Delete;
            node.lhs = pointer.template_value_expr.root;
            node.result_type = type_ref(builder_.void_type());
            node.value = static_cast<int64_t>(ValueCategory::PrValue);
            pointer.template_value_expr.nodes.push_back(std::move(node));
            pointer.template_value_expr.root =
                static_cast<uint32_t>(
                    pointer.template_value_expr.nodes.size() - 1);
        }
        return make_deferred_typed_expr(std::move(pointer), builder_.void_type(),
                                        ValueCategory::PrValue, loc);
    }
    if (lang_opts_.is_cxx_mode()) {
        cir::TypeId source = file_.resolved_type(pointer.type);
        if (file_.valid(source) &&
            file_.type(source).kind == cir::TypeKind::Record) {
            if (pointer.category == ValueCategory::PrValue &&
                pointer.value.valid()) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(pointer),
                                               /*is_arrow=*/false,
                                               loc);
                pointer = std::move(materialized.base_place);
            }
            cir::TypeId contextual_target;
            UserConversionSequence sequence =
                resolve_permitted_implicit_conversion(
                    pointer,
                    PermittedImplicitTarget::PointerToObject,
                    &contextual_target,
                    loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_error(
                    "delete operand has an ambiguous contextual conversion "
                    "to pointer-to-object type",
                    loc);
                ExprResult result;
                result.fragment = std::move(pointer.fragment);
                result.has_error = true;
                result.type =
                    file_.builtin_type(cir::BuiltinTypeKind::Void);
                result.category = ValueCategory::PrValue;
                return result;
            }
            if (sequence.kind ==
                UserConversionSequence::Kind::ConversionFunction) {
                pointer = apply_user_conversion_sequence(
                    std::move(pointer), contextual_target, sequence, loc);
            }
        }
    }
    ExprResult value = require_value(std::move(pointer), UseContext::RValue, loc);
    ExprResult result;
    result.has_error = value.has_error;
    result.type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    result.category = ValueCategory::PrValue;

    cir::TypeId resolved_pointer = file_.resolved_type(value.type);
    if (!file_.valid(resolved_pointer) ||
        file_.type(resolved_pointer).kind != cir::TypeKind::Pointer) {
        report_error("delete requires a pointer operand", loc);
        result.has_error = true;
        result.fragment = std::move(value.fragment);
        return result;
    }
    cir::TypeId pointee = file_.pointer_pointee_type(resolved_pointer);
    cir::TypeId leaf = input.is_array
        ? allocation_leaf_type(file_, pointee)
        : pointee;
    (void)require_complete_class_type(
        leaf, loc, cir::InstantiationDemandKind::DeletionSemantics);
    if (!validate_potentially_invoked_destructor(leaf, loc)) {
        result.has_error = true;
    }
    cir::TypeId void_pointer =
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
    cir::EntityId destructor = record_destructor(leaf);
    DeallocationSelection deallocation = select_deallocation_function(
        leaf, input.is_array, input.force_global,
        /*placement_matching=*/false, nullptr, {}, loc);
    if (!deallocation.valid()) {
        result.has_error = true;
        result.fragment = std::move(value.fragment);
        return result;
    }

    auto emit_deallocation = [&](cir::InstId pointer_value) {
        const cir::FunctionTypePayload* payload =
            allocation_function_payload(file_, deallocation.entity);
        if (!payload || payload->parameters.empty()) {
            result.has_error = true;
            return;
        }
        std::vector<cir::InstId> call_arguments;
        cir::TypeId first_type = payload->parameters.front().type;
        cir::InstId first = pointer_value;
        if (!type_equal(file_.inst(first).result_type, first_type)) {
            first = builder_.cast(first_type, first, "conversion", loc);
        }
        call_arguments.push_back(first);
        size_t parameter = 1;
        if (deallocation.form.is_destroying) {
            cir::TypeId tag_type = payload->parameters[parameter++].type;
            cir::InstId tag;
            cir::TypeId resolved_tag = file_.resolved_type(tag_type);
            if (file_.valid(resolved_tag) &&
                file_.type(resolved_tag).kind == cir::TypeKind::Record) {
                cir::EntityId temporary = builder_.add_entity(
                    cir::EntityKind::Variable,
                    ".destroying.delete.tag." +
                        std::to_string(compound_literal_counter_++),
                    tag_type, {}, loc, cir::StorageDuration::Automatic);
                file_.entity_mut(temporary).is_definition = true;
                cir::InstId place = builder_.local_place(
                    temporary, tag_type, loc);
                builder_.zero_object(place, loc);
                tag = builder_.lvalue_to_rvalue(place, loc);
            } else {
                tag = builder_.integer_literal(
                    0, builder_.usize_type(), "0", loc);
                if (!type_equal(tag_type, builder_.usize_type())) {
                    tag = builder_.cast(tag_type, tag, "conversion", loc);
                }
            }
            call_arguments.push_back(tag);
        }
        if (deallocation.form.is_sized) {
            std::optional<size_t> bytes = size_of_type(pointee, loc);
            cir::InstId size = builder_.integer_literal(
                static_cast<int64_t>(bytes.value_or(0)),
                builder_.usize_type(), {}, loc);
            cir::TypeId parameter_type = payload->parameters[parameter++].type;
            if (!type_equal(parameter_type, builder_.usize_type())) {
                size = builder_.cast(parameter_type, size, "conversion", loc);
            }
            call_arguments.push_back(size);
        }
        if (deallocation.form.is_aligned) {
            std::optional<size_t> bytes = align_of_type(pointee, loc);
            cir::InstId alignment = builder_.integer_literal(
                static_cast<int64_t>(bytes.value_or(1)),
                builder_.usize_type(), {}, loc);
            cir::TypeId parameter_type = payload->parameters[parameter++].type;
            if (!type_equal(parameter_type, builder_.usize_type())) {
                alignment = builder_.cast(parameter_type, alignment,
                                          "conversion", loc);
            }
            call_arguments.push_back(alignment);
        }
        builder_.call(deallocation.entity, builder_.void_type(),
                      call_arguments, loc);
    };

    cir::Fragment fragment =
        adopt_or_create_fragment_entry(std::move(value.fragment), "expr.delete");

    cir::BlockId previous = builder_.current_block();
    builder_.switch_to_block(fragment.exit);
    cir::InstId null_value = builder_.cast(
        void_pointer,
        builder_.integer_literal(0, builder_.usize_type(), "0", loc),
        "nullptr", loc);
    cir::InstId erased = builder_.cast(void_pointer, value.value, "value", loc);
    cir::InstId is_set = builder_.binary(cir::BinaryOpKind::NotEqual,
                                         builder_.int_type(), erased,
                                         null_value, loc);
    cir::BlockId destroy_block =
        builder_.create_detached_block("delete.nonnull");
    cir::BlockId continue_block =
        builder_.create_detached_block("delete.done");
    builder_.cond_branch_from(fragment.exit, is_set, destroy_block,
                              continue_block, {}, loc);
    builder_.switch_to_block(destroy_block);
    if (input.is_array) {
        fragment.blocks.push_back(destroy_block);
        std::optional<size_t> leaf_size = size_of_type(leaf, loc);
        std::optional<size_t> leaf_alignment = align_of_type(leaf, loc);
        bool cookie_required = destructor.valid() ||
            deallocation.form.is_sized;
        size_t size_type_bytes =
            static_cast<size_t>(file_.target_info().pointer_width / 8);
        abi::ArrayAllocationLayout layout =
            abi::itanium_array_allocation_layout(
                size_type_bytes, leaf_alignment.value_or(1),
                cookie_required);
        cir::TypeId usize = builder_.usize_type();
        cir::TypeId size_type = allocation_size_type(file_);
        cir::InstId data_number = builder_.cast(
            usize, value.value, "value", loc);
        cir::InstId raw_number = data_number;
        if (layout.prefix_bytes != 0) {
            raw_number = builder_.binary(
                cir::BinaryOpKind::Sub, usize, data_number,
                builder_.integer_literal(
                    static_cast<int64_t>(layout.prefix_bytes), usize, {},
                    loc),
                loc);
        }
        cir::InstId raw_pointer = builder_.cast(
            void_pointer, raw_number, "value", loc);
        cir::InstId count;
        if (layout.has_cookie) {
            cir::InstId cookie_number = builder_.binary(
                cir::BinaryOpKind::Sub, usize, data_number,
                builder_.integer_literal(
                    static_cast<int64_t>(layout.cookie_bytes), usize, {},
                    loc),
                loc);
            cir::InstId cookie_pointer = builder_.cast(
                builder_.pointer_type(file_.type_ref(size_type)),
                cookie_number, "value", loc);
            count = builder_.lvalue_to_rvalue(
                builder_.deref(cookie_pointer, loc), loc);
            if (!type_equal(file_.inst(count).result_type, usize)) {
                count = builder_.cast(usize, count, "conversion", loc);
            }
        }
        cir::InstId total_size;
        if (deallocation.form.is_sized) {
            cir::InstId element_bytes = builder_.integer_literal(
                static_cast<int64_t>(leaf_size.value_or(0)), usize, {}, loc);
            cir::InstId payload_bytes = count.valid()
                ? builder_.binary(cir::BinaryOpKind::Mul, usize, count,
                                  element_bytes, loc)
                : builder_.integer_literal(0, usize, "0", loc);
            total_size = builder_.binary(
                cir::BinaryOpKind::Add, usize, payload_bytes,
                builder_.integer_literal(
                    static_cast<int64_t>(layout.prefix_bytes), usize, {},
                    loc),
                loc);
        }
        cir::BlockId delete_exit = destroy_block;
        if (destructor.valid() && count.valid()) {
            cir::InstId leaf_pointer = builder_.cast(
                builder_.pointer_type(file_.type_ref(leaf)), data_number,
                "value", loc);
            cir::EntityId progress = builder_.add_entity(
                cir::EntityKind::Variable,
                ".delete.array.remaining." +
                    std::to_string(compound_literal_counter_++),
                usize, {}, loc, cir::StorageDuration::Automatic);
            file_.entity_mut(progress).is_definition = true;
            cir::InstId progress_place = builder_.local_place(
                progress, usize, loc);
            builder_.store(progress_place, count, loc);

            cir::BlockId outer_target =
                file_.block(destroy_block).unwind_target;
            cir::BlockId pad = builder_.create_detached_block(
                "delete.array.dtor.lpad");
            cir::BlockId action = builder_.create_detached_block(
                "delete.array.dtor.act");
            fragment.blocks.push_back(pad);
            fragment.blocks.push_back(action);
            builder_.set_block_unwind_target(pad, {});
            builder_.set_block_unwind_target(action, {});
            builder_.set_block_unwind_target(destroy_block, pad);
            builder_.switch_to_block(pad);
            cir::EhLandingPadPayload pad_payload;
            pad_payload.is_cleanup = true;
            cir::InstId landing_pad = builder_.eh_landing_pad(
                std::move(pad_payload), loc);
            cir::InstId selector = builder_.eh_selector(landing_pad, loc);
            builder_.branch(action, {landing_pad, selector}, loc);
            cir::InstId exn = builder_.add_block_parameter(
                action, void_pointer, "exn", loc);
            cir::InstId sel = builder_.add_block_parameter(
                action, builder_.int_type(), "sel", loc);
            builder_.switch_to_block(action);
            cir::InstId remaining = builder_.lvalue_to_rvalue(
                builder_.local_place(progress, usize, loc), loc);
            cir::BlockId saved_target = builder_.current_unwind_target();
            builder_.set_current_unwind_target({});
            cir::Fragment cleanup_destruction =
                dynamic_array_destroy_fragment(
                    leaf_pointer, leaf, remaining, {}, loc);
            cir::BlockId cleanup_exit = action;
            if (!cleanup_destruction.empty()) {
                builder_.branch(cleanup_destruction.entry, {}, loc);
                cleanup_exit = cleanup_destruction.exit;
                fragment.blocks.insert(fragment.blocks.end(),
                                       cleanup_destruction.blocks.begin(),
                                       cleanup_destruction.blocks.end());
            }
            builder_.switch_to_block(cleanup_exit);
            emit_deallocation_call(deallocation, raw_pointer, leaf, loc,
                                   total_size);
            emit_unwind_continue(cleanup_exit, exn, sel, outer_target, loc);
            builder_.set_current_unwind_target(saved_target);
            eh_pads_in_flight_.push_back(landing_pad);
            track_speculative_rollback([this]() {
                if (!eh_pads_in_flight_.empty()) {
                    eh_pads_in_flight_.pop_back();
                }
            });
            eh_code_targets_[pad.index] = action;
            track_speculative_rollback([this, index = pad.index]() {
                eh_code_targets_.erase(index);
            });
            builder_.set_current_unwind_target(pad);
            cir::Fragment destruction = dynamic_array_destroy_fragment(
                leaf_pointer, leaf, count, progress_place, loc);
            builder_.set_current_unwind_target(outer_target);
            builder_.switch_to_block(destroy_block);
            if (!destruction.empty()) {
                builder_.branch(destruction.entry, {}, loc);
                fragment.blocks.insert(fragment.blocks.end(),
                                       destruction.blocks.begin(),
                                       destruction.blocks.end());
                delete_exit = destruction.exit;
                builder_.switch_to_block(delete_exit);
            }
        }
        emit_deallocation_call(deallocation, raw_pointer, leaf, loc,
                               total_size);
        builder_.branch_from(delete_exit, continue_block, {}, loc);
        fragment.blocks.push_back(continue_block);
        fragment.exit = continue_block;
        builder_.switch_to_block(previous);
        fragment.falls_through = true;
        result.fragment = std::move(fragment);
        return result;
    }
    cir::InstId object_place = builder_.deref(value.value, loc);
    const cir::RecordMethodFact* destructor_fact =
        file_.method_fact(destructor);
    std::vector<cir::EntityId> vptr_path;
    bool virtual_d0 = !input.is_array && !input.force_global &&
        destructor_fact && destructor_fact->is_virtual &&
        destructor_fact->vtable_slot >= 0 &&
        vptr_field_path(pointee, &vptr_path);
    if (virtual_d0) {

            cir::TypeId usize = builder_.usize_type();
            cir::TypeId fn_pointer =
                builder_.pointer_type(file_.entity(destructor).type);
            cir::InstId vptr_place = object_place;
            for (cir::EntityId step : vptr_path) {
                vptr_place = builder_.field_addr(vptr_place, step,
                                                 file_.entity(step).type, loc);
            }
            cir::InstId vptr = builder_.lvalue_to_rvalue(vptr_place, loc);
            cir::InstId raw = builder_.cast(usize, vptr, "value", loc);

            int32_t deleting_slot = destructor_fact->vtable_slot + 1;
            int64_t slot_bytes =
                static_cast<int64_t>(file_.target_info().pointer_width / 8) *
                deleting_slot;
            cir::InstId slot_offset = builder_.integer_literal(
                slot_bytes, usize, std::to_string(slot_bytes), loc);
            cir::InstId slot_address =
                builder_.binary(cir::BinaryOpKind::Add, usize, raw, slot_offset, loc);
            cir::InstId slot_pointer = builder_.cast(
                builder_.pointer_type(fn_pointer), slot_address, "value", loc);
            cir::InstId slot_place = builder_.deref(slot_pointer, loc);
            cir::InstId target = builder_.lvalue_to_rvalue(slot_place, loc);
            builder_.call_indirect(target,
                                   file_.builtin_type(cir::BuiltinTypeKind::Void),
                                   {value.value},
                                   loc);
    } else if (deallocation.form.is_destroying) {
        emit_deallocation(value.value);
    } else {
        if (destructor.valid()) {
            cir::BlockId outer_target =
                file_.block(destroy_block).unwind_target;
            cir::BlockId pad =
                builder_.create_detached_block("delete.dtor.lpad");
            cir::BlockId action =
                builder_.create_detached_block("delete.dtor.act");
            builder_.set_block_unwind_target(pad, {});
            builder_.set_block_unwind_target(action, {});
            builder_.set_block_unwind_target(destroy_block, pad);
            builder_.switch_to_block(pad);
            cir::EhLandingPadPayload pad_payload;
            pad_payload.is_cleanup = true;
            cir::InstId landing_pad =
                builder_.eh_landing_pad(std::move(pad_payload), loc);
            cir::InstId selector = builder_.eh_selector(landing_pad, loc);
            builder_.branch(action, {landing_pad, selector}, loc);
            cir::InstId exn = builder_.add_block_parameter(
                action, void_pointer, "exn", loc);
            cir::InstId sel = builder_.add_block_parameter(
                action, builder_.int_type(), "sel", loc);
            builder_.switch_to_block(action);
            emit_deallocation(value.value);
            emit_unwind_continue(action, exn, sel, outer_target, loc);
            eh_pads_in_flight_.push_back(landing_pad);
            track_speculative_rollback([this]() {
                if (!eh_pads_in_flight_.empty()) {
                    eh_pads_in_flight_.pop_back();
                }
            });
            eh_code_targets_[pad.index] = action;
            track_speculative_rollback([this, index = pad.index]() {
                eh_code_targets_.erase(index);
            });
            fragment.blocks.push_back(pad);
            fragment.blocks.push_back(action);
            builder_.switch_to_block(destroy_block);
            emit_destroy(object_place,
                         structor_complete_variant(destructor), loc);
        }
        emit_deallocation(value.value);
    }
    builder_.branch_from(destroy_block, continue_block, {}, loc);
    fragment.blocks.push_back(destroy_block);
    fragment.blocks.push_back(continue_block);
    fragment.exit = continue_block;
    builder_.switch_to_block(previous);
    fragment.falls_through = true;
    result.fragment = std::move(fragment);
    return result;
}

bool Session::diagnose_constructor_delegation_cycle(
    cir::EntityId constructor,
    SrcLoc loc) {
    if (!constructor.valid() || !file_.valid(constructor)) {
        return false;
    }
    cir::EntityId owner = file_.entity(constructor).parent;
    const cir::RecordFacts* facts = file_.record_facts(owner);
    if (!facts) {
        return false;
    }

    std::vector<cir::EntityId> nodes;
    std::unordered_map<uint64_t, size_t> node_by_entity;
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (!method.entity.valid() || !file_.valid(method.entity) ||
            file_.entity(method.entity).kind != cir::EntityKind::Constructor) {
            continue;
        }
        node_by_entity.emplace(static_cast<uint64_t>(method.entity.index),
                               nodes.size());
        nodes.push_back(method.entity);
    }
    auto closing = node_by_entity.find(
        static_cast<uint64_t>(constructor.index));
    if (closing == node_by_entity.end()) {
        return false;
    }

    std::vector<std::optional<size_t>> edges(nodes.size());
    for (size_t i = 0; i < nodes.size(); ++i) {
        const cir::RecordMethodFact* method = file_.method_fact(nodes[i]);
        if (!method || !method->constructor_delegation ||
            !method->constructor_delegation->resolved()) {
            continue;
        }
        auto target = node_by_entity.find(static_cast<uint64_t>(
            method->constructor_delegation->target_constructor.index));
        if (target != node_by_entity.end()) {
            edges[i] = target->second;
        }
    }

    std::vector<int64_t> indexes(nodes.size(), -1);
    std::vector<int64_t> lowlinks(nodes.size(), -1);
    std::vector<size_t> stack;
    std::vector<bool> on_stack(nodes.size(), false);
    int64_t next_index = 0;
    bool closing_cycle = false;
    std::vector<size_t> closing_component;
    std::function<void(size_t)> visit = [&](size_t node) {
        indexes[node] = next_index;
        lowlinks[node] = next_index;
        ++next_index;
        stack.push_back(node);
        on_stack[node] = true;

        if (edges[node]) {
            size_t target = *edges[node];
            if (indexes[target] < 0) {
                visit(target);
                lowlinks[node] = std::min(lowlinks[node], lowlinks[target]);
            } else if (on_stack[target]) {
                lowlinks[node] = std::min(lowlinks[node], indexes[target]);
            }
        }
        if (lowlinks[node] != indexes[node]) {
            return;
        }

        std::vector<size_t> component;
        while (!stack.empty()) {
            size_t member = stack.back();
            stack.pop_back();
            on_stack[member] = false;
            component.push_back(member);
            if (member == node) {
                break;
            }
        }
        bool cyclic = component.size() > 1 ||
            (component.size() == 1 && edges[component.front()] &&
             *edges[component.front()] == component.front());
        if (cyclic &&
            std::find(component.begin(), component.end(), closing->second) !=
                component.end()) {
            closing_cycle = true;
            closing_component = std::move(component);
        }
    };
    for (size_t node = 0; node < nodes.size(); ++node) {
        if (indexes[node] < 0) {
            visit(node);
        }
    }
    if (!closing_cycle) {
        return false;
    }

    report_error("constructor delegates to itself, directly or through other "
                 "constructors",
                 loc);
    std::sort(closing_component.begin(), closing_component.end());
    for (size_t member : closing_component) {
        const cir::RecordMethodFact* method = file_.method_fact(nodes[member]);
        if (!method || !method->constructor_delegation) {
            continue;
        }
        SrcLoc edge_loc = method->constructor_delegation->initializer_loc;
        if (edge_loc.isInvalid() || edge_loc.offset == loc.offset) {
            continue;
        }
        report_note("delegation edge in the cycle is here", edge_loc);
    }
    return true;
}

StmtResult Session::collect_constructor_initializers(
    std::vector<MemberInitializerInput> initializers,
    SrcLoc loc) {
    StmtResult result;
    result.falls_through = true;
    auto discard_initializer_boundaries = [&]() {
        for (const MemberInitializerInput& initializer : initializers) {
            discard_lifetime_boundary(initializer.boundary);
        }
    };
    if (!current_member_record_.valid()) {
        discard_initializer_boundaries();
        return result;
    }
    const cir::RecordFacts* facts = file_.record_facts(current_member_record_);
    if (!facts) {
        discard_initializer_boundaries();
        return result;
    }
    RecordLifecyclePlan lifecycle = record_lifecycle_plan(
        *facts, RecordLifecycleOperation::DefaultConstruct);
    bool diagnose_omitted_required_members = true;
    if (current_function_.valid() && file_.valid(current_function_)) {
        cir::EntityId function_entity = file_.function(current_function_).entity;
        const cir::RecordMethodFact* current_method =
            file_.method_fact(function_entity);
        if (current_method && current_method->is_defaulted) {
            diagnose_omitted_required_members = false;
        }
    }
    if (diagnose_omitted_required_members) {
        for (const cir::RecordFieldFact& field : facts->fields) {
            if (facts->is_abstract && field.is_virtual_base_storage) {
                continue;
            }

            if (field.is_anonymous_union_object) {
                continue;
            }
            SrcLoc invocation_loc =
                field.entity.valid() && file_.valid(field.entity)
                    ? file_.entity(field.entity).loc
                    : loc;
            if (!validate_potentially_invoked_destructor(field.type.type,
                                                         invocation_loc)) {
                result.has_error = true;
            }
        }
    }

    if (lang_opts_.is_cxx_mode() && !initializers.empty() &&
        current_this_place_.valid()) {
        cir::TypeId own_type =
            file_.resolved_type(file_.entity(current_member_record_).type);
        auto names_own_class = [&](const MemberInitializerInput& initializer) {
            if (initializer.base_type.valid()) {
                return file_.resolved_type(initializer.base_type) == own_type;
            }
            const cir::Entity& record = file_.entity(current_member_record_);
            return record.name.valid() &&
                   file_.name(record.name) == initializer.name;
        };
        size_t delegating_index = initializers.size();
        for (size_t i = 0; i < initializers.size(); ++i) {
            if (names_own_class(initializers[i])) {
                delegating_index = i;
                break;
            }
        }
        if (delegating_index < initializers.size()) {
            SrcLoc use_loc = initializers[delegating_index].loc.isInvalid()
                ? loc
                : initializers[delegating_index].loc;
            if (initializers.size() > 1) {
                report_error("a delegating constructor must be the only "
                             "member initializer",
                             use_loc);
                result.has_error = true;
                discard_initializer_boundaries();
                return result;
            }
            MemberInitializerInput initializer =
                std::move(initializers.front());
            cir::EntityId self_entity =
                current_function_.valid() && file_.valid(current_function_)
                    ? file_.function(current_function_).entity
                    : cir::EntityId{};
            auto publish_delegation = [&](cir::ConstructorDelegationState state,
                                          cir::EntityId target) {
                if (!self_entity.valid()) {
                    return;
                }
                cir::RecordMethodFact* self_fact =
                    file_.method_fact_mut(self_entity);
                if (!self_fact) {
                    return;
                }
                cir::ConstructorDelegationFact delegation;
                delegation.state = state;
                delegation.initialization_kind = initializer.braced
                    ? cir::ConstructorDelegationInitializationKind::Braced
                    : cir::ConstructorDelegationInitializationKind::Parenthesized;
                delegation.target_constructor = target;
                delegation.initializer_loc = use_loc;
                self_fact->constructor_delegation = std::move(delegation);
            };
            bool dependent_arguments = std::any_of(
                initializer.arguments.begin(), initializer.arguments.end(),
                [&](const ExprResult& argument) {
                    return expr_is_dependent(argument) ||
                        expr_is_value_dependent(argument);
                });
            if (in_template_definition() && dependent_arguments) {
                publish_delegation(
                    cir::ConstructorDelegationState::Dependent, {});
                result.requires_token_replay = true;

                discard_initializer_boundaries();
                return result;
            }
            bool ambiguous = false;
            cir::EntityId target = select_constructor(
                own_type, initializer.arguments, &ambiguous, use_loc);
            if (!target.valid()) {
                const cir::RecordFacts* own_facts =
                    file_.record_facts(current_member_record_);
                bool dependent_constructor_set = false;
                if (in_template_definition() && own_facts) {
                    dependent_constructor_set = std::any_of(
                        own_facts->methods.begin(),
                        own_facts->methods.end(),
                        [&](const cir::RecordMethodFact& method) {
                            return method.entity.valid() &&
                                file_.entity(method.entity).kind ==
                                    cir::EntityKind::Constructor &&
                                (type_contains_type_param_except_record(
                                     method.type.type,
                                     current_member_record_) ||
                                 method.explicit_specifier ==
                                     cir::ExplicitSpecifierKind::Dependent ||
                                 method.constraint_satisfaction ==
                                     cir::ConstraintSatisfactionKind::Dependent);
                        });
                }
                if (in_template_definition() && own_facts &&
                    (dependent_constructor_set ||
                     !own_facts->dependent_bases.empty() ||
                     own_facts->definition_data
                         .has_inherited_constructor)) {

                    publish_delegation(
                        cir::ConstructorDelegationState::Dependent, {});
                    result.requires_token_replay = true;
                    discard_initializer_boundaries();
                    return result;
                }
                report_error(
                    std::string(ambiguous
                                    ? "delegation to a constructor of '"
                                    : "no matching constructor to delegate "
                                      "to for '") +
                        file_.format_type(own_type) +
                        (ambiguous ? "' is ambiguous" : "'"),
                    use_loc);
                result.has_error = true;
                discard_initializer_boundaries();
                return result;
            }
            publish_delegation(cir::ConstructorDelegationState::Resolved,
                               target);
            if (self_entity.valid()) {
                if (diagnose_constructor_delegation_cycle(self_entity,
                                                          use_loc)) {
                    result.has_error = true;
                    discard_initializer_boundaries();
                    return result;
                }
            }
            bool uses_default_arguments = false;
            if (in_template_definition()) {
                const cir::RecordMethodFact* target_fact =
                    file_.method_fact(target);
                const auto* target_type =
                    target_fact
                        ? std::get_if<cir::FunctionTypePayload>(
                              &file_.type_payload(file_.resolved_type(
                                  target_fact->type.type)))
                        : nullptr;
                size_t provided_arguments = initializer.arguments.size();
                if (provided_arguments == 1 &&
                    initializer.arguments.front().category ==
                        ValueCategory::InitList &&
                    initializer.arguments.front().init_list &&
                    !constructor_initializer_list_element_type(target)
                         .has_value()) {
                    provided_arguments =
                        initializer.arguments.front()
                            .init_list->elements.size();
                }
                if (target_type) {
                    for (size_t parameter = provided_arguments;
                         parameter < target_type->parameters.size();
                         ++parameter) {
                        uses_default_arguments =
                            uses_default_arguments ||
                            callable_default_argument(target, parameter);
                    }
                }
            }
            if (uses_default_arguments) {

                result.requires_token_replay = true;
                discard_initializer_boundaries();
                return result;
            }
            ConstructorCallMaterialization materialized =
                materialize_selected_constructor_call(
                    target, std::move(initializer.arguments), use_loc);
            result.has_error = result.has_error || materialized.has_error;
            result.fragment = chain(std::move(result.fragment),
                                    std::move(materialized.argument_fragment),
                                    use_loc);
            if (materialized.has_error) {
                discard_lifetime_boundary(initializer.boundary);
                return result;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("ctor.delegate");
            cir::InstId this_value =
                builder_.lvalue_to_rvalue(current_this_place_, use_loc);
            if (current_structor_flag_.valid()) {

                cir::EntityId impl = structor_impl_entity(target);
                std::vector<cir::InstId> call_arguments;
                call_arguments.reserve(materialized.argument_values.size() +
                                       3);
                call_arguments.push_back(this_value);
                call_arguments.insert(call_arguments.end(),
                                      materialized.argument_values.begin(),
                                      materialized.argument_values.end());
                call_arguments.push_back(current_structor_flag_);
                cir::TypeId vtt_type = builder_.pointer_type(
                    builder_.pointer_type(
                        file_.builtin_type(cir::BuiltinTypeKind::Void)));
                cir::InstId vtt_value;
                if (current_structor_vtt_place_.valid()) {
                    vtt_value = builder_.lvalue_to_rvalue(
                        current_structor_vtt_place_, use_loc);
                } else {
                    cir::InstId null_raw = builder_.integer_literal(
                        0, builder_.usize_type(), "0", use_loc);
                    vtt_value =
                        builder_.cast(vtt_type, null_raw, "value", use_loc);
                }
                call_arguments.push_back(vtt_value);
                emit_structor_call(
                    impl, file_.builtin_type(cir::BuiltinTypeKind::Void),
                    call_arguments, use_loc);
            } else {
                cir::InstId object = builder_.deref(this_value, use_loc);
                emit_construct_in_place(object,
                                        structor_complete_variant(target),
                                        materialized.argument_values, use_loc);
            }
            result.fragment = chain(std::move(result.fragment),
                                    finish_fragment_block(block, previous),
                                    use_loc);
            result.fragment = chain(
                std::move(result.fragment),
                finish_lifetime_boundary(initializer.boundary, use_loc),
                use_loc);

            cir::EntityId own_destructor = record_destructor(own_type);
            if (own_destructor.valid() &&
                builder_.current_function().valid()) {
                cir::BlockId saved_target = builder_.current_unwind_target();
                builder_.set_current_unwind_target({});
                cir::BlockId pad = builder_.create_block("ctor.delegate.lpad");
                cir::BlockId action =
                    builder_.create_block("ctor.delegate.act");
                cir::BlockId pad_previous = builder_.current_block();
                builder_.switch_to_block(pad);
                cir::EhLandingPadPayload pad_payload;
                pad_payload.is_cleanup = true;
                cir::InstId landing_pad =
                    builder_.eh_landing_pad(std::move(pad_payload), use_loc);
                cir::InstId selector =
                    builder_.eh_selector(landing_pad, use_loc);
                builder_.branch(action, {landing_pad, selector}, use_loc);
                cir::TypeId void_ptr =
                    builder_.pointer_type(builder_.void_type());
                cir::InstId exn_param = builder_.add_block_parameter(
                    action, void_ptr, "exn", use_loc);
                cir::InstId sel_param = builder_.add_block_parameter(
                    action, builder_.int_type(), "sel", use_loc);
                builder_.switch_to_block(action);
                cir::InstId action_this = builder_.lvalue_to_rvalue(
                    rematerialize_entity_place(current_this_place_, use_loc),
                    use_loc);
                if (current_structor_flag_.valid()) {

                    cir::EntityId destructor_impl =
                        structor_impl_entity(own_destructor);
                    std::vector<cir::InstId> destroy_arguments;
                    destroy_arguments.push_back(action_this);
                    destroy_arguments.push_back(current_structor_flag_);
                    if (current_structor_vtt_place_.valid()) {
                        destroy_arguments.push_back(builder_.lvalue_to_rvalue(
                            current_structor_vtt_place_, use_loc));
                    } else {
                        cir::TypeId vtt_type = builder_.pointer_type(
                            builder_.pointer_type(file_.builtin_type(
                                cir::BuiltinTypeKind::Void)));
                        cir::InstId null_raw = builder_.integer_literal(
                            0, builder_.usize_type(), "0", use_loc);
                        destroy_arguments.push_back(builder_.cast(
                            vtt_type, null_raw, "value", use_loc));
                    }
                    emit_structor_call(
                        destructor_impl,
                        file_.builtin_type(cir::BuiltinTypeKind::Void),
                        destroy_arguments, use_loc);
                } else {
                    emit_destroy(builder_.deref(action_this, use_loc),
                                 structor_complete_variant(own_destructor),
                                 use_loc);
                }
                emit_unwind_continue(action, exn_param, sel_param,
                                     saved_target, use_loc);
                builder_.switch_to_block(pad_previous);
                eh_pads_in_flight_.push_back(landing_pad);
                track_speculative_rollback([this]() {
                    if (!eh_pads_in_flight_.empty()) {
                        eh_pads_in_flight_.pop_back();
                    }
                });
                eh_code_targets_[pad.index] = action;
                track_speculative_rollback([this, pad_index = pad.index]() {
                    eh_code_targets_.erase(pad_index);
                });
                builder_.set_current_unwind_target(pad);
            }
            return result;
        }
    }

    std::vector<bool> consumed(initializers.size(), false);
    std::vector<cir::EntityId> initializer_targets(initializers.size());
    std::vector<std::optional<uint32_t>> initializer_dependent_bases(
        initializers.size());
    std::vector<bool> initializer_deferred_base_resolution(
        initializers.size(), false);
    std::vector<std::vector<cir::EntityId>> initializer_object_paths(
        initializers.size());
    for (size_t i = 0; i < initializers.size(); ++i) {
        const MemberInitializerInput& initializer = initializers[i];

        for (const cir::RecordFieldFact& field : facts->fields) {
            if (!field.is_base_subobject && field.name.valid() &&
                file_.name(field.name) == initializer.name) {
                initializer_targets[i] = field.entity;
                initializer_object_paths[i].push_back(field.entity);
                break;
            }
        }
        if (initializer_targets[i].valid()) {
            continue;
        }

        for (const cir::VariantMemberFact& variant : facts->variant_members) {
            if (!variant.member.valid() || !file_.valid(variant.member) ||
                !file_.entity(variant.member).name.valid() ||
                file_.name(file_.entity(variant.member).name) !=
                    initializer.name ||
                variant.path.size() < 2) {
                continue;
            }
            initializer_targets[i] = variant.member;
            initializer_object_paths[i] = variant.path;
            break;
        }
        if (initializer_targets[i].valid()) {
            continue;
        }

        FieldPathLookupResult promoted = lookup_field_path(
            file_.entity(current_member_record_).type,
            initializer.name);
        if (promoted.ambiguous) {
            report_error("member initializer for '" + initializer.name +
                             "' is ambiguous",
                         initializer.loc);
            result.has_error = true;
            consumed[i] = true;
            discard_lifetime_boundary(initializers[i].boundary);
            continue;
        }
        if (promoted.found && promoted.entities.size() > 1) {
            initializer_targets[i] = promoted.entities.back();
            initializer_object_paths[i] =
                std::move(promoted.entities);
            continue;
        }

        std::vector<cir::EntityId> matching_bases;
        cir::TypeId requested_base =
            file_.resolved_type(initializer.base_type);
        for (const cir::RecordFieldFact& field : facts->fields) {
            if (!field.is_base_subobject) {
                continue;
            }
            bool matches = requested_base.valid() &&
                file_.resolved_type(field.type.type) == requested_base;
            if (!matches && !initializer.base_type.valid()) {
                cir::EntityId base = file_.record_entity(field.type.type);
                matches = base.valid() && file_.entity(base).name.valid() &&
                    file_.name(file_.entity(base).name) == initializer.name;
            }
            if (matches) {
                matching_bases.push_back(field.entity);
            }
        }
        if (matching_bases.size() == 1) {
            initializer_targets[i] = matching_bases.front();
        } else if (matching_bases.size() > 1) {
            report_error("base initializer for '" + initializer.name +
                             "' is ambiguous",
                         initializer.loc);
            result.has_error = true;
            consumed[i] = true;
            discard_lifetime_boundary(initializers[i].boundary);
            continue;
        }
        if (!initializer_targets[i].valid() && requested_base.valid()) {
            std::vector<uint32_t> matching_dependent_bases;
            for (const cir::RecordDependentBaseFact& base :
                 facts->dependent_bases) {
                if (file_.resolved_type(base.type.type) == requested_base) {
                    matching_dependent_bases.push_back(
                        base.declaration_index);
                }
            }
            if (matching_dependent_bases.size() == 1) {
                initializer_dependent_bases[i] =
                    matching_dependent_bases.front();
            } else if (matching_dependent_bases.size() > 1) {
                report_error("base initializer for '" + initializer.name +
                                 "' is ambiguous",
                             initializer.loc);
                result.has_error = true;
                consumed[i] = true;
                discard_lifetime_boundary(initializers[i].boundary);
            } else if (is_dependent_type(requested_base)) {

                initializer_deferred_base_resolution[i] = true;
            }
        }
    }

    std::unordered_map<uint32_t, size_t> first_initializer_for_target;
    std::unordered_map<uint32_t, size_t>
        first_initializer_for_dependent_base;
    cir::EntityId first_union_variant;
    for (size_t i = 0; i < initializer_targets.size(); ++i) {
        cir::EntityId target = initializer_targets[i];
        if (consumed[i]) {
            continue;
        }
        if (!target.valid()) {
            if (initializer_dependent_bases[i].has_value()) {
                auto [first, inserted] =
                    first_initializer_for_dependent_base.emplace(
                        *initializer_dependent_bases[i], i);
                if (!inserted) {
                    report_error("base or member '" + initializers[i].name +
                                     "' is initialized more than once",
                                 initializers[i].loc);
                    result.has_error = true;
                    consumed[i] = true;
                    discard_lifetime_boundary(initializers[i].boundary);
                }
            }
            continue;
        }
        auto [first, inserted] = first_initializer_for_target.emplace(
            static_cast<uint32_t>(target.index), i);
        if (!inserted) {
            report_error("base or member '" + initializers[i].name +
                             "' is initialized more than once",
                         initializers[i].loc);
            result.has_error = true;
            consumed[i] = true;
            discard_lifetime_boundary(initializers[i].boundary);
            continue;
        }
        if (facts->kind == cir::RecordKind::Union &&
            !file_.entity(target).name.valid()) {
            continue;
        }
        if (facts->kind == cir::RecordKind::Union &&
            !first_union_variant.valid()) {
            first_union_variant = target;
        } else if (facts->kind == cir::RecordKind::Union &&
                   target != first_union_variant) {
            report_error("more than one union member is explicitly initialized",
                         initializers[i].loc);
            result.has_error = true;
            consumed[i] = true;
            discard_lifetime_boundary(initializers[i].boundary);
        }
    }

    auto initializer_for_field = [&](const cir::RecordFieldFact& field) -> int {
        for (size_t i = 0; i < initializers.size(); ++i) {
            bool direct = initializer_targets[i] == field.entity;
            bool promoted = is_anonymous_record_member(file_, field) &&
                !initializer_object_paths[i].empty() &&
                initializer_object_paths[i].front() == field.entity;
            if (!consumed[i] && (direct || promoted)) {
                consumed[i] = true;
                return static_cast<int>(i);
            }
        }
        return -1;
    };

    auto member_place = [&](const cir::RecordFieldFact& field,
                            SrcLoc use_loc,
                            const std::vector<cir::EntityId>* object_path = nullptr)
        -> std::pair<cir::InstId, cir::Fragment> {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("ctor.subobject");
        cir::InstId this_value = builder_.lvalue_to_rvalue(current_this_place_, use_loc);
        cir::InstId object_place = builder_.deref(this_value, use_loc);
        cir::InstId place = object_place;
        if (object_path && !object_path->empty()) {
            place = emit_subobject_path(place, *object_path, use_loc);
        } else {
            place = builder_.field_addr(object_place, field.entity,
                                        field.type.type, use_loc);
        }
        return {place, finish_fragment_block(block, previous)};
    };

    auto install_subobject_rollback =
        [&](const cir::RecordFieldFact& field, SrcLoc use_loc,
            const std::vector<cir::EntityId>* object_path = nullptr) {
        RecordLifecycleStep step;
        step.field = field;
        step.array_shape = class_array_shape(field.type.type);
        step.complete_object_only = field.is_virtual_base_storage;
        std::function<cir::InstId(SrcLoc)> rematerialize =
            [this, field_entity = field.entity,
             field_type = field.type.type,
             path = object_path ? *object_path
                                : std::vector<cir::EntityId>{}](SrcLoc action_loc) {
                cir::InstId this_place = rematerialize_entity_place(
                    current_this_place_, action_loc);
                cir::InstId this_value = builder_.lvalue_to_rvalue(
                    this_place, action_loc);
                cir::InstId place = builder_.deref(this_value, action_loc);
                if (!path.empty()) {
                    return emit_subobject_path(place, path, action_loc);
                }
                return builder_.field_addr(place, field_entity,
                                           field_type, action_loc);
            };
        this->install_subobject_rollback(step, use_loc, rematerialize);
    };

    auto construct_subobject_body = [&](const cir::RecordFieldFact& field,
                                        std::vector<ExprResult> arguments,
                                        SrcLoc use_loc,
                                        bool braced,
                                        const std::vector<cir::EntityId>* object_path,
                                        bool explicitly_initialized) {
        cir::TypeId subobject_type = file_.resolved_type(field.type.type);
        bool dependent_arguments = std::any_of(
            arguments.begin(), arguments.end(),
            [&](const ExprResult& argument) {
                return expr_is_dependent(argument) ||
                    expr_is_value_dependent(argument);
            });
        if (in_template_definition() &&
            (is_dependent_type(field.type.type) || dependent_arguments)) {

            for (const ExprResult& argument : arguments) {
                result.has_error = result.has_error || argument.has_error;
            }
            result.requires_token_replay = true;
            return;
        }
        if (file_.valid(subobject_type) &&
            file_.type(subobject_type).kind == cir::TypeKind::Array &&
            braced && arguments.size() == 1 &&
            arguments.front().init_list) {
            auto [place, place_fragment] =
                member_place(field, use_loc, object_path);
            std::function<cir::InstId(SrcLoc)> remat =
                [this, field_entity = field.entity,
                 field_type = field.type.type,
                 path = object_path ? *object_path
                                    : std::vector<cir::EntityId>{}](SrcLoc l) {
                    cir::InstId this_place =
                        rematerialize_entity_place(current_this_place_, l);
                    cir::InstId this_ptr =
                        builder_.lvalue_to_rvalue(this_place, l);
                    cir::InstId place = builder_.deref(this_ptr, l);
                    return path.empty()
                        ? builder_.field_addr(place, field_entity,
                                              field_type, l)
                        : emit_subobject_path(place, path, l);
                };
            result.fragment = chain(std::move(result.fragment),
                                    std::move(place_fragment), use_loc);
            result.fragment = chain(
                std::move(result.fragment),
                emit_initializer_for_place(place, field.type.type,
                                           std::move(arguments.front()),
                                           use_loc, UseContext::Init,
                                           &remat),
                use_loc);
            return;
        }
        if (braced && arguments.size() == 1 &&
            arguments.front().init_list &&
            initializer_list_element_type(subobject_type).has_value()) {
            report_error(
                "initializer_list backing array cannot bind to a member in "
                "a constructor initializer because its lifetime ends when "
                "the constructor exits",
                use_loc);
            result.has_error = true;
        }

        if (cir::TypeId member_array_leaf =
                array_class_element_leaf(subobject_type);
            member_array_leaf.valid()) {
            if (!arguments.empty()) {
                report_error(
                    "initializing a class-array member from a braced element "
                    "list is not supported yet",
                    use_loc);
                result.has_error = true;
                return;
            }
            bool needs_elements = record_requires_default_constructor_selection(
                member_array_leaf);
            if (!needs_elements && !braced) {
                return;
            }
            auto [place, place_fragment] =
                member_place(field, use_loc, object_path);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(place_fragment), use_loc);
            if (braced) {
                result.fragment = chain(std::move(result.fragment),
                                        emit_zero_initializer(
                                            place, field.type.type, use_loc),
                                        use_loc);
            }
            if (needs_elements) {
                std::function<cir::InstId(SrcLoc)> remat =
                    [this, field_entity = field.entity,
                     field_type = field.type.type,
                     path = object_path ? *object_path
                                        : std::vector<cir::EntityId>{}](SrcLoc l) {
                        cir::InstId this_place =
                            rematerialize_entity_place(current_this_place_, l);
                        cir::InstId this_ptr =
                            builder_.lvalue_to_rvalue(this_place, l);
                        cir::InstId place = builder_.deref(this_ptr, l);
                        return path.empty()
                            ? builder_.field_addr(place, field_entity,
                                                  field_type, l)
                            : emit_subobject_path(place, path, l);
                    };
                bool construct_error = false;
                ClassArrayShape shape = class_array_shape(subobject_type);
                result.fragment = chain(
                    std::move(result.fragment),
                    array_construct_loop_fragment(place, subobject_type, 0,
                                                  shape.total_leaf_count,
                                                  use_loc, &construct_error,
                                                  &remat),
                    use_loc);
                result.has_error = result.has_error || construct_error;
            }
            return;
        }
        bool needs_ctor = record_needs_construction(subobject_type) ||
            (arguments.empty() &&
             record_requires_default_constructor_selection(subobject_type));

        if (!needs_ctor && arguments.empty() &&
            (braced || explicitly_initialized) &&
            !is_reference_type(field.type.type)) {
            if (field.subobject_size ==
                cir::SubobjectSizeKind::Zero) {

                return;
            }
            auto [place, place_fragment] =
                member_place(field, use_loc, object_path);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(place_fragment), use_loc);
            result.fragment = chain(std::move(result.fragment),
                                    emit_zero_initializer(place,
                                                          field.type.type,
                                                          use_loc),
                                    use_loc);
            return;
        }
        if (!needs_ctor && arguments.empty()) {
            return;
        }
        auto [place, place_fragment] =
            member_place(field, use_loc, object_path);
        bool initializes_from_same_type_prvalue =
            explicitly_initialized && !braced &&
            !field.is_base_subobject && !field.is_no_unique_address &&
            arguments.size() == 1 &&
            arguments.front().category == ValueCategory::PrValue &&
            arguments.front().type.valid() &&
            file_.resolved_type(arguments.front().type) == subobject_type;
        if (initializes_from_same_type_prvalue) {

            result.has_error =
                result.has_error || arguments.front().has_error;
            result.fragment = chain(std::move(result.fragment),
                                    std::move(place_fragment), use_loc);
            result.fragment = chain(
                std::move(result.fragment),
                emit_initializer_for_place(
                    place, field.type.type, std::move(arguments.front()),
                    use_loc, UseContext::DirectInit),
                use_loc);
            return;
        }
        if (lang_opts_.is_cxx20_or_later() &&
            explicitly_initialized && !braced && !arguments.empty() &&
            file_.valid(subobject_type) &&
            file_.type(subobject_type).kind == cir::TypeKind::Record &&
            is_aggregate_type(subobject_type)) {

            bool ambiguous = false;
            cir::EntityId constructor =
                select_constructor(subobject_type, arguments, &ambiguous,
                                   use_loc);
            if (!constructor.valid() && !ambiguous) {
                std::vector<InitElementInput> elements;
                elements.reserve(arguments.size());
                for (ExprResult& argument : arguments) {
                    InitElementInput element;
                    element.value = std::move(argument);
                    element.loc = use_loc;
                    elements.push_back(std::move(element));
                }
                ExprResult initializer = collect_init_list_expr(
                    std::move(elements), use_loc,
                    InitListSyntax::Parenthesized);
                std::function<cir::InstId(SrcLoc)> remat =
                    [this, field_entity = field.entity,
                     field_type = field.type.type,
                     path = object_path ? *object_path
                                        : std::vector<cir::EntityId>{}](
                        SrcLoc loc) {
                        cir::InstId this_place =
                            rematerialize_entity_place(current_this_place_,
                                                       loc);
                        cir::InstId this_ptr =
                            builder_.lvalue_to_rvalue(this_place, loc);
                        cir::InstId member = builder_.deref(this_ptr, loc);
                        return path.empty()
                            ? builder_.field_addr(member, field_entity,
                                                  field_type, loc)
                            : emit_subobject_path(member, path, loc);
                    };
                result.fragment = chain(std::move(result.fragment),
                                        std::move(place_fragment), use_loc);
                result.fragment = chain(
                    std::move(result.fragment),
                    emit_initializer_for_place(
                        place, field.type.type, std::move(initializer),
                        use_loc, UseContext::Init, &remat),
                    use_loc);
                return;
            }
        }
        if (needs_ctor) {
            bool ambiguous = false;
            cir::EntityId constructor =
                select_constructor(subobject_type, arguments, &ambiguous,
                                   use_loc);
            bool can_trivial_copy = !constructor.valid() && !ambiguous &&
                arguments.size() == 1 &&
                types_compatible(
                    cir::TypeRef{file_.resolved_type(arguments.front().type),
                                 cir::QualNone, cir::MemorySpace::Default},
                    cir::TypeRef{subobject_type, cir::QualNone,
                                 cir::MemorySpace::Default});
            if (can_trivial_copy) {

                needs_ctor = false;
            }
            if (!needs_ctor) {
                ExprResult converted = convert_to(std::move(arguments.front()),
                                                  field.type.type,
                                                  UseContext::Init,
                                                  use_loc);
                result.has_error = result.has_error || converted.has_error;
                result.fragment = chain(std::move(result.fragment),
                                        std::move(place_fragment), use_loc);
                result.fragment = chain(std::move(result.fragment),
                                        std::move(converted.fragment), use_loc);

                if (converted.value.valid() &&
                    !expr_is_dependent(converted) &&
                    field.subobject_size !=
                        cir::SubobjectSizeKind::Zero) {
                    cir::BlockId copy_previous = builder_.current_block();
                    cir::BlockId copy_block =
                        begin_fragment_block("ctor.subobject.copy");
                    builder_.store(place, converted.value, use_loc);
                    cir::Fragment copy_fragment =
                        finish_fragment_block(copy_block, copy_previous);
                    result.fragment = chain(std::move(result.fragment),
                                            std::move(copy_fragment), use_loc);
                }
                return;
            }
            if (!constructor.valid()) {
                report_error(std::string(ambiguous
                                             ? "ambiguous constructor for base or member '"
                                             : "no matching constructor for base or member '") +
                                 file_.format_type(field.type.type) + "'",
                             use_loc);
                result.has_error = true;
                return;
            }

            if (field.is_base_subobject) {
                const cir::RecordMethodFact* selected_fact =
                    file_.method_fact(constructor);
                const cir::RecordFacts* selected_owner =
                    selected_fact
                    ? file_.record_facts(file_.entity(constructor).parent)
                    : nullptr;
                bool omitted_virtual_origin = false;
                if (selected_fact && selected_fact->inherited_constructor &&
                    selected_owner) {
                    for (const cir::InheritedConstructorRouteFact& route :
                         selected_fact->inherited_constructor->routes) {
                        if (route.origin_subobject <
                                selected_owner->virtual_subobjects.size() &&
                            selected_owner->virtual_subobjects[
                                route.origin_subobject]
                                .is_virtual) {
                            omitted_virtual_origin = true;
                            break;
                        }
                    }
                }
                if (omitted_virtual_origin) {
                    const cir::RecordMethodFact* default_constructor =
                        canonical_special_member(
                            file_, subobject_type,
                            cir::SpecialMemberKind::DefaultConstructor);
                    if (default_constructor &&
                        default_constructor->entity.valid() &&
                        !default_constructor->is_deleted) {
                        constructor = default_constructor->entity;
                        arguments.clear();
                    }
                }
            }
            ConstructorCallMaterialization materialized =
                materialize_selected_constructor_call(constructor,
                                                      std::move(arguments),
                                                      use_loc);
            result.has_error = result.has_error || materialized.has_error;
            result.fragment = chain(std::move(result.fragment),
                                    std::move(place_fragment), use_loc);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(materialized.argument_fragment),
                                    use_loc);
            if (materialized.has_error) {
                return;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("ctor.subobject.construct");
            cir::EntityId ctor_variant = field.is_base_subobject
                ? structor_base_variant(constructor)
                : structor_complete_variant(constructor);

            if (field.is_base_subobject &&
                current_structor_vtt_place_.valid()) {
                const cir::RecordFacts* subobject_facts =
                    file_.record_facts_for_type(subobject_type);
                if (subobject_facts &&
                    !subobject_facts->virtual_bases.empty()) {
                    const cir::RecordFacts* own_facts =
                        file_.record_facts(current_member_record_);
                    cir::EntityId subobject_record =
                        file_.record_entity(subobject_type);
                    size_t slice_index = 0;
                    bool slice_found = false;
                    if (own_facts) {
                        VttInfo info = compute_vtt_info(*own_facts);
                        const auto& slices = field.is_virtual_base_storage
                            ? info.vbase_slices
                            : info.base_slices;
                        for (const VttInfo::Slice& slice : slices) {
                            if (slice.record_entity == subobject_record) {
                                slice_index = slice.start;
                                slice_found = true;
                                break;
                            }
                        }
                    }
                    if (slice_found) {
                        materialized.argument_values.insert(
                            materialized.argument_values.begin(),
                            vtt_slice_value(slice_index, use_loc));
                    }
                }
            }
            emit_construct_in_place(place, ctor_variant,
                                    materialized.argument_values,
                                    use_loc);
            cir::Fragment construct_fragment = finish_fragment_block(block, previous);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(construct_fragment), use_loc);
            return;
        }

        if (arguments.size() != 1) {
            report_error("member initializer expects one value", use_loc);
            result.has_error = true;
            return;
        }

        if (braced && !arguments.front().init_list &&
            !is_reference_type(field.type.type) &&
            diagnose_braced_narrowing(field.type.type, arguments.front(),
                                      use_loc)) {
            result.has_error = true;
        }
        ExprResult converted = convert_to(std::move(arguments.front()),
                                          field.type.type,
                                          UseContext::Init,
                                          use_loc);
        if (is_reference_type(field.type.type) &&
            converted.reference_binds_to_temporary) {
            report_error("temporary expression cannot bind to reference member '" +
                             std::string(file_.name(field.name)) + "'",
                         use_loc);
            converted.has_error = true;
        }
        result.has_error = result.has_error || converted.has_error;
        result.fragment = chain(std::move(result.fragment),
                                std::move(place_fragment), use_loc);
        result.fragment = chain(std::move(result.fragment),
                                std::move(converted.fragment), use_loc);
        if (converted.value.valid() &&
            !expr_is_dependent(converted) &&
            field.subobject_size != cir::SubobjectSizeKind::Zero) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("ctor.subobject.store");
            builder_.store(place, converted.value, use_loc);
            cir::Fragment store_fragment = finish_fragment_block(block, previous);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(store_fragment), use_loc);
        }
    };
    auto construct_subobject = [&](const cir::RecordFieldFact& field,
                                   std::vector<ExprResult> arguments,
                                   SrcLoc use_loc,
                                   bool braced = false,
                                   LifetimeBoundary boundary = {},
                                   const std::vector<cir::EntityId>* object_path = nullptr,
                                   bool explicitly_initialized = false) {
        size_t blocks_before = result.fragment.blocks.size();
        construct_subobject_body(field, std::move(arguments), use_loc,
                                 braced, object_path,
                                 explicitly_initialized);
        if (result.fragment.blocks.size() != blocks_before) {
            install_subobject_rollback(field, use_loc, object_path);
        }
        result.fragment = chain(
            std::move(result.fragment),
            finish_lifetime_boundary(boundary, use_loc), use_loc);
    };

    if (current_structor_flag_.valid() && !facts->is_abstract) {
        cir::Fragment saved = std::move(result.fragment);
        result.fragment = {};
        for (const RecordLifecycleStep& step : lifecycle.steps) {
            const cir::RecordFieldFact& field = step.field;
            if (!field.is_virtual_base_storage) {
                continue;
            }
            int found = initializer_for_field(field);
            construct_subobject(field,
                                found >= 0
                                    ? std::move(initializers[found].arguments)
                                    : std::vector<ExprResult>{},
                                found >= 0 ? initializers[found].loc : loc,
                                found >= 0 && initializers[found].braced,
                                found >= 0
                                    ? initializers[found].boundary
                                    : LifetimeBoundary{},
                                nullptr,
                                found >= 0);
        }
        cir::Fragment vbase_fragment = std::move(result.fragment);
        result.fragment = std::move(saved);
        result.fragment =
            chain(std::move(result.fragment),
                  guard_on_structor_flag(std::move(vbase_fragment), loc), loc);
    }
    {

        for (const RecordLifecycleStep& step : lifecycle.steps) {
            const cir::RecordFieldFact& field = step.field;
            if (!field.is_base_subobject ||
                field.is_virtual_base_storage) {
                continue;
            }
            int found = initializer_for_field(field);
            construct_subobject(field,
                                found >= 0
                                    ? std::move(initializers[found].arguments)
                                    : std::vector<ExprResult>{},
                                found >= 0 ? initializers[found].loc : loc,
                                found >= 0 && initializers[found].braced,
                                found >= 0
                                    ? initializers[found].boundary
                                    : LifetimeBoundary{},
                                nullptr,
                                found >= 0);
        }
    }
    {
        StmtResult vptr_store = store_vptr_fragment(loc);
        if (current_structor_flag_.valid()) {
            vptr_store.fragment = branch_on_structor_flag(
                std::move(vptr_store.fragment),
                vtt_vptr_store_fragment(loc), loc);
        }
        result.fragment =
            chain(std::move(result.fragment), std::move(vptr_store.fragment), loc);
    }
    bool union_variant_initialized = false;
    cir::RecordKind constructor_record_kind = facts->kind;

    std::vector<cir::RecordFieldFact> constructor_member_fields;
    if (facts->kind == cir::RecordKind::Union) {
        constructor_member_fields = facts->fields;
    } else {
        for (const RecordLifecycleStep& step : lifecycle.steps) {
            if (!step.field.is_base_subobject) {
                constructor_member_fields.push_back(step.field);
            }
        }
    }
    for (const cir::RecordFieldFact& field : constructor_member_fields) {
        if (field.is_base_subobject ||
            (!field.name.valid() &&
             !is_anonymous_record_member(file_, field))) {
            continue;
        }
        if (is_anonymous_record_member(file_, field)) {
            bool initialized_promoted_member = false;
            cir::EntityId selected_union_variant;
            for (size_t i = 0; i < initializers.size(); ++i) {
                const std::vector<cir::EntityId>& path =
                    initializer_object_paths[i];
                if (consumed[i] || path.size() < 2 ||
                    path.front() != field.entity) {
                    continue;
                }
                const cir::RecordFieldFact* promoted =
                    file_.field_fact(initializer_targets[i]);
                if (!promoted) {
                    continue;
                }
                if (field.is_anonymous_union_object) {
                    cir::EntityId variant = path[1];
                    if (!selected_union_variant.valid()) {
                        selected_union_variant = variant;
                    } else if (variant != selected_union_variant) {
                        report_error(
                            "more than one union member is explicitly initialized",
                            initializers[i].loc);
                        result.has_error = true;
                        consumed[i] = true;
                        discard_lifetime_boundary(
                            initializers[i].boundary);
                        continue;
                    }
                }
                consumed[i] = true;
                initialized_promoted_member = true;
                construct_subobject(*promoted,
                                    std::move(initializers[i].arguments),
                                    initializers[i].loc,
                                    initializers[i].braced,
                                    initializers[i].boundary,
                                    &path,
                                    true);
            }
            if (initialized_promoted_member) {
                union_variant_initialized =
                    union_variant_initialized ||
                    field.is_anonymous_union_object;
                continue;
            }
        }
        int found = initializer_for_field(field);
        if (found >= 0) {
            const std::vector<cir::EntityId>& path =
                initializer_object_paths[found];
            const cir::RecordFieldFact* initialized_field = &field;
            if (path.size() > 1) {
                const cir::RecordFieldFact* promoted =
                    file_.field_fact(initializer_targets[found]);
                if (promoted) {
                    initialized_field = promoted;
                }
            }
            construct_subobject(*initialized_field,
                                std::move(initializers[found].arguments),
                                initializers[found].loc,
                                initializers[found].braced,
                                initializers[found].boundary,
                                path.size() > 1 ? &path : nullptr,
                                true);
            union_variant_initialized =
                union_variant_initialized ||
                constructor_record_kind == cir::RecordKind::Union;
        } else {

            if (constructor_record_kind == cir::RecordKind::Union &&
                (union_variant_initialized ||
                 !field.has_default_member_initializer)) {
                continue;
            }
            if (field.has_default_member_initializer &&
                default_member_initializer_replay_callback_) {
                union_variant_initialized =
                    union_variant_initialized ||
                    constructor_record_kind == cir::RecordKind::Union;
                SrcLoc dmi_loc = field.default_member_initializer_loc;
                LifetimeBoundary dmi_boundary = begin_lifetime_boundary();
                ExprResult dmi_value =
                    default_member_initializer_replay_callback_(field.entity,
                                                                {},
                                                                dmi_loc);
                close_lifetime_boundary_without_cleanup(dmi_boundary);
                if (dmi_value.has_error) {
                    result.has_error = true;
                    result.fragment = chain(
                        std::move(result.fragment),
                        finish_lifetime_boundary(dmi_boundary, dmi_loc),
                        dmi_loc);
                    continue;
                }
                if (dmi_value.init_list) {
                    std::vector<InitElementInput>& elements =
                        dmi_value.init_list->elements;
                    cir::TypeId member_resolved =
                        file_.resolved_type(field.type.type);
                    if (elements.empty()) {
                        construct_subobject(field, {}, dmi_loc,
                                            /*braced=*/true, dmi_boundary,
                                            nullptr,
                                            /*explicitly_initialized=*/true);
                        continue;
                    }
                    if (is_aggregate_type(member_resolved) ||
                        elements.size() > 1) {
                        auto [place, place_fragment] =
                            member_place(field, dmi_loc);
                        result.fragment = chain(std::move(result.fragment),
                                                std::move(place_fragment),
                                                dmi_loc);
                        result.fragment = chain(
                            std::move(result.fragment),
                            emit_initializer_for_place(place,
                                                       field.type.type,
                                                       std::move(dmi_value),
                                                       dmi_loc),
                            dmi_loc);
                        install_subobject_rollback(field, dmi_loc);
                        result.fragment = chain(
                            std::move(result.fragment),
                            finish_lifetime_boundary(dmi_boundary, dmi_loc),
                            dmi_loc);
                        continue;
                    }
                    std::vector<ExprResult> dmi_arguments;
                    dmi_arguments.push_back(
                        std::move(elements.front().value));
                    construct_subobject(field, std::move(dmi_arguments),
                                        dmi_loc, /*braced=*/true,
                                        dmi_boundary, nullptr,
                                        /*explicitly_initialized=*/true);
                    continue;
                }
                if (dmi_value.value.valid() || dmi_value.place.valid()) {
                    std::vector<ExprResult> dmi_arguments;
                    dmi_arguments.push_back(std::move(dmi_value));
                    construct_subobject(field, std::move(dmi_arguments),
                                        dmi_loc, /*braced=*/false,
                                        dmi_boundary, nullptr,
                                        /*explicitly_initialized=*/true);
                    continue;
                }
                result.fragment = chain(
                    std::move(result.fragment),
                    finish_lifetime_boundary(dmi_boundary, dmi_loc), dmi_loc);
            }
            cir::TypeId member_type = file_.resolved_type(field.type.type);
            if (is_reference_type(member_type)) {
                if (diagnose_omitted_required_members) {
                    report_error(
                        "constructor must explicitly initialize reference member '" +
                            std::string(file_.name(field.name)) + "'",
                        loc);
                    result.has_error = true;
                }
                continue;
            }
            if ((field.type.qualifiers & cir::QualConst) != 0) {
                bool const_default_constructible = false;
                const cir::RecordFacts* member_facts =
                    file_.record_facts_for_type(member_type);
                if (member_facts) {
                    for (const cir::RecordMethodFact& method :
                         member_facts->methods) {
                        if (method.special_member_kind ==
                                cir::SpecialMemberKind::DefaultConstructor &&
                            method.is_eligible && !method.is_deleted &&
                            method.is_user_provided) {
                            const_default_constructible = true;
                            break;
                        }
                    }
                }
                if (!const_default_constructible) {
                    if (diagnose_omitted_required_members) {
                        report_error(
                            "constructor must explicitly initialize const member '" +
                                std::string(file_.name(field.name)) + "'",
                            loc);
                        result.has_error = true;
                    }
                    continue;
                }
            }
            cir::TypeId member_array_leaf =
                array_class_element_leaf(member_type);
            if (member_array_leaf.valid()
                    ? record_requires_default_constructor_selection(
                          member_array_leaf)
                    : (file_.valid(member_type) &&
                       file_.type(member_type).kind ==
                           cir::TypeKind::Record &&
                       (record_needs_construction(member_type) ||
                        record_requires_default_constructor_selection(
                            member_type)))) {
                construct_subobject(field, {}, loc);
            }
        }
    }
    for (size_t i = 0; i < initializers.size(); ++i) {
        if (!consumed[i] &&
            (initializer_dependent_bases[i].has_value() ||
             initializer_deferred_base_resolution[i])) {

            for (const ExprResult& argument : initializers[i].arguments) {
                result.has_error = result.has_error || argument.has_error;
            }
            consumed[i] = true;
            result.fragment = chain(
                std::move(result.fragment),
                finish_lifetime_boundary(initializers[i].boundary,
                                         initializers[i].loc),
                initializers[i].loc);
        }
        if (!consumed[i]) {
            std::string initializer_name = initializers[i].name;
            if (initializer_name.empty() &&
                initializers[i].base_type.valid()) {
                initializer_name = file_.format_type(initializers[i].base_type);
            }
            report_error("class has no base or member named '" +
                             initializer_name + "' to initialize",
                         initializers[i].loc);
            result.has_error = true;
            discard_lifetime_boundary(initializers[i].boundary);
        }
    }
    return result;
}

bool Session::vptr_field_path(cir::TypeId record_type,
                              std::vector<cir::EntityId>* path_out) const {
    const cir::RecordFacts* facts =
        file_.record_facts_for_type(file_.resolved_type(record_type));
    if (!facts || !facts->is_polymorphic) {
        return false;
    }
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.name.valid() && file_.name(field.name) == ".vptr") {
            if (path_out) {
                path_out->push_back(field.entity);
            }
            return true;
        }
    }

    for (const cir::RecordFieldFact& field : facts->fields) {
        if (!field.is_base_subobject) {
            continue;
        }
        if (path_out) {
            path_out->push_back(field.entity);
            if (vptr_field_path(field.type.type, path_out)) {
                return true;
            }
            path_out->pop_back();
        } else if (vptr_field_path(field.type.type, nullptr)) {
            return true;
        }
        break;
    }
    return false;
}

StmtResult Session::store_vptr_fragment(SrcLoc loc) {
    StmtResult result;
    result.falls_through = true;
    if (!current_member_record_.valid() || !current_this_place_.valid()) {
        return result;
    }
    cir::TypeId record_type = file_.entity(current_member_record_).type;
    const cir::RecordFacts* facts =
        file_.record_facts_for_type(file_.resolved_type(record_type));
    if (!facts || !facts->is_polymorphic || !facts->vtable_entity.valid()) {
        return result;
    }
    cir::TypeId usize = builder_.usize_type();
    cir::TypeId void_pointer =
        builder_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("ctor.vptr");
    auto store_one = [&](const std::vector<cir::EntityId>& path,
                         size_t address_point) {
        cir::InstId this_value =
            builder_.lvalue_to_rvalue(current_this_place_, loc);
        cir::InstId place = builder_.deref(this_value, loc);
        for (cir::EntityId step : path) {
            place = builder_.field_addr(place, step, file_.entity(step).type, loc);
        }
        cir::InstId vtable_place =
            builder_.global_place(facts->vtable_entity, loc);
        cir::InstId vtable_address = builder_.addr_of(vtable_place, loc);
        cir::InstId raw = builder_.cast(usize, vtable_address, "value", loc);
        cir::InstId offset = builder_.integer_literal(
            static_cast<int64_t>(address_point), usize,
            std::to_string(address_point), loc);
        cir::InstId adjusted =
            builder_.binary(cir::BinaryOpKind::Add, usize, raw, offset, loc);
        cir::InstId pointer = builder_.cast(void_pointer, adjusted, "value", loc);
        builder_.store(place, pointer, loc);
    };

    std::vector<cir::EntityId> path;
    if (vptr_field_path(record_type, &path)) {
        store_one(path, facts->vtable_address_point);
    }

    for (const cir::RecordFacts::SecondaryVtable& secondary :
         facts->secondary_vtables) {
        std::vector<cir::EntityId> secondary_path = secondary.storage_path;
        if (!vptr_field_path(secondary.base_type.type,
                             &secondary_path)) {
            continue;
        }
        store_one(secondary_path, secondary.address_point_bytes);
    }
    result.fragment = finish_fragment_block(block, previous);
    return result;
}

cir::InstId Session::emit_virtual_base_adjust(cir::InstId place,
                                              cir::EntityId vbase_field,
                                              SrcLoc loc) {
    // The current subobject's vtable carries the virtual base's offset at
    // (address point - 24 - 8 * index); the adjustment is always dynamic
    // because the storage lives with the complete object (Itanium 2.5.2).
    cir::EntityId owner = file_.entity(vbase_field).parent;
    const cir::RecordFacts* facts = file_.record_facts(owner);
    if (!facts) {
        return builder_.field_addr(place, vbase_field,
                                   file_.entity(vbase_field).type, loc);
    }
    size_t index = 0;
    cir::TypeId vbase_type = file_.entity(vbase_field).type;
    for (const cir::RecordFacts::VirtualBase& vbase : facts->virtual_bases) {
        if (vbase.storage_field == vbase_field) {
            index = vbase.vtable_index;
            vbase_type = vbase.type.type;
            break;
        }
    }
    std::vector<cir::EntityId> vptr_path;
    if (!vptr_field_path(facts->type.type, &vptr_path)) {
        return builder_.field_addr(place, vbase_field,
                                   file_.entity(vbase_field).type, loc);
    }
    cir::TypeId usize = builder_.usize_type();
    cir::InstId vptr_place = place;
    for (cir::EntityId step : vptr_path) {
        vptr_place = builder_.field_addr(vptr_place, step,
                                         file_.entity(step).type, loc);
    }
    cir::InstId vptr = builder_.lvalue_to_rvalue(vptr_place, loc);
    cir::InstId vptr_raw = builder_.cast(usize, vptr, "value", loc);
    cir::InstId entry_offset = builder_.integer_literal(
        static_cast<int64_t>(24 + 8 * index), usize,
        std::to_string(24 + 8 * index), loc);
    cir::InstId entry_address = builder_.binary(
        cir::BinaryOpKind::Sub, usize, vptr_raw, entry_offset, loc);
    cir::InstId entry_pointer =
        builder_.cast(builder_.pointer_type(usize), entry_address, "value", loc);
    cir::InstId entry_place = builder_.deref(entry_pointer, loc);
    cir::InstId vbase_offset = builder_.lvalue_to_rvalue(entry_place, loc);
    cir::InstId object_address = builder_.addr_of(place, loc);
    cir::InstId object_raw = builder_.cast(usize, object_address, "value", loc);
    cir::InstId adjusted_raw = builder_.binary(
        cir::BinaryOpKind::Add, usize, object_raw, vbase_offset, loc);
    cir::InstId adjusted_pointer = builder_.cast(
        builder_.pointer_type(vbase_type), adjusted_raw, "value", loc);
    return builder_.deref(adjusted_pointer, loc);
}

cir::InstId Session::emit_subobject_path(cir::InstId place,
                                         const std::vector<cir::EntityId>& path,
                                         SrcLoc loc) {
    for (cir::EntityId step : path) {
        const cir::RecordFieldFact* fact = file_.field_fact(step);
        if (fact && fact->is_virtual_base_storage) {
            place = emit_virtual_base_adjust(place, step, loc);
        } else {
            place = builder_.field_addr(place, step,
                                        file_.entity(step).type, loc);
        }
    }
    return place;
}

cir::EntityId Session::structor_complete_variant(cir::EntityId structor) const {
    auto found = structor_complete_variants_.find(
        static_cast<uint64_t>(structor.index));
    return found != structor_complete_variants_.end() ? found->second
                                                      : structor;
}

cir::EntityId Session::structor_base_variant(cir::EntityId structor) const {
    auto found =
        structor_base_variants_.find(static_cast<uint64_t>(structor.index));
    return found != structor_base_variants_.end() ? found->second : structor;
}

cir::EntityId Session::structor_impl_entity(cir::EntityId structor) const {
    auto found =
        structor_variant_impls_.find(static_cast<uint64_t>(structor.index));
    return found != structor_variant_impls_.end() ? found->second : structor;
}

void Session::ensure_structor_variants(cir::EntityId structor, SrcLoc loc) {
    cir::EntityId impl = structor_impl_entity(structor);
    if (!impl.valid() || !file_.valid(impl)) {
        return;
    }
    cir::EntityKind kind = file_.entity(impl).kind;
    if (kind != cir::EntityKind::Constructor &&
        kind != cir::EntityKind::Destructor) {
        return;
    }
    cir::EntityId owner = file_.entity(impl).parent;
    const cir::RecordFacts* facts = owner.valid()
        ? file_.record_facts(owner)
        : nullptr;
    if (!facts || facts->virtual_bases.empty()) {
        return;
    }

    cir::EntityId inherited_origin;
    if (const cir::RecordMethodFact* method = file_.method_fact(impl);
        method && method->inherited_constructor) {
        inherited_origin = method->inherited_constructor->origin_record;
    }
    uint64_t key = static_cast<uint64_t>(impl.index);
    if (structor_complete_variants_.find(key) ==
        structor_complete_variants_.end()) {
        synthesize_structor_variant(impl, true, loc, inherited_origin);
    }
    if (structor_base_variants_.find(key) ==
        structor_base_variants_.end()) {
        synthesize_structor_variant(impl, false, loc, inherited_origin);
    }
}

cir::EntityId Session::synthesize_structor_variant(cir::EntityId impl,
                                                   bool complete,
                                                   SrcLoc loc,
                                                   cir::EntityId
                                                       inherited_origin) {

    cir::EntityKind kind = file_.entity(impl).kind;
    const char* variant = kind == cir::EntityKind::Constructor
        ? (complete ? "C1" : "C2")
        : (complete ? "D1" : "D2");
    std::string symbol = abi::itanium_structor_variant_name(
        file_, impl, variant, /*skip_trailing_param=*/true,
        inherited_origin);
    if (symbol.empty()) {
        return impl;
    }
    auto cached = collecting_pattern_ ? vtable_thunks_.end()
                                      : vtable_thunks_.find(symbol);
    if (cached != vtable_thunks_.end()) {
        return cached->second;
    }
    cir::TypeId impl_type = file_.resolved_type(file_.entity(impl).type);
    const auto* payload =
        std::get_if<cir::FunctionTypePayload>(&file_.type_payload(impl_type));
    if (!payload || payload->parameters.size() < 3) {
        return impl;
    }

    cir::TypeRef return_type = payload->return_type;
    std::vector<cir::TypeRef> declared_types(payload->parameters.begin(),
                                             payload->parameters.end() - 2);
    cir::TypeRef vtt_type = payload->parameters.back();
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    std::vector<cir::TypeRef> parameter_types;
    if (complete) {
        parameter_types = declared_types;
    } else {
        parameter_types.push_back(declared_types.front());
        parameter_types.push_back(vtt_type);
        parameter_types.insert(parameter_types.end(),
                               declared_types.begin() + 1,
                               declared_types.end());
    }
    cir::TypeId wrapper_type =
        function_type(return_type, parameter_types, false, true);

    std::vector<ParamInput> params;
    params.reserve(parameter_types.size());
    for (size_t i = 0; i < parameter_types.size(); ++i) {
        ParamInput param;
        param.name = ".variant.p" + std::to_string(i);
        param.type = parameter_types[i];
        param.loc = loc;
        params.push_back(std::move(param));
    }

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags flags;
    FunctionDeclStart fn = begin_function_type(symbol, wrapper_type,
                                               return_type, params, loc, flags);
    file_.entity_mut(fn.decl.entity).is_extern_c = true;
    file_.entity_mut(fn.decl.entity).linkage = cir::LinkageKind::LinkOnceODR;
    mark_generated_abi_entity(fn.decl.entity, impl,
                              cir::GeneratedSymbolRole::StructorVariant);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("structor.variant");
    std::vector<cir::InstId> arguments;
    arguments.reserve(fn.function.parameters.size() + 2);
    cir::InstId vtt_argument{};
    for (size_t i = 0; i < fn.function.parameters.size(); ++i) {
        if (!complete && i == 1) {
            vtt_argument = fn.function.parameters[i].value.inst;
            continue;
        }
        arguments.push_back(fn.function.parameters[i].value.inst);
    }
    arguments.push_back(builder_.integer_literal(
        complete ? 1 : 0, builder_.int_type(), complete ? "1" : "0", loc));
    if (!vtt_argument.valid()) {
        cir::InstId null_raw = builder_.integer_literal(
            0, builder_.usize_type(), "0", loc);
        vtt_argument =
            builder_.cast(vtt_type.type, null_raw, "value", loc);
    }
    arguments.push_back(vtt_argument);
    builder_.call(impl, void_type, arguments, loc);
    builder_.return_void(loc);
    cir::Fragment body = finish_fragment_block(block, previous);
    finish_function(make_stmt_result(std::move(body), true, false), loc);
    restore_function_context(std::move(saved));

    if (!collecting_pattern_) {
        if (auto [thunk, inserted] =
                vtable_thunks_.emplace(symbol, fn.decl.entity);
            inserted) {
            track_speculative_rollback(
                [this, symbol] { vtable_thunks_.erase(symbol); });
        }
    }
    uint64_t impl_key = static_cast<uint64_t>(impl.index);
    auto& variants =
        complete ? structor_complete_variants_ : structor_base_variants_;
    if (auto [variant, inserted] = variants.emplace(impl_key, fn.decl.entity);
        inserted) {
        track_speculative_rollback([this, complete, impl_key] {
            (complete ? structor_complete_variants_ : structor_base_variants_)
                .erase(impl_key);
        });
    }
    uint64_t variant_key = static_cast<uint64_t>(fn.decl.entity.index);
    if (auto [reverse, inserted] =
            structor_variant_impls_.emplace(variant_key, impl);
        inserted) {
        track_speculative_rollback([this, variant_key] {
            structor_variant_impls_.erase(variant_key);
        });
    }
    return fn.decl.entity;
}

cir::EntityId Session::synthesize_deleting_destructor(cir::EntityId destructor,
                                                      SrcLoc loc) {
    bool vbase_structor =
        structor_complete_variant(destructor) != destructor;
    std::string symbol = abi::itanium_structor_variant_name(
        file_, destructor, "D0", vbase_structor);
    if (symbol.empty()) {
        return destructor;
    }
    auto cached = collecting_pattern_ ? vtable_thunks_.end()
                                      : vtable_thunks_.find(symbol);
    if (cached != vtable_thunks_.end()) {
        return cached->second;
    }
    const cir::Entity& target_entity = file_.entity(destructor);
    cir::TypeId fn_type = file_.resolved_type(target_entity.type);
    const auto* payload =
        std::get_if<cir::FunctionTypePayload>(&file_.type_payload(fn_type));
    if (!payload || payload->parameters.empty()) {
        return destructor;
    }
    cir::TypeRef this_type = payload->parameters.front();
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::DeallocationFunctionSelectionFact selected_deallocation;
    const cir::RecordMethodFact* destructor_fact =
        file_.method_fact(destructor);
    if (destructor_fact) {
        selected_deallocation =
            destructor_fact->deleting_destructor_deallocation;
    }
    if (!selected_deallocation.valid()) {

        if (destructor_fact) {
            return destructor;
        }
        cir::TypeId owner_type = target_entity.parent.valid() &&
                file_.valid(target_entity.parent)
            ? file_.entity(target_entity.parent).type
            : cir::TypeId{};
        DeallocationSelection fallback = select_deallocation_function(
            owner_type, /*is_array=*/false, /*force_global=*/false,
            /*placement_matching=*/false, nullptr, {}, loc,
            /*diagnose=*/true, /*check_access=*/false);
        selected_deallocation.entity = fallback.entity;
        selected_deallocation.form = fallback.form;
    }
    if (!selected_deallocation.valid()) {
        return destructor;
    }

    std::vector<ParamInput> params;
    ParamInput this_param;
    this_param.name = ".delete.this";
    this_param.type = this_type;
    this_param.loc = loc;
    params.push_back(std::move(this_param));

    // The ABI deleting destructor is a wrapper with the declared `this`-only
    // destructor signature. A virtual-base implementation may carry Aburi's
    // internal complete/VTT parameters, but those belong to D4 and must never
    // leak into D0 or its adjustor thunks.
    cir::TypeId deleting_type = function_type(
        payload->return_type, {this_type}, false, true,
        payload->member_is_const, payload->exception_spec, {},
        payload->member_ref_qualifier, payload->member_is_volatile);

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags flags;
    FunctionDeclStart fn = begin_function_type(
        symbol, deleting_type, file_.type_ref(void_type), params, loc, flags);
    file_.entity_mut(fn.decl.entity).is_extern_c = true;
    mark_generated_abi_entity(fn.decl.entity, destructor,
                              cir::GeneratedSymbolRole::DeletingDestructor);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("dtor.deleting");
    cir::InstId this_value = fn.function.parameters[0].value.inst;
    cir::TypeId owner_type = target_entity.parent.valid() &&
            file_.valid(target_entity.parent)
        ? file_.entity(target_entity.parent).type
        : cir::TypeId{};
    DeallocationSelection selection;
    selection.entity = selected_deallocation.entity;
    selection.form = selected_deallocation.form;
    if (!selected_deallocation.form.is_destroying) {
        cir::BlockId outer_target = builder_.current_unwind_target();
        builder_.set_current_unwind_target({});
        cir::BlockId pad = builder_.create_block("dtor.deleting.lpad");
        cir::BlockId action = builder_.create_block("dtor.deleting.act");
        builder_.set_block_unwind_target(pad, {});
        builder_.set_block_unwind_target(action, {});
        builder_.switch_to_block(pad);
        cir::EhLandingPadPayload pad_payload;
        pad_payload.is_cleanup = true;
        cir::InstId landing_pad =
            builder_.eh_landing_pad(std::move(pad_payload), loc);
        cir::InstId selector = builder_.eh_selector(landing_pad, loc);
        builder_.branch(action, {landing_pad, selector}, loc);
        cir::TypeId exception_pointer =
            builder_.pointer_type(builder_.void_type());
        cir::InstId exn = builder_.add_block_parameter(
            action, exception_pointer, "exn", loc);
        cir::InstId sel = builder_.add_block_parameter(
            action, builder_.int_type(), "sel", loc);
        builder_.switch_to_block(action);
        emit_deallocation_call(selection, this_value, owner_type, loc);
        emit_unwind_continue(action, exn, sel, outer_target, loc);
        eh_pads_in_flight_.push_back(landing_pad);
        track_speculative_rollback([this]() {
            if (!eh_pads_in_flight_.empty()) {
                eh_pads_in_flight_.pop_back();
            }
        });
        eh_code_targets_[pad.index] = action;
        track_speculative_rollback([this, index = pad.index]() {
            eh_code_targets_.erase(index);
        });
        builder_.set_block_unwind_target(block, pad);
        builder_.set_current_unwind_target(pad);
        builder_.switch_to_block(block);
        builder_.call(structor_complete_variant(destructor), void_type,
                      {this_value}, loc);
        builder_.set_current_unwind_target(outer_target);
    }
    emit_deallocation_call(selection, this_value, owner_type, loc);
    builder_.return_void(loc);
    cir::Fragment body = finish_fragment_block(block, previous);
    finish_function(make_stmt_result(std::move(body), true, false), loc);
    restore_function_context(std::move(saved));

    file_.entity_mut(fn.decl.entity).linkage = cir::LinkageKind::LinkOnceODR;
    if (!collecting_pattern_) {
        if (auto [thunk, inserted] =
                vtable_thunks_.emplace(symbol, fn.decl.entity);
            inserted) {
            track_speculative_rollback(
                [this, symbol] { vtable_thunks_.erase(symbol); });
        }
    }
    return fn.decl.entity;
}

cir::EntityId Session::synthesize_vtable_thunk(cir::EntityId target,
                                               size_t this_offset_bytes,
                                               SrcLoc loc) {
    cir::VirtualAdjustmentFact adjustment;
    adjustment.kind = cir::VirtualAdjustmentKind::NonVirtual;
    adjustment.static_offset_bytes =
        -static_cast<int64_t>(this_offset_bytes);
    return synthesize_vtable_thunk(target, target, adjustment, {}, loc);
}

cir::EntityId Session::synthesize_vtable_thunk(
    cir::EntityId target,
    cir::EntityId slot_declaration,
    const cir::VirtualAdjustmentFact& this_adjustment,
    const cir::VirtualAdjustmentFact& result_adjustment,
    SrcLoc loc) {
    std::string symbol = abi::itanium_virtual_thunk_symbol(
        file_, target, this_adjustment, result_adjustment);
    if (symbol.empty()) {
        return target;
    }
    auto cached = collecting_pattern_ ? vtable_thunks_.end()
                                      : vtable_thunks_.find(symbol);
    if (cached != vtable_thunks_.end()) {
        return cached->second;
    }

    cir::TypeId target_fn_type =
        file_.resolved_type(file_.entity(target).type);
    cir::TypeId slot_fn_type = file_.resolved_type(
        file_.entity(slot_declaration).type);
    const auto* target_payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(target_fn_type));
    const auto* slot_payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(slot_fn_type));
    if (!target_payload || !slot_payload ||
        target_payload->parameters.empty() ||
        slot_payload->parameters.empty()) {
        return target;
    }
    if (target_payload->is_variadic || slot_payload->is_variadic) {
        report_error("variadic virtual functions in secondary vtables are not "
                     "supported yet",
                     loc);
        return target;
    }

    cir::TypeRef slot_return_type = slot_payload->return_type;
    cir::TypeRef target_return_type = target_payload->return_type;
    std::vector<cir::TypeRef> slot_parameter_types =
        slot_payload->parameters;
    std::vector<cir::TypeRef> target_parameter_types =
        target_payload->parameters;

    std::vector<ParamInput> params;
    params.reserve(slot_parameter_types.size());
    for (size_t i = 0; i < slot_parameter_types.size(); ++i) {
        ParamInput param;
        param.name = ".thunk.p" + std::to_string(i);
        param.type = slot_parameter_types[i];
        param.loc = loc;
        params.push_back(std::move(param));
    }

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags thunk_flags;
    FunctionDeclStart fn = begin_function_type(symbol, slot_fn_type,
                                               slot_return_type, params, loc,
                                               thunk_flags);
    file_.entity_mut(fn.decl.entity).is_extern_c = true;
    file_.entity_mut(fn.decl.entity).decl_flags.is_constexpr =
        file_.entity(target).decl_flags.is_constexpr ||
        file_.entity(target).decl_flags.is_consteval;
    mark_generated_abi_entity(fn.decl.entity, target,
                              cir::GeneratedSymbolRole::Thunk);

    cir::TypeId usize = builder_.usize_type();
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("thunk.body");
    cir::InstId this_value = fn.function.parameters[0].value.inst;
    cir::InstId raw = builder_.cast(usize, this_value, "value", loc);
    cir::InstId adjusted_raw = raw;
    if (this_adjustment.kind == cir::VirtualAdjustmentKind::Virtual) {
        cir::TypeId usize_pointer = builder_.pointer_type(usize);
        cir::InstId words = builder_.cast(usize_pointer, this_value,
                                          "value", loc);
        cir::InstId vptr_place = builder_.deref(words, loc);
        cir::InstId vptr_raw = builder_.lvalue_to_rvalue(vptr_place, loc);
        int64_t table_offset = this_adjustment.vtable_offset_bytes;
        cir::InstId table_delta = builder_.integer_literal(
            table_offset < 0 ? -table_offset : table_offset,
            usize, std::to_string(table_offset), loc);
        cir::InstId entry_raw = builder_.binary(
            table_offset < 0 ? cir::BinaryOpKind::Sub
                             : cir::BinaryOpKind::Add,
            usize, vptr_raw, table_delta, loc);
        cir::InstId entry_pointer = builder_.cast(
            usize_pointer, entry_raw, "value", loc);
        cir::InstId entry_place = builder_.deref(entry_pointer, loc);
        cir::InstId dynamic_offset =
            builder_.lvalue_to_rvalue(entry_place, loc);
        adjusted_raw = builder_.binary(cir::BinaryOpKind::Add, usize,
                                       adjusted_raw, dynamic_offset, loc);
    }
    if (this_adjustment.static_offset_bytes != 0) {
        int64_t static_offset = this_adjustment.static_offset_bytes;
        cir::InstId offset = builder_.integer_literal(
            static_offset < 0 ? -static_offset : static_offset,
            usize, std::to_string(static_offset), loc);
        adjusted_raw = builder_.binary(
            static_offset < 0 ? cir::BinaryOpKind::Sub
                              : cir::BinaryOpKind::Add,
            usize, adjusted_raw, offset, loc);
    }
    cir::InstId adjusted =
        builder_.cast(target_parameter_types.front().type, adjusted_raw,
                      "value", loc);
    std::vector<cir::InstId> arguments;
    arguments.push_back(adjusted);
    for (size_t i = 1; i < fn.function.parameters.size(); ++i) {
        arguments.push_back(fn.function.parameters[i].value.inst);
    }
    cir::InstId call_result =
        builder_.call(target, target_return_type.type, arguments, loc);
    cir::TypeId resolved_return =
        file_.resolved_type(slot_return_type.type);
    bool returns_void = !file_.valid(resolved_return) ||
        (file_.type(resolved_return).kind == cir::TypeKind::Builtin &&
         std::get<cir::BuiltinTypePayload>(file_.type_payload(resolved_return))
                 .kind == cir::BuiltinTypeKind::Void);
    if (returns_void) {
        builder_.return_void(loc);
    } else if (result_adjustment.required()) {
        cir::TypeId target_result =
            file_.resolved_type(target_return_type.type);
        bool pointer_result = file_.valid(target_result) &&
            file_.type(target_result).kind == cir::TypeKind::Pointer;
        auto adjusted_result = [&]() {
            cir::InstId result_place = builder_.deref(call_result, loc);
            result_place = emit_subobject_path(
                result_place, result_adjustment.path, loc);
            cir::InstId result_pointer = builder_.addr_of(result_place, loc);
            return builder_.cast(slot_return_type.type, result_pointer,
                                 "covariant", loc);
        };
        if (!pointer_result) {
            builder_.return_value(adjusted_result(), loc);
        } else {
            cir::InstId null_value = builder_.cast(
                target_return_type.type,
                builder_.nullptr_literal("nullptr", loc), "nullptr", loc);
            cir::InstId is_null = builder_.binary(
                cir::BinaryOpKind::Equal, builder_.bool_type(), call_result,
                null_value, loc);
            cir::BlockId null_block =
                builder_.create_detached_block("thunk.result.null");
            cir::BlockId adjust_block =
                builder_.create_detached_block("thunk.result.adjust");
            cir::BlockId merge_block =
                builder_.create_detached_block("thunk.result.merge");
            cir::InstId merge_value = builder_.add_block_parameter(
                merge_block, slot_return_type.type, ".thunk.result", loc);
            builder_.cond_branch(is_null, null_block, adjust_block, {}, loc);

            builder_.switch_to_block(null_block);
            cir::InstId result_null = builder_.cast(
                slot_return_type.type,
                builder_.nullptr_literal("nullptr", loc), "nullptr", loc);
            builder_.branch(merge_block, {result_null}, loc);

            builder_.switch_to_block(adjust_block);
            builder_.branch(merge_block, {adjusted_result()}, loc);

            builder_.switch_to_block(merge_block);
            builder_.return_value(merge_value, loc);

            cir::Fragment body = builder_.block_fragment(block);
            body.blocks.push_back(null_block);
            body.blocks.push_back(adjust_block);
            body.blocks.push_back(merge_block);
            body.exit = merge_block;
            body.falls_through = false;
            builder_.switch_to_block(previous);
            finish_function(make_stmt_result(std::move(body), true, false),
                            loc);
            restore_function_context(std::move(saved));
            file_.entity_mut(fn.decl.entity).linkage =
                cir::LinkageKind::LinkOnceODR;
            if (!collecting_pattern_) {
                if (auto [thunk, inserted] =
                        vtable_thunks_.emplace(symbol, fn.decl.entity);
                    inserted) {
                    track_speculative_rollback(
                        [this, symbol] { vtable_thunks_.erase(symbol); });
                }
            }
            return fn.decl.entity;
        }
    } else {
        cir::InstId result = call_result;
        if (file_.resolved_type(target_return_type.type) !=
                file_.resolved_type(slot_return_type.type) ||
            target_return_type.qualifiers != slot_return_type.qualifiers) {
            result = builder_.cast(slot_return_type.type, call_result,
                                   "covariant", loc);
        }
        builder_.return_value(result, loc);
    }
    cir::Fragment body = finish_fragment_block(block, previous);
    finish_function(make_stmt_result(std::move(body), true, false), loc);
    restore_function_context(std::move(saved));

    file_.entity_mut(fn.decl.entity).linkage = cir::LinkageKind::LinkOnceODR;
    if (!collecting_pattern_) {
        if (auto [thunk, inserted] =
                vtable_thunks_.emplace(symbol, fn.decl.entity);
            inserted) {
            track_speculative_rollback(
                [this, symbol] { vtable_thunks_.erase(symbol); });
        }
    }
    return fn.decl.entity;
}

void Session::begin_destructor_lifecycle_region(SrcLoc loc) {
    current_destructor_lifecycle_region_ = {};
    if (!current_member_record_.valid() || !current_this_place_.valid() ||
        !builder_.current_function().valid()) {
        return;
    }
    const cir::RecordFacts* facts = file_.record_facts(current_member_record_);
    if (!facts) {
        return;
    }

    DestructorLifecycleRegion region;
    region.active = true;
    region.outer_unwind_target = builder_.current_unwind_target();
    RecordLifecyclePlan plan = record_lifecycle_plan(
        *facts, RecordLifecycleOperation::Destroy);
    for (RecordLifecycleStep& step : plan.steps) {
        cir::TypeId type = file_.resolved_type(step.field.type.type);
        cir::TypeId array_leaf = step.array_shape.leaf_type;
        if ((array_leaf.valid() && record_destructor(array_leaf).valid()) ||
            (!array_leaf.valid() && record_destructor(type).valid())) {
            DestructorCleanupStep cleanup;
            cleanup.lifecycle = std::move(step);
            region.steps.push_back(std::move(cleanup));
        }
    }

    cir::BlockId next_target = region.outer_unwind_target;
    cir::BlockId original_block = builder_.current_block();
    builder_.set_current_unwind_target({});
    for (size_t index = region.steps.size(); index-- > 0;) {
        DestructorCleanupStep& cleanup = region.steps[index];
        const RecordLifecycleStep& step = cleanup.lifecycle;
        const cir::RecordFieldFact& field = step.field;
        cir::TypeId subobject_type = file_.resolved_type(field.type.type);

        cir::BlockId pad = builder_.create_block("dtor.subobject.lpad");
        cir::BlockId action = builder_.create_block("dtor.subobject.act");
        builder_.set_block_unwind_target(pad, {});
        builder_.set_block_unwind_target(action, {});
        builder_.switch_to_block(pad);
        cir::EhLandingPadPayload payload;
        payload.is_cleanup = true;
        cir::InstId landing_pad =
            builder_.eh_landing_pad(std::move(payload), loc);
        cir::InstId selector = builder_.eh_selector(landing_pad, loc);
        builder_.branch(action, {landing_pad, selector}, loc);
        cir::TypeId void_type = builder_.void_type();
        cir::InstId exn_param = builder_.add_block_parameter(
            action, builder_.pointer_type(void_type), "exn", loc);
        cir::InstId sel_param = builder_.add_block_parameter(
            action, builder_.int_type(), "sel", loc);
        builder_.switch_to_block(action);

        cir::BlockId destroy_block = action;
        cir::BlockId skip_block{};
        if (step.complete_object_only && current_structor_flag_.valid()) {
            destroy_block = builder_.create_block("dtor.vbase.unwind");
            skip_block = builder_.create_block("dtor.vbase.unwind.skip");
            builder_.set_block_unwind_target(destroy_block, {});
            builder_.set_block_unwind_target(skip_block, {});
            cir::InstId zero = builder_.integer_literal(
                0, builder_.int_type(), "0", loc);
            cir::InstId is_complete = builder_.binary(
                cir::BinaryOpKind::NotEqual, builder_.int_type(),
                current_structor_flag_, zero, loc);
            builder_.cond_branch_from(action, is_complete, destroy_block,
                                      skip_block, {}, loc);
            builder_.switch_to_block(destroy_block);
        }

        cir::InstId action_this_place =
            rematerialize_entity_place(current_this_place_, loc);
        cir::InstId action_this =
            builder_.lvalue_to_rvalue(action_this_place, loc);
        cir::InstId place = builder_.field_addr(
            builder_.deref(action_this, loc), field.entity,
            field.type.type, loc);
        cir::BlockId destroy_exit = destroy_block;
        if (step.array_shape.leaf_type.valid()) {
            cir::Fragment array_destroy = array_destroy_loop_fragment(
                place, subobject_type, {}, loc,
                ArrayDestructionMode::UnwindCleanup);
            builder_.attach_fragment_to_function(builder_.current_function(),
                                                 array_destroy);
            builder_.branch(array_destroy.entry, {}, loc);
            destroy_exit = array_destroy.exit;
        } else {
            cir::EntityId destructor = record_destructor(subobject_type);
            destructor = field.is_base_subobject
                ? structor_base_variant(destructor)
                : structor_complete_variant(destructor);
            bool vtt_call = false;
            if (field.is_base_subobject &&
                current_structor_vtt_place_.valid()) {
                const cir::RecordFacts* subobject_facts =
                    file_.record_facts_for_type(subobject_type);
                if (subobject_facts &&
                    !subobject_facts->virtual_bases.empty()) {
                    cir::EntityId subobject_record =
                        file_.record_entity(subobject_type);
                    VttInfo info = compute_vtt_info(*facts);
                    const auto& slices = field.is_virtual_base_storage
                        ? info.vbase_slices
                        : info.base_slices;
                    for (const VttInfo::Slice& slice : slices) {
                        if (slice.record_entity != subobject_record) {
                            continue;
                        }
                        cir::InstId saved_vtt = current_structor_vtt_place_;
                        current_structor_vtt_place_ =
                            rematerialize_entity_place(saved_vtt, loc);
                        cir::InstId slice_value =
                            vtt_slice_value(slice.start, loc);
                        current_structor_vtt_place_ = saved_vtt;
                        emit_structor_call(
                            destructor, void_type,
                            {builder_.addr_of(place, loc), slice_value}, loc);
                        vtt_call = true;
                        break;
                    }
                }
            }
            if (!vtt_call) {
                emit_destroy(place, destructor, loc);
            }
        }

        cir::BlockId continue_block = destroy_exit;
        if (skip_block.valid()) {
            cir::BlockId joined =
                builder_.create_block("dtor.vbase.unwind.continue");
            builder_.set_block_unwind_target(joined, {});
            builder_.branch_from(destroy_exit, joined, {}, loc);
            builder_.branch_from(skip_block, joined, {}, loc);
            continue_block = joined;
        }
        emit_unwind_continue(continue_block, exn_param, sel_param,
                             next_target, loc);
        builder_.switch_to_block(original_block);

        cleanup.landing_pad = landing_pad;
        cleanup.pad_block = pad;
        cleanup.action_block = action;
        eh_pads_in_flight_.push_back(landing_pad);
        track_speculative_rollback([this]() {
            if (!eh_pads_in_flight_.empty()) {
                eh_pads_in_flight_.pop_back();
            }
        });
        eh_code_targets_[pad.index] = action;
        track_speculative_rollback([this, pad_index = pad.index]() {
            eh_code_targets_.erase(pad_index);
        });
        next_target = pad;
    }

    region.body_unwind_target = next_target;
    current_destructor_lifecycle_region_ = std::move(region);
    builder_.set_current_unwind_target(next_target);
    builder_.switch_to_block(original_block);
}

StmtResult Session::collect_destructor_epilogue(SrcLoc loc) {
    StmtResult result;
    result.falls_through = true;
    if (!current_member_record_.valid() || !current_this_place_.valid() ||
        !current_destructor_lifecycle_region_.active) {
        return result;
    }
    const cir::RecordFacts* facts = file_.record_facts(current_member_record_);
    if (!facts) {
        return result;
    }

    RecordLifecyclePlan semantic_plan = record_lifecycle_plan(
        *facts, RecordLifecycleOperation::Destroy);
    for (const RecordLifecycleStep& step : semantic_plan.steps) {
        const cir::RecordFieldFact& field = step.field;
        SrcLoc invocation_loc =
            field.entity.valid() && file_.valid(field.entity)
            ? file_.entity(field.entity).loc
            : loc;
        if (!validate_potentially_invoked_destructor(field.type.type,
                                                     invocation_loc)) {
            result.has_error = true;
        }
    }

    DestructorLifecycleRegion& region =
        current_destructor_lifecycle_region_;
    cir::BlockId caller_unwind_target = builder_.current_unwind_target();
    for (size_t index = 0; index < region.steps.size(); ++index) {
        const RecordLifecycleStep& step = region.steps[index].lifecycle;
        const cir::RecordFieldFact& field = step.field;
        cir::BlockId next_target = index + 1 < region.steps.size()
            ? region.steps[index + 1].pad_block
            : region.outer_unwind_target;
        builder_.set_current_unwind_target(next_target);
        cir::Fragment one;
        if (step.array_shape.leaf_type.valid()) {
            cir::BlockId array_previous = builder_.current_block();
            cir::BlockId array_block =
                begin_fragment_block("dtor.subobject.array");
            cir::InstId this_ptr =
                builder_.lvalue_to_rvalue(current_this_place_, loc);
            cir::InstId member = builder_.field_addr(
                builder_.deref(this_ptr, loc), field.entity, field.type.type,
                loc);
            one = finish_fragment_block(array_block, array_previous);
            std::function<cir::InstId(SrcLoc)> action_place =
                [this, field_entity = field.entity,
                 field_type = field.type.type](SrcLoc action_loc) {
                    cir::InstId this_place = rematerialize_entity_place(
                        current_this_place_, action_loc);
                    cir::InstId this_value = builder_.lvalue_to_rvalue(
                        this_place, action_loc);
                    return builder_.field_addr(
                        builder_.deref(this_value, action_loc), field_entity,
                        field_type, action_loc);
                };
            one = chain(
                std::move(one),
                array_destroy_loop_fragment(
                    member, field.type.type, {}, loc,
                    ArrayDestructionMode::Normal, &action_place),
                loc);
        } else {
            cir::EntityId destructor = record_destructor(field.type.type);
            if (!destructor.valid()) {
                continue;
            }
            destructor = field.is_base_subobject
                ? structor_base_variant(destructor)
                : structor_complete_variant(destructor);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("dtor.subobject");
            cir::InstId this_value =
                builder_.lvalue_to_rvalue(current_this_place_, loc);
            cir::InstId object_place = builder_.deref(this_value, loc);
            cir::InstId place = builder_.field_addr(
                object_place, field.entity, field.type.type, loc);
            bool vtt_call = false;
            if (field.is_base_subobject &&
                current_structor_vtt_place_.valid()) {
                const cir::RecordFacts* subobject_facts =
                    file_.record_facts_for_type(
                        file_.resolved_type(field.type.type));
                if (subobject_facts &&
                    !subobject_facts->virtual_bases.empty()) {
                    cir::EntityId subobject_record = file_.record_entity(
                        file_.resolved_type(field.type.type));
                    VttInfo info = compute_vtt_info(*facts);
                    const auto& slices = field.is_virtual_base_storage
                        ? info.vbase_slices
                        : info.base_slices;
                    for (const VttInfo::Slice& slice : slices) {
                        if (slice.record_entity == subobject_record) {
                            cir::InstId pointer = builder_.addr_of(place, loc);
                            cir::InstId slice_value =
                                vtt_slice_value(slice.start, loc);
                            emit_structor_call(
                                destructor, builder_.void_type(),
                                {pointer, slice_value}, loc);
                            vtt_call = true;
                            break;
                        }
                    }
                }
            }
            if (!vtt_call) {
                emit_destroy(place, destructor, loc);
            }
            one = finish_fragment_block(block, previous);
        }

        if (step.complete_object_only && current_structor_flag_.valid()) {
            one = guard_on_structor_flag(std::move(one), loc);
        }
        result.fragment = chain(std::move(result.fragment), std::move(one),
                                loc);
    }
    builder_.set_current_unwind_target(caller_unwind_target);
    return result;
}

Session::CompleteClassInitializerScope
Session::begin_complete_class_initializer(cir::EntityId record,
                                          cir::InstId object_place) {
    CompleteClassInitializerScope scope;
    scope.previous_record = current_member_record_;
    scope.previous_object_place = current_complete_class_object_place_;
    scope.previous_collecting_initializer =
        collecting_default_member_initializer_;
    current_member_record_ = record;
    current_complete_class_object_place_ = object_place;
    collecting_default_member_initializer_ = true;
    return scope;
}

void Session::finish_complete_class_initializer(
    CompleteClassInitializerScope scope) {
    current_member_record_ = scope.previous_record;
    current_complete_class_object_place_ = scope.previous_object_place;
    collecting_default_member_initializer_ =
        scope.previous_collecting_initializer;
}

Session::MemberDeclaratorThisScope
Session::begin_member_declarator_this(cir::EntityId record,
                                      bool member_is_const,
                                      bool member_is_volatile,
                                      bool is_static) {
    MemberDeclaratorThisScope scope;
    scope.previous_type = member_declarator_this_type_;
    scope.previous_active = member_declarator_this_active_;
    member_declarator_this_active_ = true;
    member_declarator_this_type_ = {};
    if (is_static || !record.valid() || !file_.valid(record)) {
        return scope;
    }

    cir::TypeRef pointee = file_.type_ref(file_.entity(record).type);
    if (member_is_const) {
        pointee.qualifiers |= cir::QualConst;
    }
    if (member_is_volatile) {
        pointee.qualifiers |= cir::QualVolatile;
    }
    member_declarator_this_type_ = builder_.pointer_type(pointee);
    return scope;
}

void Session::finish_member_declarator_this(
    MemberDeclaratorThisScope scope) {
    member_declarator_this_type_ = scope.previous_type;
    member_declarator_this_active_ = scope.previous_active;
}

ExprResult Session::collect_this_expr(SrcLoc loc) {
    ExprResult result;
    if (collecting_default_member_initializer_) {
        report_error("'this' may not be used in a default member initializer",
                     loc);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }

    if (in_lambda_body()) {
        return lambda_enclosing_this_value(loc);
    }
    if (member_declarator_this_active_) {
        if (!member_declarator_this_type_.valid()) {
            report_error(
                "'this' may only be used inside a non-static member function",
                loc);
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.this.declarator");
        result.value =
            builder_.name_ref("<this>", member_declarator_this_type_, loc);
        result.fragment = finish_fragment_block(block, previous);
        result.type = member_declarator_this_type_;
        result.category = ValueCategory::PrValue;
        return result;
    }
    if (!current_this_place_.valid()) {
        report_error("'this' may only be used inside a non-static member function",
                     loc);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.this");
    cir::InstId value = builder_.lvalue_to_rvalue(current_this_place_, loc);
    result.fragment = finish_fragment_block(block, previous);
    result.value = value;
    result.type = file_.inst(value).result_type;
    result.category = ValueCategory::PrValue;
    return result;
}

} // namespace aburi::collect
