#include "metafn_eval.h"

#include <optional>
#include <string>

#include "../cir/layout.h"
#include "../cir/type.h"

namespace {

using aburi::cir::BuiltinTypeKind;
using aburi::cir::EntityId;
using aburi::cir::EntityKind;
using aburi::cir::File;
using aburi::cir::MetaInfoKind;
using aburi::cir::TypeId;
using aburi::cir::TypeKind;
using aburi::cir::TypeRef;

ConstEvalResult unsupported(std::string why, SrcLoc loc) {
    return ConstEvalResult::unsupported(std::move(why),
                                        ConstEvalDiagCode::UnsupportedExpression,
                                        loc);
}

ConstEvalResult usize_result(uint64_t value) {
    return ConstEvalResult::constant(
        ConstValue::integer(ConstIntValue::from_unsigned(value, 64)));
}

ConstEvalResult bool_result(bool value) {
    return ConstEvalResult::constant(
        ConstValue::integer(ConstIntValue::from_unsigned(value ? 1 : 0, 64)));
}

const std::shared_ptr<ConstMetaInfoValue>& handle_of(const ConstValue& value) {
    static const std::shared_ptr<ConstMetaInfoValue> null_handle;
    if (value.kind != ConstValueKind::MetaInfo) {
        return null_handle;
    }
    return value.meta_info_value;
}

bool is_type_alias_entity(const File& file, const ConstMetaInfoValue& handle) {
    return handle.kind == MetaInfoKind::Entity && handle.entity.valid() &&
           file.valid(handle.entity) &&
           file.entity(handle.entity).kind == EntityKind::TypeAlias;
}

std::optional<TypeRef> designated_type(const File& file,
                                       const ConstMetaInfoValue& handle) {
    if (handle.kind == MetaInfoKind::Type) {
        return handle.type;
    }
    if (is_type_alias_entity(file, handle)) {
        return file.type_ref(file.entity(handle.entity).type);
    }
    return std::nullopt;
}

std::optional<TypeRef> handle_type(const File& file,
                                   const ConstMetaInfoValue& handle) {
    switch (handle.kind) {
        case MetaInfoKind::Type:
            return handle.type;
        case MetaInfoKind::Entity:
            if (handle.entity.valid() && file.valid(handle.entity)) {
                return file.type_ref(file.entity(handle.entity).type);
            }
            return std::nullopt;
        case MetaInfoKind::Value:
            return handle.boxed_type;
        default:
            return std::nullopt;
    }
}

const aburi::cir::BuiltinTypePayload* builtin_payload(const File& file,
                                                      TypeId resolved) {
    if (!file.valid(resolved) || file.type(resolved).kind != TypeKind::Builtin) {
        return nullptr;
    }
    return std::get_if<aburi::cir::BuiltinTypePayload>(
        &file.type_payload(resolved));
}

bool type_is_integral(const File& file, TypeId resolved) {
    if (file.valid(resolved) && file.type(resolved).kind == TypeKind::Enum) {
        return false;
    }
    if (file.valid(resolved) && file.type(resolved).kind == TypeKind::BitInt) {
        return true;
    }
    const auto* builtin = builtin_payload(file, resolved);
    if (!builtin) {
        return false;
    }
    switch (builtin->kind) {
        case BuiltinTypeKind::Bool:
        case BuiltinTypeKind::Char:
        case BuiltinTypeKind::SChar:
        case BuiltinTypeKind::UChar:
        case BuiltinTypeKind::Char8:
        case BuiltinTypeKind::WChar:
        case BuiltinTypeKind::Char16:
        case BuiltinTypeKind::Char32:
        case BuiltinTypeKind::Short:
        case BuiltinTypeKind::UShort:
        case BuiltinTypeKind::Int:
        case BuiltinTypeKind::UInt:
        case BuiltinTypeKind::Long:
        case BuiltinTypeKind::ULong:
        case BuiltinTypeKind::LongLong:
        case BuiltinTypeKind::ULongLong:
        case BuiltinTypeKind::Int128:
        case BuiltinTypeKind::UInt128:
        case BuiltinTypeKind::USize:
            return true;
        default:
            return false;
    }
}

bool type_is_floating(const File& file, TypeId resolved) {
    const auto* builtin = builtin_payload(file, resolved);
    if (!builtin) {
        return false;
    }
    switch (builtin->kind) {
        case BuiltinTypeKind::Float16:
        case BuiltinTypeKind::Float:
        case BuiltinTypeKind::Double:
        case BuiltinTypeKind::LongDouble:
            return true;
        default:
            return false;
    }
}

ConstEvalResult query_int(const File& file,
                          const std::vector<ConstValue>& args,
                          int64_t selector,
                          SrcLoc loc) {
    const auto& handle = handle_of(args[1]);
    if (!handle) {
        return unsupported("reflection query operand is not a reflection", loc);
    }
    auto query = static_cast<MetafnIntQuery>(selector);

    switch (query) {
        case MetafnIntQuery::SizeOf:
        case MetafnIntQuery::AlignOf: {
            std::optional<TypeRef> type = handle_type(file, *handle);
            if (!type.has_value()) {
                return unsupported("reflection has no queryable type", loc);
            }
            std::optional<size_t> value = query == MetafnIntQuery::SizeOf
                ? aburi::cir::size_of_type(file, type->type)
                : aburi::cir::align_of_type(file, type->type);
            if (!value.has_value()) {
                return unsupported("type is incomplete in reflection query",
                                   loc);
            }
            return usize_result(*value);
        }
        case MetafnIntQuery::OffsetOf:
        case MetafnIntQuery::BitOffsetOf:
        case MetafnIntQuery::BitSizeOf: {
            if (handle->kind != MetaInfoKind::Entity) {
                return unsupported(
                    "layout query requires a member reflection", loc);
            }
            const aburi::cir::RecordFieldFact* field =
                file.field_fact(handle->entity);
            if (!field) {
                return unsupported(
                    "layout query requires a non-static data member", loc);
            }
            if (query == MetafnIntQuery::OffsetOf) {
                return usize_result(field->offset);
            }
            if (query == MetafnIntQuery::BitOffsetOf) {
                return usize_result(field->is_bitfield
                                        ? field->bit_offset
                                        : field->offset * 8);
            }
            if (!field->is_bitfield) {
                return unsupported("bit_size_of requires a bit-field", loc);
            }
            return usize_result(field->bit_width);
        }
        case MetafnIntQuery::IsType:
            return bool_result(handle->kind == MetaInfoKind::Type ||
                               is_type_alias_entity(file, *handle));
        case MetafnIntQuery::IsNamespace:
            return bool_result(handle->kind == MetaInfoKind::Namespace);
        case MetafnIntQuery::IsTemplate:
            return bool_result(handle->kind == MetaInfoKind::Template);
        case MetafnIntQuery::IsValue:
            return bool_result(handle->kind == MetaInfoKind::Value);
        case MetafnIntQuery::IsFunction:
        case MetafnIntQuery::IsVariable:
        case MetafnIntQuery::IsEnumerator:
        case MetafnIntQuery::IsNonstaticDataMember:
        case MetafnIntQuery::IsStaticDataMember:
        case MetafnIntQuery::IsConstructor:
        case MetafnIntQuery::IsDestructor: {
            if (handle->kind != MetaInfoKind::Entity ||
                !file.valid(handle->entity)) {
                return bool_result(false);
            }
            EntityKind kind = file.entity(handle->entity).kind;
            switch (query) {
                case MetafnIntQuery::IsFunction:
                    return bool_result(kind == EntityKind::Function ||
                                       kind == EntityKind::Method);
                case MetafnIntQuery::IsVariable:
                    return bool_result(kind == EntityKind::Variable ||
                                       kind == EntityKind::Parameter);
                case MetafnIntQuery::IsEnumerator:
                    return bool_result(kind == EntityKind::Enumerator);
                case MetafnIntQuery::IsNonstaticDataMember:
                    return bool_result(kind == EntityKind::Field);
                case MetafnIntQuery::IsStaticDataMember:
                    return bool_result(
                        kind == EntityKind::Variable &&
                        file.entity(handle->entity).parent.valid() &&
                        file.valid(file.entity(handle->entity).parent) &&
                        file.entity(file.entity(handle->entity).parent).kind ==
                            EntityKind::Record);
                case MetafnIntQuery::IsConstructor:
                    return bool_result(kind == EntityKind::Constructor);
                case MetafnIntQuery::IsDestructor:
                    return bool_result(kind == EntityKind::Destructor);
                default:
                    return bool_result(false);
            }
        }
        case MetafnIntQuery::IsClassType:
        case MetafnIntQuery::IsUnionType:
        case MetafnIntQuery::IsEnumType: {
            if (handle->kind != MetaInfoKind::Type) {
                return bool_result(false);
            }
            TypeId resolved = file.resolved_type(handle->type.type);
            if (!file.valid(resolved)) {
                return bool_result(false);
            }
            if (query == MetafnIntQuery::IsEnumType) {
                return bool_result(file.type(resolved).kind == TypeKind::Enum);
            }
            if (file.type(resolved).kind != TypeKind::Record) {
                return bool_result(false);
            }
            const aburi::cir::RecordFacts* facts =
                file.record_facts_for_type(resolved);
            bool is_union =
                facts && facts->kind == aburi::cir::RecordKind::Union;
            return bool_result(query == MetafnIntQuery::IsUnionType
                                   ? is_union
                                   : !is_union);
        }
        case MetafnIntQuery::TypeIsSame: {
            if (args.size() < 3) {
                return unsupported("type_is_same requires two reflections",
                                   loc);
            }
            const auto& rhs = handle_of(args[2]);
            if (!rhs) {
                return unsupported(
                    "reflection query operand is not a reflection", loc);
            }
            std::optional<TypeRef> lhs_type = designated_type(file, *handle);
            std::optional<TypeRef> rhs_type = designated_type(file, *rhs);
            return bool_result(lhs_type.has_value() && rhs_type.has_value() &&
                               *lhs_type == *rhs_type);
        }
        default:
            break;
    }

    std::optional<TypeRef> classified = designated_type(file, *handle);
    if (!classified.has_value()) {
        return bool_result(false);
    }
    TypeRef type = *classified;
    TypeId resolved = file.resolved_type(type.type);
    if (!file.valid(resolved)) {
        return bool_result(false);
    }
    TypeKind kind = file.type(resolved).kind;
    switch (query) {
        case MetafnIntQuery::TypeIsIntegral:
            return bool_result(type_is_integral(file, resolved));
        case MetafnIntQuery::TypeIsFloatingPoint:
            return bool_result(type_is_floating(file, resolved));
        case MetafnIntQuery::TypeIsPointer:
            return bool_result(kind == TypeKind::Pointer);
        case MetafnIntQuery::TypeIsLValueReference:
            return bool_result(kind == TypeKind::LValueReference);
        case MetafnIntQuery::TypeIsRValueReference:
            return bool_result(kind == TypeKind::RValueReference);
        case MetafnIntQuery::TypeIsReference:
            return bool_result(kind == TypeKind::LValueReference ||
                               kind == TypeKind::RValueReference);
        case MetafnIntQuery::TypeIsArithmetic:
            return bool_result(type_is_integral(file, resolved) ||
                               type_is_floating(file, resolved));
        case MetafnIntQuery::TypeIsConst:
            return bool_result((type.qualifiers & aburi::cir::QualConst) != 0);
        case MetafnIntQuery::TypeIsVolatile:
            return bool_result((type.qualifiers & aburi::cir::QualVolatile) !=
                               0);
        case MetafnIntQuery::TypeIsFunction:
            return bool_result(kind == TypeKind::Function);
        case MetafnIntQuery::TypeIsArray:
            return bool_result(kind == TypeKind::Array);
        case MetafnIntQuery::TypeIsScalar:
            return bool_result(kind == TypeKind::Pointer ||
                               kind == TypeKind::MemberPointer ||
                               kind == TypeKind::Enum ||
                               type_is_integral(file, resolved) ||
                               type_is_floating(file, resolved) ||
                               (builtin_payload(file, resolved) &&
                                (builtin_payload(file, resolved)->kind ==
                                     BuiltinTypeKind::NullPtr ||
                                 builtin_payload(file, resolved)->kind ==
                                     BuiltinTypeKind::MetaInfo)));
        default:
            return unsupported("unknown reflection integer query", loc);
    }
}

ConstEvalResult query_info(const File& file,
                           File* mutable_file,
                           const std::vector<ConstValue>& args,
                           int64_t selector,
                           SrcLoc loc) {
    const auto& handle = handle_of(args[1]);
    if (!handle) {
        return unsupported("reflection query operand is not a reflection", loc);
    }
    auto query = static_cast<MetafnInfoQuery>(selector);

    switch (query) {
        case MetafnInfoQuery::TypeOf: {
            if (handle->kind == MetaInfoKind::Entity &&
                file.valid(handle->entity)) {
                return ConstEvalResult::constant(ConstValue::meta_info_type(
                    file.type_ref(file.entity(handle->entity).type)));
            }
            if (handle->kind == MetaInfoKind::Value &&
                handle->boxed_type.type.valid()) {
                return ConstEvalResult::constant(
                    ConstValue::meta_info_type(handle->boxed_type));
            }
            return unsupported("type_of requires an entity or value", loc);
        }
        case MetafnInfoQuery::ParentOf: {
            EntityId parent{};
            if (handle->kind == MetaInfoKind::Entity ||
                handle->kind == MetaInfoKind::Namespace ||
                handle->kind == MetaInfoKind::Template) {
                if (file.valid(handle->entity)) {
                    parent = file.entity(handle->entity).parent;
                    if (!parent.valid()) {
                        // Namespace members: the owner of the declaring
                        // context.
                        aburi::cir::DeclContextId context =
                            file.entity(handle->entity).semantic_context;
                        if (context.valid()) {
                            parent = file.decl_context(context).owner;
                        }
                    }
                }
            } else if (handle->kind == MetaInfoKind::Type) {
                TypeId resolved = file.resolved_type(handle->type.type);
                if (file.valid(resolved) &&
                    file.type(resolved).kind == TypeKind::Record) {
                    EntityId record = file.record_entity(resolved);
                    if (record.valid()) {
                        aburi::cir::DeclContextId context =
                            file.entity(record).lexical_context;
                        if (context.valid()) {
                            parent = file.decl_context(context).owner;
                        }
                    }
                }
            }
            if (!parent.valid() || !file.valid(parent)) {
                return unsupported("reflection has no parent", loc);
            }
            EntityKind kind = file.entity(parent).kind;
            MetaInfoKind handle_kind =
                (kind == EntityKind::Namespace ||
                 kind == EntityKind::TranslationUnit)
                    ? MetaInfoKind::Namespace
                    : MetaInfoKind::Entity;
            if (kind == EntityKind::Record || kind == EntityKind::Enum) {
                return ConstEvalResult::constant(ConstValue::meta_info_type(
                    file.type_ref(file.entity(parent).type)));
            }
            return ConstEvalResult::constant(
                ConstValue::meta_info_entity(handle_kind, parent));
        }
        case MetafnInfoQuery::Dealias: {
            std::optional<TypeRef> designated = designated_type(file, *handle);
            if (!designated.has_value()) {
                return unsupported("dealias requires a type reflection", loc);
            }
            TypeRef resolved = file.type_ref(
                file.resolved_type(designated->type),
                designated->qualifiers);
            return ConstEvalResult::constant(
                ConstValue::meta_info_type(resolved));
        }
        default:
            break;
    }

    std::optional<TypeRef> transform_source = designated_type(file, *handle);
    if (!transform_source.has_value() || !transform_source->type.valid()) {
        return unsupported("type transformation requires a type reflection",
                           loc);
    }
    TypeRef type = *transform_source;
    auto type_result = [&](TypeRef out) {
        return ConstEvalResult::constant(ConstValue::meta_info_type(out));
    };
    switch (query) {
        case MetafnInfoQuery::RemoveConst:
            type.qualifiers &= ~aburi::cir::QualConst;
            return type_result(type);
        case MetafnInfoQuery::RemoveVolatile:
            type.qualifiers &= ~aburi::cir::QualVolatile;
            return type_result(type);
        case MetafnInfoQuery::RemoveCv:
            type.qualifiers &=
                ~(aburi::cir::QualConst | aburi::cir::QualVolatile);
            return type_result(type);
        case MetafnInfoQuery::AddConst:
            type.qualifiers |= aburi::cir::QualConst;
            return type_result(type);
        case MetafnInfoQuery::AddVolatile:
            type.qualifiers |= aburi::cir::QualVolatile;
            return type_result(type);
        case MetafnInfoQuery::AddCv:
            type.qualifiers |=
                aburi::cir::QualConst | aburi::cir::QualVolatile;
            return type_result(type);
        case MetafnInfoQuery::AddPointer: {
            if (!mutable_file) {
                return unsupported(
                    "type transformation is unavailable in this evaluation",
                    loc);
            }
            return type_result(
                mutable_file->type_ref(mutable_file->pointer_type(type)));
        }
        case MetafnInfoQuery::RemovePointer: {
            TypeId resolved = file.resolved_type(type.type);
            if (!file.valid(resolved) ||
                file.type(resolved).kind != TypeKind::Pointer) {
                return type_result(type);
            }
            return type_result(
                file.type_ref(file.pointer_pointee_type(resolved)));
        }
        case MetafnInfoQuery::AddLValueReference:
        case MetafnInfoQuery::AddRValueReference: {
            if (!mutable_file) {
                return unsupported(
                    "type transformation is unavailable in this evaluation",
                    loc);
            }
            return type_result(mutable_file->type_ref(
                mutable_file->reference_type(
                    type,
                    query == MetafnInfoQuery::AddLValueReference
                        ? aburi::cir::ReferenceKind::LValue
                        : aburi::cir::ReferenceKind::RValue)));
        }
        case MetafnInfoQuery::RemoveReference:
        case MetafnInfoQuery::RemoveCvref: {
            TypeRef out = type;
            TypeId resolved = file.resolved_type(out.type);
            if (file.valid(resolved) &&
                (file.type(resolved).kind == TypeKind::LValueReference ||
                 file.type(resolved).kind == TypeKind::RValueReference)) {
                out = file.type_ref(file.reference_referred_type(resolved));
            }
            if (query == MetafnInfoQuery::RemoveCvref) {
                out.qualifiers &=
                    ~(aburi::cir::QualConst | aburi::cir::QualVolatile);
            }
            return type_result(out);
        }
        default:
            return unsupported("unknown reflection type query", loc);
    }
}

ConstEvalResult query_name(const File& file,
                           EvalMemory& memory,
                           const std::vector<ConstValue>& args,
                           int64_t selector,
                           bool want_data,
                           SrcLoc loc) {
    const auto& handle = handle_of(args[1]);
    if (!handle) {
        return unsupported("reflection query operand is not a reflection", loc);
    }
    auto query = static_cast<MetafnNameQuery>(selector);
    std::string name;
    switch (handle->kind) {
        case MetaInfoKind::Type: {

            TypeId direct = handle->type.type;
            EntityId named{};
            if (file.valid(direct)) {
                if (file.type(direct).kind == TypeKind::Typedef) {
                    const auto* payload = std::get_if<aburi::cir::TypedefTypePayload>(
                        &file.type_payload(direct));
                    if (payload) {
                        named = payload->entity;
                    }
                }
                TypeId resolved = file.resolved_type(direct);
                if (!named.valid() && file.valid(resolved)) {
                    if (file.type(resolved).kind == TypeKind::Record) {
                        named = file.record_entity(resolved);
                    } else if (file.type(resolved).kind == TypeKind::Enum) {
                        named = std::get<aburi::cir::EnumTypePayload>(
                                    file.type_payload(resolved))
                                    .entity;
                    }
                }
            }
            if (file.type(direct).kind == TypeKind::Typedef ||
                !file.valid(file.resolved_type(direct)) ||
                named.valid()) {
                if (named.valid() && file.valid(named) &&
                    file.entity(named).name.valid()) {
                    name = std::string(file.name(file.entity(named).name));
                    break;
                }
            }
            name = file.format_type(handle->type.type);
            break;
        }
        case MetaInfoKind::Entity:
        case MetaInfoKind::Namespace:
        case MetaInfoKind::Template:
            if (file.valid(handle->entity) &&
                file.entity(handle->entity).name.valid()) {
                name = std::string(file.name(file.entity(handle->entity).name));
            }
            break;
        default:
            break;
    }
    if (query == MetafnNameQuery::DisplayNameOf && name.empty()) {
        name = "<unnamed>";
    }
    if (!want_data) {
        return usize_result(name.size());
    }
    uint64_t allocation = memory.allocate(name.size() + 1);
    std::vector<uint8_t> bytes(name.begin(), name.end());
    bytes.push_back(0);
    memory.store_bytes(allocation, 0, bytes);
    return ConstEvalResult::constant(
        ConstValue::allocation_address(allocation));
}

std::vector<ConstValue> range_elements(const File& file,
                                       const ConstMetaInfoValue& handle,
                                       MetafnRangeQuery query) {
    std::vector<ConstValue> out;
    auto record_facts = [&]() -> const aburi::cir::RecordFacts* {
        std::optional<TypeRef> type = designated_type(file, handle);
        if (!type.has_value()) {
            return nullptr;
        }
        TypeId resolved = file.resolved_type(type->type);
        if (!file.valid(resolved) ||
            file.type(resolved).kind != TypeKind::Record) {
            return nullptr;
        }
        return file.record_facts_for_type(resolved);
    };
    switch (query) {
        case MetafnRangeQuery::NonstaticDataMembersOf: {
            const aburi::cir::RecordFacts* facts = record_facts();
            if (!facts) {
                break;
            }
            for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member || !field.entity.valid()) {
                    continue;
                }
                out.push_back(ConstValue::meta_info_entity(
                    MetaInfoKind::Entity, field.entity));
            }
            break;
        }
        case MetafnRangeQuery::StaticDataMembersOf: {
            const aburi::cir::RecordFacts* facts = record_facts();
            if (!facts) {
                break;
            }
            for (const aburi::cir::RecordStaticDataMemberFact& member :
                 facts->static_data_members) {
                if (member.entity.valid()) {
                    out.push_back(ConstValue::meta_info_entity(
                        MetaInfoKind::Entity, member.entity));
                }
            }
            break;
        }
        case MetafnRangeQuery::BasesOf: {
            const aburi::cir::RecordFacts* facts = record_facts();
            if (!facts) {
                break;
            }
            for (const aburi::cir::RecordBaseFact& base : facts->bases) {
                if (base.type.type.valid()) {
                    out.push_back(ConstValue::meta_info_type(base.type));
                }
            }
            break;
        }
        case MetafnRangeQuery::MembersOf: {

            if (handle.kind == MetaInfoKind::Namespace &&
                file.valid(handle.entity)) {
                aburi::cir::DeclContextId context =
                    file.entity(handle.entity).semantic_context;
                if (!context.valid()) {
                    break;
                }
                std::vector<uint32_t> seen;
                for (aburi::cir::BindingId binding_id :
                     file.decl_context(context).bindings) {
                    const aburi::cir::Binding& binding =
                        file.binding(binding_id);
                    if (binding.entities.empty()) {
                        continue;
                    }
                    aburi::cir::EntityId entity = binding.entities.back();
                    if (!entity.valid() || !file.valid(entity)) {
                        continue;
                    }

                    bool duplicate = false;
                    for (uint32_t index : seen) {
                        if (index == entity.index) {
                            duplicate = true;
                            break;
                        }
                    }
                    if (duplicate) {
                        continue;
                    }
                    seen.push_back(entity.index);
                    EntityKind kind = file.entity(entity).kind;
                    if (kind == EntityKind::Namespace) {
                        out.push_back(ConstValue::meta_info_entity(
                            MetaInfoKind::Namespace, entity));
                    } else if (kind == EntityKind::Record ||
                               kind == EntityKind::Enum) {
                        out.push_back(ConstValue::meta_info_type(
                            file.type_ref(file.entity(entity).type)));
                    } else {
                        out.push_back(ConstValue::meta_info_entity(
                            MetaInfoKind::Entity, entity));
                    }
                }
                break;
            }
            const aburi::cir::RecordFacts* facts = record_facts();
            if (!facts) {
                break;
            }
            for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member || !field.entity.valid()) {
                    continue;
                }
                out.push_back(ConstValue::meta_info_entity(
                    MetaInfoKind::Entity, field.entity));
            }
            for (const aburi::cir::RecordStaticDataMemberFact& member :
                 facts->static_data_members) {
                if (member.entity.valid()) {
                    out.push_back(ConstValue::meta_info_entity(
                        MetaInfoKind::Entity, member.entity));
                }
            }
            for (const aburi::cir::RecordMethodFact& method : facts->methods) {
                if (method.entity.valid()) {
                    out.push_back(ConstValue::meta_info_entity(
                        MetaInfoKind::Entity, method.entity));
                }
            }
            break;
        }
        case MetafnRangeQuery::EnumeratorsOf: {
            std::optional<TypeRef> type = designated_type(file, handle);
            if (!type.has_value()) {
                break;
            }
            TypeId resolved = file.resolved_type(type->type);
            if (!file.valid(resolved) ||
                file.type(resolved).kind != TypeKind::Enum) {
                break;
            }
            EntityId owner =
                std::get<aburi::cir::EnumTypePayload>(file.type_payload(resolved))
                    .entity;
            if (!owner.valid() || !file.valid(owner)) {
                break;
            }
            aburi::cir::DeclContextId context =
                file.entity(owner).semantic_context;
            if (!context.valid()) {
                break;
            }
            for (aburi::cir::BindingId binding_id :
                 file.decl_context(context).bindings) {
                const aburi::cir::Binding& binding = file.binding(binding_id);
                for (aburi::cir::EntityId entity : binding.entities) {
                    if (entity.valid() && file.valid(entity) &&
                        file.entity(entity).kind == EntityKind::Enumerator) {
                        out.push_back(ConstValue::meta_info_entity(
                            MetaInfoKind::Entity, entity));
                    }
                }
            }
            break;
        }
    }
    return out;
}

ConstEvalResult query_range(const File& file,
                            const std::vector<ConstValue>& args,
                            int64_t selector,
                            bool want_count,
                            SrcLoc loc) {
    const auto& handle = handle_of(args[1]);
    if (!handle) {
        return unsupported("reflection query operand is not a reflection", loc);
    }
    std::vector<ConstValue> elements =
        range_elements(file, *handle, static_cast<MetafnRangeQuery>(selector));
    if (want_count) {
        return usize_result(elements.size());
    }
    if (args.size() < 3) {
        return unsupported("range element query is missing its index", loc);
    }
    std::optional<int64_t> index = args[2].try_as_int64();
    if (!index.has_value() || *index < 0 ||
        static_cast<size_t>(*index) >= elements.size()) {
        return unsupported("range element index is out of bounds", loc);
    }
    return ConstEvalResult::constant(elements[static_cast<size_t>(*index)]);
}

} // namespace

ConstEvalResult evaluate_metafunction(BuiltinKind kind,
                                      const aburi::cir::File& file,
                                      aburi::cir::File* mutable_file,
                                      EvalMemory& memory,
                                      const std::vector<ConstValue>& args,
                                      aburi::cir::TypeId result_type,
                                      SrcLoc loc) {
    (void)result_type;
    if (args.size() < 2) {
        return unsupported("reflection query is missing its operands", loc);
    }
    std::optional<int64_t> selector = args[0].try_as_int64();
    if (!selector.has_value()) {
        return unsupported("reflection query selector is not a constant", loc);
    }
    switch (kind) {
        case BuiltinKind::METAFN_QUERY_INT:
            return query_int(file, args, *selector, loc);
        case BuiltinKind::METAFN_QUERY_INFO:
            return query_info(file, mutable_file, args, *selector, loc);
        case BuiltinKind::METAFN_NAME_DATA:
            return query_name(file, memory, args, *selector, true, loc);
        case BuiltinKind::METAFN_NAME_SIZE:
            return query_name(file, memory, args, *selector, false, loc);
        case BuiltinKind::METAFN_RANGE_COUNT:
            return query_range(file, args, *selector, true, loc);
        case BuiltinKind::METAFN_RANGE_AT:
            return query_range(file, args, *selector, false, loc);
        default:
            return unsupported("unknown reflection metafunction", loc);
    }
}
