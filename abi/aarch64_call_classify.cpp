#include "aarch64_call_classify.h"

#include <algorithm>
#include <optional>
#include <variant>

#include "../cir/layout.h"

namespace aburi::abi {

namespace {

bool is_aarch64_aapcs(const TargetInfo& target) {
    return target.arch == TargetArch::AARCH64 &&
           (target.os == TargetOS::MACOS || target.os == TargetOS::LINUX);
}

bool is_hfa_builtin_kind(cir::BuiltinTypeKind kind, const TargetInfo& target) {
    switch (kind) {
        case cir::BuiltinTypeKind::Float16:
        case cir::BuiltinTypeKind::Float:
        case cir::BuiltinTypeKind::Double:
            return true;
        case cir::BuiltinTypeKind::LongDouble:

            return target.long_double_format == LongDoubleFormat::IEEE_QUAD;
        default:
            return false;
    }
}

cir::BuiltinTypeKind normalize_hfa_builtin_kind(cir::BuiltinTypeKind kind,
                                                const TargetInfo& target) {
    if (kind == cir::BuiltinTypeKind::LongDouble &&
        target.long_double_format == LongDoubleFormat::IEEE_DOUBLE) {
        return cir::BuiltinTypeKind::Double;
    }
    return kind;
}

uint8_t int_slot_count_for_size(uint64_t size_bytes) {
    return static_cast<uint8_t>(std::max<uint64_t>(1, (size_bytes + 7) / 8));
}

} // namespace

bool is_complete_record_type(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) || file.type(type_id).kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file.record_facts_for_type(type_id);
    return facts && !facts->is_incomplete;
}

bool is_empty_record_abi_ignored(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) || file.type(type_id).kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file.record_facts_for_type(type_id);
    return facts && !facts->is_incomplete &&
           facts->kind != cir::RecordKind::Union &&
           facts->is_empty == cir::ClassPropertyState::True;
}

bool collect_hfa_members(const cir::File& file,
                                const TargetInfo& target,
                                cir::TypeRef type,
                                cir::BuiltinTypeKind& element_kind,
                                unsigned& element_count) {
    if (!file.valid(type.type)) {
        return false;
    }
    cir::TypeId type_id = file.resolved_type(type.type);
    if (!file.valid(type_id)) {
        return false;
    }

    const cir::Type& cir_type = file.type(type_id);
    const cir::TypePayload& payload = file.type_payload(type_id);
    if (cir_type.kind == cir::TypeKind::Builtin) {
        cir::BuiltinTypeKind candidate =
            normalize_hfa_builtin_kind(std::get<cir::BuiltinTypePayload>(payload).kind,
                                       target);
        if (!is_hfa_builtin_kind(candidate, target)) {
            return false;
        }
        if (element_count == 0) {
            element_kind = candidate;
        } else if (element_kind != candidate) {
            return false;
        }
        ++element_count;
        return element_count <= 4;
    }

    if (cir_type.kind == cir::TypeKind::Array) {
        const auto& array = std::get<cir::ArrayTypePayload>(payload);
        if (array.size_kind != cir::ArraySizeKind::Constant ||
            !array.size.has_value() ||
            *array.size == 0 ||
            *array.size > 4) {
            return false;
        }
        for (size_t i = 0; i < *array.size; ++i) {
            if (!collect_hfa_members(file,
                                            target,
                                            array.element_type,
                                            element_kind,
                                            element_count)) {
                return false;
            }
        }
        return true;
    }

    if (cir_type.kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file.record_facts_for_type(type_id);
    if (!facts || facts->is_incomplete || facts->kind == cir::RecordKind::Union) {
        return false;
    }
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.subobject_size == cir::SubobjectSizeKind::Zero) {
            continue;
        }
        if (field.is_bitfield ||
            field.storage_size_override > 0 ||
            field.storage_alignment_override > 0) {
            return false;
        }
        if (!collect_hfa_members(file, target, field.type,
                                        element_kind, element_count)) {
            return false;
        }
    }
    return element_count > 0 && element_count <= 4;
}

AggregateClass classify_aarch64_argument(const cir::File& file,
                                                cir::TypeRef type,
                                                const TargetInfo* target) {
    AggregateClass result;
    if (!target || !is_aarch64_aapcs(*target) ||
        !is_complete_record_type(file, type.type)) {
        return result;
    }

    auto size_align = cir::size_align_of_type(file, type.type);
    if (!size_align) {
        return result;
    }
    result.byte_size = size_align->size_bytes;

    if (is_empty_record_abi_ignored(file, type.type)) {

        if (target->os == TargetOS::MACOS || size_align->size_bytes == 0) {
            result.pass = AggregatePass::Ignore;
            return result;
        }
        result.pass = AggregatePass::CoerceIntSlots;
        result.int_slot_count = 1;
        return result;
    }

    cir::BuiltinTypeKind hfa_kind = cir::BuiltinTypeKind::Other;
    unsigned hfa_count = 0;
    if (collect_hfa_members(file, *target, type, hfa_kind, hfa_count) &&
        hfa_count > 0 &&
        hfa_count <= 4) {
        result.pass = AggregatePass::CoerceHfa;
        result.hfa_element = hfa_kind;
        result.hfa_count = static_cast<uint8_t>(hfa_count);
        return result;
    }

    if (size_align->size_bytes > 16) {
        result.pass = AggregatePass::Indirect;
        return result;
    }

    result.pass = AggregatePass::CoerceIntSlots;
    result.int_slot_count = int_slot_count_for_size(size_align->size_bytes);
    return result;
}

namespace {

std::optional<AggregateClass> classify_complex(const cir::File& file,
                                               cir::TypeRef type,
                                               const TargetInfo& target,
                                               bool is_vararg) {
    cir::TypeId resolved = file.resolved_type(type.type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Complex) {
        return std::nullopt;
    }
    auto size_align = cir::size_align_of_type(file, resolved);
    if (!size_align) {
        return std::nullopt;
    }
    AggregateClass result;
    result.byte_size = size_align->size_bytes;

    const auto& payload =
        std::get<cir::ComplexTypePayload>(file.type_payload(resolved));
    cir::TypeId element = file.resolved_type(payload.element_type.type);
    cir::BuiltinTypeKind element_kind = cir::BuiltinTypeKind::Other;
    if (file.valid(element) &&
        file.type(element).kind == cir::TypeKind::Builtin) {
        element_kind = normalize_hfa_builtin_kind(
            std::get<cir::BuiltinTypePayload>(file.type_payload(element)).kind,
            target);
    }

    if (!is_vararg && is_hfa_builtin_kind(element_kind, target)) {
        result.pass = AggregatePass::CoerceHfa;
        result.hfa_element = element_kind;
        result.hfa_count = 2;
        return result;
    }

    if (size_align->size_bytes > 16) {
        result.pass = AggregatePass::Indirect;
        return result;
    }
    result.pass = AggregatePass::CoerceIntSlots;
    result.int_slot_count = int_slot_count_for_size(size_align->size_bytes);
    return result;
}

} // namespace

AggregateClass classify_aarch64_argument_native(const cir::File& file,
                                                       cir::TypeRef type,
                                                       const TargetInfo* target) {
    if (target && is_aarch64_aapcs(*target)) {
        if (auto complex = classify_complex(file, type, *target, false)) {
            return *complex;
        }
    }
    return classify_aarch64_argument(file, type, target);
}

AggregateClass classify_aarch64_vararg_native(const cir::File& file,
                                                     cir::TypeRef type,
                                                     const TargetInfo* target) {
    if (target && target->va_list_kind != VaListKind::CHAR_PTR) {

        return classify_aarch64_argument_native(file, type, target);
    }
    if (target && target->va_list_kind == VaListKind::CHAR_PTR) {
        if (auto complex = classify_complex(file, type, *target, true)) {
            return *complex;
        }
    }
    return classify_aarch64_vararg(file, type, target);
}

AggregateClass classify_aarch64_vararg(const cir::File& file,
                                              cir::TypeRef type,
                                              const TargetInfo* target) {
    AggregateClass result;
    if (!target) {
        return result;
    }
    if (target->va_list_kind != VaListKind::CHAR_PTR) {

        return classify_aarch64_argument(file, type, target);
    }
    if (!is_complete_record_type(file, type.type)) {
        return result;
    }

    auto size_align = cir::size_align_of_type(file, type.type);
    if (!size_align) {
        return result;
    }
    result.byte_size = size_align->size_bytes;

    if (size_align->size_bytes > 16) {
        result.pass = AggregatePass::Indirect;
        return result;
    }

    result.pass = AggregatePass::CoerceIntSlots;
    result.int_slot_count = int_slot_count_for_size(size_align->size_bytes);
    return result;
}

} // namespace aburi::abi
