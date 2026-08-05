#include "layout.h"

#include <algorithm>
#include <variant>

namespace aburi::cir {
namespace {

BuiltinTypeKind builtin_kind(const File& file, TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != TypeKind::Builtin) {
        return BuiltinTypeKind::Other;
    }
    const auto* builtin = std::get_if<BuiltinTypePayload>(&file.type_payload(type));
    return builtin ? builtin->kind : BuiltinTypeKind::Other;
}

size_t bytes_for_bits(int bits) {
    return static_cast<size_t>(std::max(1, (bits + 7) / 8));
}

size_t next_power_of_two(size_t value) {
    if (value <= 1) {
        return 1;
    }
    size_t power = 1;
    while (power < value) {
        power <<= 1;
    }
    return power;
}

std::optional<TypeSizeAlign> builtin_size_align(BuiltinTypeKind kind,
                                                const TargetInfo& target) {
    size_t pointer_bytes = bytes_for_bits(target.pointer_width);
    size_t long_bytes = bytes_for_bits(target.long_width);
    size_t wchar_bytes = bytes_for_bits(target.wchar_width);
    switch (kind) {
        case BuiltinTypeKind::Void:
            return TypeSizeAlign{1, 1};
        case BuiltinTypeKind::NullPtr:
        case BuiltinTypeKind::USize:
        case BuiltinTypeKind::MetaInfo:
            return TypeSizeAlign{pointer_bytes, pointer_bytes};
        case BuiltinTypeKind::Bool:
        case BuiltinTypeKind::Char:
        case BuiltinTypeKind::SChar:
        case BuiltinTypeKind::UChar:
        case BuiltinTypeKind::Char8:
            return TypeSizeAlign{1, 1};
        case BuiltinTypeKind::Short:
        case BuiltinTypeKind::UShort:
        case BuiltinTypeKind::Char16:
        case BuiltinTypeKind::Float16:
            return TypeSizeAlign{2, 2};
        case BuiltinTypeKind::Int:
        case BuiltinTypeKind::UInt:
        case BuiltinTypeKind::Char32:
        case BuiltinTypeKind::Float:
            return TypeSizeAlign{4, 4};
        case BuiltinTypeKind::WChar:
            return TypeSizeAlign{wchar_bytes, wchar_bytes};
        case BuiltinTypeKind::Long:
        case BuiltinTypeKind::ULong:
            return TypeSizeAlign{long_bytes, long_bytes};
        case BuiltinTypeKind::LongLong:
        case BuiltinTypeKind::ULongLong:
        case BuiltinTypeKind::Double:
            return TypeSizeAlign{8, 8};
        case BuiltinTypeKind::Int128:
        case BuiltinTypeKind::UInt128:
            return TypeSizeAlign{16, 16};
        case BuiltinTypeKind::LongDouble:
            if (target.long_double_format == LongDoubleFormat::IEEE_DOUBLE) {
                return TypeSizeAlign{8, 8};
            }

            if (target.long_double_storage_bytes > 0) {
                return TypeSizeAlign{
                    static_cast<size_t>(target.long_double_storage_bytes),
                    static_cast<size_t>(std::max(1, target.long_double_align_bytes))};
            }
            return TypeSizeAlign{16, 16};
        case BuiltinTypeKind::Other:
            return std::nullopt;
    }
    return std::nullopt;
}

uint16_t builtin_integer_width(BuiltinTypeKind kind, const TargetInfo& target) {
    switch (kind) {
        case BuiltinTypeKind::Bool:
        case BuiltinTypeKind::Char:
        case BuiltinTypeKind::SChar:
        case BuiltinTypeKind::UChar:
        case BuiltinTypeKind::Char8:
            return 8;
        case BuiltinTypeKind::Short:
        case BuiltinTypeKind::UShort:
        case BuiltinTypeKind::Char16:
            return 16;
        case BuiltinTypeKind::Int:
        case BuiltinTypeKind::UInt:
        case BuiltinTypeKind::Char32:
            return 32;
        case BuiltinTypeKind::WChar:
            return static_cast<uint16_t>(target.wchar_width);
        case BuiltinTypeKind::Long:
        case BuiltinTypeKind::ULong:
            return static_cast<uint16_t>(target.long_width);
        case BuiltinTypeKind::LongLong:
        case BuiltinTypeKind::ULongLong:
            return 64;
        case BuiltinTypeKind::NullPtr:
        case BuiltinTypeKind::USize:
        case BuiltinTypeKind::MetaInfo:
            return static_cast<uint16_t>(target.pointer_width);
        case BuiltinTypeKind::Int128:
        case BuiltinTypeKind::UInt128:
            return 128;
        default:
            return 64;
    }
}

bool builtin_is_unsigned(BuiltinTypeKind kind, const TargetInfo& target) {
    switch (kind) {
        case BuiltinTypeKind::Bool:
        case BuiltinTypeKind::UChar:
        case BuiltinTypeKind::Char8:
        case BuiltinTypeKind::UShort:
        case BuiltinTypeKind::UInt:
        case BuiltinTypeKind::ULong:
        case BuiltinTypeKind::ULongLong:
        case BuiltinTypeKind::UInt128:
        case BuiltinTypeKind::USize:
        case BuiltinTypeKind::NullPtr:
        case BuiltinTypeKind::MetaInfo:
        case BuiltinTypeKind::Char16:
        case BuiltinTypeKind::Char32:
            return true;
        case BuiltinTypeKind::Char:
            return target.char_is_unsigned;
        case BuiltinTypeKind::WChar:
            return target.wchar_is_unsigned;
        default:
            return false;
    }
}

bool builtin_is_integer_like(BuiltinTypeKind kind) {
    switch (kind) {
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

} // namespace

std::optional<TypeSizeAlign> size_align_of_type(const File& file, TypeId type_id) {
    return size_align_of_type(file, type_id, file.target_info());
}

std::optional<TypeSizeAlign> size_align_of_type(const File& file,
                                                TypeId type_id,
                                                const TargetInfo& target) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id)) {
        return std::nullopt;
    }

    const Type& type = file.type(type_id);
    const TypePayload& payload = file.type_payload(type_id);
    switch (type.kind) {
        case TypeKind::Builtin: {
            const auto* builtin = std::get_if<BuiltinTypePayload>(&payload);
            return builtin ? builtin_size_align(builtin->kind, target) : std::nullopt;
        }
        case TypeKind::Pointer:
        case TypeKind::BlockPointer:
        case TypeKind::LValueReference:
        case TypeKind::RValueReference:
            return TypeSizeAlign{bytes_for_bits(target.pointer_width),
                                 bytes_for_bits(target.pointer_width)};
        case TypeKind::MemberPointer: {
            size_t pointer_bytes = bytes_for_bits(target.pointer_width);
            size_t size = file.member_pointer_points_to_function(type_id)
                ? pointer_bytes * 2
                : pointer_bytes;
            return TypeSizeAlign{size, pointer_bytes};
        }
        case TypeKind::Function:
            return TypeSizeAlign{1, 1};
        case TypeKind::Array: {
            const auto* array = std::get_if<ArrayTypePayload>(&payload);
            if (!array || !array->size.has_value()) {
                return std::nullopt;
            }
            auto element = size_align_of_type(file, array->element_type.type, target);
            if (!element) {
                return std::nullopt;
            }
            return TypeSizeAlign{element->size_bytes * *array->size,
                                 element->alignment_bytes};
        }
        case TypeKind::Record: {
            const RecordFacts* facts = file.record_facts_for_type(type_id);
            if (!facts || facts->is_incomplete) {
                return std::nullopt;
            }
            return TypeSizeAlign{(facts->size_bits + 7) / 8,
                                 facts->alignment > 0 ? facts->alignment : 1};
        }
        case TypeKind::Enum: {
            const auto* enum_payload = std::get_if<EnumTypePayload>(&payload);
            if (enum_payload && enum_payload->underlying_type.valid()) {
                return size_align_of_type(file, enum_payload->underlying_type.type, target);
            }
            return TypeSizeAlign{4, 4};
        }
        case TypeKind::Vector: {
            const auto* vector = std::get_if<VectorTypePayload>(&payload);
            if (!vector || !vector->element_type.valid() ||
                vector->element_count == 0 || vector->size_bytes == 0) {
                return std::nullopt;
            }
            auto element = size_align_of_type(file, vector->element_type.type, target);
            if (!element) {
                return std::nullopt;
            }
            size_t preferred = next_power_of_two(
                static_cast<size_t>(vector->size_bytes));
            size_t capped = std::min<size_t>(
                preferred,
                target.max_alignment_bytes > 0 ? target.max_alignment_bytes : 1);
            return TypeSizeAlign{
                static_cast<size_t>(vector->size_bytes),
                std::max<size_t>(element->alignment_bytes, std::max<size_t>(1, capped))};
        }
        case TypeKind::Complex: {
            const auto* complex = std::get_if<ComplexTypePayload>(&payload);
            if (!complex || !complex->element_type.valid()) {
                return std::nullopt;
            }
            auto element = size_align_of_type(file, complex->element_type.type, target);
            if (!element) {
                return std::nullopt;
            }
            return TypeSizeAlign{element->size_bytes * 2,
                                 element->alignment_bytes};
        }
        case TypeKind::BitInt: {
            const auto* bit_int = std::get_if<BitIntTypePayload>(&payload);
            if (!bit_int || bit_int->bits == 0 || bit_int->bits > 128) {
                return std::nullopt;
            }

            size_t bytes = 1;
            while (bytes * 8 < bit_int->bits) {
                bytes *= 2;
            }
            return TypeSizeAlign{bytes, bytes};
        }
        case TypeKind::Typedef: {
            const auto* typedef_payload = std::get_if<TypedefTypePayload>(&payload);
            if (typedef_payload && typedef_payload->underlying_type.valid()) {
                return size_align_of_type(file, typedef_payload->underlying_type.type, target);
            }
            return std::nullopt;
        }
        default:
            return std::nullopt;
    }
}

std::optional<size_t> size_of_type(const File& file, TypeId type) {
    auto size_align = size_align_of_type(file, type);
    return size_align ? std::optional<size_t>(size_align->size_bytes) : std::nullopt;
}

std::optional<size_t> align_of_type(const File& file, TypeId type) {

    TypeId resolved = file.resolved_type(type);
    if (file.valid(resolved) &&
        file.type(resolved).kind == TypeKind::Array) {
        const auto* array =
            std::get_if<ArrayTypePayload>(&file.type_payload(resolved));
        if (array) {
            return align_of_type(file, array->element_type.type);
        }
    }
    auto size_align = size_align_of_type(file, type);
    return size_align ? std::optional<size_t>(size_align->alignment_bytes) : std::nullopt;
}

bool is_integer_like_type(const File& file, TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return false;
    }
    const TypePayload& payload = file.type_payload(type);
    if (file.type(type).kind == TypeKind::Enum) {
        return true;
    }
    if (file.type(type).kind == TypeKind::Typedef) {
        const auto* typedef_payload = std::get_if<TypedefTypePayload>(&payload);
        return typedef_payload &&
               is_integer_like_type(file, typedef_payload->underlying_type.type);
    }
    if (file.type(type).kind == TypeKind::BitInt) {
        return true;
    }
    return file.type(type).kind == TypeKind::Builtin &&
           builtin_is_integer_like(builtin_kind(file, type));
}

bool is_floating_type(const File& file, TypeId type) {
    switch (builtin_kind(file, type)) {
        case BuiltinTypeKind::Float16:
        case BuiltinTypeKind::Float:
        case BuiltinTypeKind::Double:
        case BuiltinTypeKind::LongDouble:
            return true;
        default:
            return false;
    }
}

IntegerTypeShape integer_shape_for_type(const File& file, TypeId type) {
    return integer_shape_for_type(file, type, file.target_info());
}

IntegerTypeShape integer_shape_for_type(const File& file,
                                        TypeId type,
                                        const TargetInfo& target) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return {};
    }

    const TypePayload& payload = file.type_payload(type);
    if (file.type(type).kind == TypeKind::Enum) {
        const auto* enum_payload = std::get_if<EnumTypePayload>(&payload);
        if (enum_payload && enum_payload->underlying_type.valid()) {
            return integer_shape_for_type(file, enum_payload->underlying_type.type, target);
        }
        return {32, false};
    }
    if (file.type(type).kind == TypeKind::Typedef) {
        const auto* typedef_payload = std::get_if<TypedefTypePayload>(&payload);
        if (typedef_payload && typedef_payload->underlying_type.valid()) {
            return integer_shape_for_type(file, typedef_payload->underlying_type.type, target);
        }
        return {};
    }
    if (file.type(type).kind == TypeKind::BitInt) {
        const auto* bit_int = std::get_if<BitIntTypePayload>(&payload);
        if (bit_int) {
            return {static_cast<uint16_t>(bit_int->bits), bit_int->is_unsigned};
        }
        return {};
    }

    BuiltinTypeKind kind = builtin_kind(file, type);
    return {builtin_integer_width(kind, target), builtin_is_unsigned(kind, target)};
}

bool type_has_known_no_padding(const File& file, TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return false;
    }
    std::optional<size_t> size = size_of_type(file, type);
    if (is_integer_like_type(file, type)) {
        IntegerTypeShape shape = integer_shape_for_type(file, type);
        return size.has_value() && *size * 8 == shape.bit_width;
    }

    switch (file.type(type).kind) {
        case TypeKind::Pointer:
        case TypeKind::BlockPointer:
        case TypeKind::MemberPointer:
            return true;
        case TypeKind::Builtin: {
            switch (builtin_kind(file, type)) {
                case BuiltinTypeKind::NullPtr:
                case BuiltinTypeKind::Float16:
                case BuiltinTypeKind::Float:
                case BuiltinTypeKind::Double:
                    return true;
                case BuiltinTypeKind::LongDouble:
                    return file.target_info().long_double_format !=
                        LongDoubleFormat::X87_EXTENDED;
                default:
                    return false;
            }
        }
        case TypeKind::Array: {
            const auto* array = std::get_if<ArrayTypePayload>(
                &file.type_payload(type));
            return size.has_value() && array &&
                type_has_known_no_padding(file, array->element_type.type);
        }
        case TypeKind::Vector: {
            const auto* vector = std::get_if<VectorTypePayload>(
                &file.type_payload(type));
            std::optional<size_t> element_size =
                vector
                    ? size_of_type(file, vector->element_type.type)
                    : std::nullopt;
            return vector && size.has_value() && element_size.has_value() &&
                *size == *element_size * vector->element_count &&
                type_has_known_no_padding(file, vector->element_type.type);
        }
        case TypeKind::Complex: {
            const auto* complex = std::get_if<ComplexTypePayload>(
                &file.type_payload(type));
            std::optional<size_t> element_size =
                complex
                    ? size_of_type(file, complex->element_type.type)
                    : std::nullopt;
            return complex && size.has_value() && element_size.has_value() &&
                *size == *element_size * 2 &&
                type_has_known_no_padding(file, complex->element_type.type);
        }
        default:
            return false;
    }
}

uint32_t bitfield_value_width(const File& file,
                              const RecordFieldFact& field) {
    uint32_t declared_width = field.bit_width;
    uint32_t type_width = integer_shape_for_type(file, field.type.type).bit_width;
    if (declared_width == 0 || type_width == 0) {
        return declared_width;
    }
    return std::min(declared_width, type_width);
}

bool type_has_mutable_subobject(const File& file, TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type)) {
        return false;
    }
    if (file.type(type).kind == TypeKind::Array) {
        const auto* array =
            std::get_if<ArrayTypePayload>(&file.type_payload(type));
        return array &&
            type_has_mutable_subobject(file, array->element_type.type);
    }
    if (file.type(type).kind != TypeKind::Record) {
        return false;
    }
    const RecordFacts* facts = file.record_facts_for_type(type);
    if (!facts) {
        return false;
    }
    for (const RecordFieldFact& field : facts->fields) {
        if (field.is_mutable ||
            type_has_mutable_subobject(file, field.type.type)) {
            return true;
        }
    }
    return false;
}

} // namespace aburi::cir
