#include "constant_state.h"

#include "../cir/file.h"
#include "../cir/layout.h"
#include "../abi/endian.h"
#include "../numeric/floating_cir.h"

namespace {

using aburi::cir::ConstantLifetimeState;
using aburi::cir::ConstantStateFact;
using aburi::cir::ConstantStateKind;
using aburi::cir::TypeId;

bool fail(std::string* error, std::string message) {
    if (error) {
        *error = std::move(message);
    }
    return false;
}

bool build_state(const aburi::cir::File& file,
                 TypeId type,
                 const ConstValue& value,
                 ConstantStateFact& out,
                 std::string* error,
                 const ConstantStateAddressPolicy* address_is_durable) {
    TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return fail(error, "constant state has an invalid type");
    }
    out = ConstantStateFact{};
    out.type = file.type_ref(type);
    out.initialized = value.kind != ConstValueKind::Invalid;
    out.lifetime = ConstantLifetimeState::Alive;

    switch (value.kind) {
        case ConstValueKind::Integer: {
            out.kind = ConstantStateKind::Integer;
            aburi::cir::IntegerTypeShape shape =
                aburi::cir::integer_shape_for_type(file, resolved);
            out.integer_value = value.int_value.cast(shape.bit_width,
                                                     shape.is_unsigned);
            return true;
        }
        case ConstValueKind::Boolean:
            out.kind = ConstantStateKind::Boolean;
            out.boolean_value = value.bool_value;
            return true;
        case ConstValueKind::Floating:
            out.kind = ConstantStateKind::Floating;
            out.floating_value = value.float_value.value;
            return true;
        case ConstValueKind::Complex:
            if (!value.complex_value.valid()) {
                return fail(error, "complex constant has mismatched component formats");
            }
            out.kind = ConstantStateKind::Complex;
            if (value.complex_value.has_integer_components) {
                out.complex_is_integer = true;
                out.complex_integer_real =
                    value.complex_value.integer_real;
                out.complex_integer_imag =
                    value.complex_value.integer_imag;
                return true;
            }
            out.floating_real = value.complex_value.real;
            out.floating_imag = value.complex_value.imag;
            return true;
        case ConstValueKind::Null:
            out.kind = ConstantStateKind::Null;
            switch (value.null_kind) {
                case ConstNullKind::Nullptr:
                    out.null_kind = aburi::cir::TemplateNullKind::Nullptr;
                    break;
                case ConstNullKind::Pointer:
                    out.null_kind = aburi::cir::TemplateNullKind::Pointer;
                    break;
                case ConstNullKind::MemberPointer:
                    out.null_kind = aburi::cir::TemplateNullKind::MemberPointer;
                    break;
                case ConstNullKind::None:
                    out.null_kind = aburi::cir::TemplateNullKind::None;
                    break;
            }
            return true;
        case ConstValueKind::Address: {

            bool durable_string_literal =
                value.address_value.string_literal.valid();
            if (value.address_value.allocation_id != 0 &&
                !durable_string_literal &&
                !(value.address_value.entity.valid() && address_is_durable &&
                  (*address_is_durable)(value.address_value.entity))) {
                return fail(error,
                            "constant state contains an evaluator-owned address");
            }
            out.kind = ConstantStateKind::Address;
            out.address_entity = value.address_value.entity;
            out.address_string_literal = value.address_value.string_literal;
            out.address_byte_offset = value.address_value.byte_offset;
            out.address_subobjects.clear();
            out.address_subobjects.reserve(
                value.address_value.subobjects.size());
            for (const ConstSubobjectPathEntry& step :
                 value.address_value.subobjects) {
                out.address_subobjects.push_back(
                    aburi::cir::ConstantStateSubobject{
                        step.entity, step.array_index, step.is_array_element});
            }
            return true;
        }
        case ConstValueKind::MemberPointer:
            out.kind = ConstantStateKind::MemberPointer;
            out.member_entity = value.member_pointer_value.method_entity;
            out.member_byte_offset = value.member_pointer_value.byte_offset;
            out.member_virtual_slot =
                value.member_pointer_value.virtual_slot_index;
            out.member_is_function =
                value.member_pointer_value.is_function_member;
            return true;
        case ConstValueKind::Object:
            break;
        case ConstValueKind::MetaInfo:
            out.kind = ConstantStateKind::MetaInfo;
            if (value.meta_info_value) {
                out.member_entity = value.meta_info_value->entity;
                out.type = value.meta_info_value->type.type.valid()
                    ? value.meta_info_value->type
                    : out.type;
            }
            return true;
        case ConstValueKind::Invalid:
        case ConstValueKind::Void:
            return fail(error, "constant state contains no object value");
    }

    if (!value.object_value) {
        return fail(error, "constant state contains an invalid object");
    }
    if (file.type(resolved).kind == aburi::cir::TypeKind::Array) {
        const auto* array = std::get_if<aburi::cir::ArrayTypePayload>(
            &file.type_payload(resolved));
        if (!array || !array->size.has_value() ||
            value.object_value->kind != ConstObjectValueKind::Array ||
            value.object_value->elements.size() != *array->size) {
            return fail(error, "constant array state has the wrong shape");
        }
        out.kind = ConstantStateKind::Array;
        out.elements.reserve(*array->size);
        for (size_t index = 0; index < *array->size; ++index) {
            ConstantStateFact child;
            if (!build_state(file, array->element_type.type,
                             value.object_value->elements[index], child,
                             error, address_is_durable)) {
                return false;
            }
            child.subobject_index = index;
            out.elements.push_back(std::move(child));
        }
        return true;
    }
    if (file.type(resolved).kind != aburi::cir::TypeKind::Record) {
        return fail(error, "constant object state has a non-object type");
    }
    const aburi::cir::RecordFacts* facts = file.record_facts_for_type(resolved);
    if (!facts || facts->is_incomplete ||
        value.object_value->kind != ConstObjectValueKind::Record) {
        return fail(error, "constant record state has the wrong shape");
    }
    out.kind = ConstantStateKind::Record;
    if (facts->is_lambda_closure) {
        if (!file.valid(facts->closure_identity) ||
            facts->lambda_has_capture) {
            return fail(error,
                        "constant closure state has invalid identity");
        }
        out.closure_identity = facts->closure_identity;
    }
    out.active_union_member = value.object_value->active_union_member;
    bool sparse_union = facts->kind == aburi::cir::RecordKind::Union &&
        out.active_union_member.valid() &&
        value.object_value->elements.size() == 1;
    size_t element_index = 0;
    for (const aburi::cir::RecordFieldFact& field : facts->fields) {
        if (field.is_virtual_base_storage || field.is_flexible_array_member) {
            continue;
        }
        if (sparse_union && field.entity != out.active_union_member) {
            continue;
        }
        if (element_index >= value.object_value->elements.size()) {
            return fail(error, "constant record state has too few subobjects");
        }
        ConstantStateFact child;
        if (!build_state(file, field.type.type,
                         value.object_value->elements[element_index], child,
                         error, address_is_durable)) {
            return false;
        }
        child.subobject_entity = field.entity;
        out.elements.push_back(std::move(child));
        ++element_index;
    }
    if (element_index != value.object_value->elements.size()) {
        return fail(error, "constant record state has too many subobjects");
    }
    return true;
}

} // namespace

std::optional<aburi::cir::ConstantStateFact> constant_state_from_value(
    const aburi::cir::File& file,
    aburi::cir::TypeId type,
    const ConstValue& value,
    std::string* error,
    const ConstantStateAddressPolicy* address_is_durable) {
    aburi::cir::ConstantStateFact state;
    if (!build_state(file, type, value, state, error, address_is_durable)) {
        return std::nullopt;
    }
    return state;
}

std::optional<ConstValue> const_value_from_constant_state(
    const aburi::cir::ConstantStateFact& state,
    std::string* error) {
    using aburi::cir::ConstantStateKind;
    switch (state.kind) {
        case ConstantStateKind::Integer: {
            return ConstValue::integer(state.integer_value);
        }
        case ConstantStateKind::Boolean:
            return ConstValue::boolean(state.boolean_value);
        case ConstantStateKind::Floating:
            return ConstValue::floating(state.floating_value);
        case ConstantStateKind::Complex:
            if (state.complex_is_integer) {
                return ConstValue::complex_integer(
                    state.complex_integer_real,
                    state.complex_integer_imag);
            }
            return ConstValue::complex(state.floating_real,
                                       state.floating_imag);
        case ConstantStateKind::Null:
            switch (state.null_kind) {
                case aburi::cir::TemplateNullKind::Nullptr:
                    return ConstValue::nullptr_value();
                case aburi::cir::TemplateNullKind::Pointer:
                    return ConstValue::null_pointer();
                case aburi::cir::TemplateNullKind::MemberPointer:
                    return ConstValue::null_member_pointer();
                case aburi::cir::TemplateNullKind::None:
                    break;
            }
            break;
        case ConstantStateKind::Address: {
            ConstAddressValue address;
            address.entity = state.address_entity;
            address.string_literal = state.address_string_literal;
            address.byte_offset = state.address_byte_offset;

            for (const aburi::cir::ConstantStateSubobject& step :
                 state.address_subobjects) {
                address.subobjects.push_back(ConstSubobjectPathEntry{
                    step.entity, step.array_index, step.is_array_element});
            }
            return ConstValue::address_value_of(address);
        }
        case ConstantStateKind::MemberPointer:
            return ConstValue::member_pointer(state.member_byte_offset,
                                              state.member_is_function,
                                              state.member_entity,
                                              state.member_virtual_slot);
        case ConstantStateKind::Record:
        case ConstantStateKind::Array: {
            std::vector<ConstValue> elements;
            elements.reserve(state.elements.size());
            for (const aburi::cir::ConstantStateFact& child : state.elements) {
                std::optional<ConstValue> value =
                    const_value_from_constant_state(child, error);
                if (!value.has_value()) {
                    return std::nullopt;
                }
                elements.push_back(std::move(*value));
            }
            ConstValue result = ConstValue::object(
                state.kind == ConstantStateKind::Array
                    ? ConstObjectValueKind::Array
                    : ConstObjectValueKind::Record,
                std::move(elements));
            result.object_value->active_union_member =
                state.active_union_member;
            return result;
        }
        case ConstantStateKind::MetaInfo:
        case ConstantStateKind::Invalid:
            break;
    }
    fail(error, "durable constant state cannot be converted to a value");
    return std::nullopt;
}

bool constant_state_equals(const aburi::cir::ConstantStateFact& lhs,
                           const aburi::cir::ConstantStateFact& rhs) {
    std::optional<ConstValue> lhs_value = const_value_from_constant_state(lhs);
    std::optional<ConstValue> rhs_value = const_value_from_constant_state(rhs);
    return lhs.type == rhs.type && lhs.lifetime == rhs.lifetime &&
           lhs.initialized == rhs.initialized && lhs_value.has_value() &&
           rhs_value.has_value() &&
           lhs.closure_identity == rhs.closure_identity &&
           const_value_equals(*lhs_value, *rhs_value);
}

std::optional<aburi::cir::ConstantStateFact>
constant_state_from_static_image(
    const aburi::cir::File& file,
    aburi::cir::TypeId type,
    const std::vector<uint8_t>& bytes,
    size_t offset,
    const std::vector<aburi::cir::StaticInitializerRelocation>& relocations,
    aburi::cir::EntityId active_union_member,
    std::string* error) {
    using namespace aburi::cir;
    TypeId resolved = file.resolved_type(type);
    std::optional<size_t> size = size_of_type(file, resolved);
    if (!file.valid(resolved) || !size.has_value() ||
        offset > bytes.size() || *size > bytes.size() - offset) {
        fail(error, "static constant image is outside its object bounds");
        return std::nullopt;
    }

    ConstantStateFact state;
    state.type = file.type_ref(type);
    state.initialized = true;
    state.lifetime = ConstantLifetimeState::Alive;

    auto relocation_at = [&](size_t at)
        -> const StaticInitializerRelocation* {
        for (const StaticInitializerRelocation& relocation : relocations) {
            if (relocation.offset == at && !relocation.block.valid() &&
                !relocation.subtract_block.valid()) {
                return &relocation;
            }
        }
        return nullptr;
    };

    TypeKind kind = file.type(resolved).kind;
    if (kind == TypeKind::Array) {
        const auto* array = std::get_if<ArrayTypePayload>(
            &file.type_payload(resolved));
        std::optional<size_t> element_size = array
            ? size_of_type(file, array->element_type.type)
            : std::nullopt;
        if (!array || !array->size.has_value() ||
            !element_size.has_value()) {
            fail(error, "static constant array has incomplete type");
            return std::nullopt;
        }
        state.kind = ConstantStateKind::Array;
        for (size_t index = 0; index < *array->size; ++index) {
            auto child = constant_state_from_static_image(
                file, array->element_type.type, bytes,
                offset + index * *element_size, relocations, {}, error);
            if (!child.has_value()) {
                return std::nullopt;
            }
            child->subobject_index = index;
            state.elements.push_back(std::move(*child));
        }
        return state;
    }
    if (kind == TypeKind::Record) {
        const RecordFacts* facts = file.record_facts_for_type(resolved);
        if (!facts || facts->is_incomplete) {
            fail(error, "static constant record has incomplete type");
            return std::nullopt;
        }
        state.kind = ConstantStateKind::Record;
        if (facts->is_lambda_closure) {
            if (!file.valid(facts->closure_identity) ||
                facts->lambda_has_capture) {
                fail(error, "static closure state has invalid identity");
                return std::nullopt;
            }
            state.closure_identity = facts->closure_identity;
        }
        state.active_union_member = active_union_member;
        if (facts->kind == RecordKind::Union &&
            !state.active_union_member.valid()) {
            for (const RecordFieldFact& field : facts->fields) {
                if (!field.is_virtual_base_storage &&
                    !field.is_flexible_array_member) {
                    state.active_union_member = field.entity;
                    break;
                }
            }
        }
        for (const RecordFieldFact& field : facts->fields) {
            if (field.is_virtual_base_storage ||
                field.is_flexible_array_member) {
                continue;
            }
            ConstantStateFact child;
            if (field.is_bitfield) {
                uint32_t storage_bits =
                    field.storage_size == 0 ? 32 : field.storage_size;
                size_t storage_bytes = (storage_bits + 7) / 8;
                if (offset + field.offset + storage_bytes > bytes.size() ||
                    storage_bits > 64) {
                    fail(error, "static bit-field image is outside its storage");
                    return std::nullopt;
                }
                uint64_t raw = aburi::abi::read_scalar_bits(
                    bytes.data() + offset + field.offset, storage_bytes,
                    file.target_info().endianness).low;
                uint32_t width = bitfield_value_width(file, field);
                uint64_t mask = width == 64
                    ? ~uint64_t{0}
                    : ((uint64_t{1} << width) - 1);
                raw = (raw >> field.bit_offset) & mask;
                IntegerTypeShape shape =
                    integer_shape_for_type(file, field.type.type);
                if (!shape.is_unsigned && width < 64 &&
                    (raw & (uint64_t{1} << (width - 1))) != 0) {
                    raw |= ~mask;
                }
                child.kind = ConstantStateKind::Integer;
                child.type = field.type;
                child.initialized = true;
                child.integer_value = ConstIntValue::from_unsigned(
                    raw, shape.bit_width).cast(shape.bit_width,
                                               shape.is_unsigned);
            } else {
                auto decoded = constant_state_from_static_image(
                    file, field.type.type, bytes, offset + field.offset,
                    relocations, {}, error);
                if (!decoded.has_value()) {
                    return std::nullopt;
                }
                child = std::move(*decoded);
            }
            child.subobject_entity = field.entity;
            state.elements.push_back(std::move(child));
        }
        return state;
    }
    if (kind == TypeKind::Pointer || kind == TypeKind::BlockPointer ||
        kind == TypeKind::LValueReference ||
        kind == TypeKind::RValueReference) {
        if (const StaticInitializerRelocation* relocation =
                relocation_at(offset)) {
            state.kind = ConstantStateKind::Address;
            state.address_entity = relocation->entity;
            state.address_byte_offset = relocation->addend;
            return state;
        }
        if (kind == TypeKind::LValueReference ||
            kind == TypeKind::RValueReference) {
            fail(error, "static reference image has no address identity");
            return std::nullopt;
        }
        state.kind = ConstantStateKind::Null;
        state.null_kind = TemplateNullKind::Pointer;
        return state;
    }
    if (kind == TypeKind::MemberPointer) {
        if (const StaticInitializerRelocation* relocation =
                relocation_at(offset)) {
            state.kind = ConstantStateKind::MemberPointer;
            state.member_entity = relocation->entity;
            state.member_byte_offset = relocation->addend;
            state.member_is_function = true;
            return state;
        }
        aburi::abi::ScalarBits raw = aburi::abi::read_scalar_bits(
            bytes.data() + offset, *size, file.target_info().endianness);
        bool points_to_function =
            file.member_pointer_points_to_function(resolved);
        bool is_null = points_to_function
            ? raw.low == 0 && raw.high == 0
            : raw.low == ~uint64_t{0} &&
                (*size <= sizeof(uint64_t) || raw.high == ~uint64_t{0});
        if (is_null) {
            state.kind = ConstantStateKind::Null;
            state.null_kind = TemplateNullKind::MemberPointer;
            return state;
        }
        state.kind = ConstantStateKind::MemberPointer;
        state.member_byte_offset = static_cast<int64_t>(raw.low);
        state.member_is_function = points_to_function;
        return state;
    }
    if (kind == TypeKind::Complex) {
        const auto* complex = std::get_if<ComplexTypePayload>(
            &file.type_payload(resolved));
        std::optional<size_t> element_size = complex
            ? size_of_type(file, complex->element_type.type)
            : std::nullopt;
        if (!complex || !element_size.has_value()) {
            fail(error, "static complex image has invalid element type");
            return std::nullopt;
        }
        auto real = constant_state_from_static_image(
            file, complex->element_type.type, bytes, offset,
            relocations, {}, error);
        auto imag = constant_state_from_static_image(
            file, complex->element_type.type, bytes,
            offset + *element_size, relocations, {}, error);
        if (!real || !imag || real->kind != imag->kind ||
            (real->kind != ConstantStateKind::Floating &&
             real->kind != ConstantStateKind::Integer)) {
            return std::nullopt;
        }
        state.kind = ConstantStateKind::Complex;
        if (real->kind == ConstantStateKind::Integer) {
            state.complex_is_integer = true;
            state.complex_integer_real = real->integer_value;
            state.complex_integer_imag = imag->integer_value;
            return state;
        }
        state.floating_real = real->floating_value;
        state.floating_imag = imag->floating_value;
        return state;
    }
    if (is_integer_like_type(file, resolved)) {
        aburi::abi::ScalarBits raw = aburi::abi::read_scalar_bits(
            bytes.data() + offset, *size, file.target_info().endianness);
        IntegerTypeShape shape = integer_shape_for_type(file, resolved);
        state.kind = ConstantStateKind::Integer;
        state.integer_value = ConstIntValue::from_words(
            raw.low, raw.high, shape.bit_width, shape.is_unsigned);
        if (file.type(resolved).kind == TypeKind::Builtin) {
            const auto* builtin = std::get_if<BuiltinTypePayload>(
                &file.type_payload(resolved));
            if (builtin && builtin->kind == BuiltinTypeKind::Bool) {
                state.kind = ConstantStateKind::Boolean;
                state.boolean_value = raw.low != 0 || raw.high != 0;
            }
        }
        return state;
    }
    if (kind == TypeKind::Builtin) {
        const auto* builtin = std::get_if<BuiltinTypePayload>(
            &file.type_payload(resolved));
        FloatingSemantics semantics =
            aburi::floating::semantics_for_type(file, resolved);
        if (builtin && semantics != FloatingSemantics::Invalid &&
            *size <= 16) {
            aburi::abi::ScalarBits bits = aburi::abi::read_scalar_bits(
                bytes.data() + offset,
                *size,
                file.target_info().endianness);
            state.kind = ConstantStateKind::Floating;
            state.floating_value = FloatingValue{
                semantics, bits.low, bits.high};
            if (semantics == FloatingSemantics::IEEEBinary16) {
                state.floating_value.low_bits &= 0xffffu;
                state.floating_value.high_bits = 0;
            } else if (semantics == FloatingSemantics::IEEEBinary32) {
                state.floating_value.low_bits &= 0xffffffffu;
                state.floating_value.high_bits = 0;
            } else if (semantics == FloatingSemantics::IEEEBinary64) {
                state.floating_value.high_bits = 0;
            } else if (semantics == FloatingSemantics::X87Extended80) {
                state.floating_value.high_bits &= 0xffffu;
            }
            return state;
        }
        if (builtin && builtin->kind == BuiltinTypeKind::NullPtr) {
            state.kind = ConstantStateKind::Null;
            state.null_kind = TemplateNullKind::Nullptr;
            return state;
        }
    }
    fail(error, "static constant image has an unsupported type");
    return std::nullopt;
}
