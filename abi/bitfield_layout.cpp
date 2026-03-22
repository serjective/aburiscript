#include "bitfield_layout.h"
#include "helpers/casting.h"
#include <algorithm>

BitfieldLayoutEngine::BitfieldLayoutEngine(BitfieldLayoutConfig config)
    : config_(config) {}

uint32_t BitfieldLayoutEngine::get_storage_unit_size(const std::shared_ptr<CType>& type) {
    if (auto builtin = dyn_cast_shared<BuiltinType>(type)) {
        switch (builtin->builtin_kind) {
            case BuiltinTypes::Bool:
            case BuiltinTypes::Char:
            case BuiltinTypes::UChar:
                return 8;
            case BuiltinTypes::Short:
            case BuiltinTypes::UShort:
                return 16;
            case BuiltinTypes::Int:
            case BuiltinTypes::UInt:
                return 32;
            case BuiltinTypes::Long:
            case BuiltinTypes::ULong:
            case BuiltinTypes::LongLong:
            case BuiltinTypes::ULongLong:
                return 64;
            default:
                return 32;
        }
    }
    if (type->kind == TypeKind::Enum) {
        return 32;
    }
    return 32;
}

size_t BitfieldLayoutEngine::get_type_alignment(const std::shared_ptr<CType>& type) {
    auto canonical = desugar_type(type);
    if (!canonical) {
        return 1;
    }
    if (auto builtin = dyn_cast_shared<BuiltinType>(canonical)) {
        int64_t width = builtin->getWidth();
        size_t align = static_cast<size_t>((width + 7) / 8);
        align = std::min(align, static_cast<size_t>(8));
        if (config_.pack_alignment > 0 && align > config_.pack_alignment) {
            align = config_.pack_alignment;
        }
        return align;
    }
    if (canonical->kind == TypeKind::Enum) {
        size_t align = 4;
        if (config_.pack_alignment > 0 && align > config_.pack_alignment) {
            align = config_.pack_alignment;
        }
        return align;
    }
    if (canonical->kind == TypeKind::Pointer) {
        size_t align = 8;
        if (config_.pack_alignment > 0 && align > config_.pack_alignment) {
            align = config_.pack_alignment;
        }
        return align;
    }
    if (canonical->kind == TypeKind::Array) {
        auto arr = dyn_cast_shared<ArrayType>(canonical);
        return get_type_alignment(arr->element_type.get_shared());
    }
    if (canonical->kind == TypeKind::Object) {
        auto obj = dyn_cast_shared<ObjectType>(canonical);
        size_t align = obj->getAlignment();
        if (config_.pack_alignment > 0 && align > config_.pack_alignment) {
            align = config_.pack_alignment;
        }
        return align;
    }
    return 1;
}

void BitfieldLayoutEngine::compute_layout(std::vector<ObjectType::Field>& fields,
                                          bool is_union,
                                          size_t& out_total_size,
                                          size_t& out_alignment) {
    if (is_union) {
        compute_union_layout(fields, out_total_size, out_alignment);
    } else if (config_.abi == BitfieldABI::MSVC) {
        compute_struct_layout_msvc(fields, out_total_size, out_alignment);
    } else {
        compute_struct_layout_itanium(fields, out_total_size, out_alignment);
    }
}

// Itanium ABI. For regular records we keep storage-unit boundary behavior.
// For packed records / pack(1), GCC-compatible behavior is byte-stream
// packing where bitfields may straddle declared-type storage units.
void BitfieldLayoutEngine::compute_struct_layout_itanium(
        std::vector<ObjectType::Field>& fields,
        size_t& out_total_size,
        size_t& out_alignment) {
    if (fields.empty()) {
        out_total_size = 0;
        out_alignment = 1;
        return;
    }

    size_t current_bit_pos = 0;
    size_t max_alignment = 1;
    const bool tight_packed_bitfields =
        config_.record_packed || config_.pack_alignment == 1;

    for (auto& field : fields) {
        if (field.is_bitfield) {
            uint32_t field_width = field.bit_width;
            uint32_t storage_unit_size = get_storage_unit_size(field.type.get_shared());
            size_t unit_align_bytes = storage_unit_size / 8;
            if (config_.pack_alignment > 0 && unit_align_bytes > config_.pack_alignment) {
                unit_align_bytes = config_.pack_alignment;
            }
            size_t unit_align_bits = unit_align_bytes * 8;
            if (unit_align_bits == 0) {
                unit_align_bits = 8;
            }

            if (field_width == 0) {
                if (current_bit_pos % unit_align_bits != 0) {
                    current_bit_pos += unit_align_bits - (current_bit_pos % unit_align_bits);
                }
                field.offset = current_bit_pos / 8;
                field.bit_offset = 0;
                field.storage_size = storage_unit_size;
                if (unit_align_bytes > max_alignment) {
                    max_alignment = unit_align_bytes;
                }
                continue;
            }

            if (tight_packed_bitfields) {
                size_t start_byte = current_bit_pos / 8;
                uint32_t bit_within_byte = static_cast<uint32_t>(current_bit_pos % 8);
                uint32_t storage_bits =
                    static_cast<uint32_t>(((bit_within_byte + field_width + 7) / 8) * 8);

                field.offset = start_byte;
                field.bit_offset = bit_within_byte;
                field.storage_size = storage_bits;
                current_bit_pos += field_width;

                if (unit_align_bytes > max_alignment) {
                    max_alignment = unit_align_bytes;
                }
                continue;
            } else {
                size_t unit_start = (current_bit_pos / unit_align_bits) * unit_align_bits;
                size_t unit_end = unit_start + storage_unit_size;
                if (current_bit_pos + field_width > unit_end) {
                    current_bit_pos = unit_end;
                    if (current_bit_pos % unit_align_bits != 0) {
                        current_bit_pos += unit_align_bits - (current_bit_pos % unit_align_bits);
                    }
                }

                size_t storage_byte_offset =
                    (current_bit_pos / storage_unit_size) * (storage_unit_size / 8);
                uint32_t bit_within_unit = static_cast<uint32_t>(current_bit_pos % storage_unit_size);

                field.offset = storage_byte_offset;
                field.bit_offset = bit_within_unit;
                field.storage_size = storage_unit_size;
                current_bit_pos += field_width;

                if (unit_align_bytes > max_alignment) {
                    max_alignment = unit_align_bytes;
                }
            }
        } else {
            // Non-bitfield: advance to the next byte, then align
            size_t current_byte = (current_bit_pos + 7) / 8;

            size_t field_align = get_type_alignment(field.type.get_shared());
            size_t field_size = static_cast<size_t>(field.type->getWidthBytes());
            if (field_size == 0) {
                auto arr = dyn_cast_shared<ArrayType>(field.type.get_shared());
                if (!arr || arr->size_kind != ArraySizeKind::Incomplete) {
                    field_size = 1;
                }
            }

            if (current_byte % field_align != 0) {
                current_byte += field_align - (current_byte % field_align);
            }

            field.offset = current_byte;
            field.bit_offset = 0;
            field.bit_width = 0;
            field.storage_size = 0;
            field.is_bitfield = false;

            current_bit_pos = (current_byte + field_size) * 8;

            if (field_align > max_alignment) {
                max_alignment = field_align;
            }
        }
    }

    // Finalize: round up to bytes, then align to struct alignment
    size_t total_bytes = (current_bit_pos + 7) / 8;
    if (total_bytes % max_alignment != 0) {
        total_bytes += max_alignment - (total_bytes % max_alignment);
    }

    out_total_size = total_bytes * 8;
    out_alignment = max_alignment;
}

// MSVC ABI: bitfields always use full storage units of the declared type.
// Adjacent bitfields of different types start new storage units.
void BitfieldLayoutEngine::compute_struct_layout_msvc(
        std::vector<ObjectType::Field>& fields,
        size_t& out_total_size,
        size_t& out_alignment) {
    if (fields.empty()) {
        out_total_size = 0;
        out_alignment = 1;
        return;
    }

    size_t current_byte_offset = 0;
    uint32_t current_bit_offset = 0;
    uint32_t current_storage_size = 0;
    size_t current_storage_byte_offset = 0;
    size_t max_alignment = 1;

    for (auto& field : fields) {
        if (field.is_bitfield) {
            uint32_t field_width = field.bit_width;
            uint32_t storage_unit_size = get_storage_unit_size(field.type.get_shared());
            size_t storage_unit_bytes = storage_unit_size / 8;
            size_t unit_align = storage_unit_bytes;
            if (config_.pack_alignment > 0 && unit_align > config_.pack_alignment) {
                unit_align = config_.pack_alignment;
            }

            if (field_width == 0) {
                if (current_storage_size > 0) {
                    current_byte_offset = current_storage_byte_offset + (current_storage_size / 8);
                    current_storage_size = 0;
                    current_bit_offset = 0;
                }
                if (current_byte_offset % unit_align != 0) {
                    current_byte_offset += unit_align - (current_byte_offset % unit_align);
                }
                field.offset = current_byte_offset;
                field.bit_offset = 0;
                field.storage_size = storage_unit_size;
                continue;
            }

            // MSVC: only pack if same storage unit size AND fits
            bool fits = false;
            if (current_storage_size > 0 && current_storage_size == storage_unit_size) {
                fits = (current_bit_offset + field_width) <= storage_unit_size;
            }

            if (!fits) {
                if (current_storage_size > 0) {
                    current_byte_offset = current_storage_byte_offset + (current_storage_size / 8);
                }
                if (current_byte_offset % unit_align != 0) {
                    current_byte_offset += unit_align - (current_byte_offset % unit_align);
                }
                current_storage_byte_offset = current_byte_offset;
                current_storage_size = storage_unit_size;
                current_bit_offset = 0;
            }

            field.offset = current_storage_byte_offset;
            field.bit_offset = current_bit_offset;
            field.storage_size = storage_unit_size;
            current_bit_offset += field_width;

            if (unit_align > max_alignment) {
                max_alignment = unit_align;
            }
        } else {
            if (current_storage_size > 0) {
                current_byte_offset = current_storage_byte_offset + (current_storage_size / 8);
                current_storage_size = 0;
                current_bit_offset = 0;
            }

            size_t field_align = get_type_alignment(field.type.get_shared());
            size_t field_size = static_cast<size_t>(field.type->getWidthBytes());
            if (field_size == 0) {
                auto arr = dyn_cast_shared<ArrayType>(field.type.get_shared());
                if (!arr || arr->size_kind != ArraySizeKind::Incomplete) {
                    field_size = 1;
                }
            }

            if (current_byte_offset % field_align != 0) {
                current_byte_offset += field_align - (current_byte_offset % field_align);
            }

            field.offset = current_byte_offset;
            field.bit_offset = 0;
            field.bit_width = 0;
            field.storage_size = 0;
            field.is_bitfield = false;

            current_byte_offset += field_size;

            if (field_align > max_alignment) {
                max_alignment = field_align;
            }
        }
    }

    if (current_storage_size > 0) {
        current_byte_offset = current_storage_byte_offset + (current_storage_size / 8);
    }

    if (current_byte_offset % max_alignment != 0) {
        current_byte_offset += max_alignment - (current_byte_offset % max_alignment);
    }

    out_total_size = current_byte_offset * 8;
    out_alignment = max_alignment;
}

void BitfieldLayoutEngine::compute_union_layout(std::vector<ObjectType::Field>& fields,
                                                 size_t& out_total_size,
                                                 size_t& out_alignment) {
    if (fields.empty()) {
        out_total_size = 0;
        out_alignment = 1;
        return;
    }

    size_t max_size = 0;
    size_t max_alignment = 1;

    for (auto& field : fields) {
        field.offset = 0;

        if (field.is_bitfield) {
            uint32_t storage_unit_size = get_storage_unit_size(field.type.get_shared());
            field.bit_offset = 0;
            field.storage_size = storage_unit_size;

            // For unions, the bitfield contributes its actual used bytes
            size_t field_size = (field.bit_width + 7) / 8;
            if (config_.abi == BitfieldABI::MSVC) {
                field_size = storage_unit_size / 8;
            }
            if (field_size > max_size) {
                max_size = field_size;
            }

            size_t field_align = storage_unit_size / 8;
            if (config_.pack_alignment > 0 && field_align > config_.pack_alignment) {
                field_align = config_.pack_alignment;
            }
            if (field_align > max_alignment) {
                max_alignment = field_align;
            }
        } else {
            field.bit_offset = 0;
            field.bit_width = 0;
            field.storage_size = 0;

            size_t field_size = static_cast<size_t>(field.type->getWidthBytes());
            if (field_size == 0) {
                auto arr = dyn_cast_shared<ArrayType>(field.type.get_shared());
                if (!arr || arr->size_kind != ArraySizeKind::Incomplete) {
                    field_size = 1;
                }
            }

            if (field_size > max_size) {
                max_size = field_size;
            }

            size_t field_align = get_type_alignment(field.type.get_shared());
            if (field_align > max_alignment) {
                max_alignment = field_align;
            }
        }
    }

    if (max_size % max_alignment != 0) {
        max_size += max_alignment - (max_size % max_alignment);
    }

    out_total_size = max_size * 8;
    out_alignment = max_alignment;
}
