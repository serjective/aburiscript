#ifndef ABURI_CIR_LAYOUT_H
#define ABURI_CIR_LAYOUT_H

#include <cstddef>
#include <cstdint>
#include <optional>

#include "file.h"
#include "../abi/target_info.h"

namespace aburi::cir {

struct TypeSizeAlign {
    size_t size_bytes = 0;
    size_t alignment_bytes = 1;
};

struct IntegerTypeShape {
    uint16_t bit_width = 64;
    bool is_unsigned = false;
};

std::optional<TypeSizeAlign> size_align_of_type(const File& file, TypeId type);
std::optional<TypeSizeAlign> size_align_of_type(const File& file,
                                                TypeId type,
                                                const TargetInfo& target);
std::optional<size_t> size_of_type(const File& file, TypeId type);
std::optional<size_t> align_of_type(const File& file, TypeId type);

bool is_integer_like_type(const File& file, TypeId type);
bool is_floating_type(const File& file, TypeId type);
IntegerTypeShape integer_shape_for_type(const File& file, TypeId type);
IntegerTypeShape integer_shape_for_type(const File& file,
                                        TypeId type,
                                        const TargetInfo& target);

bool type_has_known_no_padding(const File& file, TypeId type);

uint32_t bitfield_value_width(const File& file,
                              const RecordFieldFact& field);

bool type_has_mutable_subobject(const File& file, TypeId type);

} // namespace aburi::cir

#endif // ABURI_CIR_LAYOUT_H
