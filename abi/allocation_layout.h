#ifndef ABURI_ABI_ALLOCATION_LAYOUT_H
#define ABURI_ABI_ALLOCATION_LAYOUT_H

#include <algorithm>
#include <cstddef>

namespace aburi::abi {

// Target-independent description of the Itanium array-new prefix
struct ArrayAllocationLayout {
    bool has_cookie = false;
    size_t prefix_bytes = 0;
    size_t cookie_bytes = 0;
    size_t cookie_offset_from_allocation = 0;
};

inline ArrayAllocationLayout itanium_array_allocation_layout(
    size_t size_type_bytes,
    size_t element_alignment,
    bool cookie_required) {
    ArrayAllocationLayout result;
    if (!cookie_required) {
        return result;
    }
    result.has_cookie = true;
    result.cookie_bytes = size_type_bytes;
    result.prefix_bytes = std::max(size_type_bytes, element_alignment);
    result.cookie_offset_from_allocation =
        result.prefix_bytes - result.cookie_bytes;
    return result;
}

} // namespace aburi::abi

#endif // ABURI_ABI_ALLOCATION_LAYOUT_H
