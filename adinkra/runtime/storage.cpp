#include <__adinkra/storage>
#include <stdexcept>

_ADINKRA_BEGIN_NAMESPACE_STD

namespace __storage {

size_t recommend_capacity(
    size_t current, size_t minimum, size_t maximum) {
    if (minimum > maximum) {
        throw length_error("container capacity exceeds max_size");
    }

    size_t grown = current;
    if (grown < 8) {
        grown = 8;
    } else if (grown > maximum - grown / 2) {
        grown = maximum;
    } else {
        grown += grown / 2;
    }

    return grown < minimum ? minimum : grown;
}

void copy_bytes(
    void* destination, const void* source, size_t count) noexcept {
    __builtin_memcpy(destination, source, count);
}

void move_bytes(
    void* destination, const void* source, size_t count) noexcept {
    __builtin_memmove(destination, source, count);
}

void fill_bytes(
    void* destination, unsigned char value, size_t count) noexcept {
    __builtin_memset(destination, value, count);
}

int compare_bytes(
    const void* left, const void* right, size_t count) noexcept {
    return __builtin_memcmp(left, right, count);
}

} // namespace __storage

_ADINKRA_END_NAMESPACE_STD
