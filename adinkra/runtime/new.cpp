#include <new>

#include <stdlib.h>

namespace {

std::new_handler active_new_handler = nullptr;

void* allocate_unaligned(std::size_t size) {
    const std::size_t requested = size == 0 ? 1 : size;
    for (;;) {
        if (void* pointer = ::malloc(requested)) {
            return pointer;
        }
        std::new_handler handler =
            __atomic_load_n(&active_new_handler, __ATOMIC_ACQUIRE);
        if (handler == nullptr) {
            throw std::bad_alloc();
        }
        handler();
    }
}

void* allocate_aligned(std::size_t size, std::align_val_t alignment) {
    const std::size_t requested = size == 0 ? 1 : size;
    std::size_t alignment_value = static_cast<std::size_t>(alignment);
    if (alignment_value < sizeof(void*)) {
        alignment_value = sizeof(void*);
    }

    for (;;) {
        void* pointer = nullptr;
        if (::posix_memalign(&pointer, alignment_value, requested) == 0) {
            return pointer;
        }
        std::new_handler handler =
            __atomic_load_n(&active_new_handler, __ATOMIC_ACQUIRE);
        if (handler == nullptr) {
            throw std::bad_alloc();
        }
        handler();
    }
}

} // namespace

namespace std {

const nothrow_t nothrow{};

new_handler set_new_handler(new_handler handler) noexcept {
    return __atomic_exchange_n(
        &active_new_handler, handler, __ATOMIC_ACQ_REL);
}

new_handler get_new_handler() noexcept {
    return __atomic_load_n(&active_new_handler, __ATOMIC_ACQUIRE);
}

} // namespace std

__attribute__((weak)) void* operator new(std::size_t size) {
    return allocate_unaligned(size);
}

__attribute__((weak)) void* operator new[](std::size_t size) {
    return allocate_unaligned(size);
}

__attribute__((weak)) void* operator new(
    std::size_t size, std::align_val_t alignment) {
    return allocate_aligned(size, alignment);
}

__attribute__((weak)) void* operator new[](
    std::size_t size, std::align_val_t alignment) {
    return allocate_aligned(size, alignment);
}

__attribute__((weak)) void* operator new(
    std::size_t size, const std::nothrow_t&) noexcept {
    try {
        return allocate_unaligned(size);
    } catch (...) {
        return nullptr;
    }
}

__attribute__((weak)) void* operator new[](
    std::size_t size, const std::nothrow_t&) noexcept {
    return ::operator new(size, std::nothrow);
}

__attribute__((weak)) void* operator new(
    std::size_t size, std::align_val_t alignment,
    const std::nothrow_t&) noexcept {
    try {
        return allocate_aligned(size, alignment);
    } catch (...) {
        return nullptr;
    }
}

__attribute__((weak)) void* operator new[](
    std::size_t size, std::align_val_t alignment,
    const std::nothrow_t&) noexcept {
    return ::operator new(size, alignment, std::nothrow);
}

__attribute__((weak)) void operator delete(void* pointer) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete[](void* pointer) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete(
    void* pointer, std::size_t) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete[](
    void* pointer, std::size_t) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete(
    void* pointer, std::align_val_t) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete[](
    void* pointer, std::align_val_t) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete(
    void* pointer, std::size_t, std::align_val_t) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete[](
    void* pointer, std::size_t, std::align_val_t) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete(
    void* pointer, const std::nothrow_t&) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete[](
    void* pointer, const std::nothrow_t&) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete(
    void* pointer, std::align_val_t, const std::nothrow_t&) noexcept {
    ::free(pointer);
}

__attribute__((weak)) void operator delete[](
    void* pointer, std::align_val_t, const std::nothrow_t&) noexcept {
    ::free(pointer);
}
