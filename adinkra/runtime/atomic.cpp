#include <atomic>

#include <pthread.h>
#include <string.h>

namespace {

pthread_mutex_t atomic_wait_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t atomic_wait_condition = PTHREAD_COND_INITIALIZER;
pthread_mutex_t atomic_bytes_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t shared_ptr_atomic_mutex = PTHREAD_MUTEX_INITIALIZER;

bool atomic_value_equals(
    const volatile void* address,
    const void* expected,
    std::size_t size) noexcept {
    switch (size) {
    case 1:
        return __atomic_load_n(
                   static_cast<const volatile unsigned char*>(address),
                   __ATOMIC_RELAXED) ==
               *static_cast<const unsigned char*>(expected);
    case 2:
        return __atomic_load_n(
                   static_cast<const volatile unsigned short*>(address),
                   __ATOMIC_RELAXED) ==
               *static_cast<const unsigned short*>(expected);
    case 4:
        return __atomic_load_n(
                   static_cast<const volatile unsigned int*>(address),
                   __ATOMIC_RELAXED) ==
               *static_cast<const unsigned int*>(expected);
    case 8:
        return __atomic_load_n(
                   static_cast<const volatile unsigned long long*>(address),
                   __ATOMIC_RELAXED) ==
               *static_cast<const unsigned long long*>(expected);
    default:
        (void)::pthread_mutex_lock(&atomic_bytes_mutex);
        const bool equal = ::memcmp(
            const_cast<const void*>(address), expected, size) == 0;
        (void)::pthread_mutex_unlock(&atomic_bytes_mutex);
        return equal;
    }
}

} // namespace

namespace std {
inline namespace __adinkra_v1 {

void __adinkra_atomic_wait(
    const volatile void* address,
    const void* expected,
    size_t size) noexcept {
    (void)::pthread_mutex_lock(&atomic_wait_mutex);
    while (atomic_value_equals(address, expected, size)) {
        (void)::pthread_cond_wait(
            &atomic_wait_condition, &atomic_wait_mutex);
    }
    (void)::pthread_mutex_unlock(&atomic_wait_mutex);
}

void __adinkra_atomic_load_bytes(
    const volatile void* address, void* result, size_t size) noexcept {
    (void)::pthread_mutex_lock(&atomic_bytes_mutex);
    ::memcpy(result, const_cast<const void*>(address), size);
    (void)::pthread_mutex_unlock(&atomic_bytes_mutex);
}

void __adinkra_atomic_store_bytes(
    volatile void* address, const void* desired, size_t size) noexcept {
    (void)::pthread_mutex_lock(&atomic_bytes_mutex);
    ::memcpy(const_cast<void*>(address), desired, size);
    (void)::pthread_mutex_unlock(&atomic_bytes_mutex);
}

void __adinkra_atomic_exchange_bytes(
    volatile void* address, const void* desired, void* previous,
    size_t size) noexcept {
    (void)::pthread_mutex_lock(&atomic_bytes_mutex);
    ::memcpy(previous, const_cast<const void*>(address), size);
    ::memcpy(const_cast<void*>(address), desired, size);
    (void)::pthread_mutex_unlock(&atomic_bytes_mutex);
}

bool __adinkra_atomic_compare_exchange_bytes(
    volatile void* address, void* expected, const void* desired,
    size_t size) noexcept {
    (void)::pthread_mutex_lock(&atomic_bytes_mutex);
    const bool equal =
        ::memcmp(const_cast<const void*>(address), expected, size) == 0;
    if (equal) {
        ::memcpy(const_cast<void*>(address), desired, size);
    } else {
        ::memcpy(expected, const_cast<const void*>(address), size);
    }
    (void)::pthread_mutex_unlock(&atomic_bytes_mutex);
    return equal;
}

void __adinkra_shared_ptr_atomic_lock() noexcept {
    (void)::pthread_mutex_lock(&shared_ptr_atomic_mutex);
}

void __adinkra_shared_ptr_atomic_unlock() noexcept {
    (void)::pthread_mutex_unlock(&shared_ptr_atomic_mutex);
}

void __adinkra_atomic_notify() noexcept {
    (void)::pthread_mutex_lock(&atomic_wait_mutex);
    (void)::pthread_cond_broadcast(&atomic_wait_condition);
    (void)::pthread_mutex_unlock(&atomic_wait_mutex);
}

}
} // namespace std
