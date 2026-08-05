#include <exception>
#include <new>
#include <typeinfo>

#include <stdint.h>
#include <string.h>

namespace __cxxabiv1 {

extern "C" void* __cxa_current_primary_exception() noexcept;
extern "C" void
__cxa_increment_exception_refcount(void*) noexcept;
extern "C" void
__cxa_decrement_exception_refcount(void*) noexcept;
extern "C" [[noreturn]] void
__cxa_rethrow_primary_exception(void*);
extern "C" unsigned int
__cxa_uncaught_exceptions() noexcept;

} // namespace __cxxabiv1

namespace {

const char* unpack_type_name(const char* value) noexcept {
#if defined(__APPLE__) && defined(__aarch64__)
    constexpr uintptr_t non_unique_bit =
        uintptr_t{1} << (sizeof(uintptr_t) * 8 - 1);
    return reinterpret_cast<const char*>(
        reinterpret_cast<uintptr_t>(value) & ~non_unique_bit);
#else
    return value;
#endif
}

bool type_name_is_unique(const char* value) noexcept {
#if defined(__APPLE__) && defined(__aarch64__)
    constexpr uintptr_t non_unique_bit =
        uintptr_t{1} << (sizeof(uintptr_t) * 8 - 1);
    return (reinterpret_cast<uintptr_t>(value) & non_unique_bit) == 0;
#else
    (void)value;
    return true;
#endif
}

} // namespace

namespace std {

exception::~exception() noexcept = default;

const char* exception::what() const noexcept {
    return "std::exception";
}

bad_exception::~bad_exception() noexcept = default;

const char* bad_exception::what() const noexcept {
    return "std::bad_exception";
}

exception_ptr::exception_ptr(const exception_ptr& other) noexcept
    : pointer_(other.pointer_) {
    if (pointer_ != nullptr) {
        __cxxabiv1::__cxa_increment_exception_refcount(pointer_);
    }
}

exception_ptr&
exception_ptr::operator=(const exception_ptr& other) noexcept {
    void* replacement = other.pointer_;
    if (replacement != nullptr) {
        __cxxabiv1::__cxa_increment_exception_refcount(replacement);
    }
    if (pointer_ != nullptr) {
        __cxxabiv1::__cxa_decrement_exception_refcount(pointer_);
    }
    pointer_ = replacement;
    return *this;
}

exception_ptr::~exception_ptr() noexcept {
    if (pointer_ != nullptr) {
        __cxxabiv1::__cxa_decrement_exception_refcount(pointer_);
    }
}

exception_ptr current_exception() noexcept {
    return exception_ptr(
        __cxxabiv1::__cxa_current_primary_exception());
}

[[noreturn]] void rethrow_exception(exception_ptr value) {
    if (!value) {
        terminate();
    }
    __cxxabiv1::__cxa_rethrow_primary_exception(value.pointer_);
}

int uncaught_exceptions() noexcept {
    return static_cast<int>(
        __cxxabiv1::__cxa_uncaught_exceptions());
}

bad_alloc::~bad_alloc() noexcept = default;

const char* bad_alloc::what() const noexcept {
    return "std::bad_alloc";
}

bad_array_new_length::~bad_array_new_length() noexcept = default;

const char* bad_array_new_length::what() const noexcept {
    return "std::bad_array_new_length";
}

type_info::~type_info() = default;

const char* type_info::name() const noexcept {
    return unpack_type_name(type_name_);
}

bool type_info::operator==(const type_info& other) const noexcept {
    if (type_name_ == other.type_name_) {
        return true;
    }
    if (type_name_is_unique(type_name_) ||
        type_name_is_unique(other.type_name_)) {
        return false;
    }
    return __builtin_strcmp(name(), other.name()) == 0;
}

bool type_info::before(const type_info& other) const noexcept {
    return __builtin_strcmp(name(), other.name()) < 0;
}

size_t type_info::hash_code() const noexcept {
    size_t hash = 5381;
    const unsigned char* cursor =
        reinterpret_cast<const unsigned char*>(name());
    while (*cursor != 0) {
        hash = hash * 33 ^ *cursor++;
    }
    return hash;
}

bad_cast::~bad_cast() noexcept = default;

const char* bad_cast::what() const noexcept {
    return "std::bad_cast";
}

bad_typeid::~bad_typeid() noexcept = default;

const char* bad_typeid::what() const noexcept {
    return "std::bad_typeid";
}

} // namespace std
