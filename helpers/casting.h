#ifndef ABURI_CASTING_H
#define ABURI_CASTING_H

#include <cassert>
#include <memory>
#include <type_traits>

// isa<T>(val) - returns true if val is of type T
template <typename To, typename From>
[[nodiscard]] inline bool isa(const From *val) {
    return val && To::classof(val);
}

// cast<T>(val) - assert-checked downcast (use when you KNOW the type)
template <typename To, typename From>
[[nodiscard]] inline To *cast(From *val) {
    assert(val && "cast<> called on null");
    assert(To::classof(val) && "cast<> type mismatch");
    return static_cast<To *>(val);
}

template <typename To, typename From>
[[nodiscard]] inline const To *cast(const From *val) {
    assert(val && "cast<> called on null");
    assert(To::classof(val) && "cast<> type mismatch");
    return static_cast<const To *>(val);
}

// dyn_cast<T>(val) - checked downcast, returns nullptr on mismatch
template <typename To, typename From>
[[nodiscard]] inline To *dyn_cast(From *val) {
    if (!val || !To::classof(val)) return nullptr;
    return static_cast<To *>(val);
}

template <typename To, typename From>
[[nodiscard]] inline const To *dyn_cast(const From *val) {
    if (!val || !To::classof(val)) return nullptr;
    return static_cast<const To *>(val);
}

// dyn_cast_shared<T>(val) - for shared_ptr casts (replaces dynamic_pointer_cast)
template <typename To, typename From>
[[nodiscard]] inline std::shared_ptr<To> dyn_cast_shared(const std::shared_ptr<From> &val) {
    if (!val || !To::classof(val.get())) return nullptr;
    return std::static_pointer_cast<To>(val);
}

#endif // ABURI_CASTING_H
