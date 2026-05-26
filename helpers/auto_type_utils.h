#ifndef ABURI_AUTO_TYPE_UTILS_H
#define ABURI_AUTO_TYPE_UTILS_H

#include "ast/types.h"

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>

namespace auto_type_utils {

constexpr uint8_t kGnuAutoFlavor = 0x1;
constexpr uint8_t kCxxAutoFlavor = 0x2;
constexpr uint8_t kDecltypeAutoFlavor = 0x4;

enum class DependentValueTemplateArgumentAutoPolicy {
    Count,
    IgnoreValueType,
};

inline bool is_ordinary_cxx_auto_flavor(AutoTypeFlavor flavor) {
    return flavor == AutoTypeFlavor::Cxx ||
           flavor == AutoTypeFlavor::TemplateNonType;
}

inline bool is_decltype_auto_flavor(AutoTypeFlavor flavor) {
    return flavor == AutoTypeFlavor::DecltypeAuto ||
           flavor == AutoTypeFlavor::DecltypeAutoTemplateNonType;
}

uint8_t auto_type_flavors_in(
    const std::shared_ptr<CType>& type,
    DependentValueTemplateArgumentAutoPolicy dependent_value_policy =
        DependentValueTemplateArgumentAutoPolicy::Count);

inline bool has_gnu_auto_type(const std::shared_ptr<CType>& type) {
    return (auto_type_flavors_in(type) & kGnuAutoFlavor) != 0;
}

inline bool has_cxx_auto_type(const std::shared_ptr<CType>& type) {
    return (auto_type_flavors_in(type) &
            static_cast<uint8_t>(kCxxAutoFlavor | kDecltypeAutoFlavor)) != 0;
}

inline bool has_ordinary_cxx_auto_type(const std::shared_ptr<CType>& type) {
    return (auto_type_flavors_in(type) & kCxxAutoFlavor) != 0;
}

inline bool has_decltype_auto_type(const std::shared_ptr<CType>& type) {
    return (auto_type_flavors_in(type) & kDecltypeAutoFlavor) != 0;
}

inline bool is_decltype_auto_placeholder(const std::shared_ptr<CType>& type) {
    if (!type || type->kind != TypeKind::Auto) {
        return false;
    }
    auto* auto_type = static_cast<AutoType*>(type.get());
    return is_decltype_auto_flavor(auto_type->flavor);
}

std::optional<QualType> extract_auto_placeholder_replacement(
    QualType pattern,
    QualType actual);

std::shared_ptr<CType> replace_auto_placeholder(
    const std::shared_ptr<CType>& type,
    const std::shared_ptr<CType>& deduced);

std::shared_ptr<CType> replace_cxx_auto_placeholders_with_callback(
    const std::shared_ptr<CType>& type,
    const std::function<QualType(size_t, const AutoType&)>& replacement_for_placeholder,
    size_t* next_placeholder_index = nullptr);

std::shared_ptr<CType> retag_cxx_auto_placeholders(
    const std::shared_ptr<CType>& type,
    AutoTypeFlavor new_flavor);

const AutoType* find_first_constrained_auto_placeholder(
    const std::shared_ptr<CType>& type);

} // namespace auto_type_utils

#endif // ABURI_AUTO_TYPE_UTILS_H
