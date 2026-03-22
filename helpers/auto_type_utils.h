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

uint8_t auto_type_flavors_in(const std::shared_ptr<CType>& type);

inline bool has_gnu_auto_type(const std::shared_ptr<CType>& type) {
    return (auto_type_flavors_in(type) & kGnuAutoFlavor) != 0;
}

inline bool has_cxx_auto_type(const std::shared_ptr<CType>& type) {
    return (auto_type_flavors_in(type) & kCxxAutoFlavor) != 0;
}

std::optional<QualType> extract_auto_placeholder_replacement(
    QualType pattern,
    QualType actual);

std::shared_ptr<CType> replace_auto_placeholder(
    const std::shared_ptr<CType>& type,
    const std::shared_ptr<CType>& deduced);

std::shared_ptr<CType> replace_cxx_auto_placeholders_with_callback(
    const std::shared_ptr<CType>& type,
    const std::function<QualType(size_t)>& replacement_for_placeholder,
    size_t* next_placeholder_index = nullptr);

std::shared_ptr<CType> retag_cxx_auto_placeholders(
    const std::shared_ptr<CType>& type,
    AutoTypeFlavor new_flavor);

} // namespace auto_type_utils

#endif // ABURI_AUTO_TYPE_UTILS_H
