#ifndef ABURI_CONSTANT_STATE_H
#define ABURI_CONSTANT_STATE_H

#include <functional>
#include <optional>
#include <string>

#include "const_value.h"

namespace aburi::cir {
class File;
struct StaticInitializerRelocation;
}

using ConstantStateAddressPolicy = std::function<bool(aburi::cir::EntityId)>;

std::optional<aburi::cir::ConstantStateFact> constant_state_from_value(
    const aburi::cir::File& file,
    aburi::cir::TypeId type,
    const ConstValue& value,
    std::string* error = nullptr,
    const ConstantStateAddressPolicy* address_is_durable = nullptr);

std::optional<ConstValue> const_value_from_constant_state(
    const aburi::cir::ConstantStateFact& state,
    std::string* error = nullptr);

bool constant_state_equals(const aburi::cir::ConstantStateFact& lhs,
                           const aburi::cir::ConstantStateFact& rhs);

std::optional<aburi::cir::ConstantStateFact>
constant_state_from_static_image(
    const aburi::cir::File& file,
    aburi::cir::TypeId type,
    const std::vector<uint8_t>& bytes,
    size_t offset,
    const std::vector<aburi::cir::StaticInitializerRelocation>& relocations,
    aburi::cir::EntityId active_union_member = {},
    std::string* error = nullptr);

#endif // ABURI_CONSTANT_STATE_H
