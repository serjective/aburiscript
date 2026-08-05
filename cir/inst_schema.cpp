#include "inst_schema.h"

#include <limits>

namespace aburi::cir {
namespace {

constexpr InstSchema kUnknownInstSchema{
    InstKind::Invalid,
    "UnknownInstKind",
    "unknown",
    OperandShape::None,
    ResultShape::NoResult,
    "Unknown instruction kind."
};

constexpr InstSchema kInstSchemas[] = {
#define ABURI_CIR_INST(kind, mnemonic, operands, result, description) \
    {InstKind::kind, #kind, mnemonic, operands, result, description},
#include "inst.def"
#undef ABURI_CIR_INST
};

constexpr uint32_t kVariadicMax = std::numeric_limits<uint32_t>::max();

} // namespace

std::span<const InstSchema> all_inst_schemas() {
    return kInstSchemas;
}

const InstSchema& inst_schema(InstKind kind) {
    for (const InstSchema& schema : kInstSchemas) {
        if (schema.kind == kind) {
            return schema;
        }
    }
    return kUnknownInstSchema;
}

std::string_view inst_mnemonic(InstKind kind) {
    return inst_schema(kind).mnemonic;
}

bool inst_has_result(InstKind kind) {
    return inst_schema(kind).result_shape != ResultShape::NoResult;
}

uint32_t inst_min_operands(OperandShape shape) {
    switch (shape) {
        case OperandShape::None:
            return 0;
        case OperandShape::OneValue:
        case OperandShape::OnePlace:
        case OperandShape::OneEntity:
        case OperandShape::OneName:
        case OperandShape::OneType:
        case OperandShape::TypeOrEntity:
            return 1;
        case OperandShape::PlaceValue:
        case OperandShape::BaseIndex:
        case OperandShape::TwoValues:
        case OperandShape::TypeValue:
        case OperandShape::PlaceEntity:
            return 2;
        case OperandShape::PlaceOptionalEntity:
            return 1;
        case OperandShape::CalleeAndArguments:
        case OperandShape::NameAndArguments:
        case OperandShape::PlaceAndArguments:
            return 1;
        case OperandShape::PlaceEntityAndArguments:
            return 2;
        case OperandShape::VariadicValues:
            return 0;
    }
    return 0;
}

uint32_t inst_max_operands(OperandShape shape) {
    switch (shape) {
        case OperandShape::None:
            return 0;
        case OperandShape::OneValue:
        case OperandShape::OnePlace:
        case OperandShape::OneEntity:
        case OperandShape::OneName:
        case OperandShape::OneType:
        case OperandShape::TypeOrEntity:
            return 1;
        case OperandShape::PlaceValue:
        case OperandShape::BaseIndex:
        case OperandShape::TwoValues:
        case OperandShape::TypeValue:
        case OperandShape::PlaceEntity:
            return 2;
        case OperandShape::PlaceOptionalEntity:
            return 2;
        case OperandShape::CalleeAndArguments:
        case OperandShape::NameAndArguments:
        case OperandShape::PlaceAndArguments:
        case OperandShape::PlaceEntityAndArguments:
        case OperandShape::VariadicValues:
            return kVariadicMax;
    }
    return 0;
}

bool inst_operand_count_matches(OperandShape shape, uint32_t count) {
    return count >= inst_min_operands(shape) && count <= inst_max_operands(shape);
}

bool inst_operand_kinds_match(OperandShape shape, std::span<const Operand> operands) {
    if (!inst_operand_count_matches(shape, static_cast<uint32_t>(operands.size()))) {
        return false;
    }

    auto is_value = [](const Operand& operand) {
        return operand.kind == OperandKind::Value;
    };
    auto is_entity = [](const Operand& operand) {
        return operand.kind == OperandKind::Entity;
    };
    auto is_type = [](const Operand& operand) {
        return operand.kind == OperandKind::Type;
    };
    auto is_name = [](const Operand& operand) {
        return operand.kind == OperandKind::Name;
    };
    auto rest_are_values = [&](size_t first) {
        for (size_t i = first; i < operands.size(); ++i) {
            if (!is_value(operands[i])) {
                return false;
            }
        }
        return true;
    };

    switch (shape) {
        case OperandShape::None:
            return operands.empty();
        case OperandShape::OneValue:
        case OperandShape::OnePlace:
            return operands.size() == 1 && is_value(operands[0]);
        case OperandShape::OneEntity:
            return operands.size() == 1 && is_entity(operands[0]);
        case OperandShape::OneName:
            return operands.size() == 1 && is_name(operands[0]);
        case OperandShape::OneType:
            return operands.size() == 1 && is_type(operands[0]);
        case OperandShape::TypeOrEntity:
            return operands.size() == 1 &&
                   (is_type(operands[0]) || is_entity(operands[0]));
        case OperandShape::PlaceValue:
        case OperandShape::BaseIndex:
        case OperandShape::TwoValues:
            return operands.size() == 2 && is_value(operands[0]) && is_value(operands[1]);
        case OperandShape::TypeValue:
            return operands.size() == 2 && is_type(operands[0]) && is_value(operands[1]);
        case OperandShape::PlaceEntity:
            return operands.size() == 2 && is_value(operands[0]) && is_entity(operands[1]);
        case OperandShape::CalleeAndArguments:
            return !operands.empty() &&
                   (is_entity(operands[0]) || is_value(operands[0])) &&
                   rest_are_values(1);
        case OperandShape::NameAndArguments:
            return !operands.empty() && is_name(operands[0]) && rest_are_values(1);
        case OperandShape::PlaceAndArguments:
            return !operands.empty() && is_value(operands[0]) && rest_are_values(1);
        case OperandShape::PlaceEntityAndArguments:
            return operands.size() >= 2 &&
                   is_value(operands[0]) &&
                   is_entity(operands[1]) &&
                   rest_are_values(2);
        case OperandShape::PlaceOptionalEntity:
            return !operands.empty() &&
                   is_value(operands[0]) &&
                   (operands.size() == 1 || is_entity(operands[1]));
        case OperandShape::VariadicValues:
            return rest_are_values(0);
    }
    return false;
}

} // namespace aburi::cir
