#ifndef ABURI_CIR_INST_SCHEMA_H
#define ABURI_CIR_INST_SCHEMA_H

#include <cstdint>
#include <span>
#include <string_view>

#include "file.h"

namespace aburi::cir {

enum class OperandShape : uint8_t {
    None,
    OneValue,
    OnePlace,
    OneEntity,
    OneName,
    OneType,
    PlaceValue,
    BaseIndex,
    TwoValues,
    TypeValue,
    PlaceEntity,
    CalleeAndArguments,
    NameAndArguments,
    PlaceAndArguments,
    PlaceEntityAndArguments,
    PlaceOptionalEntity,
    TypeOrEntity,
    VariadicValues
};

enum class ResultShape : uint8_t {
    NoResult,
    Explicit,
    BuiltinInt,
    BuiltinBool,
    PointerToChar,
    PlaceObject,
    PointerToPlaceObject,
    PlaceOfPointerPointee
};

struct InstSchema {
    InstKind kind = InstKind::Invalid;
    std::string_view kind_name;
    std::string_view mnemonic;
    OperandShape operand_shape = OperandShape::None;
    ResultShape result_shape = ResultShape::NoResult;
    std::string_view description;
};

std::span<const InstSchema> all_inst_schemas();
const InstSchema& inst_schema(InstKind kind);
std::string_view inst_mnemonic(InstKind kind);
bool inst_has_result(InstKind kind);
uint32_t inst_min_operands(OperandShape shape);
uint32_t inst_max_operands(OperandShape shape);
bool inst_operand_count_matches(OperandShape shape, uint32_t count);
bool inst_operand_kinds_match(OperandShape shape, std::span<const Operand> operands);

} // namespace aburi::cir

#endif // ABURI_CIR_INST_SCHEMA_H
