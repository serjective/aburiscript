#include "insts.h"

#include <array>

namespace aburi::air {

namespace {

struct OpcodeTraits {
    std::string_view mnemonic;
    int operand_count;
    bool is_terminator;
    ResultKind result_kind;
    bool has_side_effects;
};

constexpr OpcodeTraits kTraits[] = {
#define ABURI_AIR_OPCODE(Name, mnemonic, operand_count, is_terminator, result_kind, \
                         has_side_effects)                                          \
    {mnemonic, operand_count, is_terminator != 0,                                   \
     static_cast<ResultKind>(result_kind), has_side_effects != 0},
#include "opcodes.def"
#undef ABURI_AIR_OPCODE
};

constexpr uint16_t kOpcodeCount = sizeof(kTraits) / sizeof(kTraits[0]);

constexpr std::string_view kIntCondNames[] = {
    "eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge",
};

constexpr std::string_view kFloatCondNames[] = {
    "oeq", "one", "olt", "ole", "ogt", "oge", "ord", "uno",
    "ueq", "une", "ult", "ule", "ugt", "uge",
};

constexpr std::string_view kMemOrderNames[] = {
    "relaxed", "acquire", "release", "acq_rel", "seq_cst",
};

constexpr std::string_view kRmwOpNames[] = {
    "xchg", "add", "sub", "and", "nand", "or", "xor", "max", "min", "umax", "umin",
};

const OpcodeTraits& traits(Opcode op) {
    return kTraits[static_cast<uint16_t>(op)];
}

} // namespace

uint16_t opcode_count() { return kOpcodeCount; }

std::string_view opcode_mnemonic(Opcode op) { return traits(op).mnemonic; }

int opcode_operand_count(Opcode op) { return traits(op).operand_count; }

bool opcode_is_terminator(Opcode op) { return traits(op).is_terminator; }

ResultKind opcode_result_kind(Opcode op) { return traits(op).result_kind; }

bool opcode_has_side_effects(Opcode op) { return traits(op).has_side_effects; }

bool opcode_is_cast(Opcode op) {
    switch (op) {
        case Opcode::Trunc:
        case Opcode::Zext:
        case Opcode::Sext:
        case Opcode::Fptrunc:
        case Opcode::Fpext:
        case Opcode::Fptosi:
        case Opcode::Fptoui:
        case Opcode::Sitofp:
        case Opcode::Uitofp:
        case Opcode::Ptrtoint:
        case Opcode::Inttoptr:
        case Opcode::Bitcast:
            return true;
        default:
            return false;
    }
}

std::optional<Opcode> opcode_from_mnemonic(std::string_view mnemonic) {
    for (uint16_t i = 0; i < kOpcodeCount; ++i) {
        if (kTraits[i].mnemonic == mnemonic) {
            return static_cast<Opcode>(i);
        }
    }
    return std::nullopt;
}

std::string_view int_cond_mnemonic(IntCond cond) {
    return kIntCondNames[static_cast<uint8_t>(cond)];
}

std::string_view float_cond_mnemonic(FloatCond cond) {
    return kFloatCondNames[static_cast<uint8_t>(cond)];
}

std::optional<IntCond> int_cond_from_mnemonic(std::string_view mnemonic) {
    for (uint8_t i = 0; i < sizeof(kIntCondNames) / sizeof(kIntCondNames[0]); ++i) {
        if (kIntCondNames[i] == mnemonic) {
            return static_cast<IntCond>(i);
        }
    }
    return std::nullopt;
}

std::optional<FloatCond> float_cond_from_mnemonic(std::string_view mnemonic) {
    for (uint8_t i = 0; i < sizeof(kFloatCondNames) / sizeof(kFloatCondNames[0]);
         ++i) {
        if (kFloatCondNames[i] == mnemonic) {
            return static_cast<FloatCond>(i);
        }
    }
    return std::nullopt;
}

std::string_view mem_order_mnemonic(MemOrder order) {
    return kMemOrderNames[static_cast<uint8_t>(order)];
}

std::optional<MemOrder> mem_order_from_mnemonic(std::string_view mnemonic) {
    for (uint8_t i = 0; i < sizeof(kMemOrderNames) / sizeof(kMemOrderNames[0]); ++i) {
        if (kMemOrderNames[i] == mnemonic) {
            return static_cast<MemOrder>(i);
        }
    }
    return std::nullopt;
}

std::string_view rmw_op_mnemonic(RmwOp op) {
    return kRmwOpNames[static_cast<uint8_t>(op)];
}

std::optional<RmwOp> rmw_op_from_mnemonic(std::string_view mnemonic) {
    for (uint8_t i = 0; i < sizeof(kRmwOpNames) / sizeof(kRmwOpNames[0]); ++i) {
        if (kRmwOpNames[i] == mnemonic) {
            return static_cast<RmwOp>(i);
        }
    }
    return std::nullopt;
}

} // namespace aburi::air
