#ifndef ABURI_AIR_INSTS_H
#define ABURI_AIR_INSTS_H

#include <cstdint>
#include <optional>
#include <string_view>

namespace aburi::air {

enum class Opcode : uint16_t {
#define ABURI_AIR_OPCODE(Name, mnemonic, operand_count, is_terminator, result_kind, \
                         has_side_effects)                                          \
    Name,
#include "opcodes.def"
#undef ABURI_AIR_OPCODE
};

enum class ResultKind : uint8_t {
    None,
    Value,
    SigDependent,
};

enum class IntCond : uint8_t {
    Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge,
};

enum class FloatCond : uint8_t {
    Oeq, One, Olt, Ole, Ogt, Oge, Ord, Uno,
    Ueq, Une, Ult, Ule, Ugt, Uge,
};

enum class MemOrder : uint8_t {
    Relaxed, Acquire, Release, AcqRel, SeqCst,
};

enum class RmwOp : uint8_t {
    Xchg, Add, Sub, And, Nand, Or, Xor, Max, Min, UMax, UMin,
};

inline constexpr uint16_t INST_FLAG_VOLATILE = 1u << 0;

inline uint64_t pack_atomic_access_aux(MemOrder order, uint8_t align_log2) {
    return static_cast<uint64_t>(order) | (static_cast<uint64_t>(align_log2) << 8);
}
inline MemOrder atomic_access_order(uint64_t aux) {
    return static_cast<MemOrder>(aux & 0xFF);
}
inline uint8_t atomic_access_align_log2(uint64_t aux) {
    return static_cast<uint8_t>(aux >> 8);
}
inline uint64_t pack_rmw_aux(RmwOp op, MemOrder order) {
    return static_cast<uint64_t>(op) | (static_cast<uint64_t>(order) << 8);
}
inline RmwOp rmw_op(uint64_t aux) { return static_cast<RmwOp>(aux & 0xFF); }
inline MemOrder rmw_order(uint64_t aux) { return static_cast<MemOrder>(aux >> 8); }
inline uint64_t pack_cas_aux(MemOrder success, MemOrder failure) {
    return static_cast<uint64_t>(success) | (static_cast<uint64_t>(failure) << 8);
}
inline MemOrder cas_success_order(uint64_t aux) {
    return static_cast<MemOrder>(aux & 0xFF);
}
inline MemOrder cas_failure_order(uint64_t aux) {
    return static_cast<MemOrder>(aux >> 8);
}

uint16_t opcode_count();
std::string_view opcode_mnemonic(Opcode op);
int opcode_operand_count(Opcode op);
bool opcode_is_terminator(Opcode op);
ResultKind opcode_result_kind(Opcode op);
bool opcode_has_side_effects(Opcode op);
bool opcode_is_cast(Opcode op);
std::optional<Opcode> opcode_from_mnemonic(std::string_view mnemonic);

std::string_view int_cond_mnemonic(IntCond cond);
std::string_view float_cond_mnemonic(FloatCond cond);
std::optional<IntCond> int_cond_from_mnemonic(std::string_view mnemonic);
std::optional<FloatCond> float_cond_from_mnemonic(std::string_view mnemonic);

std::string_view mem_order_mnemonic(MemOrder order);
std::optional<MemOrder> mem_order_from_mnemonic(std::string_view mnemonic);
std::string_view rmw_op_mnemonic(RmwOp op);
std::optional<RmwOp> rmw_op_from_mnemonic(std::string_view mnemonic);

} // namespace aburi::air

#endif // ABURI_AIR_INSTS_H
