#ifndef ABURI_BACKEND_COMMON_MIR_VERIFIER_H
#define ABURI_BACKEND_COMMON_MIR_VERIFIER_H

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "mir.h"
#include "regalloc.h"

namespace aburi::backend {

enum class MirStage : uint8_t {
    PostIsel,
    PostRegAlloc,
    PostFrame,
};

std::string_view mir_stage_name(MirStage stage);

struct MirOpcodeFacts {
    bool is_terminator = false;
    bool is_call = false;
    bool is_pseudo = false;
    bool defines_operand0 = false;
    bool reads_operand0 = false;
    bool is_conditional_branch = false;
    bool is_frame_pseudo = false;
    bool is_asm_block = false;
    bool is_eh_label = false;
};

inline constexpr uint8_t MK_Reg = 1u << 0;
inline constexpr uint8_t MK_Imm = 1u << 1;
inline constexpr uint8_t MK_Frame = 1u << 2;
inline constexpr uint8_t MK_Symbol = 1u << 3;
inline constexpr uint8_t MK_Label = 1u << 4;

inline constexpr uint8_t kMirShapePositions = 4;
inline constexpr uint8_t kMirUnbounded = 0xFF;

struct MirShape {
    uint8_t min_operands = 0;
    uint8_t max_operands = 0;
    uint8_t kinds[kMirShapePositions] = {};
    uint8_t class_checked = 0;
    RegClass classes[kMirShapePositions] = {};
};

inline MirShape mir_shape(uint8_t min, uint8_t max,
                          std::initializer_list<uint8_t> kinds) {
    MirShape shape;
    shape.min_operands = min;
    shape.max_operands = max;
    size_t position = 0;
    for (uint8_t kind : kinds) {
        if (position >= kMirShapePositions) {
            break;
        }
        shape.kinds[position++] = kind;
    }
    return shape;
}

inline MirShape mir_shape_class(MirShape shape, size_t position,
                                RegClass cls) {
    if (position < kMirShapePositions) {
        shape.class_checked |= static_cast<uint8_t>(1u << position);
        shape.classes[position] = cls;
    }
    return shape;
}

struct MirTargetInfo {
    std::string_view (*mnemonic)(uint16_t opcode) = nullptr;
    MirOpcodeFacts (*facts)(uint16_t opcode) = nullptr;
    MirShape (*shape)(uint16_t opcode) = nullptr;
    uint32_t phys_reg_count = 0;
};

struct MirVerifierDiag {
    enum class Severity : uint8_t {
        Error,
        Note,
    };
    Severity severity = Severity::Error;
    std::string message;
};

struct MirVerifyResult {
    std::vector<MirVerifierDiag> diags;

    bool ok() const {
        for (const MirVerifierDiag& diag : diags) {
            if (diag.severity == MirVerifierDiag::Severity::Error) {
                return false;
            }
        }
        return true;
    }
    uint32_t error_count() const {
        uint32_t count = 0;
        for (const MirVerifierDiag& diag : diags) {
            if (diag.severity == MirVerifierDiag::Severity::Error) {
                ++count;
            }
        }
        return count;
    }
    std::string to_string() const;
};

MirVerifyResult verify_mfunction(const MFunction& func,
                                 const TargetRegInfo& regs,
                                 const MirTargetInfo& target, MirStage stage,
                                 int opt_level);

void verify_mfunction_into(const MFunction& func, const TargetRegInfo& regs,
                           const MirTargetInfo& target, MirStage stage,
                           int opt_level, MirVerifyResult& result);

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_MIR_VERIFIER_H
