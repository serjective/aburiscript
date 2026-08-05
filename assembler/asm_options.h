#ifndef ABURI_ASSEMBLER_ASM_OPTIONS_H
#define ABURI_ASSEMBLER_ASM_OPTIONS_H

#include <memory>
#include <string>

#include "../abi/target_info.h"
namespace aburi::assembler {

struct AsmOptions {
    std::shared_ptr<const TargetInfo> target;
    std::string filename = "<asm>";
    bool fragment_mode = false;
};
inline bool asm_target_is_elf(const TargetInfo& target) {
    return target.os != TargetOS::MACOS;
}

}

#endif
