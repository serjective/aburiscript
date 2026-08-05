#ifndef ABURI_ASSEMBLER_AARCH64_ASM_AARCH64_H
#define ABURI_ASSEMBLER_AARCH64_ASM_AARCH64_H

#include "../assembler.h"

namespace aburi::assembler::aarch64 {

void parse_instruction(Assembler& assembler, Lexer& lexer,
                       const Token& mnemonic);

}

#endif
