#ifndef ABURI_ASSEMBLER_X86_ASM_X86_H
#define ABURI_ASSEMBLER_X86_ASM_X86_H

#include "../assembler.h"

namespace aburi::assembler::x86 {

void parse_instruction(Assembler& assembler, Lexer& lexer,
                       const Token& mnemonic);

}

#endif
