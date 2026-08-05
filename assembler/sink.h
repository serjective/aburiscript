#ifndef ABURI_ASSEMBLER_SINK_H
#define ABURI_ASSEMBLER_SINK_H

#include <ostream>
#include <string>

#include "../abi/target_info.h"
#include "unit.h"

namespace aburi::assembler {

bool write_macho_object(AsmUnit& unit, const TargetInfo& target,
                        std::ostream& out, std::string& error);

}

#endif
