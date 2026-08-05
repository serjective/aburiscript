#ifndef ABURI_CIRPASSES_OBJC_LOWER_H
#define ABURI_CIRPASSES_OBJC_LOWER_H

#include "../cir/file.h"

namespace aburi::cirpasses {

struct ObjCLowerResult {
    bool changed = false;
};

ObjCLowerResult lower_objc(cir::File& file, bool arc = false);

} // namespace aburi::cirpasses

#endif // ABURI_CIRPASSES_OBJC_LOWER_H
