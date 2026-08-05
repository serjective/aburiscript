#ifndef ABURI_BACKEND_X86_FRAME_H
#define ABURI_BACKEND_X86_FRAME_H

#include "../common/mir.h"

namespace aburi::backend::x86 {

void lower_frame(MFunction& function);

} // namespace aburi::backend::x86

#endif // ABURI_BACKEND_X86_FRAME_H
