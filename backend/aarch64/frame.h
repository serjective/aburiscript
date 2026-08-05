#ifndef ABURI_BACKEND_AARCH64_FRAME_H
#define ABURI_BACKEND_AARCH64_FRAME_H

#include "../common/mir.h"

namespace aburi::backend::aarch64 {

void lower_frame(MFunction& function);

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_FRAME_H
