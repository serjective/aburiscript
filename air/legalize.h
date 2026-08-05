#ifndef ABURI_AIR_LEGALIZE_H
#define ABURI_AIR_LEGALIZE_H

#include "module.h"

#include <cstdint>
#include <string>

namespace aburi::air {

enum class LegalizeAction : uint8_t {
    Keep,
    Expand,
    Libcall,
};

enum class LibcallId : uint16_t {
    MulDI3, DivDI3, UDivDI3, ModDI3, UModDI3,
    AshlDI3, AshrDI3, LshrDI3,
    FloatDISF, FloatDIDF, FloatUnDISF, FloatUnDIDF,
    FixSFDI, FixDFDI, FixUnsSFDI, FixUnsDFDI,
    AddSF3, SubSF3, MulSF3, DivSF3,
    AddDF3, SubDF3, MulDF3, DivDF3,
    EqSF2, NeSF2, LtSF2, LeSF2, GtSF2, GeSF2, UnordSF2,
    EqDF2, NeDF2, LtDF2, LeDF2, GtDF2, GeDF2, UnordDF2,
    TruncDFSF2, ExtendSFDF2,
    FloatSISF, FloatSIDF, FloatUnSISF, FloatUnSIDF,
    FixSFSI, FixDFSI, FixUnsSFSI, FixUnsDFSI,
    FmodF, Fmod,
};

const char* default_libcall_name(LibcallId id);

struct I64Actions {
    LegalizeAction add_sub   = LegalizeAction::Expand;
    LegalizeAction mul       = LegalizeAction::Libcall;
    LegalizeAction div_rem   = LegalizeAction::Libcall;
    LegalizeAction shifts    = LegalizeAction::Libcall;
    LegalizeAction bit_manip = LegalizeAction::Expand;
};

struct SoftFloatActions {
    bool soften_f32 = true;
    bool soften_f64 = true;
};

struct LegalizeConfig {
    uint32_t word_bytes = 8;
    EndiannessKind endianness = EndiannessKind::Little;
    bool split_i64 = false;
    I64Actions i64;
    bool soft_float = false;
    SoftFloatActions floats;
    const char* (*libcall_override)(LibcallId) = nullptr;
};

struct LegalizeResult {
    bool changed = false;
    bool ok = true;
    std::string error;
};

LegalizeResult run_legalize(Module& mod, const LegalizeConfig& config);

} // namespace aburi::air

#endif // ABURI_AIR_LEGALIZE_H
