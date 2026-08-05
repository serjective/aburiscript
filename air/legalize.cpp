#include "legalize.h"
#include "legalize_internal.h"

#include "verifier.h"

namespace aburi::air {

const char* default_libcall_name(LibcallId id) {
    switch (id) {
        case LibcallId::MulDI3: return "__muldi3";
        case LibcallId::DivDI3: return "__divdi3";
        case LibcallId::UDivDI3: return "__udivdi3";
        case LibcallId::ModDI3: return "__moddi3";
        case LibcallId::UModDI3: return "__umoddi3";
        case LibcallId::AshlDI3: return "__ashldi3";
        case LibcallId::AshrDI3: return "__ashrdi3";
        case LibcallId::LshrDI3: return "__lshrdi3";
        case LibcallId::FloatDISF: return "__floatdisf";
        case LibcallId::FloatDIDF: return "__floatdidf";
        case LibcallId::FloatUnDISF: return "__floatundisf";
        case LibcallId::FloatUnDIDF: return "__floatundidf";
        case LibcallId::FixSFDI: return "__fixsfdi";
        case LibcallId::FixDFDI: return "__fixdfdi";
        case LibcallId::FixUnsSFDI: return "__fixunssfdi";
        case LibcallId::FixUnsDFDI: return "__fixunsdfdi";
        case LibcallId::AddSF3: return "__addsf3";
        case LibcallId::SubSF3: return "__subsf3";
        case LibcallId::MulSF3: return "__mulsf3";
        case LibcallId::DivSF3: return "__divsf3";
        case LibcallId::AddDF3: return "__adddf3";
        case LibcallId::SubDF3: return "__subdf3";
        case LibcallId::MulDF3: return "__muldf3";
        case LibcallId::DivDF3: return "__divdf3";
        case LibcallId::EqSF2: return "__eqsf2";
        case LibcallId::NeSF2: return "__nesf2";
        case LibcallId::LtSF2: return "__ltsf2";
        case LibcallId::LeSF2: return "__lesf2";
        case LibcallId::GtSF2: return "__gtsf2";
        case LibcallId::GeSF2: return "__gesf2";
        case LibcallId::UnordSF2: return "__unordsf2";
        case LibcallId::EqDF2: return "__eqdf2";
        case LibcallId::NeDF2: return "__nedf2";
        case LibcallId::LtDF2: return "__ltdf2";
        case LibcallId::LeDF2: return "__ledf2";
        case LibcallId::GtDF2: return "__gtdf2";
        case LibcallId::GeDF2: return "__gedf2";
        case LibcallId::UnordDF2: return "__unorddf2";
        case LibcallId::TruncDFSF2: return "__truncdfsf2";
        case LibcallId::ExtendSFDF2: return "__extendsfdf2";
        case LibcallId::FloatSISF: return "__floatsisf";
        case LibcallId::FloatSIDF: return "__floatsidf";
        case LibcallId::FloatUnSISF: return "__floatunsisf";
        case LibcallId::FloatUnSIDF: return "__floatunsidf";
        case LibcallId::FixSFSI: return "__fixsfsi";
        case LibcallId::FixDFSI: return "__fixdfsi";
        case LibcallId::FixUnsSFSI: return "__fixunssfsi";
        case LibcallId::FixUnsDFSI: return "__fixunsdfsi";
        case LibcallId::FmodF: return "fmodf";
        case LibcallId::Fmod: return "fmod";
    }
    return "";
}

namespace legalize_detail {

const char* libcall_name(const LegalizeConfig& config, LibcallId id) {
    if (config.libcall_override != nullptr) {
        if (const char* name = config.libcall_override(id)) {
            return name;
        }
    }
    return default_libcall_name(id);
}

FuncId find_or_declare(Module& mod, std::string_view name, const SigData& sig) {
    FuncId existing = mod.find_function(name);
    if (mod.is_valid(existing)) {
        return existing;
    }
    return mod.create_function(std::string(name), mod.types().get_signature(sig));
}

} // namespace legalize_detail

LegalizeResult run_legalize(Module& mod, const LegalizeConfig& config) {
    LegalizeResult result;

    if (config.soft_float) {
        legalize_detail::StageState state(config);
        legalize_detail::run_soft_float_stage(mod, state);
        result.changed |= state.changed;
        if (!state.ok) {
            result.ok = false;
            result.error = std::move(state.error);
            return result;
        }
    }

    if (config.split_i64 && config.word_bytes == 4) {
        legalize_detail::StageState state(config);
        legalize_detail::run_i64_stage(mod, state);
        result.changed |= state.changed;
        if (!state.ok) {
            result.ok = false;
            result.error = std::move(state.error);
            return result;
        }
    }

    if (result.changed) {
        VerifyResult verified = verify_module(mod);
        if (!verified.ok()) {
            result.ok = false;
            result.error = "legalized module failed verification: " +
                           verified.to_string();
        }
    }
    return result;
}

} // namespace aburi::air
