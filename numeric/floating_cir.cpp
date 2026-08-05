#include "floating_cir.h"

#include "../abi/target_info.h"
#include "../cir/file.h"

namespace aburi::floating {

numeric::FloatFormat semantics_for_builtin(cir::BuiltinTypeKind kind,
                                           const TargetInfo& target) {
    switch (kind) {
        case cir::BuiltinTypeKind::Float16:
            return numeric::FloatFormat::IEEEBinary16;
        case cir::BuiltinTypeKind::Float:
            return numeric::FloatFormat::IEEEBinary32;
        case cir::BuiltinTypeKind::Double:
            return numeric::FloatFormat::IEEEBinary64;
        case cir::BuiltinTypeKind::LongDouble:
            switch (target.long_double_format) {
                case LongDoubleFormat::IEEE_DOUBLE:
                    return numeric::FloatFormat::IEEEBinary64;
                case LongDoubleFormat::X87_EXTENDED:
                    return numeric::FloatFormat::X87Extended80;
                case LongDoubleFormat::IEEE_QUAD:
                    return numeric::FloatFormat::IEEEBinary128;
            }
            break;
        default:
            break;
    }
    return numeric::FloatFormat::Invalid;
}

numeric::FloatFormat semantics_for_type(const cir::File& file,
                                        cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Builtin) {
        return numeric::FloatFormat::Invalid;
    }
    const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
        &file.type_payload(resolved));
    return builtin
        ? semantics_for_builtin(builtin->kind, file.target_info())
        : numeric::FloatFormat::Invalid;
}

} // namespace aburi::floating
