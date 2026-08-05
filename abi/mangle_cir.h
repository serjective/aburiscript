#ifndef ABURI_ABI_MANGLE_CIR_H
#define ABURI_ABI_MANGLE_CIR_H

#include <string>

#include "../cir/file.h"

namespace aburi::abi {

std::string itanium_linkage_name(const cir::File& file, cir::EntityId entity);

std::string itanium_structor_variant_name(const cir::File& file,
                                          cir::EntityId entity,
                                          const char* variant,
                                          bool skip_trailing_param = false,
                                          cir::EntityId
                                              inherited_origin_record = {});

std::string itanium_record_data_symbol(const cir::File& file,
                                       cir::EntityId record_entity,
                                       const char* prefix);

std::string itanium_type_data_symbol(const cir::File& file,
                                     cir::TypeRef type,
                                     const char* prefix);

std::string itanium_construction_vtable_symbol(const cir::File& file,
                                               cir::EntityId derived_entity,
                                               cir::EntityId base_entity,
                                               size_t offset);
std::string itanium_virtual_thunk_symbol(
    const cir::File& file,
    cir::EntityId target,
    const cir::VirtualAdjustmentFact& this_adjustment,
    const cir::VirtualAdjustmentFact& result_adjustment = {});

} // namespace aburi::abi

#endif // ABURI_ABI_MANGLE_CIR_H
