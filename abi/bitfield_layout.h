#ifndef ABURI_BITFIELD_LAYOUT_H
#define ABURI_BITFIELD_LAYOUT_H

#include "ast/types.h"
#include "abi/target_info.h"
#include <vector>

// Bitfield ABI determines how bitfields are packed relative to each other
// and to non-bitfield members.
enum class BitfieldABI {
    // Itanium ABI (GCC/Clang on ARM64, x86-64 Linux/macOS):
    // Bitfields pack tightly at the current bit position. A bitfield only
    // starts at a new aligned boundary if its bits would straddle an
    // alignment boundary of its declared type. After a bitfield group,
    // the next field starts at the next byte after the last used bit.
    ITANIUM,

    // MSVC ABI (Windows x86-64):
    // Bitfields always occupy a storage unit of the declared type's size.
    // Adjacent bitfields of different declared types start new storage units.
    // After a bitfield group, the full storage unit size is consumed.
    MSVC,
};

// Configuration for bitfield layout computation
struct BitfieldLayoutConfig {
    TargetArch arch = TargetArch::AARCH64;

    // Which ABI rules to follow for bitfield layout
    BitfieldABI abi = BitfieldABI::ITANIUM;

    // GCC default: plain 'int' bitfield is signed
    bool plain_int_is_signed = true;

    // Bit ordering within storage units
    // true = LSB first (little-endian bit allocation)
    bool lsb_first = true;

    // Max alignment from #pragma pack, 0 = default
    size_t pack_alignment = 0;

    // True if the enclosing record has __attribute__((packed)).
    bool record_packed = false;

    // ABI pointer size. C++ reference data members are stored as pointers even
    // though sizeof(T&) is the size of T.
    size_t pointer_size_bytes = 8;
};

// Engine for computing bitfield layouts according to ABI rules
//
// Usage:
//   BitfieldLayoutEngine engine;
//   size_t size, alignment;
//   engine.compute_layout(fields, is_union, size, alignment);
//
// After compute_layout, each Field will have:
//   - offset: byte offset of storage unit (or field for non-bitfields)
//   - bit_offset: bit position within storage unit (0 for non-bitfields)
//   - bit_width: width in bits (0 for non-bitfields)
//   - storage_size: storage unit size in bits (0 for non-bitfields)
class BitfieldLayoutEngine {
public:
    explicit BitfieldLayoutEngine(BitfieldLayoutConfig config = {});

    // Compute layout for all fields in a struct/union
    // Updates Field::offset, bit_offset, bit_width, storage_size
    void compute_layout(std::vector<ObjectType::Field>& fields,
                        bool is_union,
                        size_t& out_total_size,
                        size_t& out_alignment);

private:
    BitfieldLayoutConfig config_;

    // Get storage unit size for a bitfield type (in bits)
    // Returns 8, 16, 32, or 64 based on the declared type
    uint32_t get_storage_unit_size(const std::shared_ptr<CType>& type);

    // Get alignment requirement for a type (in bytes)
    size_t get_type_alignment(const std::shared_ptr<CType>& type);

    // Get non-bitfield storage size for a record member.
    size_t get_field_storage_size(const ObjectType::Field& field);

    // Compute layout for struct (non-union), Itanium ABI
    void compute_struct_layout_itanium(std::vector<ObjectType::Field>& fields,
                                       size_t& out_total_size,
                                       size_t& out_alignment);

    // Compute layout for struct (non-union), MSVC ABI
    void compute_struct_layout_msvc(std::vector<ObjectType::Field>& fields,
                                    size_t& out_total_size,
                                    size_t& out_alignment);

    // Compute layout for union
    void compute_union_layout(std::vector<ObjectType::Field>& fields,
                              size_t& out_total_size,
                              size_t& out_alignment);
};

#endif // ABURI_BITFIELD_LAYOUT_H
