#ifndef ABURI_AIR_TYPES_H
#define ABURI_AIR_TYPES_H

#include "ids.h"

#include <cstdint>
#include <span>
#include <string>
#include <unordered_map>
#include <vector>

namespace aburi::air {

enum class TypeKind : uint8_t {
    Void,
    Int,
    Float,
    Ptr,
};

enum class FloatKind : uint8_t {
    F32,
    F64,
    F128,
    F80,
};

struct TypeData {
    TypeKind kind = TypeKind::Void;
    FloatKind float_kind = FloatKind::F64;
    uint16_t int_width = 0;
    uint32_t address_space = 0;
};

enum class RetClass : uint8_t {
    Void,
    Scalar,
    IntPair,
    Hfa,
    IndirectSret,
};

enum class ParamRole : uint8_t {
    Normal,
    Sret,
    IndirectByval,
    StackByval,
};

struct SigParam {
    TypeId type;
    ParamRole role = ParamRole::Normal;
    uint32_t byval_size = 0;
    uint32_t byval_align = 0;
    // First slot of a multi-slot coerced composite: the slot count. SysV
    // assigns such groups registers all-or-nothing, so the backend needs
    // the grouping the flattened parameter list otherwise loses.
    uint8_t coerce_group = 0;
};

inline bool operator==(SigParam lhs, SigParam rhs) {
    return lhs.type == rhs.type && lhs.role == rhs.role &&
           lhs.byval_size == rhs.byval_size &&
           lhs.byval_align == rhs.byval_align &&
           lhs.coerce_group == rhs.coerce_group;
}
inline bool operator!=(SigParam lhs, SigParam rhs) { return !(lhs == rhs); }

struct SigData {
    RetClass ret_class = RetClass::Void;
    TypeId ret_type;
    uint8_t ret_count = 0;
    uint8_t ret_sse_mask = 0;
    std::vector<SigParam> params;
    bool is_variadic = false;
    uint32_t fixed_param_count = 0;
};

namespace types {
inline constexpr TypeId VOID{1};
inline constexpr TypeId I8{2};
inline constexpr TypeId I16{3};
inline constexpr TypeId I32{4};
inline constexpr TypeId I64{5};
inline constexpr TypeId I128{6};
inline constexpr TypeId F32{7};
inline constexpr TypeId F64{8};
inline constexpr TypeId F128{9};
inline constexpr TypeId PTR{10};
inline constexpr TypeId F80{11};
} // namespace types

class TypeTable {
public:
    TypeTable();

    TypeId get_int(uint16_t bit_width);
    TypeId get_float(FloatKind kind);
    TypeId get_ptr(uint32_t address_space = 0);

    SigId get_signature(SigData sig);
    SigId get_signature(RetClass ret_class, TypeId ret_type, uint8_t ret_count,
                        std::span<const SigParam> params, bool is_variadic = false,
                        uint32_t fixed_param_count = 0);

    const TypeData& type(TypeId id) const;
    const SigData& signature(SigId id) const;

    uint32_t type_count() const { return static_cast<uint32_t>(types_.size()) - 1; }
    uint32_t signature_count() const { return static_cast<uint32_t>(sigs_.size()) - 1; }
    bool is_valid(TypeId id) const { return id.index > 0 && id.index < types_.size(); }
    bool is_valid(SigId id) const { return id.index > 0 && id.index < sigs_.size(); }

    bool is_void(TypeId id) const { return type(id).kind == TypeKind::Void; }
    bool is_int(TypeId id) const { return type(id).kind == TypeKind::Int; }
    bool is_float(TypeId id) const { return type(id).kind == TypeKind::Float; }
    bool is_ptr(TypeId id) const { return type(id).kind == TypeKind::Ptr; }
    bool is_scalar(TypeId id) const {
        TypeKind k = type(id).kind;
        return k == TypeKind::Int || k == TypeKind::Float || k == TypeKind::Ptr;
    }
    uint16_t int_width(TypeId id) const { return type(id).int_width; }

    uint64_t byte_size(TypeId id, uint32_t ptr_size_bytes) const;
    std::string spelling(TypeId id) const;

private:
    TypeId intern(const TypeData& data);

    std::vector<TypeData> types_;
    std::vector<SigData> sigs_;
    std::unordered_multimap<uint64_t, uint32_t> type_lookup_;
    std::unordered_multimap<uint64_t, uint32_t> sig_lookup_;
};

} // namespace aburi::air

#endif // ABURI_AIR_TYPES_H
