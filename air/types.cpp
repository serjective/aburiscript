#include "types.h"

#include <cassert>

namespace aburi::air {

namespace {

uint64_t hash_combine(uint64_t seed, uint64_t value) {
    return seed ^ (value + UINT64_C(0x9e3779b97f4a7c15) + (seed << 12) + (seed >> 4));
}

uint64_t hash_type(const TypeData& data) {
    uint64_t h = hash_combine(0x11u, static_cast<uint64_t>(data.kind));
    h = hash_combine(h, static_cast<uint64_t>(data.float_kind));
    h = hash_combine(h, data.int_width);
    h = hash_combine(h, data.address_space);
    return h;
}

bool type_equals(const TypeData& a, const TypeData& b) {
    return a.kind == b.kind && a.float_kind == b.float_kind &&
           a.int_width == b.int_width && a.address_space == b.address_space;
}

uint64_t hash_sig(const SigData& sig) {
    uint64_t h = hash_combine(0x51u, static_cast<uint64_t>(sig.ret_class));
    h = hash_combine(h, sig.ret_type.index);
    h = hash_combine(h, sig.ret_count);
    h = hash_combine(h, sig.is_variadic ? 1 : 0);
    h = hash_combine(h, sig.fixed_param_count);
    h = hash_combine(h, sig.ret_sse_mask);
    for (SigParam param : sig.params) {
        h = hash_combine(h, param.type.index);
        h = hash_combine(h, static_cast<uint64_t>(param.role));
        h = hash_combine(h, param.byval_size);
        h = hash_combine(h, param.byval_align);
        h = hash_combine(h, param.coerce_group);
    }
    return h;
}

bool sig_equals(const SigData& a, const SigData& b) {
    return a.ret_class == b.ret_class && a.ret_type == b.ret_type &&
           a.ret_count == b.ret_count && a.ret_sse_mask == b.ret_sse_mask &&
           a.is_variadic == b.is_variadic &&
           a.fixed_param_count == b.fixed_param_count && a.params == b.params;
}

} // namespace

TypeTable::TypeTable() {
    types_.emplace_back();
    sigs_.emplace_back();

    auto put = [&](TypeData data, TypeId expected) {
        TypeId id = intern(data);
        assert(id == expected);
        (void)id;
        (void)expected;
    };
    put({TypeKind::Void, FloatKind::F64, 0, 0}, types::VOID);
    put({TypeKind::Int, FloatKind::F64, 8, 0}, types::I8);
    put({TypeKind::Int, FloatKind::F64, 16, 0}, types::I16);
    put({TypeKind::Int, FloatKind::F64, 32, 0}, types::I32);
    put({TypeKind::Int, FloatKind::F64, 64, 0}, types::I64);
    put({TypeKind::Int, FloatKind::F64, 128, 0}, types::I128);
    put({TypeKind::Float, FloatKind::F32, 0, 0}, types::F32);
    put({TypeKind::Float, FloatKind::F64, 0, 0}, types::F64);
    put({TypeKind::Float, FloatKind::F128, 0, 0}, types::F128);
    put({TypeKind::Ptr, FloatKind::F64, 0, 0}, types::PTR);
    put({TypeKind::Float, FloatKind::F80, 0, 0}, types::F80);
}

TypeId TypeTable::get_int(uint16_t bit_width) {
    return intern({TypeKind::Int, FloatKind::F64, bit_width, 0});
}

TypeId TypeTable::get_float(FloatKind kind) {
    return intern({TypeKind::Float, kind, 0, 0});
}

TypeId TypeTable::get_ptr(uint32_t address_space) {
    return intern({TypeKind::Ptr, FloatKind::F64, 0, address_space});
}

SigId TypeTable::get_signature(SigData sig) {
    if (!sig.is_variadic) {

        sig.fixed_param_count = static_cast<uint32_t>(sig.params.size());
    }
    uint64_t h = hash_sig(sig);
    auto range = sig_lookup_.equal_range(h);
    for (auto it = range.first; it != range.second; ++it) {
        if (sig_equals(sigs_[it->second], sig)) {
            return SigId{it->second};
        }
    }
    SigId id{static_cast<uint32_t>(sigs_.size())};
    sigs_.push_back(std::move(sig));
    sig_lookup_.emplace(h, id.index);
    return id;
}

SigId TypeTable::get_signature(RetClass ret_class, TypeId ret_type, uint8_t ret_count,
                               std::span<const SigParam> params, bool is_variadic,
                               uint32_t fixed_param_count) {
    SigData sig;
    sig.ret_class = ret_class;
    sig.ret_type = ret_type;
    sig.ret_count = ret_count;
    sig.params.assign(params.begin(), params.end());
    sig.is_variadic = is_variadic;
    sig.fixed_param_count =
        is_variadic ? fixed_param_count : static_cast<uint32_t>(params.size());
    return get_signature(std::move(sig));
}

const TypeData& TypeTable::type(TypeId id) const {
    assert(is_valid(id));
    return types_[id.index];
}

const SigData& TypeTable::signature(SigId id) const {
    assert(is_valid(id));
    return sigs_[id.index];
}

uint64_t TypeTable::byte_size(TypeId id, uint32_t ptr_size_bytes) const {
    const TypeData& data = type(id);
    switch (data.kind) {
        case TypeKind::Void:
            return 0;
        case TypeKind::Int:
            return (static_cast<uint64_t>(data.int_width) + 7) / 8;
        case TypeKind::Float:
            switch (data.float_kind) {
                case FloatKind::F32: return 4;
                case FloatKind::F64: return 8;
                case FloatKind::F128: return 16;
                case FloatKind::F80: return 16;
            }
            return 8;
        case TypeKind::Ptr:
            return ptr_size_bytes;
    }
    return 0;
}

std::string TypeTable::spelling(TypeId id) const {
    const TypeData& data = type(id);
    switch (data.kind) {
        case TypeKind::Void:
            return "void";
        case TypeKind::Int:
            return "i" + std::to_string(data.int_width);
        case TypeKind::Float:
            switch (data.float_kind) {
                case FloatKind::F32: return "f32";
                case FloatKind::F64: return "f64";
                case FloatKind::F128: return "f128";
                case FloatKind::F80: return "f80";
            }
            return "f?";
        case TypeKind::Ptr:
            if (data.address_space == 0) {
                return "ptr";
            }
            return "ptr(" + std::to_string(data.address_space) + ")";
    }
    return "?";
}

TypeId TypeTable::intern(const TypeData& data) {
    uint64_t h = hash_type(data);
    auto range = type_lookup_.equal_range(h);
    for (auto it = range.first; it != range.second; ++it) {
        if (type_equals(types_[it->second], data)) {
            return TypeId{it->second};
        }
    }
    TypeId id{static_cast<uint32_t>(types_.size())};
    types_.push_back(data);
    type_lookup_.emplace(h, id.index);
    return id;
}

} // namespace aburi::air
