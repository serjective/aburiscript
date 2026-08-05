#include "x86_64_call_classify.h"

#include <algorithm>
#include <optional>
#include <variant>

#include "../cir/layout.h"
#include "aarch64_call_classify.h"

namespace aburi::abi {

namespace {

bool is_x86_64_sysv(const TargetInfo& target) {
    return target.arch == TargetArch::X86_64 &&
           (target.os == TargetOS::MACOS || target.os == TargetOS::LINUX);
}

enum class SlotCls : uint8_t { None, Sse, Int };

struct ClassifyState {
    SlotCls slots[2] = {SlotCls::None, SlotCls::None};
    bool memory = false;
};

void merge_slot(SlotCls& slot, SlotCls cls) {
    if (cls == SlotCls::Int || slot == SlotCls::None) {
        slot = std::max(slot, cls);
    }
}

void mark_bytes(ClassifyState& state, uint64_t offset, uint64_t size,
                SlotCls cls) {
    uint64_t end = offset + size;
    for (int slot = 0; slot < 2; ++slot) {
        uint64_t lo = 8ull * static_cast<uint64_t>(slot);
        if (offset < lo + 8 && end > lo) {
            merge_slot(state.slots[slot], cls);
        }
    }
}

void classify_bytes(const cir::File& file, const TargetInfo& target,
                    cir::TypeId type, uint64_t offset, ClassifyState& state) {
    if (state.memory) {
        return;
    }
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        state.memory = true;
        return;
    }
    auto size_align = cir::size_align_of_type(file, resolved);
    if (!size_align) {
        state.memory = true;
        return;
    }
    uint64_t size = size_align->size_bytes;

    const cir::Type& cir_type = file.type(resolved);
    const cir::TypePayload& payload = file.type_payload(resolved);
    switch (cir_type.kind) {
        case cir::TypeKind::Builtin: {
            cir::BuiltinTypeKind kind =
                std::get<cir::BuiltinTypePayload>(payload).kind;
            switch (kind) {
                case cir::BuiltinTypeKind::Float16:
                case cir::BuiltinTypeKind::Float:
                case cir::BuiltinTypeKind::Double:
                    mark_bytes(state, offset, size, SlotCls::Sse);
                    return;
                case cir::BuiltinTypeKind::LongDouble:

                    state.memory = true;
                    return;
                case cir::BuiltinTypeKind::Void:
                    return;
                default:
                    mark_bytes(state, offset, size, SlotCls::Int);
                    return;
            }
        }
        case cir::TypeKind::Pointer:
        case cir::TypeKind::Enum:
            mark_bytes(state, offset, size, SlotCls::Int);
            return;
        case cir::TypeKind::Complex: {
            const auto& complex = std::get<cir::ComplexTypePayload>(payload);
            cir::TypeId element = file.resolved_type(complex.element_type.type);
            auto element_size = cir::size_align_of_type(file, element);
            if (!element_size) {
                state.memory = true;
                return;
            }
            classify_bytes(file, target, element, offset, state);
            classify_bytes(file, target, element,
                           offset + element_size->size_bytes, state);
            return;
        }
        case cir::TypeKind::Array: {
            const auto& array = std::get<cir::ArrayTypePayload>(payload);
            if (array.size_kind != cir::ArraySizeKind::Constant ||
                !array.size.has_value()) {
                state.memory = true;
                return;
            }
            cir::TypeId element = file.resolved_type(array.element_type.type);
            auto element_size = cir::size_align_of_type(file, element);
            if (!element_size) {
                state.memory = true;
                return;
            }
            for (uint64_t i = 0; i < *array.size && !state.memory; ++i) {
                classify_bytes(file, target, element,
                               offset + i * element_size->size_bytes, state);
            }
            return;
        }
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts = file.record_facts_for_type(resolved);
            if (!facts || facts->is_incomplete) {
                state.memory = true;
                return;
            }
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (state.memory) {
                    return;
                }
                if (field.is_flexible_array_member ||
                    field.subobject_size == cir::SubobjectSizeKind::Zero) {
                    continue;
                }
                uint64_t field_offset = offset + field.offset;
                if (field.is_bitfield) {
                    if (field.bit_width == 0) {
                        continue;
                    }
                    uint64_t first = field_offset + field.bit_offset / 8;
                    uint64_t last =
                        field_offset + (field.bit_offset + field.bit_width + 7) / 8;
                    mark_bytes(state, first, std::max<uint64_t>(1, last - first),
                               SlotCls::Int);
                    continue;
                }
                cir::TypeId field_type = file.resolved_type(field.type.type);
                auto field_size = cir::size_align_of_type(file, field_type);
                if (!field_size) {
                    state.memory = true;
                    return;
                }

                if (field_size->alignment_bytes > 0 &&
                    field_offset % field_size->alignment_bytes != 0) {
                    state.memory = true;
                    return;
                }
                classify_bytes(file, target, field_type, field_offset, state);
            }
            return;
        }
        default:
            state.memory = true;
            return;
    }
}

AggregateClass from_state(const ClassifyState& state, uint64_t size_bytes,
                          uint32_t align_bytes) {
    AggregateClass result;
    result.byte_size = size_bytes;
    result.byte_align = std::max<uint32_t>(1, align_bytes);
    if (state.memory || size_bytes > 16) {
        result.pass = AggregatePass::MemoryByval;
        return result;
    }
    uint8_t slot_count =
        static_cast<uint8_t>(std::max<uint64_t>(1, (size_bytes + 7) / 8));
    bool any_marked = false;
    uint8_t sse_mask = 0;
    for (uint8_t slot = 0; slot < slot_count; ++slot) {
        if (state.slots[slot] != SlotCls::None) {
            any_marked = true;
        }
        if (state.slots[slot] == SlotCls::Sse) {
            sse_mask |= static_cast<uint8_t>(1u << slot);
        }
    }
    if (!any_marked) {

        result.pass = AggregatePass::Ignore;
        return result;
    }
    result.int_slot_count = slot_count;
    if (sse_mask == 0) {
        result.pass = AggregatePass::CoerceIntSlots;
    } else {
        result.pass = AggregatePass::CoerceClassedSlots;
        result.sse_slot_mask = sse_mask;
    }
    return result;
}

} // namespace

AggregateClass classify_x86_64_argument_native(const cir::File& file,
                                               cir::TypeRef type,
                                               const TargetInfo* target) {
    AggregateClass result;
    if (!target || !is_x86_64_sysv(*target) || !file.valid(type.type)) {
        return result;
    }
    cir::TypeId resolved = file.resolved_type(type.type);
    if (!file.valid(resolved)) {
        return result;
    }
    bool is_complex = file.type(resolved).kind == cir::TypeKind::Complex;
    if (!is_complex && !is_complete_record_type(file, resolved)) {
        return result;
    }
    auto size_align = cir::size_align_of_type(file, resolved);
    if (!size_align) {
        return result;
    }

    ClassifyState state;
    classify_bytes(file, *target, resolved, 0, state);
    return from_state(state, size_align->size_bytes,
                      static_cast<uint32_t>(size_align->alignment_bytes));
}

AggregateClass classify_x86_64_vararg_native(const cir::File& file,
                                             cir::TypeRef type,
                                             const TargetInfo* target) {
    return classify_x86_64_argument_native(file, type, target);
}

} // namespace aburi::abi
