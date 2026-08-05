#ifndef ABURI_EVAL_MEMORY_H
#define ABURI_EVAL_MEMORY_H

#include <cstddef>
#include <cstdint>
#include <optional>
#include <unordered_map>
#include <vector>

#include "const_value.h"

struct EvalAddressSlot {
    size_t offset = 0;
    size_t size = 0;
    ConstAddressValue value{};
};

struct EvalMetaSlot {
    size_t offset = 0;
    size_t size = 0;
    ConstValue value{};
};

struct EvalActiveUnion {
    size_t offset = 0;
    aburi::cir::EntityId member{};
};

struct EvalAllocation {
    uint64_t id = 0;
    std::vector<uint8_t> bytes;
    std::vector<bool> initialized;
    std::vector<EvalAddressSlot> address_slots;
    std::vector<EvalMetaSlot> meta_slots;
    std::vector<EvalActiveUnion> active_unions;
    bool read_only = false;
    bool is_dynamic = false;
    bool deallocated = false;
};

enum class EvalDeallocStatus {
    Ok,
    NotAnAllocation,
    NotDynamic,
    AlreadyDeallocated
};

class EvalMemory {
public:
    uint64_t allocate(size_t size, bool read_only = false);
    uint64_t allocate_dynamic(size_t size);
    EvalDeallocStatus deallocate_dynamic(uint64_t allocation_id);
    size_t live_dynamic_count() const;
    bool is_live_dynamic(uint64_t allocation_id) const;
    bool is_dynamic_allocation(uint64_t allocation_id) const;

    bool store_bytes(uint64_t allocation_id, size_t offset, const std::vector<uint8_t>& data);
    bool store_address(uint64_t allocation_id,
                       size_t offset,
                       size_t size,
                       ConstAddressValue value);

    std::optional<std::vector<uint8_t>> load_bytes(
        uint64_t allocation_id, size_t offset, size_t size) const;
    std::optional<ConstAddressValue> load_address(
        uint64_t allocation_id, size_t offset, size_t size) const;
    bool store_meta(uint64_t allocation_id,
                    size_t offset,
                    size_t size,
                    ConstValue value);
    std::optional<ConstValue> load_meta(
        uint64_t allocation_id, size_t offset, size_t size) const;

    bool is_read_only(uint64_t allocation_id) const;
    bool set_active_union(uint64_t allocation_id,
                          size_t offset,
                          aburi::cir::EntityId member);
    aburi::cir::EntityId active_union_member(uint64_t allocation_id,
                                              size_t offset) const;

    size_t allocation_count() const;

    void reset();

private:
    void clear_address_slots(EvalAllocation& allocation,
                             size_t offset,
                             size_t size);

    uint64_t next_id_ = 1;
    size_t live_dynamic_ = 0;
    std::unordered_map<uint64_t, EvalAllocation> allocations_;
};

#endif // ABURI_EVAL_MEMORY_H
