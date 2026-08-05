#include "eval_memory.h"

#include <algorithm>

namespace {

bool ranges_overlap(size_t lhs_offset,
                    size_t lhs_size,
                    size_t rhs_offset,
                    size_t rhs_size) {
    return lhs_offset < rhs_offset + rhs_size &&
           rhs_offset < lhs_offset + lhs_size;
}

} // namespace

uint64_t EvalMemory::allocate(size_t size, bool read_only) {
    uint64_t id = next_id_++;
    EvalAllocation allocation;
    allocation.id = id;
    allocation.bytes.resize(size, 0);
    allocation.initialized.resize(size, false);
    allocation.read_only = read_only;
    allocations_[id] = std::move(allocation);
    return id;
}

uint64_t EvalMemory::allocate_dynamic(size_t size) {
    uint64_t id = allocate(size);
    allocations_[id].is_dynamic = true;
    ++live_dynamic_;
    return id;
}

EvalDeallocStatus EvalMemory::deallocate_dynamic(uint64_t allocation_id) {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end()) {
        return EvalDeallocStatus::NotAnAllocation;
    }
    if (!it->second.is_dynamic) {
        return EvalDeallocStatus::NotDynamic;
    }
    if (it->second.deallocated) {
        return EvalDeallocStatus::AlreadyDeallocated;
    }
    it->second.deallocated = true;
    --live_dynamic_;
    return EvalDeallocStatus::Ok;
}

size_t EvalMemory::live_dynamic_count() const {
    return live_dynamic_;
}

bool EvalMemory::is_live_dynamic(uint64_t allocation_id) const {
    auto it = allocations_.find(allocation_id);
    return it != allocations_.end() && it->second.is_dynamic &&
           !it->second.deallocated;
}

bool EvalMemory::is_dynamic_allocation(uint64_t allocation_id) const {
    auto it = allocations_.find(allocation_id);
    return it != allocations_.end() && it->second.is_dynamic;
}

bool EvalMemory::store_bytes(
    uint64_t allocation_id, size_t offset, const std::vector<uint8_t>& data) {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.read_only ||
        it->second.deallocated) {
        return false;
    }
    if (offset > it->second.bytes.size()) {
        return false;
    }
    if (data.size() > it->second.bytes.size() - offset) {
        return false;
    }
    clear_address_slots(it->second, offset, data.size());
    for (size_t i = 0; i < data.size(); ++i) {
        it->second.bytes[offset + i] = data[i];
        it->second.initialized[offset + i] = true;
    }
    return true;
}

bool EvalMemory::store_address(uint64_t allocation_id,
                               size_t offset,
                               size_t size,
                               ConstAddressValue value) {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.read_only ||
        it->second.deallocated) {
        return false;
    }
    if (offset > it->second.bytes.size()) {
        return false;
    }
    if (size > it->second.bytes.size() - offset) {
        return false;
    }
    clear_address_slots(it->second, offset, size);
    for (size_t i = 0; i < size; ++i) {
        it->second.bytes[offset + i] = 0;
        it->second.initialized[offset + i] = true;
    }
    it->second.address_slots.push_back(EvalAddressSlot{
        offset,
        size,
        value,
    });
    return true;
}

std::optional<std::vector<uint8_t>> EvalMemory::load_bytes(
    uint64_t allocation_id, size_t offset, size_t size) const {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.deallocated) {
        return std::nullopt;
    }
    if (offset > it->second.bytes.size()) {
        return std::nullopt;
    }
    if (size > it->second.bytes.size() - offset) {
        return std::nullopt;
    }
    std::vector<uint8_t> out(size);
    for (size_t i = 0; i < size; ++i) {
        if (!it->second.initialized[offset + i]) {
            return std::nullopt;
        }
        out[i] = it->second.bytes[offset + i];
    }
    return out;
}

bool EvalMemory::store_meta(uint64_t allocation_id,
                            size_t offset,
                            size_t size,
                            ConstValue value) {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.read_only ||
        it->second.deallocated) {
        return false;
    }
    if (offset > it->second.bytes.size() ||
        size > it->second.bytes.size() - offset) {
        return false;
    }
    clear_address_slots(it->second, offset, size);
    for (size_t i = 0; i < size; ++i) {
        it->second.bytes[offset + i] = 0;
        it->second.initialized[offset + i] = true;
    }
    it->second.meta_slots.push_back(EvalMetaSlot{
        offset,
        size,
        std::move(value),
    });
    return true;
}

std::optional<ConstValue> EvalMemory::load_meta(
    uint64_t allocation_id, size_t offset, size_t size) const {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.deallocated) {
        return std::nullopt;
    }
    for (const EvalMetaSlot& slot : it->second.meta_slots) {
        if (slot.offset == offset && slot.size == size) {
            return slot.value;
        }
    }
    return std::nullopt;
}

std::optional<ConstAddressValue> EvalMemory::load_address(
    uint64_t allocation_id, size_t offset, size_t size) const {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.deallocated) {
        return std::nullopt;
    }
    if (offset > it->second.bytes.size()) {
        return std::nullopt;
    }
    if (size > it->second.bytes.size() - offset) {
        return std::nullopt;
    }
    for (const EvalAddressSlot& slot : it->second.address_slots) {
        if (slot.offset == offset && slot.size == size) {
            return slot.value;
        }
    }
    return std::nullopt;
}

bool EvalMemory::is_read_only(uint64_t allocation_id) const {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end()) {
        return false;
    }
    return it->second.read_only;
}

bool EvalMemory::set_active_union(uint64_t allocation_id,
                                  size_t offset,
                                  aburi::cir::EntityId member) {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.deallocated ||
        it->second.read_only) {
        return false;
    }
    for (EvalActiveUnion& active : it->second.active_unions) {
        if (active.offset == offset) {
            active.member = member;
            return true;
        }
    }
    it->second.active_unions.push_back(EvalActiveUnion{offset, member});
    return true;
}

aburi::cir::EntityId EvalMemory::active_union_member(
    uint64_t allocation_id, size_t offset) const {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.deallocated) {
        return {};
    }
    for (const EvalActiveUnion& active : it->second.active_unions) {
        if (active.offset == offset) {
            return active.member;
        }
    }
    return {};
}

size_t EvalMemory::allocation_count() const {
    return allocations_.size();
}

void EvalMemory::reset() {
    allocations_.clear();
    next_id_ = 1;
    live_dynamic_ = 0;
}

void EvalMemory::clear_address_slots(EvalAllocation& allocation,
                                     size_t offset,
                                     size_t size) {
    allocation.address_slots.erase(
        std::remove_if(allocation.address_slots.begin(),
                       allocation.address_slots.end(),
                       [&](const EvalAddressSlot& slot) {
                           return ranges_overlap(slot.offset,
                                                 slot.size,
                                                 offset,
                                                 size);
                       }),
        allocation.address_slots.end());
    allocation.meta_slots.erase(
        std::remove_if(allocation.meta_slots.begin(),
                       allocation.meta_slots.end(),
                       [&](const EvalMetaSlot& slot) {
                           return ranges_overlap(slot.offset,
                                                 slot.size,
                                                 offset,
                                                 size);
                       }),
        allocation.meta_slots.end());
}
