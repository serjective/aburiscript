#include "eval_memory.h"

uint64_t EvalMemory::allocate(size_t size, bool read_only) {
    uint64_t id = next_id_++;
    EvalAllocation allocation;
    allocation.id = id;
    allocation.bytes.resize(size, 0);
    allocation.read_only = read_only;
    allocations_[id] = std::move(allocation);
    return id;
}

bool EvalMemory::store_bytes(
    uint64_t allocation_id, size_t offset, const std::vector<uint8_t>& data) {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end() || it->second.read_only) {
        return false;
    }
    if (offset > it->second.bytes.size()) {
        return false;
    }
    if (data.size() > it->second.bytes.size() - offset) {
        return false;
    }
    for (size_t i = 0; i < data.size(); ++i) {
        it->second.bytes[offset + i] = data[i];
    }
    return true;
}

std::optional<std::vector<uint8_t>> EvalMemory::load_bytes(
    uint64_t allocation_id, size_t offset, size_t size) const {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end()) {
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
        out[i] = it->second.bytes[offset + i];
    }
    return out;
}

bool EvalMemory::is_read_only(uint64_t allocation_id) const {
    auto it = allocations_.find(allocation_id);
    if (it == allocations_.end()) {
        return false;
    }
    return it->second.read_only;
}

size_t EvalMemory::allocation_count() const {
    return allocations_.size();
}

void EvalMemory::reset() {
    allocations_.clear();
    next_id_ = 1;
}
