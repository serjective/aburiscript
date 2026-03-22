#ifndef ABURI_EVAL_MEMORY_H
#define ABURI_EVAL_MEMORY_H

#include <cstddef>
#include <cstdint>
#include <optional>
#include <unordered_map>
#include <vector>

struct EvalAllocation {
    uint64_t id = 0;
    std::vector<uint8_t> bytes;
    bool read_only = false;
};

class EvalMemory {
public:
    uint64_t allocate(size_t size, bool read_only = false);

    bool store_bytes(uint64_t allocation_id, size_t offset, const std::vector<uint8_t>& data);

    std::optional<std::vector<uint8_t>> load_bytes(
        uint64_t allocation_id, size_t offset, size_t size) const;

    bool is_read_only(uint64_t allocation_id) const;

    size_t allocation_count() const;

    void reset();

private:
    uint64_t next_id_ = 1;
    std::unordered_map<uint64_t, EvalAllocation> allocations_;
};

#endif // ABURI_EVAL_MEMORY_H
