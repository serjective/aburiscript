#ifndef ABURI_DENSE_MAP_H
#define ABURI_DENSE_MAP_H

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <cstddef>
#include <utility>

// Open-addressing hash map keyed by uint32_t.
// Uses Fibonacci hashing and linear probing with 75% max load factor.
// Sentinels: EMPTY = UINT32_MAX, TOMBSTONE = UINT32_MAX - 1
// These are unreachable by a monotonic counter that starts at 0.
template<typename V>
class DenseMap {
    static constexpr uint32_t EMPTY     = UINT32_MAX;
    static constexpr uint32_t TOMBSTONE = UINT32_MAX - 1;

    struct Bucket {
        uint32_t key = EMPTY;
        V value{};
    };

    Bucket* buckets_ = nullptr;
    uint32_t capacity_ = 0;
    uint32_t size_ = 0;
    uint32_t tombstones_ = 0;

    static uint32_t fib_hash(uint32_t k, uint32_t shift) {
        // Fibonacci hashing: multiply by golden-ratio constant, shift down
        return (k * UINT32_C(2654435769)) >> shift;
    }

    uint32_t shift() const {
        // For capacity 2^n, shift = 32 - n
        uint32_t n = 0;
        uint32_t c = capacity_;
        while (c > 1) { c >>= 1; ++n; }
        return 32 - n;
    }

    void grow() {
        uint32_t new_cap = capacity_ == 0 ? 16 : capacity_ * 2;
        Bucket* old = buckets_;
        uint32_t old_cap = capacity_;

        buckets_ = new Bucket[new_cap];
        capacity_ = new_cap;
        size_ = 0;
        tombstones_ = 0;

        if (old) {
            uint32_t s = shift();
            for (uint32_t i = 0; i < old_cap; ++i) {
                if (old[i].key != EMPTY && old[i].key != TOMBSTONE) {
                    insert_no_grow(old[i].key, std::move(old[i].value), s);
                }
            }
            delete[] old;
        }
    }

    void insert_no_grow(uint32_t key, V value, uint32_t s) {
        uint32_t idx = fib_hash(key, s) & (capacity_ - 1);
        while (true) {
            if (buckets_[idx].key == EMPTY || buckets_[idx].key == TOMBSTONE) {
                buckets_[idx].key = key;
                buckets_[idx].value = std::move(value);
                ++size_;
                return;
            }
            idx = (idx + 1) & (capacity_ - 1);
        }
    }

    void maybe_grow() {
        // Grow if size + tombstones exceeds 75% of capacity
        if (capacity_ == 0 || (size_ + tombstones_ + 1) * 4 > capacity_ * 3) {
            grow();
        }
    }

public:
    DenseMap() = default;
    ~DenseMap() { delete[] buckets_; }

    DenseMap(const DenseMap& other) : capacity_(other.capacity_), size_(other.size_), tombstones_(other.tombstones_) {
        if (capacity_ > 0) {
            buckets_ = new Bucket[capacity_];
            for (uint32_t i = 0; i < capacity_; ++i) {
                buckets_[i] = other.buckets_[i];
            }
        }
    }

    DenseMap& operator=(const DenseMap& other) {
        if (this != &other) {
            delete[] buckets_;
            buckets_ = nullptr;
            capacity_ = other.capacity_;
            size_ = other.size_;
            tombstones_ = other.tombstones_;
            if (capacity_ > 0) {
                buckets_ = new Bucket[capacity_];
                for (uint32_t i = 0; i < capacity_; ++i) {
                    buckets_[i] = other.buckets_[i];
                }
            }
        }
        return *this;
    }

    DenseMap(DenseMap&& other) noexcept
        : buckets_(other.buckets_), capacity_(other.capacity_),
          size_(other.size_), tombstones_(other.tombstones_) {
        other.buckets_ = nullptr;
        other.capacity_ = 0;
        other.size_ = 0;
        other.tombstones_ = 0;
    }

    DenseMap& operator=(DenseMap&& other) noexcept {
        if (this != &other) {
            delete[] buckets_;
            buckets_ = other.buckets_;
            capacity_ = other.capacity_;
            size_ = other.size_;
            tombstones_ = other.tombstones_;
            other.buckets_ = nullptr;
            other.capacity_ = 0;
            other.size_ = 0;
            other.tombstones_ = 0;
        }
        return *this;
    }

    V& operator[](uint32_t key) {
        assert(key != EMPTY && key != TOMBSTONE);
        maybe_grow();
        uint32_t s = shift();
        uint32_t idx = fib_hash(key, s) & (capacity_ - 1);
        uint32_t first_tombstone = UINT32_MAX;
        while (true) {
            if (buckets_[idx].key == key) {
                return buckets_[idx].value;
            }
            if (buckets_[idx].key == TOMBSTONE && first_tombstone == UINT32_MAX) {
                first_tombstone = idx;
            }
            if (buckets_[idx].key == EMPTY) {
                // Insert at first tombstone if we found one, else at this empty slot
                uint32_t ins = (first_tombstone != UINT32_MAX) ? first_tombstone : idx;
                if (first_tombstone != UINT32_MAX) {
                    --tombstones_;
                }
                buckets_[ins].key = key;
                buckets_[ins].value = V{};
                ++size_;
                return buckets_[ins].value;
            }
            idx = (idx + 1) & (capacity_ - 1);
        }
    }

    V* find(uint32_t key) {
        if (capacity_ == 0) return nullptr;
        uint32_t s = shift();
        uint32_t idx = fib_hash(key, s) & (capacity_ - 1);
        while (true) {
            if (buckets_[idx].key == key) {
                return &buckets_[idx].value;
            }
            if (buckets_[idx].key == EMPTY) {
                return nullptr;
            }
            idx = (idx + 1) & (capacity_ - 1);
        }
    }

    const V* find(uint32_t key) const {
        if (capacity_ == 0) return nullptr;
        uint32_t s = shift();
        uint32_t idx = fib_hash(key, s) & (capacity_ - 1);
        while (true) {
            if (buckets_[idx].key == key) {
                return &buckets_[idx].value;
            }
            if (buckets_[idx].key == EMPTY) {
                return nullptr;
            }
            idx = (idx + 1) & (capacity_ - 1);
        }
    }

    bool contains(uint32_t key) const {
        return find(key) != nullptr;
    }

    bool erase(uint32_t key) {
        if (capacity_ == 0) return false;
        uint32_t s = shift();
        uint32_t idx = fib_hash(key, s) & (capacity_ - 1);
        while (true) {
            if (buckets_[idx].key == key) {
                buckets_[idx].key = TOMBSTONE;
                buckets_[idx].value = V{};
                --size_;
                ++tombstones_;
                return true;
            }
            if (buckets_[idx].key == EMPTY) {
                return false;
            }
            idx = (idx + 1) & (capacity_ - 1);
        }
    }

    uint32_t size() const { return size_; }
    uint32_t capacity() const { return capacity_; }
    bool empty() const { return size_ == 0; }
    size_t bucket_memory_usage_bytes() const {
        return static_cast<size_t>(capacity_) * sizeof(Bucket);
    }
    size_t memory_usage_bytes() const {
        return sizeof(*this) + bucket_memory_usage_bytes();
    }

    void clear() {
        for (uint32_t i = 0; i < capacity_; ++i) {
            buckets_[i].key = EMPTY;
            buckets_[i].value = V{};
        }
        size_ = 0;
        tombstones_ = 0;
    }

    // Sentinel values are public for testing/debugging
    static constexpr uint32_t sentinel_empty() { return EMPTY; }
    static constexpr uint32_t sentinel_tombstone() { return TOMBSTONE; }
};

#endif // ABURI_DENSE_MAP_H
