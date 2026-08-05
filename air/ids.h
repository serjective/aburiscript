#ifndef ABURI_AIR_IDS_H
#define ABURI_AIR_IDS_H

#include <cstdint>

namespace aburi::air {

struct ValueId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

struct InstId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

struct BlockId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

struct BlockCallId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

struct TypeId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

struct SigId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

struct FuncId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

struct GlobalId {
    uint32_t index = 0;

    bool is_valid() const { return index != 0; }
    explicit operator bool() const { return is_valid(); }
};

inline bool operator==(ValueId lhs, ValueId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(ValueId lhs, ValueId rhs) { return !(lhs == rhs); }

inline bool operator==(InstId lhs, InstId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(InstId lhs, InstId rhs) { return !(lhs == rhs); }

inline bool operator==(BlockId lhs, BlockId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(BlockId lhs, BlockId rhs) { return !(lhs == rhs); }

inline bool operator==(BlockCallId lhs, BlockCallId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(BlockCallId lhs, BlockCallId rhs) { return !(lhs == rhs); }

inline bool operator==(TypeId lhs, TypeId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(TypeId lhs, TypeId rhs) { return !(lhs == rhs); }

inline bool operator==(SigId lhs, SigId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(SigId lhs, SigId rhs) { return !(lhs == rhs); }

inline bool operator==(FuncId lhs, FuncId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(FuncId lhs, FuncId rhs) { return !(lhs == rhs); }

inline bool operator==(GlobalId lhs, GlobalId rhs) { return lhs.index == rhs.index; }
inline bool operator!=(GlobalId lhs, GlobalId rhs) { return !(lhs == rhs); }

} // namespace aburi::air

#endif // ABURI_AIR_IDS_H
