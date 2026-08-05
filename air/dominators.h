#ifndef ABURI_AIR_DOMINATORS_H
#define ABURI_AIR_DOMINATORS_H

#include "function.h"

#include <span>
#include <vector>

namespace aburi::air {

class DominatorTree {
public:
    void compute(const Function& func);

    bool reachable(BlockId block) const;
    BlockId idom(BlockId block) const;
    bool dominates(BlockId a, BlockId b) const;
    std::span<const BlockId> rpo() const { return rpo_; }

private:
    std::vector<BlockId> rpo_;
    std::vector<uint32_t> rpo_index_;
    std::vector<BlockId> idom_;
    BlockId entry_;
};

} // namespace aburi::air

#endif // ABURI_AIR_DOMINATORS_H
