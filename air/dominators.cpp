#include "dominators.h"

#include <cassert>

namespace aburi::air {

namespace {

void collect_successor_blocks(const Function& func, BlockId block,
                              std::vector<BlockCallId>& calls,
                              std::vector<BlockId>& out) {
    out.clear();
    InstId last = func.block(block).last;
    if (!last.is_valid() || !opcode_is_terminator(func.inst(last).op)) {
        return;
    }
    func.successors(last, calls);
    for (BlockCallId call : calls) {
        out.push_back(func.block_call(call).target);
    }
}

} // namespace

void DominatorTree::compute(const Function& func) {
    uint32_t block_slots = func.block_count() + 1;
    rpo_.clear();
    rpo_index_.assign(block_slots, UINT32_MAX);
    idom_.assign(block_slots, BlockId{});
    entry_ = func.entry_block();
    if (!entry_.is_valid()) {
        return;
    }

    std::vector<BlockCallId> calls;
    std::vector<uint8_t> state(block_slots, 0);
    std::vector<std::pair<BlockId, uint32_t>> stack;
    std::vector<BlockId> postorder;
    std::vector<std::vector<BlockId>> succ_cache(block_slots);

    stack.emplace_back(entry_, 0);
    state[entry_.index] = 1;
    collect_successor_blocks(func, entry_, calls, succ_cache[entry_.index]);
    while (!stack.empty()) {
        auto& [block, next_succ] = stack.back();
        const std::vector<BlockId>& block_succs = succ_cache[block.index];
        if (next_succ < block_succs.size()) {
            BlockId succ = block_succs[next_succ++];
            if (state[succ.index] == 0) {
                state[succ.index] = 1;
                collect_successor_blocks(func, succ, calls, succ_cache[succ.index]);
                stack.emplace_back(succ, 0);
            }
        } else {
            state[block.index] = 2;
            postorder.push_back(block);
            stack.pop_back();
        }
    }
    rpo_.assign(postorder.rbegin(), postorder.rend());
    for (uint32_t i = 0; i < rpo_.size(); ++i) {
        rpo_index_[rpo_[i].index] = i;
    }

    std::vector<std::vector<BlockId>> preds(block_slots);
    for (BlockId block : rpo_) {
        for (BlockId succ : succ_cache[block.index]) {
            preds[succ.index].push_back(block);
        }
    }

    idom_[entry_.index] = entry_;
    bool changed = true;
    auto intersect = [&](BlockId a, BlockId b) {
        while (a != b) {
            while (rpo_index_[a.index] > rpo_index_[b.index]) {
                a = idom_[a.index];
            }
            while (rpo_index_[b.index] > rpo_index_[a.index]) {
                b = idom_[b.index];
            }
        }
        return a;
    };
    while (changed) {
        changed = false;
        for (BlockId block : rpo_) {
            if (block == entry_) {
                continue;
            }
            BlockId new_idom;
            for (BlockId pred : preds[block.index]) {
                if (!idom_[pred.index].is_valid()) {
                    continue;
                }
                new_idom = new_idom.is_valid() ? intersect(new_idom, pred) : pred;
            }
            assert(new_idom.is_valid() && "reachable block with no processed pred");
            if (idom_[block.index] != new_idom) {
                idom_[block.index] = new_idom;
                changed = true;
            }
        }
    }
}

bool DominatorTree::reachable(BlockId block) const {
    return block.index < rpo_index_.size() && rpo_index_[block.index] != UINT32_MAX;
}

BlockId DominatorTree::idom(BlockId block) const {
    if (!reachable(block) || block == entry_) {
        return BlockId{};
    }
    return idom_[block.index];
}

bool DominatorTree::dominates(BlockId a, BlockId b) const {
    if (!reachable(a) || !reachable(b)) {
        return false;
    }

    while (rpo_index_[b.index] > rpo_index_[a.index]) {
        b = idom_[b.index];
    }
    return a == b;
}

} // namespace aburi::air
