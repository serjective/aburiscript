#ifndef ABURI_EVAL_STATE_H
#define ABURI_EVAL_STATE_H

#include <cstddef>
#include <string>
#include <vector>

#include "eval_memory.h"

struct EvalFrame {
    std::string function_name;
};

class EvalState {
public:
    EvalState(size_t step_limit, size_t recursion_limit);

    bool consume_step(size_t amount = 1);

    bool push_frame(std::string function_name);

    void pop_frame();

    bool has_budget() const;

    size_t steps_used() const;

    size_t step_limit() const;

    size_t recursion_limit() const;

    size_t depth() const;

    const EvalFrame* current_frame() const;

    EvalMemory& memory();

    const EvalMemory& memory() const;

private:
    size_t step_limit_;
    size_t recursion_limit_;
    size_t steps_used_ = 0;
    std::vector<EvalFrame> call_stack_;
    EvalMemory memory_;
};

#endif // ABURI_EVAL_STATE_H
