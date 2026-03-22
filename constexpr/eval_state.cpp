#include "eval_state.h"

EvalState::EvalState(size_t step_limit, size_t recursion_limit)
    : step_limit_(step_limit), recursion_limit_(recursion_limit) {}

bool EvalState::consume_step(size_t amount) {
    if (amount == 0) {
        return true;
    }
    if (steps_used_ > step_limit_) {
        return false;
    }
    if (amount > step_limit_ - steps_used_) {
        return false;
    }
    steps_used_ += amount;
    return true;
}

bool EvalState::push_frame(std::string function_name) {
    if (call_stack_.size() >= recursion_limit_) {
        return false;
    }
    call_stack_.push_back(EvalFrame{std::move(function_name)});
    return true;
}

void EvalState::pop_frame() {
    if (!call_stack_.empty()) {
        call_stack_.pop_back();
    }
}

bool EvalState::has_budget() const {
    return steps_used_ < step_limit_;
}

size_t EvalState::steps_used() const {
    return steps_used_;
}

size_t EvalState::step_limit() const {
    return step_limit_;
}

size_t EvalState::recursion_limit() const {
    return recursion_limit_;
}

size_t EvalState::depth() const {
    return call_stack_.size();
}

const EvalFrame* EvalState::current_frame() const {
    if (call_stack_.empty()) {
        return nullptr;
    }
    return &call_stack_.back();
}

EvalMemory& EvalState::memory() {
    return memory_;
}

const EvalMemory& EvalState::memory() const {
    return memory_;
}
