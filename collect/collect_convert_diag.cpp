#include "collect.h"

void Collect::report_error(const std::string& message, SrcLoc loc) const {

    if (diag_engine_) {
        diag_engine_->report_error(message, loc);
    }
}


void Collect::report_warning(const std::string& message, SrcLoc loc) const {

    if (diag_engine_) {
        diag_engine_->report_warning(message, loc);
    }
}


void Collect::queue_delayed_error(const std::string& message, SrcLoc loc) const {

    materialize_tentative_snapshot_if_needed();
    func_state_.delayed_diagnostics.push_back(DelayedDiagnostic{true, message, loc});
}


void Collect::queue_delayed_warning(const std::string& message, SrcLoc loc) const {

    materialize_tentative_snapshot_if_needed();
    func_state_.delayed_diagnostics.push_back(DelayedDiagnostic{false, message, loc});
}


void Collect::flush_delayed_diagnostics() const {

    if (!func_state_.delayed_diagnostics.empty()) {
        materialize_tentative_snapshot_if_needed();
    }
    for (const auto& diag : func_state_.delayed_diagnostics) {
        if (diag.is_error) {
            report_error(diag.message, diag.loc);
        } else {
            report_warning(diag.message, diag.loc);
        }
    }
    func_state_.delayed_diagnostics.clear();
}


void Collect::enter_unevaluated_context(const char* reason) const {

    materialize_tentative_snapshot_if_needed();
    ++func_state_.unevaluated_depth;
    func_state_.unevaluated_context_stack.push_back(reason ? std::string(reason) : std::string());
}


void Collect::leave_unevaluated_context() const {

    if (func_state_.unevaluated_depth > 0 || !func_state_.unevaluated_context_stack.empty()) {
        materialize_tentative_snapshot_if_needed();
    }
    if (func_state_.unevaluated_depth > 0) {
        --func_state_.unevaluated_depth;
    }
    if (!func_state_.unevaluated_context_stack.empty()) {
        func_state_.unevaluated_context_stack.pop_back();
    }
}


bool Collect::in_unevaluated_context() const {

    return func_state_.unevaluated_depth > 0;
}

void Collect::report_conversion_failure(const std::string& context,
                                        QualType from,
                                        QualType to,
                                        SrcLoc loc) const {

    std::string from_name = from ? from.to_string() : "<unknown>";
    std::string to_name = to ? to.to_string() : "<unknown>";
    report_error(context + " requires implicit conversion from '" +
        from_name + "' to '" + to_name + "'", loc);
}


void Collect::report_invalid_binary_operands(const std::string& op,
                                             QualType lhs,
                                             QualType rhs,
                                             SrcLoc loc) const {

    std::string lhs_name = lhs ? lhs.to_string() : "<unknown>";
    std::string rhs_name = rhs ? rhs.to_string() : "<unknown>";
    if (op.empty() || op == "binary expression") {
        report_error("invalid operands to binary expression (have '" +
            lhs_name + "' and '" + rhs_name + "')", loc);
        return;
    }
    report_error("invalid operands to " + op + " (have '" +
        lhs_name + "' and '" + rhs_name + "')", loc);
}


void Collect::report_invalid_compound_assign_operands(const std::string& op,
                                                      QualType lhs,
                                                      QualType rhs,
                                                      SrcLoc loc) const {

    std::string lhs_name = lhs ? lhs.to_string() : "<unknown>";
    std::string rhs_name = rhs ? rhs.to_string() : "<unknown>";
    if (op.empty()) {
        report_error("invalid operands to compound assignment (have '" +
            lhs_name + "' and '" + rhs_name + "')", loc);
        return;
    }
    report_error("invalid operands to compound assignment " + op + " (have '" +
        lhs_name + "' and '" + rhs_name + "')", loc);
}
