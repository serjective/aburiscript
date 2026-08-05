#include "diagnostics.h"

void DiagnosticEngine::report_error(const std::string& msg, SrcLoc loc) {
    if (fatal_errors) {

        if (sm && !loc.isInvalid()) {
            throw std::runtime_error(sm->formatDiagnostic(DiagnosticLevel::Error, msg, loc));
        }
        throw std::runtime_error("error: " + msg);
    }

    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = msg;
    diag.location = loc;
    diag.suppressed = suppress_errors;
    diagnostics.push_back(diag);

    if (!suppress_errors) {
        error_count++;
    }
    suppress_errors = true;

    if (limit_reached()) {
        throw FatalErrorLimitReached();
    }
}

void DiagnosticEngine::report_warning(const std::string& msg, SrcLoc loc) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Warning;
    diag.message = msg;
    diag.location = loc;
    diagnostics.push_back(diag);
    warning_count++;
}

void DiagnosticEngine::report_note(const std::string& msg, SrcLoc loc) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Note;
    diag.message = msg;
    diag.location = loc;
    diagnostics.push_back(diag);
}

void DiagnosticEngine::flush_diagnostics() const {
    if (!emit_to_stderr) {
        return;
    }

    for (const auto& diag : diagnostics) {
        if (diag.suppressed) continue;
        std::string formatted = format(diag.level, diag.message, diag.location);
        std::cerr << formatted;

        if (!formatted.empty() && formatted.back() != '\n') {
            std::cerr << "\n";
        }
    }
    if (limit_reached()) {
        std::cerr << "fatal: too many errors emitted, stopping now\n";
    }
}

std::string DiagnosticEngine::format(DiagnosticLevel level, const std::string& msg, SrcLoc loc) const {
    if (sm && !loc.isInvalid()) {
        return sm->formatDiagnostic(level, msg, loc);
    }
    std::string level_text;
    switch (level) {
        case DiagnosticLevel::Error: level_text = "error"; break;
        case DiagnosticLevel::Warning: level_text = "warning"; break;
        case DiagnosticLevel::Note: level_text = "note"; break;
    }
    return level_text + ": " + msg;
}

DiagnosticEngine::Checkpoint DiagnosticEngine::checkpoint() const {
    Checkpoint cp;
    cp.diagnostics_size = diagnostics.size();
    cp.error_count = error_count;
    cp.warning_count = warning_count;
    cp.suppress_errors = suppress_errors;
    return cp;
}

void DiagnosticEngine::restore(const Checkpoint& checkpoint) {
    if (diagnostics.size() > checkpoint.diagnostics_size) {
        diagnostics.resize(checkpoint.diagnostics_size);
    }
    error_count = checkpoint.error_count;
    warning_count = checkpoint.warning_count;
    suppress_errors = checkpoint.suppress_errors;
}
