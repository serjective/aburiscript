#ifndef ABURI_DIAGNOSTICS_H
#define ABURI_DIAGNOSTICS_H

#include "source_mgnt.h"
#include <vector>
#include <string>
#include <memory>
#include <exception>
#include <iostream>

struct FixItHint {
    SrcLoc location;
    std::string insertion;  // text to insert at location
    std::string description; // human-readable description (e.g., "insert ';' here")
};

struct Diagnostic {
    DiagnosticLevel level;
    std::string message;
    SrcLoc location;
    bool suppressed = false;
    std::vector<FixItHint> fixits;
};

// Dedicated exception for parse errors — caught at recovery points.
// Distinct from std::runtime_error so we never accidentally swallow ICEs. (Internal comiler errors)
struct ParseError : std::exception {
    SrcLoc location;
    std::string message;
    ParseError(std::string msg, SrcLoc loc = SrcLoc())
        : message(std::move(msg)), location(loc) {}
    const char* what() const noexcept override { return message.c_str(); }
};

// Thrown when the error limit is reached to stop parsing entirely.
struct FatalErrorLimitReached : std::exception {
    const char* what() const noexcept override {
        return "too many errors emitted, stopping now";
    }
};

class DiagnosticEngine {
public:
    struct Checkpoint {
        size_t diagnostics_size = 0;
        size_t error_count = 0;
        size_t warning_count = 0;
        bool suppress_errors = false;
    };

    std::shared_ptr<SourceManager> sm;
    size_t error_limit = 20;
    bool fatal_errors = false; // if true, first error throws std::runtime_error (legacy)
    bool emit_to_stderr = true;

    std::vector<Diagnostic> diagnostics;

    size_t error_count = 0;
    size_t warning_count = 0;

    // Cascade suppression: set after an error triggers recovery,
    // cleared when the parser reaches a successful sync point.
    bool suppress_errors = false;

    DiagnosticEngine() = default;
    explicit DiagnosticEngine(std::shared_ptr<SourceManager> sm) : sm(std::move(sm)) {}

    // Record an error. Throws FatalErrorLimitReached if limit exceeded.
    void report_error(const std::string& msg, SrcLoc loc = SrcLoc());

    // Record a warning.
    void report_warning(const std::string& msg, SrcLoc loc = SrcLoc());

    // Record a note.
    void report_note(const std::string& msg, SrcLoc loc = SrcLoc());

    bool has_errors() const { return error_count > 0; }

    bool limit_reached() const {
        return error_limit > 0 && error_count >= error_limit;
    }

    // Called when the parser successfully processes a complete construct.
    void sync_point_reached() { suppress_errors = false; }

    // Print all accumulated diagnostics to stderr.
    void flush_diagnostics() const;

    // Format a single diagnostic.
    std::string format(DiagnosticLevel level, const std::string& msg, SrcLoc loc) const;

    // Save/restore diagnostic state for parser tentative parsing.
    Checkpoint checkpoint() const;
    void restore(const Checkpoint& checkpoint);
};

#endif // ABURI_DIAGNOSTICS_H
