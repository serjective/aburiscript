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
    std::string insertion;
    std::string description;
};

struct Diagnostic {
    DiagnosticLevel level;
    std::string message;
    SrcLoc location;
    bool suppressed = false;
    std::vector<FixItHint> fixits;
};

struct ParseError : std::exception {
    SrcLoc location;
    std::string message;
    ParseError(std::string msg, SrcLoc loc = SrcLoc())
        : message(std::move(msg)), location(loc) {}
    const char* what() const noexcept override { return message.c_str(); }
};

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
    bool fatal_errors = false;
    bool emit_to_stderr = true;

    std::vector<Diagnostic> diagnostics;

    size_t error_count = 0;
    size_t warning_count = 0;

    bool suppress_errors = false;

    DiagnosticEngine() = default;
    explicit DiagnosticEngine(std::shared_ptr<SourceManager> sm) : sm(std::move(sm)) {}

    void report_error(const std::string& msg, SrcLoc loc = SrcLoc());

    void report_warning(const std::string& msg, SrcLoc loc = SrcLoc());
    void report_note(const std::string& msg, SrcLoc loc = SrcLoc());

    bool has_errors() const { return error_count > 0; }

    bool limit_reached() const {
        return error_limit > 0 && error_count >= error_limit;
    }

    void sync_point_reached() { suppress_errors = false; }
    void flush_diagnostics() const;

    std::string format(DiagnosticLevel level, const std::string& msg, SrcLoc loc) const;
    Checkpoint checkpoint() const;
    void restore(const Checkpoint& checkpoint);
};

#endif // ABURI_DIAGNOSTICS_H
