#ifndef ABURI_NUMERIC_UTILS_H
#define ABURI_NUMERIC_UTILS_H

#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string>

inline std::optional<uint64_t> parse_integer_literal_u64(const std::string& text) {
    if (text.size() >= 2 && text[0] == '0' && (text[1] == 'b' || text[1] == 'B')) {
        if (text.size() == 2) {
            return std::nullopt;
        }
        uint64_t value = 0;
        for (size_t i = 2; i < text.size(); ++i) {
            char c = text[i];
            if (c != '0' && c != '1') {
                return std::nullopt;
            }
            value = (value << 1) | static_cast<uint64_t>(c - '0');
        }
        return value;
    }

    errno = 0;
    char* end = nullptr;
    unsigned long long value = std::strtoull(text.c_str(), &end, 0);
    if (end == text.c_str() || errno == ERANGE) {
        return std::nullopt;
    }
    // Allow trailing integer suffixes (L, l, U, u, LL, ll, etc.)
    while (*end == 'L' || *end == 'l' || *end == 'U' || *end == 'u') {
        ++end;
    }
    if (*end != '\0') {
        return std::nullopt;
    }
    return static_cast<uint64_t>(value);
}

inline std::optional<long double> parse_floating_literal_ld(const std::string& text) {
    errno = 0;
    char* end = nullptr;
    long double value = std::strtold(text.c_str(), &end);
    if (end == text.c_str() || errno == ERANGE) {
        return std::nullopt;
    }

    // Allow floating suffixes like f/F/l/L.
    while (*end == 'f' || *end == 'F' || *end == 'l' || *end == 'L') {
        ++end;
    }
    if (*end != '\0') {
        return std::nullopt;
    }
    return value;
}

#endif // ABURI_NUMERIC_UTILS_H
