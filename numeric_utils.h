#ifndef ABURI_NUMERIC_UTILS_H
#define ABURI_NUMERIC_UTILS_H

#include <cstdint>
#include <limits>
#include <optional>
#include <string_view>

struct IntegerLiteralInfo {
    uint64_t value = 0;
    int base = 10;
    bool has_unsigned_suffix = false;
    int long_suffix_count = 0;
    bool has_bitint_suffix = false;

    bool is_decimal() const { return base == 10; }
};

inline int integer_literal_digit_value(char c) {
    if (c >= '0' && c <= '9') {
        return c - '0';
    }
    if (c >= 'a' && c <= 'f') {
        return 10 + (c - 'a');
    }
    if (c >= 'A' && c <= 'F') {
        return 10 + (c - 'A');
    }
    return -1;
}

inline bool parse_integer_literal_suffix(std::string_view suffix,
                                         bool& has_unsigned,
                                         int& long_count,
                                         bool& has_bitint) {
    has_unsigned = false;
    long_count = 0;
    has_bitint = false;
    size_t index = 0;

    auto parse_unsigned = [&]() -> bool {
        if (index < suffix.size() && (suffix[index] == 'u' || suffix[index] == 'U')) {
            if (has_unsigned) {
                return false;
            }
            has_unsigned = true;
            ++index;
        }
        return true;
    };

    auto parse_long = [&]() -> bool {
        if (index >= suffix.size() || (suffix[index] != 'l' && suffix[index] != 'L')) {
            return true;
        }
        char first = suffix[index];
        ++index;
        long_count = 1;
        if (index < suffix.size() && (suffix[index] == 'l' || suffix[index] == 'L')) {
            if (suffix[index] != first) {
                return false;
            }
            ++index;
            long_count = 2;
        }
        return true;
    };

    auto parse_bitint = [&]() -> bool {
        if (index + 1 < suffix.size() &&
            ((suffix[index] == 'w' && suffix[index + 1] == 'b') ||
             (suffix[index] == 'W' && suffix[index + 1] == 'B'))) {
            has_bitint = true;
            index += 2;
        }
        return true;
    };

    if (!parse_unsigned()) {
        return false;
    }
    if (!parse_long()) {
        return false;
    }
    if (long_count == 0) {
        parse_bitint();
    }
    if (!parse_unsigned()) {
        return false;
    }
    return index == suffix.size();
}

inline std::optional<IntegerLiteralInfo>
parse_integer_literal_info(std::string_view text) {
    if (text.empty()) {
        return std::nullopt;
    }

    IntegerLiteralInfo info;
    size_t index = 0;
    if (text.size() >= 2 && text[0] == '0' &&
        (text[1] == 'x' || text[1] == 'X')) {
        info.base = 16;
        index = 2;
    } else if (text.size() >= 2 && text[0] == '0' &&
               (text[1] == 'b' || text[1] == 'B')) {
        info.base = 2;
        index = 2;
    } else if (text.size() > 1 && text[0] == '0') {
        info.base = 8;
    }

    size_t digits_begin = index;
    uint64_t value = 0;
    for (; index < text.size(); ++index) {
        if (text[index] == '\'' && index > digits_begin &&
            index + 1 < text.size()) {
            int next_digit = integer_literal_digit_value(text[index + 1]);
            if (next_digit >= 0 && next_digit < info.base) {
                continue;
            }
            break;
        }
        int digit = integer_literal_digit_value(text[index]);
        if (digit < 0 || digit >= info.base) {
            break;
        }
        uint64_t digit_value = static_cast<uint64_t>(digit);
        if (value > (std::numeric_limits<uint64_t>::max() - digit_value) /
                        static_cast<uint64_t>(info.base)) {
            return std::nullopt;
        }
        value = value * static_cast<uint64_t>(info.base) + digit_value;
    }
    if (index == digits_begin) {
        return std::nullopt;
    }

    bool has_unsigned = false;
    int long_count = 0;
    bool has_bitint = false;
    if (!parse_integer_literal_suffix(text.substr(index), has_unsigned, long_count,
                                      has_bitint)) {
        return std::nullopt;
    }

    info.value = value;
    info.has_unsigned_suffix = has_unsigned;
    info.long_suffix_count = long_count;
    info.has_bitint_suffix = has_bitint;
    return info;
}

inline std::optional<uint64_t> parse_integer_literal_u64(std::string_view text) {
    auto parsed = parse_integer_literal_info(text);
    return parsed ? std::optional<uint64_t>(parsed->value) : std::nullopt;
}

#endif // ABURI_NUMERIC_UTILS_H
