#include <__adinkra/sstream>

#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

_ADINKRA_BEGIN_NAMESPACE_STD

namespace __sstream {

namespace {

size_t formatted_size(int count, size_t capacity) noexcept {
    return count > 0 && static_cast<size_t>(count) < capacity
        ? static_cast<size_t>(count)
        : 0;
}

size_t skip_whitespace(
    const char* data, size_t size, size_t position) noexcept {
    while (position < size &&
           ::isspace(
               static_cast<unsigned char>(data[position]))) {
        ++position;
    }
    return position;
}

size_t token_end(
    const char* data, size_t size, size_t position) noexcept {
    while (position < size &&
           !::isspace(
               static_cast<unsigned char>(data[position]))) {
        ++position;
    }
    return position;
}

} // namespace

size_t format_signed(
    char* destination, size_t capacity, long long value,
    int base, bool uppercase_value, bool show_base,
    bool show_positive) noexcept {
    char format[8] = {'%', '\0', '\0', '\0', '\0', '\0', '\0', '\0'};
    int position = 1;
    if (show_positive) {
        format[position++] = '+';
    }
    if (show_base) {
        format[position++] = '#';
    }
    format[position++] = 'l';
    format[position++] = 'l';
    format[position++] =
        base == 16 ? (uppercase_value ? 'X' : 'x')
      : base == 8  ? 'o'
                   : 'd';
    format[position] = '\0';
    return formatted_size(
        ::snprintf(destination, capacity, format, value),
        capacity);
}

size_t format_unsigned(
    char* destination, size_t capacity, unsigned long long value,
    int base, bool uppercase_value, bool show_base,
    bool show_positive) noexcept {
    char format[8] = {'%', '\0', '\0', '\0', '\0', '\0', '\0', '\0'};
    int position = 1;
    if (show_positive) {
        format[position++] = '+';
    }
    if (show_base) {
        format[position++] = '#';
    }
    format[position++] = 'l';
    format[position++] = 'l';
    format[position++] =
        base == 16 ? (uppercase_value ? 'X' : 'x')
      : base == 8  ? 'o'
                   : 'u';
    format[position] = '\0';
    return formatted_size(
        ::snprintf(destination, capacity, format, value),
        capacity);
}

size_t format_floating(
    char* destination, size_t capacity, long double value,
    int precision, bool uppercase_value, bool scientific_value,
    bool fixed_value, bool show_point,
    bool show_positive) noexcept {
    char format[16] = {'%', '\0'};
    int position = 1;
    if (show_positive) {
        format[position++] = '+';
    }
    if (show_point) {
        format[position++] = '#';
    }
    format[position++] = '.';
    format[position++] = '*';
    format[position++] = 'L';
    format[position++] =
        scientific_value && fixed_value
            ? (uppercase_value ? 'A' : 'a')
      : scientific_value ? (uppercase_value ? 'E' : 'e')
      : fixed_value      ? (uppercase_value ? 'F' : 'f')
                         : (uppercase_value ? 'G' : 'g');
    format[position] = '\0';
    return formatted_size(
        ::snprintf(
            destination, capacity, format, precision, value),
        capacity);
}

size_t format_pointer(
    char* destination, size_t capacity,
    const void* value, bool uppercase_value) noexcept {
    const int count =
        ::snprintf(destination, capacity, "%p", value);
    const size_t result = formatted_size(count, capacity);
    if (uppercase_value) {
        for (size_t index = 0; index < result; ++index) {
            destination[index] = static_cast<char>(
                ::toupper(
                    static_cast<unsigned char>(
                        destination[index])));
        }
    }
    return result;
}

bool read_signed(
    const char* data, size_t size, size_t& position,
    int base, long long& value) noexcept {
    const size_t start = skip_whitespace(data, size, position);
    if (start == size) {
        return false;
    }
    char* end = nullptr;
    errno = 0;
    const long long parsed = ::strtoll(data + start, &end, base);
    if (errno == ERANGE || end == data + start ||
        end > data + size) {
        return false;
    }
    position = static_cast<size_t>(end - data);
    value = parsed;
    return true;
}

bool read_unsigned(
    const char* data, size_t size, size_t& position,
    int base, unsigned long long& value) noexcept {
    const size_t start = skip_whitespace(data, size, position);
    if (start == size) {
        return false;
    }
    char* end = nullptr;
    errno = 0;
    const unsigned long long parsed =
        ::strtoull(data + start, &end, base);
    if (errno == ERANGE || end == data + start ||
        end > data + size) {
        return false;
    }
    position = static_cast<size_t>(end - data);
    value = parsed;
    return true;
}

bool read_floating(
    const char* data, size_t size, size_t& position,
    long double& value) noexcept {
    const size_t start = skip_whitespace(data, size, position);
    if (start == size) {
        return false;
    }
    char* end = nullptr;
    errno = 0;
    const long double parsed = ::strtold(data + start, &end);
    if ((errno == ERANGE && __builtin_isinf(parsed)) ||
        end == data + start ||
        end > data + size) {
        return false;
    }
    position = static_cast<size_t>(end - data);
    value = parsed;
    return true;
}

bool read_token(
    const char* data, size_t size, size_t& position,
    size_t& start, size_t& count) noexcept {
    start = skip_whitespace(data, size, position);
    if (start == size) {
        count = 0;
        return false;
    }
    const size_t end = token_end(data, size, start);
    count = end - start;
    position = end;
    return true;
}

} // namespace __sstream

_ADINKRA_END_NAMESPACE_STD
