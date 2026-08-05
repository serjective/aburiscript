#include <cerrno>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <string>

_ADINKRA_BEGIN_NAMESPACE_STD

namespace {

template<class Value>
string format_number(const char* format, Value value) {
    const int required = ::snprintf(nullptr, 0, format, value);
    if (required < 0) {
        throw runtime_error("to_string formatting failed");
    }

    string result(static_cast<size_t>(required), '\0');
    const int written = ::snprintf(
        result.data(), result.size() + 1, format, value);
    if (written != required) {
        throw runtime_error("to_string formatting failed");
    }
    return result;
}

} // namespace

string to_string(int value) {
    return format_number("%d", value);
}

string to_string(unsigned int value) {
    return format_number("%u", value);
}

string to_string(long value) {
    return format_number("%ld", value);
}

string to_string(unsigned long value) {
    return format_number("%lu", value);
}

string to_string(long long value) {
    return format_number("%lld", value);
}

string to_string(unsigned long long value) {
    return format_number("%llu", value);
}

string to_string(float value) {
    return format_number("%f", value);
}

string to_string(double value) {
    return format_number("%f", value);
}

string to_string(long double value) {
    return format_number("%Lf", value);
}

namespace {

template<class Result, class Parse>
Result parse_integer(
    const string& value, size_t* position,
    int base, Parse parse) {
    const char* begin = value.c_str();
    char* end = nullptr;
    errno = 0;
    const Result result = parse(begin, &end, base);
    if (end == begin) {
        throw invalid_argument("invalid numeric string");
    }
    if (errno == ERANGE) {
        throw out_of_range("numeric string out of range");
    }
    if (position != nullptr) {
        *position = static_cast<size_t>(end - begin);
    }
    return result;
}

template<class Result, class Parse>
Result parse_floating(
    const string& value, size_t* position, Parse parse) {
    const char* begin = value.c_str();
    char* end = nullptr;
    errno = 0;
    const Result result = parse(begin, &end);
    if (end == begin) {
        throw invalid_argument("invalid numeric string");
    }
    if (errno == ERANGE) {
        throw out_of_range("numeric string out of range");
    }
    if (position != nullptr) {
        *position = static_cast<size_t>(end - begin);
    }
    return result;
}

} // namespace

int stoi(const string& value, size_t* position, int base) {
    const long result = stol(value, position, base);
    if (result < INT_MIN || result > INT_MAX) {
        throw out_of_range("numeric string out of range");
    }
    return static_cast<int>(result);
}

long stol(const string& value, size_t* position, int base) {
    return parse_integer<long>(
        value, position, base, ::strtol);
}

unsigned long stoul(
    const string& value, size_t* position, int base) {
    return parse_integer<unsigned long>(
        value, position, base, ::strtoul);
}

long long stoll(
    const string& value, size_t* position, int base) {
    return parse_integer<long long>(
        value, position, base, ::strtoll);
}

unsigned long long stoull(
    const string& value, size_t* position, int base) {
    return parse_integer<unsigned long long>(
        value, position, base, ::strtoull);
}

float stof(const string& value, size_t* position) {
    return parse_floating<float>(
        value, position, ::strtof);
}

double stod(const string& value, size_t* position) {
    return parse_floating<double>(
        value, position, ::strtod);
}

long double stold(const string& value, size_t* position) {
    return parse_floating<long double>(
        value, position, ::strtold);
}

_ADINKRA_END_NAMESPACE_STD
