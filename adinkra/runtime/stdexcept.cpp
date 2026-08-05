#include <stdexcept>
#include <string>
#include <new>

#include <stdlib.h>
#include <string.h>

namespace {

char* copy_message(const char* message) {
    const char* source = message == nullptr ? "" : message;
    const size_t size = ::strlen(source) + 1;
    char* result = static_cast<char*>(::malloc(size));
    if (result == nullptr) {
        throw std::bad_alloc();
    }
    ::memcpy(result, source, size);
    return result;
}

} // namespace

namespace std {
inline namespace __adinkra_v1 {

logic_error::logic_error(const char* message)
    : message_(copy_message(message)) {}

logic_error::logic_error(const string& message)
    : logic_error(message.c_str()) {}

logic_error::logic_error(const logic_error& other)
    : exception(other), message_(copy_message(other.message_)) {}

logic_error& logic_error::operator=(const logic_error& other) {
    if (this != &other) {
        char* replacement = copy_message(other.message_);
        ::free(message_);
        message_ = replacement;
    }
    return *this;
}

logic_error::~logic_error() noexcept {
    ::free(message_);
}

const char* logic_error::what() const noexcept {
    return message_;
}

runtime_error::runtime_error(const char* message)
    : message_(copy_message(message)) {}

runtime_error::runtime_error(const string& message)
    : runtime_error(message.c_str()) {}

runtime_error::runtime_error(const runtime_error& other)
    : exception(other), message_(copy_message(other.message_)) {}

runtime_error& runtime_error::operator=(const runtime_error& other) {
    if (this != &other) {
        char* replacement = copy_message(other.message_);
        ::free(message_);
        message_ = replacement;
    }
    return *this;
}

runtime_error::~runtime_error() noexcept {
    ::free(message_);
}

const char* runtime_error::what() const noexcept {
    return message_;
}

} // namespace __adinkra_v1
} // namespace std
