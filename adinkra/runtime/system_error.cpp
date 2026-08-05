#include <system_error>

#include <cerrno>
#include <cstring>
#include <string>

namespace {

std::string error_message(int value) {
    char buffer[256] = {};
    if (::strerror_r(value, buffer, sizeof(buffer)) == 0) {
        return std::string(buffer);
    }
    return std::string("Unknown error ") + std::to_string(value);
}

std::string system_error_message(
    const std::error_code& code, const char* message) {
    std::string result(message == nullptr ? "" : message);
    if (!result.empty()) {
        result += ": ";
    }
    result += code.message();
    return result;
}

class generic_error_category final : public std::error_category {
public:
    const char* name() const noexcept override {
        return "generic";
    }

    std::string message(int value) const override {
        return error_message(value);
    }
};

class system_error_category final : public std::error_category {
public:
    const char* name() const noexcept override {
        return "system";
    }

    std::error_condition
    default_error_condition(int value) const noexcept override {
        return std::error_condition(value, std::generic_category());
    }

    std::string message(int value) const override {
        return error_message(value);
    }
};

} // namespace

namespace std {
inline namespace __adinkra_v1 {

error_category::~error_category() = default;

error_condition
error_category::default_error_condition(int value) const noexcept {
    return error_condition(value, *this);
}

bool error_category::equivalent(
    int code, const error_condition& condition) const noexcept {
    return default_error_condition(code) == condition;
}

bool error_category::equivalent(
    const error_code& code, int condition) const noexcept {
    return *this == code.category() && code.value() == condition;
}

const error_category& generic_category() noexcept {
    static const generic_error_category category;
    return category;
}

const error_category& system_category() noexcept {
    static const system_error_category category;
    return category;
}

system_error::system_error(error_code code, const string& message)
    : system_error(code, message.c_str()) {}

system_error::system_error(error_code code, const char* message)
    : runtime_error(system_error_message(code, message)),
      code_(code) {}

system_error::system_error(error_code code)
    : runtime_error(code.message()), code_(code) {}

system_error::system_error(
    int value, const error_category& category,
    const string& message)
    : system_error(error_code(value, category), message) {}

system_error::system_error(
    int value, const error_category& category,
    const char* message)
    : system_error(error_code(value, category), message) {}

system_error::system_error(
    int value, const error_category& category)
    : system_error(error_code(value, category)) {}

} // namespace __adinkra_v1
} // namespace std
