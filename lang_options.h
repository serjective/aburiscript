#ifndef ABURI_LANG_OPTIONS_H
#define ABURI_LANG_OPTIONS_H

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <optional>
#include <string>

enum class LanguageMode {
    Auto,
    C,
    CXX
};

enum class BlocksMode {
    Default,
    Enabled,
    Disabled
};

enum class ConstevalFunctionInterpreterPolicy {
    LanguageDefault,
    Enabled,
    Disabled
};

struct LangOptions {
    bool implicit_function_declarations = false;
    bool implicit_int = false;

    bool kr_style_definitions = false;
    std::string standard;
    LanguageMode language_mode = LanguageMode::Auto;

    bool enable_consteval_engine = false;
    ConstevalFunctionInterpreterPolicy consteval_function_interpreter =
        ConstevalFunctionInterpreterPolicy::LanguageDefault;
    size_t consteval_step_limit = 1048576;
    size_t consteval_recursion_limit = 512;

    bool enable_c23_constexpr = true;
    bool enable_coroutine_pre_split_cir = true;
    bool syntax_only = false;

    bool trivial_auto_var_init_zero = false;
    int optimization_level = 0;
    bool optimize_for_size = false;

    bool exceptions_enabled = true;
    BlocksMode blocks_mode = BlocksMode::Default;

    bool template_pattern_cloning = true;
    bool template_fallback_notes = false;
    bool enable_cpp_reflection = false;

    bool objc = false;
    bool objc_arc = false;

    static std::string normalize_ascii(std::string value) {
        std::transform(value.begin(), value.end(), value.begin(),
            [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
        return value;
    }

    static bool is_cpp_standard_name(const std::string& std_name) {
        return std_name == "c++17" || std_name == "gnu++17" ||
               std_name == "c++20" || std_name == "gnu++20" ||
               std_name == "c++23" || std_name == "gnu++23" ||
               std_name == "c++26" || std_name == "gnu++26";
    }

    static bool is_c_standard_name(const std::string& std_name) {
        return std_name == "c89" || std_name == "c90" ||
               std_name == "gnu89" || std_name == "gnu90" ||
               std_name == "c99" || std_name == "gnu99" ||
               std_name == "c11" || std_name == "gnu11" ||
               std_name == "c17" || std_name == "gnu17" ||
               std_name == "c23" || std_name == "gnu23" ||
               std_name == "c2x" || std_name == "gnu2x";
    }

    static std::string canonical_standard_name(std::string std_name) {
        std_name = normalize_ascii(std::move(std_name));
        if (std_name == "c90") return "c89";
        if (std_name == "gnu90") return "gnu89";
        if (std_name == "c++2b") return "c++23";
        if (std_name == "gnu++2b") return "gnu++23";
        if (std_name == "c++2c") return "c++26";
        if (std_name == "gnu++2c") return "gnu++26";
        return std_name;
    }

    void clear_standard_derived_flags() {
        implicit_function_declarations = false;
        implicit_int = false;
        kr_style_definitions = false;
    }

    bool set_language_from_x(std::string language) {
        language = normalize_ascii(std::move(language));
        if (language == "auto" || language == "none") {
            language_mode = LanguageMode::Auto;
            return true;
        }
        if (language == "c") {
            language_mode = LanguageMode::C;
            objc = false;
            return true;
        }
        if (language == "c++" || language == "cpp" || language == "cxx" ||
            language == "cc" || language == "c++-cpp-output" ||
            language == "c++-module") {
            language_mode = LanguageMode::CXX;
            objc = false;
            return true;
        }
        if (language == "objective-c" || language == "objective-c-header" ||
            language == "objective-c-cpp-output") {
            language_mode = LanguageMode::C;
            objc = true;
            return true;
        }
        if (language == "objective-c++" || language == "objective-c++-header" ||
            language == "objective-c++-cpp-output") {
            language_mode = LanguageMode::CXX;
            objc = true;
            return true;
        }
        return false;
    }

    bool is_objc() const {
        return objc;
    }

    bool is_objc_arc() const {
        return objc && objc_arc;
    }

    bool is_cxx_mode() const {
        return language_mode == LanguageMode::CXX || is_cpp_standard_name(standard);
    }

    bool consteval_function_interpreter_enabled() const {
        switch (consteval_function_interpreter) {
            case ConstevalFunctionInterpreterPolicy::Enabled:
                return true;
            case ConstevalFunctionInterpreterPolicy::Disabled:
                return false;
            case ConstevalFunctionInterpreterPolicy::LanguageDefault:
                return is_cxx_mode();
        }
        return false;
    }

    bool is_cxx26_or_later() const {
        if (!is_cxx_mode()) {
            return false;
        }
        return standard == "c++26" || standard == "gnu++26";
    }

    bool is_cxx20_or_later() const {
        if (!is_cxx_mode()) {
            return false;
        }
        return standard == "c++20" || standard == "gnu++20" ||
               standard == "c++23" || standard == "gnu++23" ||
               is_cxx26_or_later();
    }

    bool modules_enabled() const {
        return is_cxx20_or_later();
    }

    bool is_cxx17_or_later() const {
        if (!is_cxx_mode()) {
            return false;
        }

        if (standard.empty()) {
            return true;
        }
        return standard == "c++17" || standard == "gnu++17" ||
               is_cxx20_or_later();
    }

    bool is_c_mode() const {
        if (language_mode == LanguageMode::C) {
            return true;
        }
        if (language_mode == LanguageMode::CXX) {
            return false;
        }
        return !is_cpp_standard_name(standard);
    }

    bool is_gnu_mode() const {
        return standard.rfind("gnu", 0) == 0;
    }

    bool is_c23_or_later() const {
        return is_c_mode() &&
               (standard == "c23" || standard == "gnu23" ||
                standard == "c2x" || standard == "gnu2x");
    }

    bool uses_gnu_inline_semantics() const {
        return is_c_mode() && (standard == "c89" || standard == "gnu89");
    }

    std::optional<long long> cplusplus_macro_value() const {
        if (!is_cxx_mode()) {
            return std::nullopt;
        }
        if (standard == "c++26" || standard == "gnu++26") {
            return 202400LL;
        }
        if (standard == "c++23" || standard == "gnu++23") {
            return 202302LL;
        }
        if (standard == "c++20" || standard == "gnu++20") {
            return 202002LL;
        }
        if (standard == "c++17" || standard == "gnu++17") {
            return 201703LL;
        }
        return 201703LL;
    }
    std::optional<long long> stdc_version_macro_value() const {
        if (is_cxx_mode()) {
            return std::nullopt;
        }
        if (standard.empty()) {
            return 201112LL;
        }
        if (standard == "c89" || standard == "gnu89") {
            return std::nullopt;
        }
        if (standard == "c99" || standard == "gnu99") {
            return 199901LL;
        }
        if (standard == "c11" || standard == "gnu11") {
            return 201112LL;
        }
        if (standard == "c17" || standard == "gnu17") {
            return 201710LL;
        }
        if (standard == "c23" || standard == "gnu23" ||
            standard == "c2x" || standard == "gnu2x") {
            return 202311LL;
        }
        return 201112LL;
    }
    bool set_standard(const std::string& std_val) {
        clear_standard_derived_flags();
        standard = canonical_standard_name(std_val);

        if (is_cpp_standard_name(standard)) {
            language_mode = LanguageMode::CXX;
            if (is_cxx26_or_later()) {
                enable_cpp_reflection = true;
            }
            return true;
        }

        if (!is_c_standard_name(standard)) {
            standard.clear();
            return false;
        }

        if (standard == "c89" || standard == "gnu89") {
            implicit_function_declarations = true;
            implicit_int = true;
            kr_style_definitions = true;
        }
        if (language_mode == LanguageMode::Auto) {
            language_mode = LanguageMode::C;
        }
        return true;
    }
};

#endif // ABURI_LANG_OPTIONS_H
