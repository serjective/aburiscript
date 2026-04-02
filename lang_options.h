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

// Language mode and feature gating options.
// Controls which language extensions and standard-specific behaviors are enabled.
struct LangOptions {
    // When true, calling an undeclared function implicitly declares it as
    // int name() (K&R, no prototype).  Enabled for C89/gnu89 modes.
    bool implicit_function_declarations = false;

    // When true, a declaration without a type specifier defaults to int.
    // K&R / C89 feature.
    bool implicit_int = false;

    // When true, K&R old-style function definitions with identifier-lists
    // and declaration-lists are accepted.  Enabled for C89/gnu89 modes.
    bool kr_style_definitions = false;

    // The language standard string (e.g. "c89", "gnu89", "c11", "gnu11").
    // Empty means the compiler default (currently C11-ish).
    std::string standard;
    LanguageMode language_mode = LanguageMode::Auto;

    // Stage-gated replacement constant-evaluation engine.
    // Kept disabled by default to preserve current behavior until migration.
    bool enable_consteval_engine = false;

    // Stage-gated constexpr function interpreter scaffolding.
    // Disabled by default until C++ constexpr/consteval call evaluation is wired.
    bool enable_consteval_function_interpreter = false;
    size_t consteval_step_limit = 100000;
    size_t consteval_recursion_limit = 67;

    // C23 constexpr declaration-specifier support gate.
    // When false, 'constexpr' is treated as an identifier in all modes.
    bool enable_c23_constexpr = true;

    // Disabled by default to preserve current parser behavior until migrated.
    bool enable_cpp_parser = false;

    // C++ exception syntax/runtime support gate.
    bool exceptions_enabled = true;

    // Darwin Blocks language extension gate.
    // Default means "follow target policy" rather than hard-enable globally.
    BlocksMode blocks_mode = BlocksMode::Default;

    static std::string normalize_ascii(std::string value) {
        std::transform(value.begin(), value.end(), value.begin(),
            [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
        return value;
    }

    static bool is_cpp_standard_name(const std::string& std_name) {
        return std_name == "c++17" || std_name == "gnu++17" ||
               std_name == "c++20" || std_name == "gnu++20";
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
            return true;
        }
        if (language == "c++" || language == "cpp" || language == "cxx" ||
            language == "cc" || language == "c++-cpp-output") {
            language_mode = LanguageMode::CXX;
            return true;
        }
        return false;
    }

    bool is_cxx_mode() const {
        return language_mode == LanguageMode::CXX || is_cpp_standard_name(standard);
    }

    bool is_cxx20_or_later() const {
        if (!is_cxx_mode()) {
            return false;
        }
        if (standard.empty()) {
            return false;
        }
        return standard == "c++20" || standard == "gnu++20";
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

    bool uses_gnu_inline_semantics() const {
        return is_c_mode() && (standard == "c89" || standard == "gnu89");
    }

    // Returns the value for __cplusplus if C++ mode is active.
    // Default C++ mode (no explicit -std) uses C++17 for deterministic behavior.
    std::optional<long long> cplusplus_macro_value() const {
        if (!is_cxx_mode()) {
            return std::nullopt;
        }
        if (standard == "c++20" || standard == "gnu++20") {
            return 202002LL;
        }
        if (standard == "c++17" || standard == "gnu++17") {
            return 201703LL;
        }
        return 201703LL;
    }

    // Returns the value for __STDC_VERSION__ if it should be defined.
    // No explicit C standard keeps historical project default (C11).
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

    // Convenience: configure options from a -std= value.
    bool set_standard(const std::string& std_val) {
        clear_standard_derived_flags();
        standard = canonical_standard_name(std_val);

        if (is_cpp_standard_name(standard)) {
            language_mode = LanguageMode::CXX;
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
