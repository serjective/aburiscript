#include "preprocessor.h"
#include "helpers/casting.h"
#include "abi/darwin_blocks.h"
#include "builtin_registry.h"
#include "constexpr/pp_consteval.h"
#include "target_feature_gate.h"
#include <ctime>
#include <cctype>
#include <filesystem>
#include <iostream>
#include <optional>

static HideSetType union_hide_sets(const HideSetType& lhs, const HideSetType& rhs) {
    if (!lhs) {
        return rhs;
    }
    if (!rhs) {
        return lhs;
    }
    auto merged = std::make_shared<std::unordered_set<std::string>>(*lhs);
    merged->insert(rhs->begin(), rhs->end());
    return merged;
}

static HideSetType intersect_hide_sets(const HideSetType& lhs, const HideSetType& rhs) {
    if (!lhs || !rhs) {
        return nullptr;
    }
    auto inter = std::make_shared<std::unordered_set<std::string>>();
    for (const auto& s : *lhs) {
        if (rhs->contains(s)) {
            inter->insert(s);
        }
    }
    if (inter->empty()) {
        return nullptr;
    }
    return inter;
}

enum class DirectiveKind {
    Define, Undef, Line, Error, Warning, Pragma, Include, IncludeNext,
    Import, If, Ifdef, Ifndef, Else, Elif, Endif, Ident, Sccs, Unknown
};

static DirectiveKind classify_directive(const std::string& name) {
    // Use a static lookup table for O(1) directive dispatch
    static const std::unordered_map<std::string_view, DirectiveKind> table = {
        {"define",       DirectiveKind::Define},
        {"undef",        DirectiveKind::Undef},
        {"line",         DirectiveKind::Line},
        {"error",        DirectiveKind::Error},
        {"warning",      DirectiveKind::Warning},
        {"pragma",       DirectiveKind::Pragma},
        {"include",      DirectiveKind::Include},
        {"include_next", DirectiveKind::IncludeNext},
        {"import",       DirectiveKind::Import},
        {"if",           DirectiveKind::If},
        {"ifdef",        DirectiveKind::Ifdef},
        {"ifndef",       DirectiveKind::Ifndef},
        {"else",         DirectiveKind::Else},
        {"elif",         DirectiveKind::Elif},
        {"endif",        DirectiveKind::Endif},
        {"ident",        DirectiveKind::Ident},
        {"sccs",         DirectiveKind::Sccs},
    };
    auto it = table.find(std::string_view(name));
    return it != table.end() ? it->second : DirectiveKind::Unknown;
}

static bool is_power_of_two(size_t value) {
    return value != 0 && (value & (value - 1)) == 0;
}

static bool is_c23_family_standard(const std::string& std_name) {
    return std_name == "c23" || std_name == "gnu23" ||
           std_name == "c2x" || std_name == "gnu2x";
}

static std::optional<size_t> parse_pack_alignment_value(const Token& tok, size_t max_alignment) {
    if (tok.type != TokenType::INTEGER_CONST && tok.type != TokenType::PP_NUMBER) {
        return std::nullopt;
    }
    const std::string& text = tok.value;
    size_t i = 0;
    while (i < text.size() && std::isdigit(static_cast<unsigned char>(text[i]))) {
        ++i;
    }
    if (i == 0) {
        return std::nullopt;
    }
    size_t value = 0;
    try {
        value = static_cast<size_t>(std::stoull(text.substr(0, i)));
    } catch (...) {
        return std::nullopt;
    }
    if (!is_power_of_two(value)) {
        return std::nullopt;
    }
    if (value > max_alignment) {
        return std::nullopt;
    }
    return value;
}

static std::optional<WarningId> warning_id_from_flag(std::string_view flag) {
    if (flag.rfind("-W", 0) == 0) {
        flag.remove_prefix(2);
    } else if (flag.rfind("W", 0) == 0) {
        flag.remove_prefix(1);
    }
    if (flag.rfind("no-", 0) == 0) {
        flag.remove_prefix(3);
    }
    if (flag == "deprecated-declarations") return WarningId::DeprecatedDeclarations;
    if (flag == "discarded-qualifiers") return WarningId::DiscardedQualifiers;
    if (flag == "unknown-attributes") return WarningId::UnknownAttributes;
    if (flag == "attributes") return WarningId::Attributes;
    if (flag == "override-init") return WarningId::OverrideInit;
    if (flag == "varargs") return WarningId::Varargs;
    return std::nullopt;
}

static std::vector<Token> tokenize_pragma_text(std::string_view text, SrcLoc loc) {
    auto is_pp_identifier_start = [](unsigned char ch, char raw) {
        return raw == '_' || raw == '$' || std::isalpha(ch);
    };
    auto is_pp_identifier_continue = [&](unsigned char ch, char raw) {
        return raw == '_' || raw == '$' || std::isalnum(ch);
    };
    std::vector<Token> tokens;
    size_t i = 0;
    while (i < text.size()) {
        unsigned char ch = static_cast<unsigned char>(text[i]);
        if (std::isspace(ch)) {
            ++i;
            continue;
        }
        if (is_pp_identifier_start(ch, text[i])) {
            size_t start = i++;
            while (i < text.size()) {
                unsigned char c = static_cast<unsigned char>(text[i]);
                if (!is_pp_identifier_continue(c, text[i])) break;
                ++i;
            }
            tokens.emplace_back(TokenType::IDENTIFIER, std::string(text.substr(start, i - start)), loc);
            continue;
        }
        if (std::isdigit(ch)) {
            size_t start = i++;
            while (i < text.size() && std::isdigit(static_cast<unsigned char>(text[i]))) {
                ++i;
            }
            tokens.emplace_back(TokenType::INTEGER_CONST, std::string(text.substr(start, i - start)), loc);
            continue;
        }
        if (text[i] == '(') {
            tokens.emplace_back(TokenType::LEFT_PAREN, "(", loc);
            ++i;
            continue;
        }
        if (text[i] == ')') {
            tokens.emplace_back(TokenType::RIGHT_PAREN, ")", loc);
            ++i;
            continue;
        }
        if (text[i] == ',') {
            tokens.emplace_back(TokenType::COMMA, ",", loc);
            ++i;
            continue;
        }
        if (text[i] == '"') {
            ++i;
            std::string value;
            while (i < text.size()) {
                char c = text[i];
                if (c == '\\' && i + 1 < text.size()) {
                    value += text[i + 1];
                    i += 2;
                    continue;
                }
                if (c == '"') {
                    ++i;
                    break;
                }
                value += c;
                ++i;
            }
            tokens.emplace_back(TokenType::STRING_LITERAL, value, loc);
            continue;
        }
        ++i;
    }
    return tokens;
}

static std::optional<std::string> parse_pragma_macro_name(const std::vector<Token>& tokens) {
    if (tokens.size() != 4) {
        return std::nullopt;
    }
    if (tokens[1].type != TokenType::LEFT_PAREN ||
        tokens[2].type != TokenType::STRING_LITERAL ||
        tokens[3].type != TokenType::RIGHT_PAREN) {
        return std::nullopt;
    }
    return tokens[2].value;
}

static std::string literal_prefix_spelling(LiteralPrefix prefix) {
    switch (prefix) {
        case LiteralPrefix::L: return "L";
        case LiteralPrefix::U8: return "u8";
        case LiteralPrefix::U: return "U";
        case LiteralPrefix::u: return "u";
        case LiteralPrefix::None:
        default:
            return "";
    }
}

static void append_hex_escape(std::string& out, unsigned char byte) {
    static const char kHex[] = "0123456789ABCDEF";
    out += "\\x";
    out.push_back(kHex[(byte >> 4) & 0xF]);
    out.push_back(kHex[byte & 0xF]);
}

static std::string escape_literal_payload(std::string_view payload, bool is_char_literal) {
    std::string escaped;
    escaped.reserve(payload.size());
    for (unsigned char byte : payload) {
        switch (byte) {
            case '\a': escaped += "\\a"; break;
            case '\b': escaped += "\\b"; break;
            case '\f': escaped += "\\f"; break;
            case '\n': escaped += "\\n"; break;
            case '\r': escaped += "\\r"; break;
            case '\t': escaped += "\\t"; break;
            case '\v': escaped += "\\v"; break;
            case '\\': escaped += "\\\\"; break;
            case '"':
                if (is_char_literal) {
                    escaped.push_back('"');
                } else {
                    escaped += "\\\"";
                }
                break;
            case '\'':
                if (is_char_literal) {
                    escaped += "\\'";
                } else {
                    escaped.push_back('\'');
                }
                break;
            default:
                if (byte < 0x20 || byte >= 0x7F) {
                    append_hex_escape(escaped, byte);
                } else {
                    escaped.push_back(static_cast<char>(byte));
                }
                break;
        }
    }
    return escaped;
}

static std::string token_spelling_for_output(const Token& t) {
    switch (t.type) {
        case TokenType::STRING_LITERAL:
            return literal_prefix_spelling(t.literal_prefix) + "\"" +
                escape_literal_payload(t.value, false) + "\"";
        case TokenType::CHAR_LITERAL:
            return literal_prefix_spelling(t.literal_prefix) + "'" +
                escape_literal_payload(t.value, true) + "'";
        case TokenType::UNSIGNED_INTEGER_CONST:
            return t.value + "U";
        case TokenType::LONG_CONST:
            return t.value + "L";
        case TokenType::UNSIGNED_LONG_CONST:
            return t.value + "UL";
        case TokenType::LONG_LONG_CONST:
            return t.value + "LL";
        case TokenType::UNSIGNED_LONG_LONG_CONST:
            return t.value + "ULL";
        case TokenType::FLOAT_CONST:
            return t.value + "F";
        case TokenType::LONG_DOUBLE_CONST:
            return t.value + "L";
        case TokenType::IMAG_INTEGER_CONST:
            return t.value + "i";
        case TokenType::IMAG_UNSIGNED_INTEGER_CONST:
            return t.value + "Ui";
        case TokenType::IMAG_LONG_CONST:
            return t.value + "Li";
        case TokenType::IMAG_UNSIGNED_LONG_CONST:
            return t.value + "ULi";
        case TokenType::IMAG_LONG_LONG_CONST:
            return t.value + "LLi";
        case TokenType::IMAG_UNSIGNED_LONG_LONG_CONST:
            return t.value + "ULLi";
        case TokenType::IMAG_FLOAT_CONST:
            return t.value + "Fi";
        case TokenType::IMAG_DOUBLE_CONST:
            return t.value + "i";
        case TokenType::IMAG_LONG_DOUBLE_CONST:
            return t.value + "Li";
        default:
            return t.value;
    }
}

static std::string token_sequence_spelling_for_macro_dump(const std::vector<Token>& tokens) {
    std::string text;
    bool first = true;
    for (const auto& token : tokens) {
        if (!first) {
            text.push_back(' ');
        }
        text += token_spelling_for_output(token);
        first = false;
    }
    return text;
}

static std::vector<Token> builtin_macro_tokens_for_dump(const PreProcess& pp,
                                                        const MacroDefinition& mdef) {
    std::vector<Token> result;
    switch (mdef.builtin_kind) {
        case MacroDefinition::BuiltinKind::Line:
            result.emplace_back(TokenType::INTEGER_CONST, "1", SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::File:
            result.emplace_back(TokenType::STRING_LITERAL, pp.base_file_name.empty() ? "<stdin>" : pp.base_file_name,
                                SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::FileName:
            result.emplace_back(TokenType::STRING_LITERAL,
                                std::filesystem::path(pp.base_file_name.empty() ? "<stdin>" : pp.base_file_name)
                                    .filename().string(),
                                SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::Counter:
            result.emplace_back(TokenType::INTEGER_CONST, "0", SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::Date:
            result.emplace_back(TokenType::STRING_LITERAL, pp.builtin_date, SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::Time:
            result.emplace_back(TokenType::STRING_LITERAL, pp.builtin_time, SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::Stdc:
            result.emplace_back(TokenType::INTEGER_CONST, "1", SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::StdcVersion: {
            auto stdc_version = pp.lang_opts.stdc_version_macro_value();
            if (stdc_version.has_value()) {
                result.emplace_back(TokenType::LONG_CONST, std::to_string(*stdc_version), SrcLoc());
            }
            break;
        }
        case MacroDefinition::BuiltinKind::StdcHosted:
            result.emplace_back(TokenType::INTEGER_CONST, "1", SrcLoc());
            break;
        case MacroDefinition::BuiltinKind::CPlusPlus: {
            auto cplusplus = pp.lang_opts.cplusplus_macro_value();
            if (cplusplus.has_value()) {
                result.emplace_back(TokenType::LONG_CONST, std::to_string(*cplusplus), SrcLoc());
            }
            break;
        }
        case MacroDefinition::BuiltinKind::None:
            break;
    }
    return result;
}

static std::string escape_line_marker_filename(std::string_view file) {
    std::string escaped;
    escaped.reserve(file.size());
    for (char ch : file) {
        if (ch == '\\' || ch == '"') {
            escaped.push_back('\\');
        }
        escaped.push_back(ch);
    }
    return escaped;
}

static const SLocEntry* resolve_file_entry_for_loc(const SourceManager& sm, SrcLoc loc) {
    if (loc.isInvalid()) {
        return nullptr;
    }
    const SLocEntry* entry = &sm.getEntryForLocation(loc);
    while (entry->is_expansion) {
        loc = entry->macro_src.caller;
        if (loc.isInvalid()) {
            return nullptr;
        }
        entry = &sm.getEntryForLocation(loc);
    }
    if (!entry->file_src) {
        return nullptr;
    }
    return entry;
}

static LiteralPrefix merge_literal_prefix(LiteralPrefix lhs, LiteralPrefix rhs) {
    if (lhs == rhs) {
        return lhs;
    }
    if (lhs == LiteralPrefix::None) {
        return rhs;
    }
    if (rhs == LiteralPrefix::None) {
        return lhs;
    }
    return lhs;
}

static bool parse_has_include_operand(const std::vector<Token>& tokens, std::string& header, bool& is_system) {
    if (tokens.empty()) {
        return false;
    }
    const Token& first = tokens[0];
    if (first.type == TokenType::STRING_LITERAL) {
        if (tokens.size() != 1) {
            return false;
        }
        is_system = false;
        header = first.value;
        return true;
    }
    if (first.type == TokenType::LESS_THAN || first.value == "<") {
        if (tokens.size() < 2) {
            return false;
        }
        const Token& last = tokens.back();
        if (!(last.type == TokenType::GREATER_THAN || last.value == ">")) {
            return false;
        }
        is_system = true;
        header.clear();
        for (size_t i = 1; i + 1 < tokens.size(); ++i) {
            if (tokens[i].type == TokenType::STRING_LITERAL) {
                header += "\"" + tokens[i].value + "\"";
            } else {
                header += tokens[i].value;
            }
        }
        return true;
    }
    return false;
}

static std::string basename_from_path(const std::string& path) {
    if (path.empty()) {
        return path;
    }
    std::filesystem::path p(path);
    auto name = p.filename().string();
    if (name.empty()) {
        return path;
    }
    return name;
}

static bool is_builtin_defined_name(const std::string& name) {
    return name == "__has_attribute" ||
           name == "__has_builtin" ||
           name == "__has_cpp_attribute" ||
           name == "__has_extension" ||
           name == "__has_feature" ||
           name == "__has_warning" ||
           name == "__has_include" ||
           name == "__has_include_next";
}

static std::string canonicalize_attribute_name(const std::string& name) {
    std::string canonical = name;
    size_t scope_pos = canonical.rfind("::");
    if (scope_pos != std::string::npos) {
        canonical = canonical.substr(scope_pos + 2);
    }
    if (canonical.size() >= 4 && canonical.starts_with("__") && canonical.ends_with("__")) {
        return canonical.substr(2, canonical.size() - 4);
    }
    return canonical;
}

struct HasQueryOperand {
    std::string query;
    std::vector<std::string> scope_segments;
    std::string leaf_name;
    bool is_string_literal = false;
};

static std::optional<HasQueryOperand> extract_has_query_operand(const std::vector<Token>& tokens) {
    auto skip_whitespace = [&](size_t& index) {
        while (index < tokens.size() && tokens[index].type == TokenType::Whitespace) {
            ++index;
        }
    };

    size_t index = 0;
    skip_whitespace(index);
    if (index >= tokens.size()) {
        return std::nullopt;
    }

    HasQueryOperand operand;
    if (tokens[index].type == TokenType::STRING_LITERAL) {
        operand.query = tokens[index].value;
        operand.leaf_name = tokens[index].value;
        operand.is_string_literal = true;
        ++index;
        skip_whitespace(index);
        if (index != tokens.size()) {
            return std::nullopt;
        }
        return operand;
    }

    std::vector<std::string> segments;
    if (!tokens[index].isIdentifierLike()) {
        return std::nullopt;
    }

    while (true) {
        segments.push_back(tokens[index].value);
        ++index;
        skip_whitespace(index);
        if (index >= tokens.size()) {
            break;
        }

        bool has_scope_resolution = false;
        size_t scope_token_count = 0;
        if (tokens[index].type == TokenType::SCOPE_RESOLUTION) {
            has_scope_resolution = true;
            scope_token_count = 1;
        } else if (index + 1 < tokens.size() &&
                   tokens[index].type == TokenType::COLON &&
                   tokens[index + 1].type == TokenType::COLON) {
            has_scope_resolution = true;
            scope_token_count = 2;
        }

        if (!has_scope_resolution) {
            return std::nullopt;
        }

        index += scope_token_count;
        skip_whitespace(index);
        if (index >= tokens.size() || !tokens[index].isIdentifierLike()) {
            return std::nullopt;
        }
    }

    if (segments.empty()) {
        return std::nullopt;
    }

    operand.leaf_name = segments.back();
    if (segments.size() > 1) {
        operand.scope_segments.assign(segments.begin(), segments.end() - 1);
    }

    for (size_t i = 0; i < segments.size(); ++i) {
        if (i != 0) {
            operand.query += "::";
        }
        operand.query += segments[i];
    }
    return operand;
}

static std::string canonicalize_attribute_namespace(const std::string& ns) {
    if (ns == "__gnu__") {
        return "gnu";
    }
    if (ns == "_Clang" || ns == "__clang__") {
        return "clang";
    }
    return ns;
}

static uint64_t cpp_standard_attribute_value(const std::string& canonical_name) {
    static const std::unordered_map<std::string, uint64_t> values = {
        {"noreturn", 200809ULL},
        {"deprecated", 201309ULL},
        {"fallthrough", 201603ULL},
        {"nodiscard", 201907ULL},
        {"maybe_unused", 201603ULL},
        {"no_unique_address", 201803ULL},
        {"likely", 201803ULL},
        {"unlikely", 201803ULL},
        {"assume", 202207ULL},
    };
    auto it = values.find(canonical_name);
    return it != values.end() ? it->second : 0;
}

static uint64_t has_cpp_attribute_value(const HasQueryOperand& operand) {
    if (operand.is_string_literal) {
        return 0;
    }

    const std::string canonical_name = canonicalize_attribute_name(operand.query);
    if (operand.scope_segments.empty()) {
        return cpp_standard_attribute_value(canonical_name);
    }

    if (operand.scope_segments.size() != 1) {
        return 0;
    }

    const std::string canonical_ns =
        canonicalize_attribute_namespace(operand.scope_segments.front());
    if (canonical_ns == "msvc") {
        return 0;
    }
    if (canonical_ns == "clang") {
        static const std::unordered_set<std::string> supported_clang_attributes = {
            "lifetimebound",
            "noescape",
            "ptrauth_vtable_pointer",
        };
        return supported_clang_attributes.contains(canonical_name) ? 1 : 0;
    }
    if (canonical_ns == "gnu") {
        return AttributeRegistry::instance().find(canonical_name) ? 1 : 0;
    }
    return 0;
}

static bool has_feature_name(const std::string& name,
                             const LangOptions& lang_opts,
                             const TargetInfo* target_info) {
    if (name == "blocks") {
        if (!target_info) {
            return false;
        }
        return darwin_blocks::blocks_enabled_for_langopts(lang_opts, *target_info);
    }
    static const std::unordered_set<std::string> kFeatures = {
        "attribute_deprecated_with_message"
    };
    if (kFeatures.contains(name)) {
        return true;
    }
    if (name == "cxx_concepts") {
        return lang_opts.is_cxx20_or_later();
    }
    return false;
}

inline bool is_hspace(char c) {
    return c == ' ' || c == '\t' || c == '\f' || c == '\v';
}

std::string_view ltrim_hspace(std::string_view text) {
    size_t i = 0;
    while (i < text.size() && is_hspace(text[i])) {
        ++i;
    }
    return text.substr(i);
}

std::string_view trim_hspace(std::string_view text) {
    size_t start = 0;
    size_t end = text.size();
    while (start < end && is_hspace(text[start])) {
        ++start;
    }
    while (end > start && is_hspace(text[end - 1])) {
        --end;
    }
    return text.substr(start, end - start);
}

bool parse_pp_identifier(std::string_view& text, std::string_view& ident) {
    auto is_pp_identifier_start = [](unsigned char ch, char raw) {
        return raw == '_' || raw == '$' || std::isalpha(ch);
    };
    auto is_pp_identifier_continue = [&](unsigned char ch, char raw) {
        return raw == '_' || raw == '$' || std::isalnum(ch);
    };
    text = ltrim_hspace(text);
    if (text.empty()) {
        return false;
    }
    const unsigned char first = static_cast<unsigned char>(text[0]);
    if (!is_pp_identifier_start(first, text[0])) {
        return false;
    }
    size_t i = 1;
    while (i < text.size()) {
        const unsigned char c = static_cast<unsigned char>(text[i]);
        if (!is_pp_identifier_continue(c, text[i])) {
            break;
        }
        ++i;
    }
    ident = text.substr(0, i);
    text.remove_prefix(i);
    return true;
}

bool parse_pragma_once_line(std::string_view line) {
    std::string_view word;
    if (!parse_pp_identifier(line, word)) {
        return false;
    }
    if (word != "once") {
        return false;
    }
    return trim_hspace(line).empty();
}

bool parse_if_not_defined_line_fast(std::string_view line, std::string& macro) {
    line = ltrim_hspace(line);
    if (line.empty() || line.front() != '!') {
        return false;
    }
    line.remove_prefix(1);
    line = ltrim_hspace(line);
    if (!line.starts_with("defined")) {
        return false;
    }
    if (line.size() > 7) {
        const unsigned char boundary = static_cast<unsigned char>(line[7]);
        if (line[7] == '_' || line[7] == '$' || std::isalnum(boundary)) {
            return false;
        }
    }
    line.remove_prefix(7);
    line = ltrim_hspace(line);

    std::string_view ident;
    if (!line.empty() && line.front() == '(') {
        line.remove_prefix(1);
        if (!parse_pp_identifier(line, ident)) {
            return false;
        }
        line = ltrim_hspace(line);
        if (line.empty() || line.front() != ')') {
            return false;
        }
        line.remove_prefix(1);
    } else {
        if (!parse_pp_identifier(line, ident)) {
            return false;
        }
    }

    if (!trim_hspace(line).empty()) {
        return false;
    }

    macro.assign(ident.data(), ident.size());
    return true;
}

bool detect_include_guard_fast(const std::string& text, std::string& guard_macro, bool& saw_pragma_once) {
    saw_pragma_once = false;
    guard_macro.clear();

    // Lightweight line scanner for the canonical header prologue:
    //   #pragma once (optional)
    //   #ifndef X or #if !defined(X)
    //   #define X
    //   ...
    //   #endif
    // with only trivia after the closing #endif. Anything else is not a
    // whole-file include guard and must not be cached as one.
    enum class GuardScanState {
        Prefix,
        ExpectDefine,
        InGuard,
        AfterGuard
    };
    GuardScanState state = GuardScanState::Prefix;
    bool in_block_comment = false;
    size_t pos = 0;
    int depth = 0;

    while (pos <= text.size()) {
        const size_t line_end = text.find('\n', pos);
        const size_t effective_end = (line_end == std::string::npos) ? text.size() : line_end;
        std::string_view line(text.data() + pos, effective_end - pos);
        pos = (line_end == std::string::npos) ? text.size() + 1 : line_end + 1;

        while (true) {
            line = ltrim_hspace(line);
            if (line.empty()) {
                break;
            }

            if (in_block_comment) {
                const size_t comment_end = line.find("*/");
                if (comment_end == std::string::npos) {
                    line = {};
                    break;
                }
                line.remove_prefix(comment_end + 2);
                in_block_comment = false;
                continue;
            }

            if (line.starts_with("//")) {
                line = {};
                break;
            }
            if (line.starts_with("/*")) {
                line.remove_prefix(2);
                in_block_comment = true;
                continue;
            }
            break;
        }

        line = trim_hspace(line);
        if (line.empty()) {
            continue;
        }
        if (line.front() != '#') {
            if (state == GuardScanState::InGuard) {
                continue;
            }
            return false;
        }
        line.remove_prefix(1);
        line = ltrim_hspace(line);

        if (line.empty()) {
            if (state == GuardScanState::ExpectDefine) {
                return false;
            }
            continue;
        }

        std::string_view directive;
        if (!parse_pp_identifier(line, directive)) {
            return false;
        }

        switch (state) {
            case GuardScanState::Prefix:
                if (directive == "pragma") {
                    if (!parse_pragma_once_line(line)) {
                        return false;
                    }
                    saw_pragma_once = true;
                    continue;
                }
                if (directive == "ifndef") {
                    std::string_view ident;
                    if (!parse_pp_identifier(line, ident) || !trim_hspace(line).empty()) {
                        return false;
                    }
                    guard_macro.assign(ident.data(), ident.size());
                    state = GuardScanState::ExpectDefine;
                    continue;
                }
                if (directive == "if") {
                    std::string macro;
                    if (!parse_if_not_defined_line_fast(line, macro)) {
                        return false;
                    }
                    guard_macro = std::move(macro);
                    state = GuardScanState::ExpectDefine;
                    continue;
                }
                return false;

            case GuardScanState::ExpectDefine:
                if (directive != "define") {
                    return false;
                }
                {
                    std::string_view ident;
                    if (!parse_pp_identifier(line, ident)) {
                        return false;
                    }
                    if (ident != guard_macro) {
                        return false;
                    }
                    state = GuardScanState::InGuard;
                    depth = 1;
                }
                continue;

            case GuardScanState::InGuard:
                if (directive == "if" || directive == "ifdef" || directive == "ifndef") {
                    depth++;
                    continue;
                }
                if (directive == "endif") {
                    depth--;
                    if (depth < 0) {
                        return false;
                    }
                    if (depth == 0) {
                        state = GuardScanState::AfterGuard;
                    }
                }
                continue;

            case GuardScanState::AfterGuard:
                return false;
        }
    }

    return state == GuardScanState::AfterGuard;
}

void inital_preproc(std::string& text, std::vector<MappingStep>& map) {
    size_t write_ptr = 0;
    size_t read_ptr = 0;
    const size_t size = text.size();
    char* buffer = text.data();

    map.clear();
    map.reserve(std::max<size_t>(8, size / 64 + 1));
    // Initial identity mapping so getRealSrcLoc can always decrement
    // the upper_bound iterator safely for positions before the first change.
    map.push_back({0, 0});

    auto update_mapping = [&](size_t logical_index, size_t physical_offset) {
        if (map.back().logical_index == logical_index) {
            map.back().physical_offset = static_cast<uint32_t>(physical_offset);
        } else {
            map.push_back({
                static_cast<uint32_t>(logical_index),
                static_cast<uint32_t>(physical_offset)
            });
        }
    };

    auto is_gnu_splice_space = [](char ch) {
        return ch == ' ' || ch == '\t' || ch == '\f' || ch == '\v';
    };

    while (read_ptr < size) {
        const char c = buffer[read_ptr];

        if (c == '\r') {
            if (read_ptr + 1 < size && buffer[read_ptr + 1] == '\n') {
                update_mapping(write_ptr, read_ptr + 1);
                read_ptr += 2;
                buffer[write_ptr++] = '\n';
            } else {
                // Treat lone CR as LF while preserving byte count.
                buffer[write_ptr++] = '\n';
                read_ptr++;
            }
            continue;
        }

        if (c == '\\' && read_ptr + 1 < size) {
            // GNU-style line splicing allows horizontal space between backslash
            // and newline. Consume the full splice and record mapping shift.
            size_t splice_ptr = read_ptr + 1;
            while (splice_ptr < size && is_gnu_splice_space(buffer[splice_ptr])) {
                ++splice_ptr;
            }
            if (splice_ptr < size && buffer[splice_ptr] == '\n') {
                read_ptr = splice_ptr + 1;
                update_mapping(write_ptr, read_ptr);
                continue;
            }
            if (splice_ptr < size && buffer[splice_ptr] == '\r') {
                if (splice_ptr + 1 < size && buffer[splice_ptr + 1] == '\n') {
                    read_ptr = splice_ptr + 2;
                } else {
                    read_ptr = splice_ptr + 1;
                }
                update_mapping(write_ptr, read_ptr);
                continue;
            }
        }

        buffer[write_ptr++] = c;
        ++read_ptr;
    }
    text.resize(write_ptr);
}
size_t TokenSrc::get_idx() {
    if (isUsingMgnt) {
        return token_mgnt->get_token_idx();
    } else {
        return lex->get_char_idx();
    }
}

void TokenSrc::set_idx(size_t idx) {
    if (isUsingMgnt) {
        token_mgnt->set_token_idx(idx);
    } else {
        lex->set_char_idx(idx);
    }
}

Token TokenSrc::nextToken() {
    if (isUsingMgnt) {
        while (true) {
            auto tok = token_mgnt->current_token();
            token_mgnt->advance();
            if (tok.type != TokenType::Whitespace) {
                return tok;
            }
        }
    } else {
        while (true) {
            auto tok_opt = lex->next_token();
            if (!tok_opt.has_value()) {
                return {TokenType::Eof, "", base_loc};
            }
            auto tok = tok_opt.value();
            if (tok.type != TokenType::Whitespace) {
                return tok;
            }
        }
    }
}

bool TokenSrc::isExhausted() {
    if (isUsingMgnt) {
        return token_mgnt->current_token().type == TokenType::Eof;
    } else {
        return lex->is_exhausted();
    }
}

void PreProcess::handleDefineDirective(SrcLoc def_loc) {
    auto nameTok = current_tok_src()->nextToken();
    if (!nameTok.isIdentifierLike()) {
        error("Expected identifier after #define", nameTok.loc);
        return;
    }
    if (nameTok.value == "defined") {
        error("Invalid name for a macro", nameTok.loc);
        return;
    }
    if (nameTok.value == "_Pragma") {
        error("Invalid name for a macro", nameTok.loc);
        return;
    }
    auto macdef = MacroDefinition(nameTok.value, def_loc);
    Token future = current_tok_src()->peekToken();

    if (future.value == "(" && future.flags.has_leading_space == 0) {
        // Function-like macros are recognized only when `(` is adjacent to name.
        macdef.is_function_like = true;
        current_tok_src()->nextToken(); // consume '('

        // Parse parameters
        Token param = current_tok_src()->nextToken();
        if (param.type == TokenType::RIGHT_PAREN) {
            // Empty parameter list
        } else {
            while (true) {
                if (param.type == TokenType::ELLIPSIS) {
                    macdef.is_variadic = true;
                    macdef.parameters.push_back("__VA_ARGS__");
                    Token closing = current_tok_src()->nextToken();
                    if (closing.type != TokenType::RIGHT_PAREN) {
                        error("Expected ')' after variadic macro parameter", closing.loc);
                    }
                    break;
                }
                if (!param.isIdentifierLike()) {
                    error("Expected identifier in macro parameter list", param.loc);
                }
                macdef.parameters.push_back(param.value);
                Token sep = current_tok_src()->nextToken();
                if (sep.type == TokenType::RIGHT_PAREN) {
                    break;
                }
                if (sep.type == TokenType::ELLIPSIS) {
                    // GNU named variadic macro syntax: NAME(args...)
                    macdef.is_variadic = true;
                    Token closing = current_tok_src()->nextToken();
                    if (closing.type != TokenType::RIGHT_PAREN) {
                        error("Expected ')' after variadic macro parameter", closing.loc);
                    }
                    break;
                }
                if (sep.type != TokenType::COMMA) {
                    error("Expected comma in macro parameter list", sep.loc);
                }
                Token next_param = current_tok_src()->nextToken();
                if (next_param.type == TokenType::ELLIPSIS) {
                    macdef.is_variadic = true;
                    macdef.parameters.push_back("__VA_ARGS__");
                    Token closing = current_tok_src()->nextToken();
                    if (closing.type != TokenType::RIGHT_PAREN) {
                        error("Expected ')' after variadic macro parameter", closing.loc);
                    }
                    break;
                }
                param = next_param;
            }
        }
    }
    while (true) {
        Token tok = current_tok_src()->nextToken();
        if (tok.type == TokenType::Newline || tok.type == TokenType::Eof) break;
        tok.flags.part_of_macro_define = 1;
        macdef.replacement_list.push_back(tok);
    }
    if (macdef.replacement_list.size() >= 2) {
        // Validate token-paste placement early so malformed `##` macros do not
        // enter the table and fail later during expansion.
        const Token& first = macdef.replacement_list[0];
        const Token& second = macdef.replacement_list[1];
        if (first.type == TokenType::POUND &&
            second.type == TokenType::POUND &&
            second.flags.has_leading_space == 0) {
            error("## cannot appear at the beginning of a macro replacement list", first.loc);
        }
        const Token& last = macdef.replacement_list[macdef.replacement_list.size() - 1];
        const Token& before_last = macdef.replacement_list[macdef.replacement_list.size() - 2];
        if (before_last.type == TokenType::POUND &&
            last.type == TokenType::POUND &&
            last.flags.has_leading_space == 0) {
            error("## cannot appear at the end of a macro replacement list", before_last.loc);
        }
    }
    macro_table[macdef.name] = std::move(macdef);

}
void PreProcess::handleUndefDirective(SrcLoc def_loc) {
    Token name_tok = current_tok_src()->nextToken();
    if (!name_tok.isIdentifierLike()) {
        error("Expected identifier after #undef", name_tok.loc);
    }
    macro_table.erase(name_tok.value);
    while (true) {
        Token tok = current_tok_src()->nextToken();
        if (tok.type == TokenType::Newline || tok.type == TokenType::Eof) break;
    }
}

void PreProcess::define_object_macro(const std::string& name, const std::string& value, SrcLoc def_loc) {
    if (name.empty()) {
        error("Invalid name for a macro", def_loc);
    }
    if (name == "defined" || name == "_Pragma") {
        error("Invalid name for a macro", def_loc);
    }
    MacroDefinition macdef(name, def_loc);
    if (!value.empty()) {
        Lexer lex(value, def_loc, sm.get(), lang_opts);
        lex.pp_number_mode = true;
        while (true) {
            auto tok_opt = lex.next_token();
            if (!tok_opt.has_value()) {
                break;
            }
            Token tok = tok_opt.value();
            if (tok.type == TokenType::Eof || tok.type == TokenType::Newline) {
                break;
            }
            tok.flags.part_of_macro_define = 1;
            macdef.replacement_list.push_back(tok);
        }
    }
    macro_table[macdef.name] = std::move(macdef);
}

void PreProcess::undef_macro(const std::string& name) {
    if (name.empty()) {
        return;
    }
    macro_table.erase(name);
}

void PreProcess::init_builtin_state() {
    std::time_t now = std::time(nullptr);
    std::tm tm = *std::localtime(&now);
    char date_buf[32];
    char time_buf[16];
    std::strftime(date_buf, sizeof(date_buf), "%b %e %Y", &tm);
    std::strftime(time_buf, sizeof(time_buf), "%H:%M:%S", &tm);
    builtin_date = date_buf;
    builtin_time = time_buf;
}

void PreProcess::init_builtin_macros() {
    auto add_builtin = [&](const std::string& name, MacroDefinition::BuiltinKind kind) {
        MacroDefinition mac(name);
        mac.builtin_kind = kind;
        macro_table[name] = std::move(mac);
    };
    add_builtin("__LINE__", MacroDefinition::BuiltinKind::Line);
    add_builtin("__FILE__", MacroDefinition::BuiltinKind::File);
    add_builtin("__FILE_NAME__", MacroDefinition::BuiltinKind::FileName);
    add_builtin("__COUNTER__", MacroDefinition::BuiltinKind::Counter);
    add_builtin("__DATE__", MacroDefinition::BuiltinKind::Date);
    add_builtin("__TIME__", MacroDefinition::BuiltinKind::Time);
    add_builtin("__STDC__", MacroDefinition::BuiltinKind::Stdc);
    add_builtin("__STDC_HOSTED__", MacroDefinition::BuiltinKind::StdcHosted);
    if (lang_opts.stdc_version_macro_value().has_value()) {
        add_builtin("__STDC_VERSION__", MacroDefinition::BuiltinKind::StdcVersion);
    }
    if (lang_opts.cplusplus_macro_value().has_value()) {
        add_builtin("__cplusplus", MacroDefinition::BuiltinKind::CPlusPlus);
    }
    if (lang_opts.is_cxx20_or_later()) {
        define_object_macro("__cpp_concepts", "202002L");
    }
    if (lang_opts.is_c_mode()) {
        if (lang_opts.uses_gnu_inline_semantics()) {
            define_object_macro("__GNUC_GNU_INLINE__", "1");
        } else if (lang_opts.stdc_version_macro_value().has_value()) {
            define_object_macro("__GNUC_STDC_INLINE__", "1");
        }
    }
    if (target_info &&
        darwin_blocks::blocks_enabled_for_langopts(lang_opts, *target_info)) {
        define_object_macro("__BLOCKS__", "1");
    }

    // Atomic memory order macros
    auto add_simple_int = [&](const std::string& name, int value) {
        MacroDefinition mac(name);
        mac.replacement_list.push_back(Token(TokenType::INTEGER_CONST, std::to_string(value), SrcLoc()));
        macro_table[name] = std::move(mac);
    };

    // Disable _FORTIFY_SOURCE: the hardened __builtin___*_chk functions are
    // not yet implemented, so prevent system headers from rewriting standard
    // library calls (e.g. strcat -> __builtin___strcat_chk).
    add_simple_int("_FORTIFY_SOURCE", 0);
    add_simple_int("__ATOMIC_RELAXED", 0);
    add_simple_int("__ATOMIC_CONSUME", 1);
    add_simple_int("__ATOMIC_ACQUIRE", 2);
    add_simple_int("__ATOMIC_RELEASE", 3);
    add_simple_int("__ATOMIC_ACQ_REL", 4);
    add_simple_int("__ATOMIC_SEQ_CST", 5);

    // GCC atomic type properties
    add_simple_int("__GCC_ATOMIC_BOOL_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_CHAR_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_CHAR16_T_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_CHAR32_T_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_WCHAR_T_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_SHORT_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_INT_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_LONG_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_LLONG_LOCK_FREE", 2);
    add_simple_int("__GCC_ATOMIC_POINTER_LOCK_FREE", 2);
    add_simple_int("__PRAGMA_REDEFINE_EXTNAME", 1);
    add_simple_int("__PRAGMA_WEAK", 1);

    // Clang atomic type properties (used by Clang's stdatomic.h)
    add_simple_int("__CLANG_ATOMIC_BOOL_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_CHAR_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_CHAR8_T_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_CHAR16_T_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_CHAR32_T_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_WCHAR_T_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_SHORT_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_INT_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_LONG_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_LLONG_LOCK_FREE", 2);
    add_simple_int("__CLANG_ATOMIC_POINTER_LOCK_FREE", 2);

    // Integer limit macros
    auto add_simple_str = [&](const std::string& name, const std::string& value, TokenType tt = TokenType::INTEGER_CONST) {
        MacroDefinition mac(name);
        mac.replacement_list.push_back(Token(tt, value, SrcLoc()));
        macro_table[name] = std::move(mac);
    };
    add_simple_str("__SCHAR_MAX__", "127");
    add_simple_str("__SHRT_MAX__", "32767");
    add_simple_str("__INT_MAX__", "2147483647");
    add_simple_str("__LONG_MAX__", "9223372036854775807L");
    add_simple_str("__LONG_LONG_MAX__", "9223372036854775807LL");
    add_simple_str("__CHAR_BIT__", "8");
    add_simple_str("__FLT_RADIX__", "2");
    add_simple_str("__SIZEOF_SHORT__", "2");
    add_simple_str("__SIZEOF_INT__", "4");
    add_simple_str("__SIZEOF_LONG__", "8");
    add_simple_str("__SIZEOF_LONG_LONG__", "8");
    add_simple_str("__SIZEOF_FLOAT__", "4");
    add_simple_str("__SIZEOF_DOUBLE__", "8");
    add_simple_str("__SIZEOF_LONG_DOUBLE__", "8");
    add_simple_str("__SIZEOF_POINTER__", "8");
    add_simple_str("__SIZEOF_WCHAR_T__", "4");
    add_simple_str("__SIZEOF_WINT_T__", "4");
    add_simple_str("__SIZEOF_SIZE_T__", "8");
    add_simple_str("__SIZEOF_PTRDIFF_T__", "8");

    // GCC-compatible __*_TYPE__ macros (LP64)
    // Helper to add a multi-token type macro
    auto add_type_macro = [&](const std::string& name, std::vector<std::pair<TokenType, std::string>> tokens) {
        MacroDefinition mac(name);
        for (auto& [tt, val] : tokens) {
            mac.replacement_list.push_back(Token(tt, val, SrcLoc()));
        }
        macro_table[name] = std::move(mac);
    };
    add_type_macro("__INT8_TYPE__", {{TokenType::SIGNED, "signed"}, {TokenType::CHAR, "char"}});
    add_type_macro("__INT16_TYPE__", {{TokenType::SHORT, "short"}});
    add_type_macro("__INT32_TYPE__", {{TokenType::INT, "int"}});
    add_type_macro("__INT64_TYPE__", {{TokenType::LONG, "long"}, {TokenType::LONG, "long"}});
    add_type_macro("__UINT8_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::CHAR, "char"}});
    add_type_macro("__UINT16_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::SHORT, "short"}});
    add_type_macro("__UINT32_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::INT, "int"}});
    add_type_macro("__UINT64_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::LONG, "long"}, {TokenType::LONG, "long"}});
    add_type_macro("__INTPTR_TYPE__", {{TokenType::LONG, "long"}});
    add_type_macro("__UINTPTR_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::LONG, "long"}});
    add_type_macro("__SIZE_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::LONG, "long"}});
    add_type_macro("__PTRDIFF_TYPE__", {{TokenType::LONG, "long"}});
    add_type_macro("__INTMAX_TYPE__", {{TokenType::LONG, "long"}});
    add_type_macro("__UINTMAX_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::LONG, "long"}});
    add_type_macro("__WCHAR_TYPE__", {{TokenType::INT, "int"}});
    add_type_macro("__WINT_TYPE__", {{TokenType::INT, "int"}});
    add_type_macro("__CHAR16_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::SHORT, "short"}});
    add_type_macro("__CHAR32_TYPE__", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::INT, "int"}});
    add_type_macro("__SIG_ATOMIC_TYPE__", {{TokenType::INT, "int"}});

    // C99 integer constant helper macros. Some system headers only define these
    // via compiler-provided internals that aburi does not predefine yet.
    auto add_unary_cast_fn_macro = [&](const std::string& name,
                                       std::vector<std::pair<TokenType, std::string>> cast_type_tokens) {
        MacroDefinition mac(name);
        mac.is_function_like = true;
        mac.parameters.push_back("v");
        mac.replacement_list.emplace_back(TokenType::LEFT_PAREN, "(", SrcLoc());
        mac.replacement_list.emplace_back(TokenType::LEFT_PAREN, "(", SrcLoc());
        for (const auto& [tt, val] : cast_type_tokens) {
            mac.replacement_list.emplace_back(tt, val, SrcLoc());
        }
        mac.replacement_list.emplace_back(TokenType::RIGHT_PAREN, ")", SrcLoc());
        mac.replacement_list.emplace_back(TokenType::LEFT_PAREN, "(", SrcLoc());
        mac.replacement_list.emplace_back(TokenType::IDENTIFIER, "v", SrcLoc());
        mac.replacement_list.emplace_back(TokenType::RIGHT_PAREN, ")", SrcLoc());
        mac.replacement_list.emplace_back(TokenType::RIGHT_PAREN, ")", SrcLoc());
        macro_table[name] = std::move(mac);
    };

    add_unary_cast_fn_macro("INT8_C", {{TokenType::INT, "int"}});
    add_unary_cast_fn_macro("INT16_C", {{TokenType::INT, "int"}});
    add_unary_cast_fn_macro("INT32_C", {{TokenType::INT, "int"}});
    add_unary_cast_fn_macro("INT64_C", {{TokenType::LONG, "long"}, {TokenType::LONG, "long"}});
    add_unary_cast_fn_macro("UINT8_C", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::INT, "int"}});
    add_unary_cast_fn_macro("UINT16_C", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::INT, "int"}});
    add_unary_cast_fn_macro("UINT32_C", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::INT, "int"}});
    add_unary_cast_fn_macro("UINT64_C", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::LONG, "long"}, {TokenType::LONG, "long"}});
    add_unary_cast_fn_macro("INTMAX_C", {{TokenType::LONG, "long"}});
    add_unary_cast_fn_macro("UINTMAX_C", {{TokenType::UNSIGNED, "unsigned"}, {TokenType::LONG, "long"}});

    // Keep a compatibility `bool` macro for C-family legacy code paths.
    // In C++ mode, `bool` is a core keyword and must not be macro-rewritten.
    if (!lang_opts.is_cxx_mode()) {
        MacroDefinition mac("bool");
        mac.replacement_list.push_back(Token(TokenType::IDENTIFIER, "_Bool", SrcLoc()));
        macro_table["bool"] = std::move(mac);
    }
    // Predefine true/false only for C23-family modes where they are
    // language keywords. Older GNU modes rely on using these names as
    // ordinary identifiers in some torture tests.
    if (is_c23_family_standard(lang_opts.standard)) {
        add_simple_int("true", 1);
        add_simple_int("false", 0);
        add_simple_int("__bool_true_false_are_defined", 1);
    }

    // Register built-in headers
    builtin_headers["stdarg.h"] = R"(
#ifndef _ABURI_STDARG_H
#define _ABURI_STDARG_H
typedef __builtin_va_list va_list;
#define va_start(ap, param) __builtin_va_start(ap, param)
#define va_end(ap) __builtin_va_end(ap)
#define va_arg(ap, type) __builtin_va_arg(ap, type)
#define va_copy(dest, src) __builtin_va_copy(dest, src)
#endif
)";

    builtin_headers["stdbool.h"] = R"(
#ifndef _ABURI_STDBOOL_H
#define _ABURI_STDBOOL_H
#define bool _Bool
#define true 1
#define false 0
#define __bool_true_false_are_defined 1
#endif
)";

    builtin_headers["stdnoreturn.h"] = R"(
#ifndef _ABURI_STDNORETURN_H
#define _ABURI_STDNORETURN_H
#define noreturn _Noreturn
#endif
)";

    builtin_headers["stdalign.h"] = R"(
#ifndef _ABURI_STDALIGN_H
#define _ABURI_STDALIGN_H
#define alignas _Alignas
#define alignof _Alignof
#define __alignas_is_defined 1
#define __alignof_is_defined 1
#endif
)";

    builtin_headers["stddef.h"] = R"(
#ifndef _ABURI_STDDEF_H
#define _ABURI_STDDEF_H
typedef __SIZE_TYPE__ size_t;
typedef __PTRDIFF_TYPE__ ptrdiff_t;
#ifndef __cplusplus
typedef __WCHAR_TYPE__ wchar_t;
#endif
typedef long double max_align_t;
#define NULL ((void*)0)
#define offsetof(type, member) __builtin_offsetof(type, member)
#endif
)";

    builtin_headers["uchar.h"] = R"(
#ifndef _ABURI_UCHAR_H
#define _ABURI_UCHAR_H
#ifndef __cplusplus
typedef __CHAR16_TYPE__ char16_t;
typedef __CHAR32_TYPE__ char32_t;
#endif
#endif
)";

    builtin_headers["stdint.h"] = R"(
#ifndef _ABURI_STDINT_H
#define _ABURI_STDINT_H
/* Also define system include guards so that system headers pulled in
   indirectly (e.g. via <stdlib.h>) do not re-typedef the same types
   with potentially different underlying types. */
#define _STDINT_H_
#define _INT8_T
#define _INT16_T
#define _INT32_T
#define _INT64_T
#define _UINT8_T
#define _UINT16_T
#define _UINT32_T
#define _UINT64_T
#define _INTPTR_T
#define _UINTPTR_T
typedef signed char int8_t;
typedef short int16_t;
typedef int int32_t;
typedef long long int64_t;
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
typedef __INTPTR_TYPE__ intptr_t;
typedef __UINTPTR_TYPE__ uintptr_t;
typedef __INTMAX_TYPE__ intmax_t;
typedef __UINTMAX_TYPE__ uintmax_t;
typedef int8_t int_least8_t;
typedef int16_t int_least16_t;
typedef int32_t int_least32_t;
typedef int64_t int_least64_t;
typedef uint8_t uint_least8_t;
typedef uint16_t uint_least16_t;
typedef uint32_t uint_least32_t;
typedef uint64_t uint_least64_t;
typedef int8_t int_fast8_t;
typedef int16_t int_fast16_t;
typedef int32_t int_fast32_t;
typedef int64_t int_fast64_t;
typedef uint8_t uint_fast8_t;
typedef uint16_t uint_fast16_t;
typedef uint32_t uint_fast32_t;
typedef uint64_t uint_fast64_t;
#define INT8_MIN (-128)
#define INT16_MIN (-32768)
#define INT32_MIN (-2147483647 - 1)
#define INT64_MIN (-9223372036854775807LL - 1)
#define INT8_MAX 127
#define INT16_MAX 32767
#define INT32_MAX 2147483647
#define INT64_MAX 9223372036854775807LL
#define UINT8_MAX 255
#define UINT16_MAX 65535
#define UINT32_MAX 4294967295U
#define UINT64_MAX 18446744073709551615ULL
#define INT_LEAST8_MIN INT8_MIN
#define INT_LEAST16_MIN INT16_MIN
#define INT_LEAST32_MIN INT32_MIN
#define INT_LEAST64_MIN INT64_MIN
#define INT_LEAST8_MAX INT8_MAX
#define INT_LEAST16_MAX INT16_MAX
#define INT_LEAST32_MAX INT32_MAX
#define INT_LEAST64_MAX INT64_MAX
#define UINT_LEAST8_MAX UINT8_MAX
#define UINT_LEAST16_MAX UINT16_MAX
#define UINT_LEAST32_MAX UINT32_MAX
#define UINT_LEAST64_MAX UINT64_MAX
#define INT_FAST8_MIN INT8_MIN
#define INT_FAST16_MIN INT16_MIN
#define INT_FAST32_MIN INT32_MIN
#define INT_FAST64_MIN INT64_MIN
#define INT_FAST8_MAX INT8_MAX
#define INT_FAST16_MAX INT16_MAX
#define INT_FAST32_MAX INT32_MAX
#define INT_FAST64_MAX INT64_MAX
#define UINT_FAST8_MAX UINT8_MAX
#define UINT_FAST16_MAX UINT16_MAX
#define UINT_FAST32_MAX UINT32_MAX
#define UINT_FAST64_MAX UINT64_MAX
#define INTPTR_MIN INT64_MIN
#define INTPTR_MAX INT64_MAX
#define UINTPTR_MAX UINT64_MAX
#define INTMAX_MIN INT64_MIN
#define INTMAX_MAX INT64_MAX
#define UINTMAX_MAX UINT64_MAX
#define SIZE_MAX UINT64_MAX
#define PTRDIFF_MIN INT64_MIN
#define PTRDIFF_MAX INT64_MAX
#endif
)";

    builtin_headers["limits.h"] = R"(
#ifndef _ABURI_LIMITS_H
#define _ABURI_LIMITS_H
#ifndef _LIMITS_H_
#define _LIMITS_H_
#endif
#define CHAR_BIT 8
#define SCHAR_MIN (-128)
#define SCHAR_MAX 127
#define UCHAR_MAX 255
#define CHAR_MIN SCHAR_MIN
#define CHAR_MAX SCHAR_MAX
#define MB_LEN_MAX 4
#define SHRT_MIN (-32768)
#define SHRT_MAX 32767
#define USHRT_MAX 65535
#define INT_MIN (-2147483647 - 1)
#define INT_MAX 2147483647
#define UINT_MAX 4294967295U
#define LONG_MIN (-9223372036854775807L - 1)
#define LONG_MAX 9223372036854775807L
#define ULONG_MAX 18446744073709551615UL
#define SSIZE_MAX LONG_MAX
#define LLONG_MIN (-9223372036854775807LL - 1)
#define LLONG_MAX 9223372036854775807LL
#define ULLONG_MAX 18446744073709551615ULL
/* Common POSIX/Darwin compatibility limits used by real-world projects. */
#define ARG_MAX (1024 * 1024)
#define CHILD_MAX 266
#define LINK_MAX 32767
#define MAX_CANON 1024
#define MAX_INPUT 1024
#define NAME_MAX 255
#define OPEN_MAX 10240
#define PATH_MAX 1024
#define PIPE_BUF 512
#define _XOPEN_IOV_MAX 16
#define IOV_MAX 1024
#define NZERO 20
#endif
)";
}

void PreProcess::init_target_macros(const TargetInfo& target) {
    for (const auto& macro : target.get_builtin_macros()) {
        define_object_macro(macro.first, macro.second);
    }
    for (const auto& macro : target.get_builtin_type_macros()) {
        define_object_macro(macro.first, macro.second);
    }
}

std::vector<Token> PreProcess::expand_builtin_macro(const MacroDefinition& mdef, const Token& trigger) {
    std::vector<Token> result;
    if (!sm) {
        return result;
    }
    auto logical = sm->getLogicalLocation(trigger.loc);
    switch (mdef.builtin_kind) {
        case MacroDefinition::BuiltinKind::Line:
            result.emplace_back(TokenType::INTEGER_CONST, std::to_string(logical.line), trigger.loc);
            break;
        case MacroDefinition::BuiltinKind::File:
            result.emplace_back(TokenType::STRING_LITERAL, logical.file, trigger.loc);
            break;
        case MacroDefinition::BuiltinKind::FileName: {
            std::string base = basename_from_path(logical.file);
            result.emplace_back(TokenType::STRING_LITERAL, base, trigger.loc);
            break;
        }
        case MacroDefinition::BuiltinKind::Counter:
            result.emplace_back(TokenType::INTEGER_CONST, std::to_string(counter++), trigger.loc);
            break;
        case MacroDefinition::BuiltinKind::Date:
            result.emplace_back(TokenType::STRING_LITERAL, builtin_date, trigger.loc);
            break;
        case MacroDefinition::BuiltinKind::Time:
            result.emplace_back(TokenType::STRING_LITERAL, builtin_time, trigger.loc);
            break;
        case MacroDefinition::BuiltinKind::Stdc:
            result.emplace_back(TokenType::INTEGER_CONST, "1", trigger.loc);
            break;
        case MacroDefinition::BuiltinKind::StdcVersion: {
            auto stdc_version = lang_opts.stdc_version_macro_value();
            if (stdc_version.has_value()) {
                result.emplace_back(TokenType::LONG_CONST, std::to_string(*stdc_version), trigger.loc);
            }
            break;
        }
        case MacroDefinition::BuiltinKind::StdcHosted:
            result.emplace_back(TokenType::INTEGER_CONST, "1", trigger.loc);
            break;
        case MacroDefinition::BuiltinKind::CPlusPlus: {
            auto cplusplus = lang_opts.cplusplus_macro_value();
            if (cplusplus.has_value()) {
                result.emplace_back(TokenType::LONG_CONST, std::to_string(*cplusplus), trigger.loc);
            }
            break;
        }
        case MacroDefinition::BuiltinKind::None:
            break;
    }
    return result;
}

// Recognizes the exact pattern: `!defined(NAME)` or `!defined NAME`
// with no extra tokens (used for include-guard detection).
bool PreProcess::parse_if_not_defined(const std::vector<Token>& tokens, std::string& macro) const {
    size_t i = 0;
    if (i >= tokens.size() || tokens[i].type != TokenType::LOGICAL_NOT) {
        return false;
    }
    i++;
    if (i >= tokens.size() || !tokens[i].isIdentifierLike() || tokens[i].value != "defined") {
        return false;
    }
    i++;
    if (i < tokens.size() && tokens[i].type == TokenType::LEFT_PAREN) {
        i++;
        if (i >= tokens.size() || !tokens[i].isIdentifierLike()) {
            return false;
        }
        macro = tokens[i].value;
        i++;
        if (i >= tokens.size() || tokens[i].type != TokenType::RIGHT_PAREN) {
            return false;
        }
        i++;
    } else {
        if (i >= tokens.size() || !tokens[i].isIdentifierLike()) {
            return false;
        }
        macro = tokens[i].value;
        i++;
    }
    return i == tokens.size();
}

void PreProcess::detect_include_guard(const std::shared_ptr<FileSrc>& file) {
    if (!file || file->include_guard_checked) {
        return;
    }
    file->include_guard_checked = true;
    ensure_initial_preprocessed(file);

    std::string fast_guard_macro;
    bool saw_pragma_once = false;
    // Fast text scan handles common guard shapes without spinning up a lexer.
    if (detect_include_guard_fast(file->modified_buffer, fast_guard_macro, saw_pragma_once)) {
        file->pragma_once = file->pragma_once || saw_pragma_once;
        file->include_guard = std::move(fast_guard_macro);
        return;
    }
    if (saw_pragma_once) {
        file->pragma_once = true;
    }

    Lexer lex(file->modified_buffer, file->offset, sm.get(), lang_opts);
    lex.enable_new_line_token = true;

    // Tokenized fallback accepts the same intent but tolerates more trivia
    // patterns than the fast scanner while still requiring that the whole file
    // be wrapped by the guard.
    enum class GuardDetectState {
        Prefix,
        ExpectDefine,
        InGuard,
        AfterGuard
    };
    GuardDetectState state = GuardDetectState::Prefix;
    std::string guard_macro;
    int depth = 0;

    auto consume_rest_of_line = [&]() {
        while (true) {
            auto t_opt = lex.next_token();
            if (!t_opt.has_value()) {
                return Token(TokenType::Eof, "", file->offset);
            }
            Token t = t_opt.value();
            if (t.type == TokenType::Newline || t.type == TokenType::Eof) {
                return t;
            }
        }
    };

    while (true) {
        auto tok_opt = lex.next_token();
        if (!tok_opt.has_value()) break;
        Token tok = tok_opt.value();
        if (tok.type == TokenType::Newline) {
            continue;
        }
        if (tok.type != TokenType::POUND || tok.flags.start_of_line == 0) {
            if (state == GuardDetectState::InGuard) {
                continue;
            }
            if (state == GuardDetectState::AfterGuard) {
                return;
            }
            break;
        }
        auto dir_opt = lex.next_token();
        if (!dir_opt.has_value()) break;
        Token dir = dir_opt.value();
        if (dir.type == TokenType::Newline) {
            if (state == GuardDetectState::ExpectDefine) {
                return;
            }
            continue;
        }
        if (!dir.isIdentifierLike()) {
            if (state == GuardDetectState::InGuard) {
                consume_rest_of_line();
            }
            return;
        }

        switch (state) {
            case GuardDetectState::Prefix:
                if (dir.value == "pragma") {
                    Token t = lex.next_token().value();
                    if (t.isIdentifierLike() && t.value == "once") {
                        file->pragma_once = true;
                    }
                    consume_rest_of_line();
                    continue;
                }
                if (dir.value == "ifndef") {
                    Token name = lex.next_token().value();
                    if (!name.isIdentifierLike()) {
                        return;
                    }
                    guard_macro = name.value;
                    state = GuardDetectState::ExpectDefine;
                    consume_rest_of_line();
                    continue;
                }
                if (dir.value == "if") {
                    std::vector<Token> line;
                    while (true) {
                        Token t = lex.next_token().value();
                        if (t.type == TokenType::Newline || t.type == TokenType::Eof) {
                            break;
                        }
                        line.push_back(t);
                    }
                    std::string macro;
                    if (!parse_if_not_defined(line, macro)) {
                        return;
                    }
                    guard_macro = std::move(macro);
                    state = GuardDetectState::ExpectDefine;
                    continue;
                }
                return;

            case GuardDetectState::ExpectDefine:
                if (dir.value != "define") {
                    return;
                }
                {
                    Token name = lex.next_token().value();
                    if (!name.isIdentifierLike() || name.value != guard_macro) {
                        return;
                    }
                    state = GuardDetectState::InGuard;
                    depth = 1;
                    consume_rest_of_line();
                }
                continue;

            case GuardDetectState::InGuard:
                if (dir.value == "if" || dir.value == "ifdef" || dir.value == "ifndef") {
                    depth++;
                } else if (dir.value == "endif") {
                    depth--;
                    if (depth < 0) {
                        return;
                    }
                    if (depth == 0) {
                        state = GuardDetectState::AfterGuard;
                    }
                }
                consume_rest_of_line();
                continue;

            case GuardDetectState::AfterGuard:
                return;
        }
    }

    if (state == GuardDetectState::AfterGuard) {
        file->include_guard = guard_macro;
    }
}

static std::string format_message_tokens(const std::vector<Token>& toks) {
    std::string msg;
    bool first = true;
    for (const auto& t : toks) {
        if (!first && t.flags.has_leading_space) {
            msg.push_back(' ');
        }
        if (t.type == TokenType::STRING_LITERAL) {
            msg += literal_prefix_spelling(t.literal_prefix);
            msg.push_back('"');
            msg += t.value;
            msg.push_back('"');
        } else if (t.type == TokenType::CHAR_LITERAL) {
            msg += literal_prefix_spelling(t.literal_prefix);
            msg.push_back('\'');
            msg += t.value;
            msg.push_back('\'');
        } else {
            msg += t.value;
        }
        first = false;
    }
    return msg;
}
void PreProcess::handleLineDirective(SrcLoc def_loc) {
    std::vector<Token> tokens;
    auto orig_tokstack_size = tok_stack.size();
    while (true) {
        Token t = nextToken(true, orig_tokstack_size);
        if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
        tokens.push_back(t);
    }
    if (tokens.empty()) {
        error("Expected line number after #line", def_loc);
    }
    Token first = tokens[0];
    // Convert PP_NUMBER to proper integer token for #line
    if (first.type == TokenType::PP_NUMBER) {
        bool decimal_digits_only = !first.value.empty();
        for (char ch : first.value) {
            if (!std::isdigit(static_cast<unsigned char>(ch))) {
                decimal_digits_only = false;
                break;
            }
        }
        if (decimal_digits_only) {
            // #line accepts a decimal digit sequence; treat PP numbers with
            // leading zeros as decimal here even if they are not valid C
            // integer constants in normal expression context (e.g. 032768).
            first.type = TokenType::INTEGER_CONST;
        } else {
            try {
                Lexer relex(first.value, first.loc, nullptr, lang_opts);
                auto tok = relex.next_token();
                if (tok.has_value() && tok->type != TokenType::UNKNOWN && tok->type != TokenType::Eof) {
                    auto next = relex.next_token();
                    if (next.has_value() && next->type == TokenType::Eof) {
                        first.type = tok->type;
                        first.value = tok->value;
                    }
                }
            } catch (...) {}
        }
    }
    if (first.type != TokenType::INTEGER_CONST &&
        first.type != TokenType::UNSIGNED_INTEGER_CONST &&
        first.type != TokenType::LONG_CONST &&
        first.type != TokenType::UNSIGNED_LONG_CONST &&
        first.type != TokenType::LONG_LONG_CONST &&
        first.type != TokenType::UNSIGNED_LONG_LONG_CONST) {
        error("Expected integer constant after #line", first.loc);
    }
    uint32_t line_num = 0;
    try {
        line_num = static_cast<uint32_t>(std::stoll(first.value));
    } catch (...) {
        error("Invalid line number in #line directive", first.loc);
    }
    if (line_num == 0) {
        error("Line number in #line must be positive", first.loc);
    }
    std::string file_name;
    bool has_file_name = false;
    if (tokens.size() >= 2) {
        Token second = tokens[1];
        if (second.type != TokenType::STRING_LITERAL) {
            error("Expected optional file name string literal after #line number", second.loc);
        }
        file_name = second.value;
        has_file_name = true;
    }
    if (tokens.size() > 2) {
        error("Extra tokens after #line directive", tokens[2].loc);
    }

    auto file = sm->getFileWithId(current_file_id);
    if (!file) {
        error("Internal error: couldn't find file for #line", def_loc);
    }
    const auto& entry = sm->getEntryForLocation(def_loc);
    SrcLoc real_loc = sm->getRealSrcLoc(entry, def_loc);
    uint32_t local_offset = real_loc.offset - entry.offset;
    const auto& lines = file->line_offsets;
    auto it = std::upper_bound(lines.begin(), lines.end(), local_offset);
    uint32_t line_idx = std::distance(lines.begin(), it) - 1;
    uint32_t next_line_idx = line_idx + 1;
    sm->addLineDirective(current_file_id, next_line_idx, line_num, file_name, has_file_name);
}
void PreProcess::handleErrorDirective(SrcLoc def_loc) {
    std::vector<Token> tokens;
    auto orig_tokstack_size = tok_stack.size();
    while (true) {
        Token t = nextToken(true, orig_tokstack_size);
        if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
        tokens.push_back(t);
    }
    std::string msg = format_message_tokens(tokens);
    if (msg.empty()) {
        msg = "error";
    }
    error(msg, def_loc);
}
void PreProcess::handleWarningDirective(SrcLoc def_loc) {
    std::vector<Token> tokens;
    auto orig_tokstack_size = tok_stack.size();
    while (true) {
        Token t = nextToken(true, orig_tokstack_size);
        if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
        tokens.push_back(t);
    }
    std::string msg = format_message_tokens(tokens);
    if (msg.empty()) {
        msg = "warning";
    }
    if (sm) {
        std::cerr << sm->formatDiagnostic(DiagnosticLevel::Warning, msg, def_loc);
    } else {
        std::cerr << "warning: " << msg << "\n";
    }
}
void PreProcess::handlePragmaDirective(SrcLoc def_loc) {
    std::vector<Token> tokens;
    while (true) {
        Token t = current_tok_src()->nextToken();
        if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
        tokens.push_back(t);
    }
    handlePragmaTokens(tokens, def_loc);
}
void PreProcess::handlePragmaOperator(SrcLoc op_loc) {
    Token open = current_tok_src()->nextToken();
    if (open.type != TokenType::LEFT_PAREN) {
        error("Expected '(' after _Pragma", op_loc);
    }

    std::vector<Token> raw_arg_tokens;
    int depth = 1;
    while (depth > 0) {
        Token tok = current_tok_src()->nextToken();
        if (tok.type == TokenType::Eof) {
            error("Expected ')' after _Pragma string literal", op_loc);
        }
        if (tok.type == TokenType::LEFT_PAREN) {
            depth++;
            raw_arg_tokens.push_back(tok);
            continue;
        }
        if (tok.type == TokenType::RIGHT_PAREN) {
            depth--;
            if (depth == 0) {
                break;
            }
            raw_arg_tokens.push_back(tok);
            continue;
        }
        raw_arg_tokens.push_back(tok);
    }

    auto expand_tokens = [&](const std::vector<Token>& tokens) -> std::vector<Token> {
        if (tokens.empty()) {
            return {};
        }
        auto src_offset = sm->createMacroEntry(tokens[0].loc, op_loc, tokens.size());
        tok_stack.push_back(std::make_unique<ExpansionTokenSrc>(tokens, src_offset));
        auto orig_stack_size = tok_stack.size();
        std::vector<Token> out;
        while (true) {
            Token t = nextToken(true, orig_stack_size);
            if (t.type == TokenType::Eof) {
                break;
            }
            out.push_back(t);
        }
        return out;
    };

    std::vector<Token> expanded_arg_tokens = expand_tokens(raw_arg_tokens);
    Token arg;
    if (expanded_arg_tokens.size() == 1) {
        arg = expanded_arg_tokens[0];
    } else if (raw_arg_tokens.size() == 1) {
        arg = raw_arg_tokens[0];
    } else {
        arg = Token(TokenType::UNKNOWN, "", op_loc);
    }
    if (arg.type != TokenType::STRING_LITERAL) {
        error("Expected string literal in _Pragma",
              arg.loc.isInvalid() ? op_loc : arg.loc);
    }
    auto tokens = tokenize_pragma_text(arg.value, op_loc);
    handlePragmaTokens(tokens, op_loc);
}

void PreProcess::handlePragmaTokens(const std::vector<Token>& tokens, SrcLoc def_loc) {
    if (tokens.empty()) {
        return;
    }
    const Token& first = tokens[0];
    if (first.type == TokenType::IDENTIFIER && first.value == "once") {
        auto file = sm->getFileWithId(current_file_id);
        if (file) {
            file->pragma_once = true;
            pragma_once_included.insert(file->file_id);
        }
        return;
    }
    if (first.type == TokenType::IDENTIFIER && first.value == "pack") {
        handlePackPragma(tokens, 0, def_loc);
        return;
    }
    auto install_pragma_alias_macro = [&](const std::string& from, const std::string& to) {
        MacroDefinition alias(from);
        Token repl(TokenType::IDENTIFIER, to, def_loc);
        repl.flags.part_of_macro_define = 1;
        alias.replacement_list.push_back(std::move(repl));
        macro_table[from] = std::move(alias);
    };
    if (first.type == TokenType::IDENTIFIER && first.value == "redefine_extname") {
        if (tokens.size() >= 3 && tokens[1].isIdentifierLike() && tokens[2].isIdentifierLike()) {
            install_pragma_alias_macro(tokens[1].value, tokens[2].value);
        }
        return;
    }
    if (first.type == TokenType::IDENTIFIER && first.value == "weak") {
        if (tokens.size() >= 4 &&
            tokens[1].isIdentifierLike() &&
            tokens[2].type == TokenType::ASSIGN &&
            tokens[3].isIdentifierLike()) {
            install_pragma_alias_macro(tokens[1].value, tokens[3].value);
        }
        return;
    }
    if (first.type == TokenType::IDENTIFIER &&
        (first.value == "GCC" || first.value == "clang")) {
        if (tokens.size() >= 2 &&
            tokens[1].type == TokenType::IDENTIFIER &&
            tokens[1].value == "diagnostic") {
            handleDiagnosticPragma(tokens, 2, def_loc);
            return;
        }
        if (tokens.size() >= 2 &&
            tokens[1].type == TokenType::IDENTIFIER &&
            tokens[1].value == "optimize") {
            handleOptimizePragma(tokens, 2, def_loc);
            return;
        }
    }
    if (first.type == TokenType::IDENTIFIER &&
        (first.value == "push_macro" || first.value == "pop_macro")) {
        auto macro_name = parse_pragma_macro_name(tokens);
        if (!macro_name.has_value()) {
            return;
        }
        if (first.value == "push_macro") {
            MacroPushEntry entry;
            auto it = macro_table.find(*macro_name);
            if (it != macro_table.end()) {
                entry.existed = true;
                entry.definition = it->second;
            }
            macro_push_stack[*macro_name].push_back(std::move(entry));
        } else {
            auto it = macro_push_stack.find(*macro_name);
            if (it == macro_push_stack.end() || it->second.empty()) {
                return;
            }
            auto entry = std::move(it->second.back());
            it->second.pop_back();
            if (it->second.empty()) {
                macro_push_stack.erase(it);
            }
            if (entry.existed) {
                macro_table[*macro_name] = std::move(entry.definition);
            } else {
                macro_table.erase(*macro_name);
            }
        }
        return;
    }
}

void PreProcess::handlePackPragma(const std::vector<Token>& tokens, size_t start_idx, SrcLoc def_loc) {
    (void)def_loc;
    size_t max_alignment = 16;
    if (target_info) {
        max_alignment = target_info->max_pack_alignment_bytes();
        if (max_alignment == 0) {
            max_alignment = 16;
        }
    }
    size_t i = start_idx + 1;
    if (i >= tokens.size() || tokens[i].type != TokenType::LEFT_PAREN) {
        return;
    }
    ++i;
    if (i >= tokens.size()) {
        return;
    }
    if (tokens[i].type == TokenType::RIGHT_PAREN) {
        current_pack_alignment = 0;
        return;
    }
    if (tokens[i].type == TokenType::IDENTIFIER && tokens[i].value == "push") {
        size_t new_pack = current_pack_alignment;
        ++i;
        if (i < tokens.size() && tokens[i].type == TokenType::COMMA) {
            ++i;
            if (i >= tokens.size()) {
                return;
            }
            auto parsed = parse_pack_alignment_value(tokens[i], max_alignment);
            if (!parsed.has_value()) {
                return;
            }
            new_pack = parsed.value();
            ++i;
        }
        pack_stack.push_back(current_pack_alignment);
        current_pack_alignment = new_pack;
        return;
    }
    if (tokens[i].type == TokenType::IDENTIFIER && tokens[i].value == "pop") {
        if (!pack_stack.empty()) {
            current_pack_alignment = pack_stack.back();
            pack_stack.pop_back();
        }
        return;
    }
    auto parsed = parse_pack_alignment_value(tokens[i], max_alignment);
    if (!parsed.has_value()) {
        return;
    }
    current_pack_alignment = parsed.value();
}

void PreProcess::handleDiagnosticPragma(const std::vector<Token>& tokens, size_t start_idx, SrcLoc def_loc) {
    (void)def_loc;
    if (start_idx >= tokens.size()) {
        return;
    }
    if (tokens[start_idx].type != TokenType::IDENTIFIER) {
        return;
    }
    const std::string& action = tokens[start_idx].value;
    if (action == "push") {
        diag_state_stack.push_back(current_diag_state_id);
        return;
    }
    if (action == "pop") {
        if (!diag_state_stack.empty()) {
            current_diag_state_id = diag_state_stack.back();
            diag_state_stack.pop_back();
        }
        return;
    }
    DiagnosticSeverity severity;
    if (action == "ignored") {
        severity = DiagnosticSeverity::Ignored;
    } else if (action == "warning") {
        severity = DiagnosticSeverity::Warning;
    } else if (action == "error") {
        severity = DiagnosticSeverity::Error;
    } else {
        return;
    }
    if (start_idx + 1 >= tokens.size()) {
        return;
    }
    if (tokens[start_idx + 1].type != TokenType::STRING_LITERAL) {
        return;
    }
    auto warn_id = warning_id_from_flag(tokens[start_idx + 1].value);
    if (!warn_id.has_value()) {
        return;
    }
    DiagnosticState next_state = sm->getDiagnosticStateById(current_diag_state_id);
    next_state.set(warn_id.value(), severity);
    current_diag_state_id = sm->addDiagnosticState(std::move(next_state));
}

void PreProcess::handleOptimizePragma(const std::vector<Token>& tokens, size_t start_idx, SrcLoc def_loc) {
    (void)tokens;
    (void)start_idx;
    (void)def_loc;
    // Compatibility behavior: accept and ignore optimization pragmas.
    // This covers #pragma GCC/clang optimize(...) and _Pragma("GCC optimize(...)").
}

static const std::string& normalize_dir(const std::string& path) {
    static std::unordered_map<std::string, std::string> cache;
    auto it = cache.find(path);
    if (it != cache.end()) {
        return it->second;
    }
    std::error_code ec;
    auto p = std::filesystem::absolute(std::filesystem::path(path), ec);
    if (ec) {
        p = std::filesystem::path(path);
    }
    auto [ins, _] = cache.emplace(path, p.lexically_normal().string());
    return ins->second;
}

static bool path_is_prefix(const std::string& base, const std::string& full) {
    if (base.empty()) {
        return false;
    }
    std::string b = normalize_dir(base);
    std::string f = normalize_dir(full);
    if (f.size() < b.size()) {
        return false;
    }
    if (f.compare(0, b.size(), b) != 0) {
        return false;
    }
    if (f.size() == b.size()) {
        return true;
    }
    char sep = std::filesystem::path::preferred_separator;
    return f[b.size()] == sep || f[b.size()] == '/';
}

static size_t find_best_matching_include_index(const std::vector<std::string>& paths,
                                               const std::string& curr_dir) {
    size_t best_idx = paths.size();
    size_t best_len = 0;
    for (size_t i = 0; i < paths.size(); ++i) {
        const auto& path = paths[i];
        if (!path_is_prefix(path, curr_dir)) {
            continue;
        }
        size_t len = normalize_dir(path).size();
        if (len > best_len) {
            best_len = len;
            best_idx = i;
        }
    }
    return best_idx;
}

static std::shared_ptr<FileSrc> resolve_include_file(SourceManager* sm,
                                                     const std::shared_ptr<FileSrc>& curr_file,
                                                     const std::string& file_name,
                                                     bool is_system,
                                                     bool is_next) {
    if (!sm) {
        return nullptr;
    }

    std::shared_ptr<FileSrc> new_file;
    const std::string curr_dir = curr_file ? curr_file->directory : "";

    if (!is_system && !is_next && curr_file) {
        new_file = sm->getFileFromLoc(file_name, curr_file->directory);
    }

    if (!new_file && !is_system) {
        if (is_next) {
            const size_t quote_idx = find_best_matching_include_index(sm->quote_look_paths, curr_dir);
            if (quote_idx != sm->quote_look_paths.size()) {
                new_file = sm->lookThroughQuotePathsFrom(file_name, quote_idx + 1);
            }
        } else {
            new_file = sm->lookThroughQuotePaths(file_name);
        }
    }

    if (new_file) {
        return new_file;
    }

    if (is_next) {
        size_t source_start_idx = 0;
        const size_t source_idx = find_best_matching_include_index(sm->source_look_paths, curr_dir);
        if (source_idx != sm->source_look_paths.size()) {
            source_start_idx = source_idx + 1;
        }
        return sm->lookThroughPathsFrom(file_name, source_start_idx);
    }

    return sm->lookThroughPaths(file_name);
}

void PreProcess::handleIncludeDirective(SrcLoc def_loc, bool is_next, bool is_import) {
    bool isSystem = false;
    std::string file_name;
    std::vector<Token> tokens;
    Token raw_first = current_tok_src()->peekToken();
    bool should_expand = !(raw_first.type == TokenType::LESS_THAN || raw_first.type == TokenType::STRING_LITERAL);
    if (should_expand) {
        auto orig_tokstack_size = tok_stack.size();
        while (true) {
            Token t = nextToken(true, orig_tokstack_size);
            if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
            tokens.push_back(t);
        }
    } else {
        while (true) {
            Token t = current_tok_src()->nextToken();
            if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
            tokens.push_back(t);
        }
    }
    if (tokens.empty()) {
        error("Invalid argument for include directive, expected \" or < but got end of line", def_loc);
    }
    if (tokens[0].type == TokenType::STRING_LITERAL) {
        // GCC/Clang accept trailing tokens after #include with a warning.
        // Keep preprocessing moving by ignoring those trailing tokens.
        isSystem = false;
        file_name = tokens[0].value;
    } else if (tokens[0].value == "<" || tokens[0].type == TokenType::LESS_THAN) {
        if (tokens.size() < 2) {
            error("Invalid system include directive", tokens[0].loc);
        }
        size_t close_idx = tokens.size();
        for (size_t i = 1; i < tokens.size(); ++i) {
            if (tokens[i].value == ">" || tokens[i].type == TokenType::GREATER_THAN) {
                close_idx = i;
                break;
            }
        }
        if (close_idx == tokens.size()) {
            error("Invalid system include directive, missing '>'", tokens.back().loc);
        }
        isSystem = true;
        for (size_t i = 1; i < close_idx; ++i) {
            if (tokens[i].type == TokenType::STRING_LITERAL) {
                file_name += "\"" + tokens[i].value + "\"";
            } else {
                file_name += tokens[i].value;
            }
        }
    } else {
        error("Invalid argument for include directive, expected \" or < but got " + tokens[0].value, tokens[0].loc);
    }
    const bool use_builtin_header_first = isSystem && !lang_opts.is_cxx_mode();
    if (use_builtin_header_first) {
        auto it = builtin_headers.find(file_name);
        if (it != builtin_headers.end()) {
            auto builtin_sloc = sm->createFileEntry(file_name, std::string(it->second));
            tok_stack.push_back(
                std::make_unique<FileTokenSrc>(builtin_sloc, builtin_sloc->offset, sm.get(), lang_opts));
            current_file_id = builtin_sloc->file_id;
            return;
        }
    }
    std::shared_ptr<FileSrc> new_file;
    auto curr_file = sm->getFileWithId(current_file_id);
    if (!isSystem && !is_next && !curr_file) {
        error("Internal error: couldn't find file_id in handleIncludeDirective", def_loc);
    }
    new_file = resolve_include_file(sm.get(), curr_file, file_name, isSystem, is_next);
    // dup code but its fine because dependence on custom headers should be temporary
    if (!new_file && isSystem && lang_opts.is_cxx_mode()) {
        auto it = builtin_headers.find(file_name);
        if (it != builtin_headers.end()) {
            auto builtin_sloc = sm->createFileEntry(file_name, std::string(it->second));
            tok_stack.push_back(
                std::make_unique<FileTokenSrc>(builtin_sloc, builtin_sloc->offset, sm.get(), lang_opts));
            current_file_id = builtin_sloc->file_id;
            return;
        }
    }
    if (!new_file) {
        error(sm->formatIncludeLookupFailure(file_name), def_loc);
    }
    detect_include_guard(new_file);
    if (import_once_included.contains(new_file->file_id)) {
        return;
    }
    if (is_import && included_files.contains(new_file->file_id)) {
        return;
    }
    if (new_file->pragma_once && pragma_once_included.contains(new_file->file_id)) {
        return;
    }
    if (!new_file->include_guard.empty() && macro_table.contains(new_file->include_guard)) {
        return;
    }
    if (is_import) {
        import_once_included.insert(new_file->file_id);
    }
    if (new_file->pragma_once) {
        pragma_once_included.insert(new_file->file_id);
    }
    tok_stack.push_back(std::make_unique<FileTokenSrc>(new_file, new_file->offset, sm.get(), lang_opts));
    current_file_id = new_file->file_id;
    included_files.insert(new_file->file_id);

}
void PreProcess::expand_object_macro(const Token& trigger, const MacroDefinition& mdef) {
    HideSetType newHideSet = nullptr;
    if (trigger.hide_set) {
        newHideSet = std::make_shared<std::unordered_set<std::string>>(*trigger.hide_set);
    } else {
        newHideSet = std::make_shared<std::unordered_set<std::string>>();
    }
    newHideSet->insert(mdef.name);
    std::vector<Token> expandedTokens;
    if (mdef.builtin_kind != MacroDefinition::BuiltinKind::None) {
        expandedTokens = expand_builtin_macro(mdef, trigger);
    } else {
        expandedTokens = mdef.replacement_list;
    }
    auto token_size = expandedTokens.size();
    SrcLoc def_loc = mdef.def_loc;
    if (def_loc.isInvalid()) {
        def_loc = trigger.loc;
    }
    auto src_offset = this->sm->createMacroEntry(def_loc, trigger.loc, token_size);
    for (auto& t : expandedTokens) {
        t.hide_set = union_hide_sets(t.hide_set, newHideSet);
        t.loc = src_offset;
        src_offset.increment();
    }
    // preserve leading/newline marker
    if (!expandedTokens.empty()) {
        expandedTokens[0].flags.has_leading_space = trigger.flags.has_leading_space;
        expandedTokens[0].flags.start_of_line = trigger.flags.start_of_line;
    }
    tok_stack.push_back(std::make_unique<ExpansionTokenSrc>(std::move(expandedTokens), src_offset));
}
std::vector<Token> PreProcess::subst(const MacroDefinition& mdef, const Token& trigger, const ArgsType &args) {
    size_t idx = 0;
    std::vector<Token> expandedTokens;
    const std::vector<Token> &body = mdef.replacement_list;
    auto src_offset = this->sm->createMacroEntry(mdef.def_loc, trigger.loc, body.size());

    auto stringify_tokens = [&](const std::vector<Token>& toks) -> std::string {
        std::string out;
        bool first = true;
        bool pending_whitespace = false;
        for (const auto& t : toks) {
            if (t.type == TokenType::Whitespace || t.type == TokenType::Newline) {
                pending_whitespace = true;
                continue;
            }
            if (!first && (pending_whitespace || t.flags.has_leading_space || t.flags.start_of_line)) {
                out.push_back(' ');
            }
            std::string spelling;
            if (t.type == TokenType::STRING_LITERAL) {
                spelling = literal_prefix_spelling(t.literal_prefix) + "\"" + t.value + "\"";
            } else if (t.type == TokenType::CHAR_LITERAL) {
                spelling = literal_prefix_spelling(t.literal_prefix) + "'" + t.value + "'";
            } else {
                spelling = t.value;
            }
            out += spelling;
            first = false;
            pending_whitespace = false;
        }
        // Token::value for string literals is already a cooked payload; adding
        // another escape pass here injects literal backslash bytes into runtime
        // strings for #stringized arguments (e.g. "\"abc\"" instead of "\"abc\"").
        return out;
    };

    auto expand_arg_tokens = [&](const std::vector<Token>& tokens) -> std::vector<Token> {
        if (tokens.empty()) {
            return {};
        }
        auto src_offset2 = this->sm->createMacroEntry(tokens[0].loc, trigger.loc, tokens.size());
        tok_stack.push_back(std::make_unique<ExpansionTokenSrc>(tokens, src_offset2));
        auto orig_stack_size = tok_stack.size();
        std::vector<Token> out;
        while (true) {
            Token t = nextToken(true, orig_stack_size);
            if (t.type == TokenType::Eof) break;
            out.push_back(t);
        }
        return out;
    };

    auto token_spelling = [](const Token& t) -> std::string {
        switch (t.type) {
            case TokenType::LONG_CONST:              return t.value + "L";
            case TokenType::LONG_LONG_CONST:         return t.value + "LL";
            case TokenType::UNSIGNED_INTEGER_CONST:   return t.value + "U";
            case TokenType::UNSIGNED_LONG_CONST:      return t.value + "UL";
            case TokenType::UNSIGNED_LONG_LONG_CONST: return t.value + "ULL";
            case TokenType::FLOAT_CONST:             return t.value + "F";
            default:                                  return t.value;
        }
    };

    auto paste_tokens = [&](const Token& lhs, const Token& rhs) -> Token {
        std::string text = token_spelling(lhs) + token_spelling(rhs);
        Lexer paste_lex(text, lhs.loc, sm.get(), lang_opts);
        paste_lex.pp_number_mode = true;
        auto first = paste_lex.next_token();
        if (!first.has_value() || first->type == TokenType::UNKNOWN || first->type == TokenType::Eof) {
            error("Invalid token pasting result: " + text, lhs.loc);
        }
        auto second = paste_lex.next_token();
        if (!second.has_value() || second->type != TokenType::Eof) {
            error("Token pasting produced multiple tokens: " + text, lhs.loc);
        }
        Token pasted = first.value();
        pasted.flags.has_leading_space = lhs.flags.has_leading_space;
        pasted.flags.start_of_line = lhs.flags.start_of_line;
        pasted.hide_set = intersect_hide_sets(lhs.hide_set, rhs.hide_set);
        return pasted;
    };

    size_t fixed_param_count = mdef.parameters.size();
    if (mdef.is_variadic && fixed_param_count > 0) {
        fixed_param_count -= 1;
    }
    int variadic_idx = mdef.variadic_param_index();
    std::vector<Token> va_args_tokens;
    if (mdef.is_variadic && args.size() > fixed_param_count) {
        for (size_t i = fixed_param_count; i < args.size(); ++i) {
            if (i > fixed_param_count) {
                SrcLoc comma_loc = trigger.loc;
                if (!args[i].empty()) {
                    comma_loc = args[i][0].loc;
                }
                Token comma(TokenType::COMMA, ",", comma_loc);
                va_args_tokens.push_back(comma);
            }
            for (const auto& t : args[i]) {
                va_args_tokens.push_back(t);
            }
        }
    }

    auto get_unexpanded_param_tokens = [&](int param_idx) -> std::vector<Token> {
        if (param_idx == variadic_idx) {
            return va_args_tokens;
        }
        if (param_idx < 0 || static_cast<size_t>(param_idx) >= args.size()) {
            return {};
        }
        return args[param_idx];
    };
    std::unordered_map<int, std::vector<Token>> expanded_param_cache;
    auto get_expanded_param_tokens = [&](int param_idx) -> const std::vector<Token>& {
        auto [it, inserted] = expanded_param_cache.emplace(param_idx, std::vector<Token>{});
        if (inserted) {
            it->second = expand_arg_tokens(get_unexpanded_param_tokens(param_idx));
        }
        return it->second;
    };

    auto append_token = [&](const Token& t) {
        Token copy = t;
        copy.loc = src_offset;
        src_offset.increment();
        expandedTokens.push_back(std::move(copy));
    };
    auto append_tokens = [&](const std::vector<Token>& toks) {
        for (const auto& t : toks) {
            append_token(t);
        }
    };

    auto is_paste_op = [&](size_t pos) -> bool {
        return pos + 1 < body.size() &&
            body[pos].type == TokenType::POUND &&
            body[pos + 1].type == TokenType::POUND &&
            body[pos + 1].flags.has_leading_space == 0;
    };

    auto is_param_token = [&](const Token& t, int& param_idx) -> bool {
        if (!t.isIdentifierLike()) {
            return false;
        }
        param_idx = mdef.get_param_idx(t.value);
        return param_idx != -1;
    };

    auto trim_paste_tokens = [&](std::vector<Token> tokens) -> std::vector<Token> {
        auto is_ws = [](const Token& t) {
            return t.type == TokenType::Whitespace || t.type == TokenType::Newline;
        };
        size_t first = 0;
        while (first < tokens.size() && is_ws(tokens[first])) {
            ++first;
        }
        size_t last = tokens.size();
        while (last > first && is_ws(tokens[last - 1])) {
            --last;
        }
        if (first == 0 && last == tokens.size()) {
            return tokens;
        }
        return std::vector<Token>(tokens.begin() + first, tokens.begin() + last);
    };

    auto glue_with = [&](const std::vector<Token>& rhs_tokens) {
        if (rhs_tokens.empty()) {
            return;
        }
        if (expandedTokens.empty()) {
            append_tokens(rhs_tokens);
            return;
        }
        Token lhs = expandedTokens.back();
        expandedTokens.pop_back();
        if (src_offset.offset > 0) {
            src_offset.offset -= 1;
        }
        Token pasted = paste_tokens(lhs, rhs_tokens[0]);
        append_token(pasted);
        for (size_t i = 1; i < rhs_tokens.size(); ++i) {
            append_token(rhs_tokens[i]);
        }
    };

    while (idx < body.size()) {
        Token tok = body[idx];

        // Stringification (# param)
        if (tok.type == TokenType::POUND && !is_paste_op(idx)) {
            if (idx + 1 < body.size()) {
                int param_idx = -1;
                if (is_param_token(body[idx + 1], param_idx)) {
                    std::vector<Token> raw_tokens = get_unexpanded_param_tokens(param_idx);
                    std::string str = stringify_tokens(raw_tokens);
                    Token str_tok(TokenType::STRING_LITERAL, str, tok.loc);
                    str_tok.flags = tok.flags;
                    append_token(str_tok);
                    idx += 2;
                    continue;
                }
            }
        }

        // Token pasting (## T)
        if (is_paste_op(idx)) {
            if (idx + 2 >= body.size()) {
                error("## at end of macro replacement list", body[idx].loc);
            }
            Token rhs_tok = body[idx + 2];
            int rhs_param_idx = -1;
            if (is_param_token(rhs_tok, rhs_param_idx)) {
                auto sel = trim_paste_tokens(get_unexpanded_param_tokens(rhs_param_idx));
                // GNU ##__VA_ARGS__ extension: when ## precedes __VA_ARGS__
                // and the preceding token is a comma:
                //   - empty __VA_ARGS__: remove the comma
                //   - non-empty __VA_ARGS__: keep the comma, substitute normally (no paste)
                if (rhs_param_idx == variadic_idx &&
                    !expandedTokens.empty() &&
                    expandedTokens.back().type == TokenType::COMMA) {
                    if (sel.empty()) {
                        // Remove the preceding comma
                        expandedTokens.pop_back();
                        if (src_offset.offset > 0) src_offset.offset -= 1;
                    } else {
                        // Don't paste, just append the variadic args
                        append_tokens(sel);
                    }
                    idx += 3;
                    continue;
                }
                if (sel.empty()) {
                    idx += 3;
                    continue;
                }
                glue_with(sel);
                idx += 3;
                continue;
            }
            glue_with(std::vector<Token>{rhs_tok});
            idx += 3;
            continue;
        }

        int param_idx = -1;
        if (is_param_token(tok, param_idx)) {
            // Parameter followed by ##
            if (idx + 2 < body.size() && is_paste_op(idx + 1)) {
                auto sel = trim_paste_tokens(get_unexpanded_param_tokens(param_idx));
                if (sel.empty()) {
                    if (idx + 3 < body.size()) {
                        int rhs_param_idx = -1;
                        if (is_param_token(body[idx + 3], rhs_param_idx)) {
                            append_tokens(trim_paste_tokens(get_unexpanded_param_tokens(rhs_param_idx)));
                            idx += 4;
                            continue;
                        }
                        idx += 4;
                        continue;
                    }
                    idx += 3;
                    continue;
                }
                append_tokens(sel);
                idx += 1;
                continue;
            }
            append_tokens(get_expanded_param_tokens(param_idx));
            idx += 1;
            continue;
        }

        append_token(tok);
        idx += 1;
    }
    return expandedTokens;

}
void PreProcess::expand_function_macro(const Token& trigger, const MacroDefinition& m) {
    // Steps we need to do
    // 1. Read the arguments of the caller and capture the right paren token. Be sure to handle nesteing
    // 2. Calculate the intersection of the hideset of the original caller token and the right paren token
    ArgsType args;
    std::vector<Token> current_arg;
    int paren_depth = 0;

    // Consume the opening parenthesis
    Token open_paren = current_tok_src()->nextToken(); // Should be '('
    if (open_paren.type != TokenType::LEFT_PAREN) {
        error("Expected '(' after function-like macro name", trigger.loc);
    }

    Token closing_paren;

    while (true) {
        Token t = current_tok_src()->nextToken();
        if (t.type == TokenType::Eof) {
            error("Unexpected EOF in macro argument list", trigger.loc);
        }

        if (t.type == TokenType::LEFT_PAREN) {
            paren_depth++;
            current_arg.push_back(t);
        } else if (t.type == TokenType::RIGHT_PAREN) {
            if (paren_depth == 0) {
                // End of arguments
                args.push_back(current_arg);
                closing_paren = t;
                break;
            } else {
                paren_depth--;
                current_arg.push_back(t);
            }
        } else if (t.type == TokenType::COMMA && paren_depth == 0) {
            args.push_back(current_arg);
            current_arg.clear();
        } else {
            current_arg.push_back(t);
        }
    }

    // Handle empty argument case (e.g. MACRO())
    if (args.size() == 1 && args[0].empty() && m.parameters.empty()) {
        args.clear();
    }
    if (args.size() == 1 && args[0].empty() && m.is_variadic && m.parameters.size() == 1) {
        args.clear();
    }

    if (m.is_variadic) {
        size_t fixed_count = m.parameters.size();
        if (fixed_count > 0) {
            fixed_count -= 1;
        }
        if (args.size() < fixed_count) {
            error("Macro argument count mismatch", trigger.loc);
        }
    } else {
        if (args.size() != m.parameters.size()) {
            error("Macro argument count mismatch", trigger.loc);
        }
    }

    // Calculate intersection of hidesets
    HideSetType newHideSet = std::make_shared<std::unordered_set<std::string>>();

    // Intersection of trigger.hide_set and closing_paren.hide_set
    if (trigger.hide_set && closing_paren.hide_set) {
        for (const auto& s : *trigger.hide_set) {
            if (closing_paren.hide_set->contains(s)) {
                newHideSet->insert(s);
            }
        }
    }


    // Add the macro name itself to the hideset
    newHideSet->insert(m.name);
    std::vector<Token> expandedTokens = subst(m, trigger, args);
    auto src_offset = this->sm->createMacroEntry(m.def_loc, trigger.loc, expandedTokens.size());
    for (auto& t : expandedTokens) {
        t.hide_set = union_hide_sets(t.hide_set, newHideSet);
    }
    if (!expandedTokens.empty()) {
        expandedTokens[0].flags.has_leading_space = trigger.flags.has_leading_space;
        expandedTokens[0].flags.start_of_line = trigger.flags.start_of_line;
    }
    tok_stack.push_back(std::make_unique<ExpansionTokenSrc>(std::move(expandedTokens), src_offset));

}
void PreProcess::peel_off_exhausted() {
    tok_stack.pop_back();
    if (tok_stack.empty()) return;
    if (auto *s = dyn_cast<FileTokenSrc>(tok_stack.back().get())) {
        current_file_id = s->file_src->file_id;
    }
}
bool PreProcess::skip_to_next_directive(Lexer* lex) {
    const std::string_view src = lex->source;
    size_t pos = lex->position;
    const size_t len = src.size();

    // Track whether we're at the start of a line.  If the lexer was just
    // positioned (e.g. after reading the previous directive's newline) we
    // treat the current position as start-of-line.
    bool at_line_start = true;  // conservative: first iteration is line start

    // If the character just before the current position is not a newline (and
    // we're not at position 0), we're in the middle of a line.
    if (pos > 0 && src[pos - 1] != '\n') {
        at_line_start = false;
    }

    while (pos < len) {
        char c = src[pos];

        // --- newline: next char starts a new line ---
        if (c == '\n') {
            pos++;
            at_line_start = true;
            continue;
        }

        // --- whitespace at start of line: skip, stay at line start ---
        if (at_line_start && (c == ' ' || c == '\t')) {
            pos++;
            continue;
        }

        // --- '#' at start of line: found a directive ---
        if (at_line_start && c == '#') {
            lex->position = pos;
            lex->pending_start_of_line = true;
            lex->pending_leading_space.reset();
            return true;
        }

        // From here, we're not at line start for subsequent characters
        at_line_start = false;

        // --- line comment: skip to end of line ---
        if (c == '/' && pos + 1 < len && src[pos + 1] == '/') {
            pos += 2;
            while (pos < len && src[pos] != '\n') {
                pos++;
            }
            // Don't consume the newline — the top of the loop will handle it
            continue;
        }

        // --- block comment: skip to closing */ ---
        if (c == '/' && pos + 1 < len && src[pos + 1] == '*') {
            pos += 2;
            while (pos + 1 < len) {
                if (src[pos] == '*' && src[pos + 1] == '/') {
                    pos += 2;
                    break;
                }
                // Track newlines inside block comments so we know if the
                // first character after the comment is at line start.
                if (src[pos] == '\n') {
                    at_line_start = true;
                }
                pos++;
            }
            if (pos >= len) {
                // Unterminated block comment — let the real lexer report it
                break;
            }
            continue;
        }

        // --- string literal: skip to closing quote or newline ---
        if (c == '"' || c == '\'') {
            char quote = c;
            pos++;
            while (pos < len && src[pos] != quote && src[pos] != '\n') {
                if (src[pos] == '\\' && pos + 1 < len) {
                    pos++; // skip the escaped character
                }
                pos++;
            }
            if (pos < len && src[pos] == quote) {
                pos++; // skip closing quote
            }
            // If we hit a newline (unterminated string), don't consume it
            continue;
        }

        // --- any other character: skip ---
        pos++;
    }

    // Reached EOF
    lex->position = pos;
    return false;
}

// todo: we probably need a wrapper that ignores "nothings".
// nextToken - "one day at a time"-kinda function, returns nothing after we process a directive
// this will never remove "old" token stack entries. It might add to stack howver
// if peeloff is true, we will  remove any exhausted sources
Token PreProcess::nextToken(bool peeloff, size_t peelofflimit) {
    // while loop that breaks
    while (true) {
        if (tok_stack.empty()) return {TokenType::Eof, "", 0};

        // When skipping preprocessor conditional blocks, tokens inside those
        // blocks don't need to be valid C tokens (e.g. deliberate syntax
        // errors used as compile-time assertions).  Use a fast raw-character
        // scanner to jump directly to the next '#' at start of line, avoiding
        // full lexer work (string allocation, keyword lookup, etc.) for every
        // token in the skipped region.
        Token tok{TokenType::Eof, "", 0};
        if (skipping && !isProcessingConditional) {
            auto* src = current_tok_src();
            if (src->lex) {
                // Fast path: scan raw characters for # at start of line
                if (!skip_to_next_directive(src->lex.get())) {
                    // Hit EOF
                    tok = Token{TokenType::Eof, "", src->lex->get_loc_at_pos()};
                } else {
                    // Positioned at #, read the token normally
                    tok = src->nextToken();
                }
            } else {
                // Expansion source (shouldn't normally happen when skipping)
                tok = src->nextToken();
            }
        } else {
            tok = current_tok_src()->nextToken();
        }
        if (tok.type == TokenType::Eof) {
            if (peeloff) {
                if (tok_stack.size() <= peelofflimit) {
                    return {TokenType::Eof, "", tok.loc};
                }
                peel_off_exhausted();
                continue;
            }
            return {TokenType::Eof, "", tok.loc};
        }
        // either directive is on a new line or the beginning of the file
        // we shouldn't be here for parsing conditional expresions
        if (tok.type == TokenType::POUND && tok.flags.start_of_line == 1 && tok.flags.part_of_macro_define == 0) {
            // If tok.flags.part_of_macro_define is null, we didn't come here as a result of macro exspansion
            // see 6.10.5.4.3 in C23 standard for why we need it to be nullptr

            // preproc directive
            auto next = current_tok_src()->nextToken();
            if (next.type == TokenType::Newline) {
                // null directive
                continue;
            }
            if (next.type == TokenType::IDENTIFIER
                || next.type == TokenType::ELSE || next.type == TokenType::IF) {
                DirectiveKind dk = classify_directive(next.value);
                if (skipping) {
                    // If skipping, we only care about directives that change conditional state
                    switch (dk) {
                        case DirectiveKind::Else:
                            handleElseDirective(tok.loc);
                            continue;
                        case DirectiveKind::Elif:
                            handleElifDirective(tok.loc);
                            continue;
                        case DirectiveKind::Endif:
                            handleEndifDirective(tok.loc);
                            continue;
                        case DirectiveKind::If:
                        case DirectiveKind::Ifdef:
                        case DirectiveKind::Ifndef:
                            // Nested conditional in skipped block
                            // Push a dummy state so we can match the corresponding endif
                            conditional_stack.push_back({true, false});
                            // fall through to consume rest of line
                            [[fallthrough]];
                        default:
                            // Consume until newline (tokens may be invalid in skipped blocks)
                            try {
                                while (true) {
                                    auto t = current_tok_src()->nextToken();
                                    if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
                                }
                            } catch (...) {
                                auto* src = current_tok_src();
                                if (src->lex) {
                                    while (!src->lex->is_exhausted() && src->lex->current_char() != '\n')
                                        src->lex->advance();
                                    if (!src->lex->is_exhausted()) src->lex->advance();
                                }
                            }
                            continue;
                    }
                }

                switch (dk) {
                    case DirectiveKind::Define:
                        handleDefineDirective(tok.loc); continue;
                    case DirectiveKind::Undef:
                        handleUndefDirective(tok.loc); continue;
                    case DirectiveKind::Line:
                        handleLineDirective(tok.loc); continue;
                    case DirectiveKind::Error:
                        handleErrorDirective(tok.loc); continue;
                    case DirectiveKind::Warning:
                        handleWarningDirective(tok.loc); continue;
                    case DirectiveKind::Pragma:
                        handlePragmaDirective(tok.loc); continue;
                    case DirectiveKind::Ident:
                    case DirectiveKind::Sccs: {
                        // #ident / #sccs — ignore rest of line
                        auto orig_tokstack_size = tok_stack.size();
                        while (true) {
                            Token t = nextToken(true, orig_tokstack_size);
                            if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
                        }
                        continue;
                    }
                    case DirectiveKind::Include:
                        handleIncludeDirective(tok.loc); continue;
                    case DirectiveKind::IncludeNext:
                        handleIncludeDirective(tok.loc, true); continue;
                    case DirectiveKind::Import:
                        handleIncludeDirective(tok.loc, false, true); continue;
                    case DirectiveKind::If:
                        handleIfDirective(tok.loc); continue;
                    case DirectiveKind::Ifdef:
                        handleIfDefDirective(tok.loc, false); continue;
                    case DirectiveKind::Ifndef:
                        handleIfDefDirective(tok.loc, true); continue;
                    case DirectiveKind::Else:
                        handleElseDirective(tok.loc); continue;
                    case DirectiveKind::Elif:
                        handleElifDirective(tok.loc); continue;
                    case DirectiveKind::Endif:
                        handleEndifDirective(tok.loc); continue;
                    case DirectiveKind::Unknown:
                        break; // fall through to non-directive handling
                }
            }

        }
        if (skipping && !isProcessingConditional) {
            continue;
        }

        if (isProcessingConditional) {
            if (tok.isIdentifierLike() && tok.value == "defined") {
                defined_state = DefinedOperatorState::SawDefined;
                return tok;
            }
            if (defined_state == DefinedOperatorState::SawDefined) {
                if (tok.type == TokenType::LEFT_PAREN) {
                    defined_state = DefinedOperatorState::SawDefinedOpenParen;
                    return tok;
                }
                if (tok.isIdentifierLike()) {
                    defined_state = DefinedOperatorState::None;
                    return tok;
                }
                defined_state = DefinedOperatorState::None;
            } else if (defined_state == DefinedOperatorState::SawDefinedOpenParen) {
                if (tok.isIdentifierLike()) {
                    defined_state = DefinedOperatorState::None;
                    return tok;
                }
                defined_state = DefinedOperatorState::None;
            }
        }

        if (tok.type == TokenType::IDENTIFIER && tok.value == "_Pragma") {
            handlePragmaOperator(tok.loc);
            continue;
        }
        if (tok.isIdentifierLike()) {
            const std::string& name = tok.value;
            if (tok.hide_set && tok.hide_set->contains(name)) {
                // we've seen this before
                return tok;
            }
            auto it = macro_table.find(name);
            if (it == macro_table.end()) {
                return tok;
            }
            if (it->second.is_function_like) {
                // Check if followed by (
                Token next = current_tok_src()->peekToken();
                // C standard: whitespace (including newlines) between a
                // function-like macro name and '(' does not prevent
                // macro invocation (C11 6.10.3p10)
                if (next.type == TokenType::Newline) {
                    while (current_tok_src()->peekToken().type == TokenType::Newline) {
                        current_tok_src()->nextToken(); // consume newline
                    }
                    next = current_tok_src()->peekToken();
                }
                // If the current expansion source is exhausted, walk down the
                // token stack to find the ( in an ancestor source. This handles
                // counting-macro patterns where expansion produces a function-like
                // macro name and the arguments live in an outer source.
                // Respect peelofflimit so we never peek across an
                // expand_arg_tokens boundary into unrelated sources.
                if (next.type == TokenType::Eof) {
                    size_t lower_bound = peelofflimit == 0 ? 0 : peelofflimit - 1;
                    for (int si = (int)tok_stack.size() - 2; si >= (int)lower_bound; --si) {
                        next = tok_stack[si]->peekToken();
                        if (next.type != TokenType::Eof) break;
                    }
                }
                if (next.type == TokenType::LEFT_PAREN) {
                    // Pop all exhausted expansion sources so that
                    // expand_function_macro reads ( from the right place.
                    size_t pop_limit = std::max((size_t)1, peelofflimit);
                    while (current_tok_src()->peekToken().type == TokenType::Eof
                           && tok_stack.size() > pop_limit) {
                        peel_off_exhausted();
                    }
                    expand_function_macro(tok, it->second);
                    continue;
                } else {
                    // Not a call, treat as normal identifier
                    return tok;
                }
            } else {
                // object-like
                expand_object_macro(tok, it->second);
                continue;
            }
        }
        return tok;
    }

}
std::vector<Token> PreProcess::tokenize() {
    std::vector<Token> tokens;
    // Pre-allocate based on source size: roughly 1 token per 4-5 characters
    auto main_file = sm->getFileWithId(0);
    if (main_file) {
        tokens.reserve(main_file->buffer.size() / 4);
    }
    while (true) {
        auto token = nextToken(true);
        if (token.type == TokenType::Newline) {
            // todo: will we ever reach here?
            continue; // don't push
        }
        // Convert PP_NUMBER to proper numeric token before emitting to parser.
        // If it re-lexes to a single valid number, replace the type/value.
        // Otherwise keep it as PP_NUMBER and let the parser handle it
        // (e.g. version numbers like 10.12.1 in availability attributes).
        if (token.type == TokenType::PP_NUMBER) {
            try {
                Lexer relex(token.value, token.loc, sm.get(), lang_opts);
                auto tok = relex.next_token();
                if (tok.has_value() && tok->type != TokenType::UNKNOWN && tok->type != TokenType::Eof) {
                    auto next = relex.next_token();
                    if (next.has_value() && next->type == TokenType::Eof) {
                        token.type = tok->type;
                        token.value = tok->value;
                    }
                    // else: can't re-lex as single token, keep as PP_NUMBER
                }
                // else: can't re-lex at all, keep as PP_NUMBER
            } catch (const std::runtime_error&) {
                // Keep non-standard pp-numbers like 10_7 intact so the parser
                // can handle platform-specific attribute spellings.
            }
        }
        if (token.type == TokenType::STRING_LITERAL &&
            !tokens.empty() &&
            tokens.back().type == TokenType::STRING_LITERAL) {
            tokens.back().value += token.value;
            tokens.back().hide_set = union_hide_sets(tokens.back().hide_set, token.hide_set);
            tokens.back().literal_prefix = merge_literal_prefix(tokens.back().literal_prefix, token.literal_prefix);
        } else {
            if (token.type != TokenType::Eof && sm) {
                sm->recordPragmaState(token.loc, current_pack_alignment, current_diag_state_id);
            }
            tokens.push_back(token);
        }
        if (token.type == TokenType::Eof) {
            break;
        }
    }
    return tokens;
}

void PreProcess::emit_preprocessed_text(std::ostream& out) {
    bool at_line_start = true;
    bool have_last_token = false;
    int32_t last_file_id = -1;
    uint32_t last_line = 0;
    uint32_t newlines_since_last_token = 0;
    std::vector<int32_t> include_stack;

    auto emit_line_marker = [&](uint32_t line, const std::string& file, int flag) {
        if (!at_line_start) {
            out.put('\n');
        }
        out << "# " << line << " \"" << escape_line_marker_filename(file) << "\"";
        if (flag != 0) {
            out << " " << flag;
        }
        out.put('\n');
        at_line_start = true;
    };

    if (!base_file_name.empty()) {
        emit_line_marker(1, base_file_name, 0);
    }
    if (sm) {
        if (auto main_file = sm->getFileWithId(0)) {
            include_stack.push_back(main_file->file_id);
            have_last_token = true;
            last_file_id = main_file->file_id;
            last_line = 1;
        }
    }

    while (true) {
        Token token = nextToken(true);
        if (token.type == TokenType::Eof) {
            break;
        }
        if (token.type == TokenType::Newline) {
            out.put('\n');
            at_line_start = true;
            if (have_last_token) {
                ++newlines_since_last_token;
            }
            continue;
        }

        int32_t file_id = -1;
        std::string logical_file;
        uint32_t logical_line = 0;
        if (sm && !token.loc.isInvalid()) {
            auto logical = sm->getLogicalLocation(token.loc);
            logical_file = std::move(logical.file);
            logical_line = logical.line;
            if (const auto* entry = resolve_file_entry_for_loc(*sm, token.loc)) {
                file_id = entry->file_src->file_id;
            }
        }

        bool need_marker = false;
        int marker_flag = 0;
        if (!have_last_token) {
            need_marker = !logical_file.empty() && logical_line > 0;
            if (file_id >= 0) {
                include_stack.push_back(file_id);
            }
        } else if (file_id != last_file_id) {
            need_marker = !logical_file.empty() && logical_line > 0;
            if (file_id >= 0) {
                if (include_stack.size() >= 2 &&
                    file_id == include_stack[include_stack.size() - 2]) {
                    marker_flag = 2;
                    include_stack.pop_back();
                } else {
                    marker_flag = 1;
                    if (include_stack.empty() || include_stack.back() != file_id) {
                        include_stack.push_back(file_id);
                    }
                }
            }
        } else if (logical_line != last_line + newlines_since_last_token) {
            need_marker = !logical_file.empty() && logical_line > 0;
        }
        if (need_marker) {
            emit_line_marker(logical_line, logical_file, marker_flag);
            newlines_since_last_token = 0;
        }

        if (!at_line_start && token.flags.start_of_line) {
            out.put('\n');
            at_line_start = true;
        }
        if (!at_line_start && token.flags.has_leading_space) {
            out.put(' ');
        }
        out << token_spelling_for_output(token);
        at_line_start = false;

        have_last_token = true;
        last_file_id = file_id;
        last_line = logical_line;
        newlines_since_last_token = 0;
    }
    if (!at_line_start) {
        out.put('\n');
    }
}

void PreProcess::emit_macro_definitions(std::ostream& out) {
    std::vector<const MacroDefinition*> definitions;
    definitions.reserve(macro_table.size());
    for (const auto& [_, macro] : macro_table) {
        definitions.push_back(&macro);
    }
    std::sort(definitions.begin(), definitions.end(),
              [](const MacroDefinition* lhs, const MacroDefinition* rhs) {
                  return lhs->name < rhs->name;
              });

    for (const auto* macro : definitions) {
        out << "#define " << macro->name;
        if (macro->is_function_like) {
            out << "(";
            for (size_t i = 0; i < macro->parameters.size(); ++i) {
                if (i != 0) {
                    out << ", ";
                }
                out << macro->parameters[i];
            }
            out << ")";
        }
        auto replacement = macro->builtin_kind == MacroDefinition::BuiltinKind::None
            ? macro->replacement_list
            : builtin_macro_tokens_for_dump(*this, *macro);
        if (!replacement.empty()) {
            out << " " << token_sequence_spelling_for_macro_dump(replacement);
        }
        out << "\n";
    }
}

bool PreProcess::evaluateConstantExpression(std::vector<Token> tokens) {
    // 1. Handle __has_* builtins
    std::vector<Token> after_has;
    for (size_t i = 0; i < tokens.size(); ++i) {
        if (tokens[i].type == TokenType::IDENTIFIER) {
            const std::string& name = tokens[i].value;
            bool is_has = (name == "__has_attribute" || name == "__has_builtin" ||
                name == "__has_cpp_attribute" || name == "__has_extension" ||
                name == "__has_feature" || name == "__has_warning" ||
                name == "__has_include" || name == "__has_include_next");
            if (is_has) {
                if (i + 1 >= tokens.size() || tokens[i + 1].type != TokenType::LEFT_PAREN) {
                    after_has.push_back(tokens[i]);
                    continue;
                }
                size_t j = i + 2;
                int depth = 1;
                std::vector<Token> arg_tokens;
                for (; j < tokens.size(); ++j) {
                    if (tokens[j].type == TokenType::LEFT_PAREN) {
                        depth++;
                        arg_tokens.push_back(tokens[j]);
                        continue;
                    }
                    if (tokens[j].type == TokenType::RIGHT_PAREN) {
                        depth--;
                        if (depth == 0) {
                            break;
                        }
                        arg_tokens.push_back(tokens[j]);
                        continue;
                    }
                    arg_tokens.push_back(tokens[j]);
                }
                if (depth != 0) {
                    error("Expected ')' after " + name, tokens[i].loc);
                }
                int result = 0;
                if (name == "__has_include" || name == "__has_include_next") {
                    std::string header;
                    bool is_system = false;
                    if (!parse_has_include_operand(arg_tokens, header, is_system)) {
                        error("Invalid argument to " + name, tokens[i].loc);
                    }
                    auto curr_file = sm->getFileWithId(current_file_id);
                    std::shared_ptr<FileSrc> found = resolve_include_file(
                        sm.get(), curr_file, header, is_system, name == "__has_include_next");
                    result = found ? 1 : 0;
                } else {
                    auto arg_name = extract_has_query_operand(arg_tokens);
                    if (arg_name.has_value()) {
                        const std::string& query = arg_name->query;
                        if (name == "__has_attribute") {
                            const std::string canon = canonicalize_attribute_name(query);
                            result = AttributeRegistry::instance().find(canon) ? 1 : 0;
                        } else if (name == "__has_cpp_attribute") {
                            result = static_cast<int>(has_cpp_attribute_value(*arg_name));
                        } else if (name == "__has_feature") {
                            result = has_feature_name(query, lang_opts, target_info.get()) ? 1 : 0;
                        } else if (name == "__has_extension") {
                            result = has_feature_name(query, lang_opts, target_info.get()) ? 1 : 0;
                        } else if (name == "__has_builtin") {
                            bool builtin_available = BuiltinRegistry::instance().is_builtin(query);
                            if (builtin_available && target_info) {
                                auto gate = TargetFeatureGate::from_target_info(*target_info);
                                builtin_available = gate.is_builtin_available(query);
                            }
                            result = builtin_available ? 1 : 0;
                            // Also check our dedicated builtins not in the registry
                            if (!result) {
                                BuiltinTypeTransformKind builtin_transform_kind;
                                if (lookup_builtin_type_transform_kind(
                                        query,
                                        builtin_transform_kind)) {
                                    result = 1;
                                }
                            }
                            if (!result) {
                                if (query == "__builtin_va_start" || query == "__builtin_va_end" ||
                                    query == "__builtin_va_arg" || query == "__builtin_va_copy" ||
                                    query == "__builtin_va_list" || query == "__builtin_offsetof") {
                                    result = 1;
                                }
                            }
                        } else if (name == "__has_warning") {
                            result = 0;
                        }
                    }
                }
                after_has.emplace_back(TokenType::INTEGER_CONST, std::to_string(result), tokens[i].loc);
                i = j;
                continue;
            }
        }
        after_has.push_back(tokens[i]);
    }
    // 2. Handle 'defined' operator
    std::vector<Token> after_defined;
    for (size_t i = 0; i < after_has.size(); ++i) {
        if (after_has[i].isIdentifierLike() && after_has[i].value == "defined") {
            // Handle defined(X) or defined X
            if (i + 1 >= after_has.size()) {
                error("Missing argument to defined", after_has[i].loc);
            }
            std::string macro_name;
            if (after_has[i+1].type == TokenType::LEFT_PAREN) {
                if (i + 2 >= after_has.size() || !after_has[i+2].isIdentifierLike()) {
                    error("Expected identifier in defined()", after_has[i].loc);
                }
                macro_name = after_has[i+2].value;
                if (i + 3 >= after_has.size() || after_has[i+3].type != TokenType::RIGHT_PAREN) {
                    error("Expected closing parenthesis in defined()", after_has[i].loc);
                }
                i += 3;
            } else if (after_has[i+1].isIdentifierLike()) {
                macro_name = after_has[i+1].value;
                i += 1;
            } else {
                error("Expected identifier after defined", after_has[i+1].loc);
            }

            bool is_defined = macro_table.find(macro_name) != macro_table.end() ||
                              is_builtin_defined_name(macro_name);
            after_defined.push_back(Token(TokenType::INTEGER_CONST, is_defined ? "1" : "0", after_has[i].loc));
        } else {
            after_defined.push_back(after_has[i]);
        }
    }
    // 3. In C++ mode, 'true' and 'false' are treated as 1/0 in #if expressions.
    if (lang_opts.is_cxx_mode()) {
        for (auto& t : after_defined) {
            if (t.type == TokenType::TRUE_KW || t.value == "true") {
                t.type = TokenType::INTEGER_CONST;
                t.value = "1";
                continue;
            }
            if (t.type == TokenType::FALSE_KW || t.value == "false") {
                t.type = TokenType::INTEGER_CONST;
                t.value = "0";
            }
        }
    }
    // 4. Replace remaining identifiers with 0
    for (auto& t : after_defined) {
        if (t.isIdentifierLike()) {
            t.type = TokenType::INTEGER_CONST;
            t.value = "0";
        }
    }
    // 5. Convert PP_NUMBER tokens to proper numeric tokens (error if invalid)
    for (auto& t : after_defined) {
        if (t.type == TokenType::PP_NUMBER) {
            bool converted = false;
            try {
                Lexer relex(t.value, t.loc, nullptr, lang_opts);
                auto tok = relex.next_token();
                if (tok.has_value() && tok->type != TokenType::UNKNOWN && tok->type != TokenType::Eof) {
                    auto next = relex.next_token();
                    if (next.has_value() && next->type == TokenType::Eof) {
                        t.type = tok->type;
                        t.value = tok->value;
                        converted = true;
                    }
                }
            } catch (...) {}
            if (!converted) {
                error("invalid token in preprocessor expression: " + t.value, t.loc);
            }
        }
    }

    auto eval_result = evaluate_pp_constant_expression(after_defined);
    if (!eval_result.ok) {
        SrcLoc fallback_loc = tokens.empty() ? SrcLoc() : tokens[0].loc;
        SrcLoc diag_loc = eval_result.loc.isInvalid() ? fallback_loc : eval_result.loc;
        std::string diag_message = eval_result.message.empty()
            ? "Invalid constant expression in #if/#elif"
            : eval_result.message;
        error(diag_message, diag_loc);
        return false;
    }

    return eval_result.value != 0;
}

void PreProcess::handleIfDirective(SrcLoc loc) {
    std::vector<Token> expr_tokens;
    isProcessingConditional = true;
    defined_state = DefinedOperatorState::None;
    auto orig_tokstack_size = tok_stack.size();
    while (true) {
        Token t = nextToken(true, orig_tokstack_size);
        if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
        expr_tokens.push_back(t);
    }
    isProcessingConditional = false;
    defined_state = DefinedOperatorState::None;
    if (skipping) {
        conditional_stack.push_back({true, false}); // Inherit skipping
        return;
    }

    bool result = evaluateConstantExpression(expr_tokens);
    conditional_stack.push_back({result, result});
    // if constexpr =0, then skip, If non zero, don't skip
    skipping = !result;
}

void PreProcess::handleIfDefDirective(SrcLoc loc, bool is_ifndef) {
    Token t = current_tok_src()->nextToken();
    if (!t.isIdentifierLike()) {
        error("Expected identifier after #ifdef/#ifndef", loc);
    }
    // Consume until newline
    while (true) {
        Token next = current_tok_src()->nextToken();
        if (next.type == TokenType::Newline || next.type == TokenType::Eof) break;
        if (next.type != TokenType::Whitespace) {
            // gcc seems to let this be?
             error("Extra tokens after #ifdef/#ifndef directive", loc);
        }
    }

    if (skipping) {
        conditional_stack.push_back({true, false});
        return;
    }

    bool is_defined = macro_table.find(t.value) != macro_table.end() || is_builtin_defined_name(t.value);
    bool result = is_ifndef ? !is_defined : is_defined;
    conditional_stack.push_back({result, result});
    skipping = !result;
}

void PreProcess::handleElseDirective(SrcLoc loc) {
    // Consume until newline
    while (true) {
        Token next = current_tok_src()->nextToken();
        if (next.type == TokenType::Newline || next.type == TokenType::Eof) break;
    }

    if (conditional_stack.empty()) {
        error("#else without #if", loc);
    }

    ConditionalState& state = conditional_stack.back();
    if (state.was_successful) {
        // If a previous branch was taken, we skip this else block
        // If we already skipping and we get a nested if block, this should help us keep skipping
        state.is_active = false;
        skipping = true;
    } else {
        // If no previous branch was taken, we take this else block
        state.is_active = true;
        state.was_successful = true;
        skipping = false;
    }


}

void PreProcess::handleElifDirective(SrcLoc loc) {
    std::vector<Token> expr_tokens;

    isProcessingConditional = true;
    defined_state = DefinedOperatorState::None;
    auto orig_tokstack_size = tok_stack.size();
    while (true) {
        Token t = nextToken(true, orig_tokstack_size);
        if (t.type == TokenType::Newline || t.type == TokenType::Eof) break;
        expr_tokens.push_back(t);
    }
    isProcessingConditional = false;
    defined_state = DefinedOperatorState::None;

    if (conditional_stack.empty()) {
        error("#elif without #if", loc);
    }

    ConditionalState& state = conditional_stack.back();
    if (state.was_successful) {
        // If a previous branch was taken, we skip this elif block
        state.is_active = false;
        skipping = true;
    } else {
        // Evaluate condition
        bool result = evaluateConstantExpression(expr_tokens);
        if (result) {
            state.is_active = true;
            state.was_successful = true;
            skipping = false;
        } else {
            state.is_active = false;
            skipping = true;
        }
    }
}

void PreProcess::handleEndifDirective(SrcLoc loc) {
    // Consume until newline
    while (true) {
        Token next = current_tok_src()->nextToken();
        if (next.type == TokenType::Newline || next.type == TokenType::Eof) break;
    }

    if (conditional_stack.empty()) {
        error("#endif without #if", loc);
    }

    conditional_stack.pop_back();

    // Restore skipping state based on parent
    if (conditional_stack.empty()) {
        skipping = false;
    } else {
        skipping = !conditional_stack.back().is_active;
    }
}
