#include "scan.h"

#include <optional>
#include <utility>

#include "../../lexer.h"
#include "../../preprocessor.h"

namespace aburi::modules {

namespace {

bool is_line_initial(const Token& token) {
    return token.flags.start_of_line == 1;
}

std::string read_dotted_name(const std::vector<Token>& tokens, size_t& i) {
    std::string name;
    while (i < tokens.size() && tokens[i].isIdentifierLike()) {
        name += tokens[i].value;
        ++i;
        if (i < tokens.size() && tokens[i].type == TokenType::DOT) {
            name += '.';
            ++i;
            continue;
        }
        return name;
    }
    return std::string();
}

} // namespace

ModuleScanResult scan_module_directives(std::string_view source,
                                        const LangOptions& lang_options) {
    ModuleScanResult result;
    if (!lang_options.modules_enabled()) {
        return result;
    }

    std::string spliced(source);
    std::vector<MappingStep> splice_map;
    inital_preproc(spliced, splice_map);

    Lexer lex(spliced, SrcLoc(1), nullptr, lang_options);
    lex.enable_new_line_token = true;
    lex.emit_comment_whitespace = true;
    lex.pp_number_mode = true;

    std::vector<Token> tokens;
    try {
        while (std::optional<Token> token = lex.next_token()) {
            if (token->type == TokenType::Eof) {
                break;
            }
            if (token->type == TokenType::Whitespace) {
                continue;
            }
            tokens.push_back(*token);
        }
    } catch (...) {

    }

    size_t i = 0;
    auto at = [&](size_t index) -> const Token* {
        return index < tokens.size() ? &tokens[index] : nullptr;
    };
    auto skip_line = [&]() {
        while (i < tokens.size() && tokens[i].type != TokenType::Newline) {
            ++i;
        }
    };
    while (i < tokens.size()) {
        const Token& token = tokens[i];
        if (token.type == TokenType::Newline || !is_line_initial(token)) {
            ++i;
            continue;
        }
        if (token.type == TokenType::POUND) {

            skip_line();
            continue;
        }
        bool exported = token.type == TokenType::EXPORT_KEYWORD;
        size_t keyword_index = exported ? i + 1 : i;
        const Token* keyword = at(keyword_index);
        bool is_module = keyword && keyword->type == TokenType::IDENTIFIER &&
                         keyword->value == "module";
        bool is_import = keyword && keyword->type == TokenType::IDENTIFIER &&
                         keyword->value == "import";
        if (!is_module && !is_import) {
            skip_line();
            continue;
        }
        const Token* follower = at(keyword_index + 1);
        if (!follower || follower->type == TokenType::Newline) {
            skip_line();
            continue;
        }
        if (is_module) {

            if (follower->type == TokenType::SEMICOLON) {
                if (result.kind == ScannedUnitKind::NotModule) {
                    result.has_global_module_fragment = true;
                }
                i = keyword_index + 2;
                continue;
            }
            if (follower->type == TokenType::COLON) {
                const Token* fragment = at(keyword_index + 2);
                if (fragment && fragment->type == TokenType::PRIVATE_KW) {
                    result.has_private_module_fragment = true;
                }
                skip_line();
                continue;
            }
            if (!follower->isIdentifierLike()) {
                skip_line();
                continue;
            }
            size_t cursor = keyword_index + 1;
            std::string module_name = read_dotted_name(tokens, cursor);
            if (module_name.empty() ||
                result.kind != ScannedUnitKind::NotModule) {
                skip_line();
                continue;
            }
            std::string partition_name;
            bool has_partition = false;
            if (const Token* colon = at(cursor);
                colon && colon->type == TokenType::COLON) {
                ++cursor;
                has_partition = true;
                partition_name = read_dotted_name(tokens, cursor);
            }
            result.module_name = std::move(module_name);
            result.partition_name = std::move(partition_name);
            if (exported) {
                result.kind = has_partition
                    ? ScannedUnitKind::InterfacePartition
                    : ScannedUnitKind::PrimaryInterface;
            } else {
                result.kind = has_partition
                    ? ScannedUnitKind::ImplementationPartition
                    : ScannedUnitKind::Implementation;
            }
            i = cursor;
            skip_line();
            continue;
        }

        ScannedImport entry;
        entry.exported = exported;
        size_t cursor = keyword_index + 1;
        if (follower->type == TokenType::LESS_THAN) {
            entry.kind = ScannedImport::Kind::HeaderAngle;
            ++cursor;
            while (const Token* part = at(cursor)) {
                if (part->type == TokenType::GREATER_THAN ||
                    part->type == TokenType::Newline) {
                    break;
                }
                entry.name += part->value;
                ++cursor;
            }
        } else if (follower->type == TokenType::STRING_LITERAL &&
                   follower->literal_prefix == LiteralPrefix::None) {
            entry.kind = ScannedImport::Kind::HeaderQuote;
            entry.name = std::string(follower->value);
            ++cursor;
        } else if (follower->type == TokenType::COLON) {
            entry.kind = ScannedImport::Kind::Partition;
            ++cursor;
            entry.name = read_dotted_name(tokens, cursor);
        } else if (follower->isIdentifierLike()) {
            entry.kind = ScannedImport::Kind::Named;
            entry.name = read_dotted_name(tokens, cursor);
        } else {
            skip_line();
            continue;
        }
        if (!entry.name.empty()) {
            result.imports.push_back(std::move(entry));
        }
        i = cursor;
        skip_line();
    }
    return result;
}

} // namespace aburi::modules
