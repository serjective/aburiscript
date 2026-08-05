

#include "parser.h"

#include <string>
#include <utility>
#include <vector>

namespace aburi::syntax {

namespace {
TextPayload text_payload(std::string_view text) {
    TextPayload payload;
    payload.text = std::string(text);
    return payload;
}
} // namespace

ParseResult Parser::parse_module_unit() {
    module_unit_replay_ = true;
    return parse_translation_unit();
}

cir::EntityId Parser::module_pattern_identity(
    cir::EntityId specialization) const {
    const cir::File& file = collect_session_.file();
    if (const cir::TemplateSpecializationFact* fact =
            file.template_specialization(specialization)) {
        if (fact->selected_template_entity.valid()) {
            return fact->selected_template_entity;
        }
        if (fact->template_entity.valid()) {
            return fact->template_entity;
        }
    }
    return specialization;
}

Parser* Parser::module_unit_parser_for(cir::EntityId pattern_entity) {
    if (!pattern_entity.valid() ||
        module_parser_registry_->by_unit_index.empty()) {
        return nullptr;
    }
    const cir::File& file = collect_session_.file();
    if (!file.valid(pattern_entity)) {
        return nullptr;
    }
    cir::ModuleAttachmentId origin = file.entity(pattern_entity).origin_unit;
    if (!origin.valid() ||
        origin == collect_session_.current_module_unit()) {
        return nullptr;
    }
    auto found = module_parser_registry_->by_unit_index.find(origin.index);
    if (found == module_parser_registry_->by_unit_index.end() ||
        found->second.parser == this) {
        return nullptr;
    }
    return found->second.parser;
}

void Parser::parse_module_preamble(std::vector<NodeId>& decls) {
    if (!lang_opts_.modules_enabled() || at_end()) {
        return;
    }
    if (check(TokenType::MODULE_KEYWORD) &&
        peek(1).type == TokenType::SEMICOLON) {
        size_t begin = current_raw_index();
        Token module_token = current();
        consume();
        consume();
        collect_session_.collect_global_module_fragment(module_token.loc);
        decls.push_back(make_node(NodeKind::GlobalModuleFragment, begin,
                                  last_consumed_raw_end()));

        return;
    }
    bool exported_module = check(TokenType::EXPORT_KEYWORD) &&
                           peek(1).type == TokenType::MODULE_KEYWORD;
    bool plain_module = check(TokenType::MODULE_KEYWORD) &&
                        !(peek(1).type == TokenType::COLON &&
                          peek(2).type == TokenType::PRIVATE_KW);
    if (!exported_module && !plain_module) {
        return;
    }
    size_t begin = current_raw_index();
    if (exported_module) {
        consume();
    }
    decls.push_back(
        parse_cxx_module_declaration(begin, exported_module, /*at_start=*/true)
            .syntax);
}

Parser::ParsedDecl Parser::parse_cxx_module_construct() {
    size_t begin = current_raw_index();
    if (check(TokenType::MODULE_KEYWORD)) {
        if (peek(1).type == TokenType::COLON &&
            peek(2).type == TokenType::PRIVATE_KW) {
            Token module_token = current();
            consume();
            consume();
            consume();
            bool has_error = false;
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after private module fragment",
                         current_loc());
                has_error = true;
            }
            collect_session_.collect_private_module_fragment(module_token.loc);
            collect::DeclResult decl;
            decl.has_error = has_error;
            return {make_node(NodeKind::PrivateModuleFragment, begin,
                              last_consumed_raw_end(), {}, {},
                              has_error ? NodeFlagHasError : NodeFlagNone),
                    std::move(decl)};
        }
        if (peek(1).type == TokenType::SEMICOLON) {

            Token module_token = current();
            consume();
            consume();
            diagnose(DiagnosticLevel::Error,
                     "the global module fragment must be the first "
                     "declaration of a module unit",
                     module_token.loc);
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::GlobalModuleFragment, begin,
                              last_consumed_raw_end(), {}, {},
                              NodeFlagHasError),
                    std::move(decl)};
        }
        return parse_cxx_module_declaration(begin, /*exported=*/false,
                                            /*at_start=*/false);
    }
    if (check(TokenType::IMPORT_KEYWORD)) {
        return parse_cxx_import_declaration(begin, /*exported=*/false);
    }
    if (peek(1).type == TokenType::MODULE_KEYWORD) {
        consume();
        return parse_cxx_module_declaration(begin, /*exported=*/true,
                                            /*at_start=*/false);
    }
    if (peek(1).type == TokenType::IMPORT_KEYWORD) {
        consume();
        return parse_cxx_import_declaration(begin, /*exported=*/true);
    }
    return parse_cxx_export_declaration();
}

bool Parser::parse_module_name_into(std::string& out) {
    while (true) {
        if (current().type != TokenType::IDENTIFIER) {
            diagnose(DiagnosticLevel::Error,
                     "expected identifier in module name", current_loc());
            return false;
        }
        if (current().value == "module" || current().value == "import") {
            diagnose(DiagnosticLevel::Error,
                     "'" + std::string(current().value) +
                         "' cannot appear in a module name",
                     current_loc());
            return false;
        }
        out += current().value;
        consume();
        if (check(TokenType::DOT)) {
            out += '.';
            consume();
            continue;
        }
        return true;
    }
}

Parser::ParsedDecl Parser::parse_cxx_module_declaration(size_t begin,
                                                        bool exported,
                                                        bool at_start) {
    Token module_token = current();
    consume();
    bool has_error = false;
    std::string module_name;
    std::string partition_name;
    bool has_partition = false;
    if (!parse_module_name_into(module_name)) {
        has_error = true;
    }
    if (!has_error && check(TokenType::COLON)) {
        consume();
        has_partition = true;
        if (!parse_module_name_into(partition_name)) {
            has_error = true;
        }
    }
    ParsedAttributes attributes;
    if (!has_error) {
        attributes = try_parse_standard_or_gnu_attributes();
    }
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after module declaration", current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }
    if (!has_error) {
        collect_session_.collect_module_declaration(module_name,
                                                    partition_name,
                                                    has_partition,
                                                    exported,
                                                    at_start,
                                                    module_token.loc);
    }
    std::string display = exported ? "export module " : "module ";
    display += module_name;
    if (has_partition) {
        display += ':';
        display += partition_name;
    }
    collect::DeclResult decl;
    decl.has_error = has_error;
    return {make_node(NodeKind::ModuleDecl, begin, last_consumed_raw_end(),
                      std::move(attributes.syntax),
                      text_payload(display),
                      has_error ? NodeFlagHasError : NodeFlagNone),
            std::move(decl)};
}

Parser::ParsedDecl Parser::parse_cxx_import_declaration(size_t begin,
                                                        bool exported) {
    Token import_token = current();
    consume();
    bool has_error = false;
    bool is_partition = false;
    std::string target;
    if (check(TokenType::LESS_THAN) ||
        check(TokenType::STRING_LITERAL)) {

        diagnose(DiagnosticLevel::Error, "header units are not supported yet",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (check(TokenType::COLON)) {
        consume();
        is_partition = true;
        target += ':';
        if (!parse_module_name_into(target)) {
            has_error = true;
        }
    } else if (!parse_module_name_into(target)) {
        has_error = true;
    }
    ParsedAttributes attributes;
    if (!has_error) {
        attributes = try_parse_standard_or_gnu_attributes();
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after import declaration", current_loc());
            skip_until_statement_boundary();
            has_error = true;
        }
    }
    if (!has_error) {
        collect_session_.collect_module_import(target, is_partition, exported,
                                               import_token.loc);
    }
    collect::DeclResult decl;
    decl.has_error = has_error;
    return {make_node(NodeKind::ImportDecl, begin, last_consumed_raw_end(),
                      std::move(attributes.syntax),
                      text_payload((exported ? "export import " : "import ") +
                                   target),
                      has_error ? NodeFlagHasError : NodeFlagNone),
            std::move(decl)};
}

Parser::ParsedDecl Parser::parse_cxx_export_declaration() {
    size_t begin = current_raw_index();
    Token export_token = current();
    consume();
    bool region_ok = collect_session_.begin_export_region(export_token.loc);
    bool has_error = !region_ok;
    std::vector<NodeId> children;
    if (match(TokenType::LEFT_BRACE)) {
        while (!check(TokenType::RIGHT_BRACE) && !at_end()) {
            size_t before = mark();
            ParsedDecl inner = parse_external_declaration();
            children.push_back(inner.syntax);
            if (!made_progress(before)) {
                size_t error_begin = current_raw_index();
                children.push_back(parse_error_node(
                    "parser made no progress", error_begin, error_begin + 1));
                consume();
            }
        }
        if (!match(TokenType::RIGHT_BRACE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '}' after export declaration group",
                     current_loc());
            has_error = true;
        }
    } else if (check(TokenType::SEMICOLON)) {

        diagnose(DiagnosticLevel::Error,
                 "export declaration does not declare anything",
                 current_loc());
        consume();
        has_error = true;
    } else {
        ParsedDecl inner = parse_external_declaration();
        children.push_back(inner.syntax);
    }
    if (region_ok) {
        collect_session_.end_export_region();
    }
    collect::DeclResult decl;
    decl.has_error = has_error;
    return {make_node(NodeKind::ExportDecl, begin, last_consumed_raw_end(),
                      std::move(children), {},
                      has_error ? NodeFlagHasError : NodeFlagNone),
            std::move(decl)};
}

} // namespace aburi::syntax
