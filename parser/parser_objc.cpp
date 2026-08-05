

#include "parser.h"

#include "../abi/objc_runtime.h"

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

} // namespace

std::string Parser::objc_directive_spelling() const {
    return std::string(peek(1).value);
}

bool Parser::take_objc_selector_piece(std::string& piece) {
    const Token& token = current();
    if (token.type == TokenType::ATTRIBUTE_KW) {

        return false;
    }
    std::string_view value = token.value;
    if (value.empty()) {
        return false;
    }
    char head = value.front();
    bool identifier_shaped =
        (head == '_' || (head >= 'a' && head <= 'z') ||
         (head >= 'A' && head <= 'Z'));
    if (!identifier_shaped) {
        return false;
    }
    if (token.type != TokenType::IDENTIFIER &&
        value.find_first_not_of("abcdefghijklmnopqrstuvwxyz"
                                "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                "0123456789_") != std::string_view::npos) {
        return false;
    }
    piece.assign(value);
    consume();
    return true;
}

Parser::ParsedDecl Parser::parse_objc_at_declaration() {
    size_t begin = current_raw_index();
    std::string directive = objc_directive_spelling();
    if (directive == "class") {
        return parse_objc_class_forward(begin);
    }
    if (directive == "interface") {
        return parse_objc_interface(begin);
    }
    if (directive == "implementation") {
        return parse_objc_implementation(begin);
    }
    if (directive == "protocol") {
        return parse_objc_protocol(begin);
    }
    diagnose(DiagnosticLevel::Error,
             "unexpected '@" + directive + "' at file scope",
             current_loc());
    size_t end = skip_balanced_until_semicolon_or_brace();
    return {make_node(NodeKind::UnknownDecl, begin, end, {}, {},
                      NodeFlagHasError),
            {}};
}

std::vector<std::string> Parser::parse_objc_angle_name_list(
    bool* saw_modifiers) {
    std::vector<std::string> names;
    consume();
    while (!at_end() && !check(TokenType::GREATER_THAN)) {
        std::string word;
        if (!take_objc_selector_piece(word)) {
            diagnose(DiagnosticLevel::Error,
                     "expected a name in the angle list", current_loc());
            break;
        }
        if (word == "__covariant" || word == "__contravariant") {
            if (saw_modifiers) {
                *saw_modifiers = true;
            }
            continue;
        }
        names.push_back(std::move(word));
        if (check(TokenType::COLON)) {

            if (saw_modifiers) {
                *saw_modifiers = true;
            }
            consume();
            int depth = 0;
            while (!at_end()) {
                if (check(TokenType::LESS_THAN)) {
                    ++depth;
                } else if (check(TokenType::GREATER_THAN)) {
                    if (depth == 0) {
                        break;
                    }
                    --depth;
                } else if (check(TokenType::RIGHT_SHIFT) && depth >= 1) {
                    depth -= 2;
                    if (depth < 0) {
                        break;
                    }
                } else if (check(TokenType::COMMA) && depth == 0) {
                    break;
                }
                consume();
            }
        }
        if (!match(TokenType::COMMA)) {
            break;
        }
    }
    if (!match(TokenType::GREATER_THAN)) {
        diagnose(DiagnosticLevel::Error, "expected '>' after the angle list",
                 current_loc());
    }
    return names;
}

void Parser::skip_objc_angle_suffix() {

    consume();
    int depth = 1;
    while (!at_end() && depth > 0) {
        if (check(TokenType::LESS_THAN)) {
            ++depth;
        } else if (check(TokenType::GREATER_THAN)) {
            --depth;
        } else if (check(TokenType::RIGHT_SHIFT) && depth >= 2) {
            depth -= 2;
        }
        consume();
    }
}

Parser::ParsedDecl Parser::parse_objc_class_forward(size_t begin) {
    SrcLoc loc = current_loc();
    consume();
    consume();
    do {
        std::string name;
        if (!take_objc_selector_piece(name)) {
            diagnose(DiagnosticLevel::Error,
                     "expected a class name after '@class'",
                     current_loc());
            break;
        }
        (void)collect_session_.declare_objc_class_forward(name, loc);
        if (check(TokenType::LESS_THAN)) {

            skip_objc_angle_suffix();
        }
    } while (match(TokenType::COMMA));
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after '@class'",
                 current_loc());
    }
    return {make_node(NodeKind::ObjCClassForwardDecl, begin,
                      last_consumed_raw_end(), {}),
            {}};
}

std::optional<collect::ObjCMethodInput> Parser::parse_objc_method_signature(
    std::vector<NodeId>& children) {
    collect::ObjCMethodInput method;
    method.loc = current_loc();
    method.is_class_method = check(TokenType::PLUS);
    consume();

    auto parse_paren_type = [&](cir::TypeRef& out, bool& is_instancetype) {
        if (!match(TokenType::LEFT_PAREN)) {
            return;
        }

        while (check(TokenType::IDENTIFIER)) {
            std::string_view word = current().value;
            if (word == "oneway" || word == "in" || word == "out" ||
                word == "inout" || word == "bycopy" || word == "byref" ||
                word == "nullable" || word == "nonnull" ||
                word == "null_unspecified" || word == "null_resettable") {
                consume();
                continue;
            }
            break;
        }
        if (check(TokenType::IDENTIFIER) &&
            current().value == "instancetype") {
            consume();
            is_instancetype = true;
        } else {
            cir::TypeId type{};
            cir::TypeRef type_ref{};
            children.push_back(
                parse_type_name(&type, nullptr, nullptr, &type_ref));
            if (type_ref.type.valid()) {
                out = type_ref;
            } else if (type.valid()) {
                out = collect_session_.type_ref(type);
            }
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after method type", current_loc());
        }
    };

    bool returns_instancetype = false;
    parse_paren_type(method.return_type, returns_instancetype);
    method.returns_instancetype = returns_instancetype;

    auto swallow_trailing_attributes = [&]() {
        while (check(TokenType::ATTRIBUTE_KW)) {
            ParsedAttributes attrs = parse_gnu_attribute_list();
            method.attrs.append(std::move(attrs.attrs));
        }
    };

    std::string selector;
    std::string piece;
    bool have_piece = take_objc_selector_piece(piece);
    if (have_piece && !check(TokenType::COLON)) {

        method.selector = std::move(piece);
        swallow_trailing_attributes();
        return method;
    }

    while (true) {
        if (!check(TokenType::COLON)) {
            break;
        }
        selector += piece;
        selector += ':';
        piece.clear();
        consume();
        collect::ParamInput param;
        param.loc = current_loc();
        bool param_instancetype = false;
        cir::TypeRef param_type{};
        parse_paren_type(param_type, param_instancetype);
        if (!param_type.type.valid()) {

            param_type = collect_session_.type_ref(
                collect_session_.lookup_type_name("id"));
        }
        param.type = param_type;
        std::string param_name;
        if (!take_objc_selector_piece(param_name)) {
            diagnose(DiagnosticLevel::Error,
                     "expected a parameter name in method declaration",
                     current_loc());
            return std::nullopt;
        }
        param.name = std::move(param_name);
        method.params.push_back(std::move(param));
        have_piece = take_objc_selector_piece(piece);
        if (!have_piece) {
            if (match(TokenType::COMMA)) {
                if (match(TokenType::ELLIPSIS)) {
                    method.is_variadic = true;
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "expected '...' after ',' in method declaration",
                             current_loc());
                }
            }
            break;
        }
    }
    if (have_piece && !check(TokenType::COLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ':' after selector fragment '" + piece + "'",
                 current_loc());
    }
    if (selector.empty()) {
        diagnose(DiagnosticLevel::Error, "expected a selector",
                 current_loc());
        return std::nullopt;
    }
    method.selector = std::move(selector);
    swallow_trailing_attributes();
    return method;
}

void Parser::parse_objc_ivar_block(cir::EntityId interface,
                                   std::vector<NodeId>& children) {
    consume();
    std::vector<collect::ObjCIvarInput> ivars;
    cir::ObjCIvarAccess access = cir::ObjCIvarAccess::Protected;
    while (!check(TokenType::RIGHT_BRACE) && !at_end()) {
        if (check(TokenType::AT)) {
            std::string directive = objc_directive_spelling();
            if (directive == "private") {
                access = cir::ObjCIvarAccess::Private;
            } else if (directive == "protected") {
                access = cir::ObjCIvarAccess::Protected;
            } else if (directive == "public") {
                access = cir::ObjCIvarAccess::Public;
            } else if (directive == "package") {
                access = cir::ObjCIvarAccess::Package;
            } else {
                diagnose(DiagnosticLevel::Error,
                         "unexpected '@" + directive +
                             "' in instance-variable block",
                         current_loc());
            }
            consume();
            consume();
            continue;
        }
        if (match(TokenType::SEMICOLON)) {
            continue;
        }
        DeclarationParser ivar_parser(*this, TypeParseContext{});
        cir::TypeRef base_ref =
            ivar_parser.parse_declaration(/*run_second_half=*/false);
        do {
            ivar_parser.reset_declarator_parsing_state();
            ParsedDeclarator declarator =
                ivar_parser.parse_declarator(base_ref,
                                             /*allow_abstract=*/false);
            collect::ObjCIvarInput ivar;
            ivar.name = declarator.name;
            ivar.type = declarator.type_ref.type.valid()
                            ? declarator.type_ref
                            : collect_session_.type_ref(declarator.type);
            ivar.access = access;
            if (check(TokenType::COLON)) {
                consume();
                ParsedExpr width = parse_expression(PrecLevel::CONDITIONAL);
                (void)width;
                ivar.is_bitfield = true;
                diagnose(DiagnosticLevel::Warning,
                         "instance-variable bit-field widths are not "
                         "evaluated yet",
                         declarator.loc);
            }
            ivar.loc = declarator.loc;
            while (check(TokenType::ATTRIBUTE_KW)) {
                ParsedAttributes trailing = parse_gnu_attribute_list();
                ivar.attrs.append(std::move(trailing.attrs));
            }
            ivars.push_back(std::move(ivar));
        } while (match(TokenType::COMMA));
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after instance variable", current_loc());
            skip_balanced_until_semicolon_or_brace();
        }
    }
    if (!match(TokenType::RIGHT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '}' at end of instance-variable block",
                 current_loc());
    }
    collect_session_.collect_objc_ivars(interface, std::move(ivars),
                                        current_loc());
}

Parser::ParsedDecl Parser::parse_objc_interface(size_t begin) {
    SrcLoc loc = current_loc();
    consume();
    consume();
    std::vector<NodeId> children;
    std::string name;
    if (!take_objc_selector_piece(name)) {
        diagnose(DiagnosticLevel::Error,
                 "expected a class name after '@interface'", current_loc());
        size_t end = skip_balanced_until_semicolon_or_brace();
        return {make_node(NodeKind::ObjCInterfaceDecl, begin, end, {}, {},
                          NodeFlagHasError),
                {}};
    }

    std::vector<std::string> header_angle_names;
    bool header_angle_is_generics = false;
    if (check(TokenType::LESS_THAN)) {
        header_angle_names =
            parse_objc_angle_name_list(&header_angle_is_generics);
    }
    std::string category_name;
    bool is_category = false;
    if (match(TokenType::LEFT_PAREN)) {
        is_category = true;
        (void)take_objc_selector_piece(category_name);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after category name", current_loc());
        }
    }
    std::string super_name;
    if (match(TokenType::COLON)) {
        if (!take_objc_selector_piece(super_name)) {
            diagnose(DiagnosticLevel::Error,
                     "expected a superclass name after ':'", current_loc());
        }
    }
    std::vector<std::string> conformance;
    if (check(TokenType::LESS_THAN)) {
        conformance = parse_objc_angle_name_list(nullptr);
    }
    if (!header_angle_names.empty()) {
        bool all_protocols = !header_angle_is_generics;
        for (const std::string& entry : header_angle_names) {
            all_protocols = all_protocols &&
                            collect_session_.is_objc_protocol_name(entry);
        }
        if (all_protocols && !is_category && super_name.empty() &&
            conformance.empty()) {
            conformance = std::move(header_angle_names);
            header_angle_names.clear();
        }
    }

    collect::ObjCInterfaceDeclResult decl;
    if (is_category) {
        decl.entity =
            collect_session_.begin_objc_category(name, category_name, loc);
    } else {
        decl = collect_session_.begin_objc_interface(name, super_name, {},
                                                     loc);
    }
    if (!conformance.empty()) {
        collect_session_.set_objc_container_protocols(decl.entity,
                                                      conformance, loc);
    }
    bool pushed_type_params = !header_angle_names.empty();
    if (pushed_type_params) {
        collect_session_.push_objc_type_parameters(
            std::move(header_angle_names));
    }

    if (check(TokenType::LEFT_BRACE)) {
        parse_objc_ivar_block(decl.entity, children);
    }
    bool current_optional = false;
    while (!at_end()) {
        if (check(TokenType::AT)) {
            std::string directive = objc_directive_spelling();
            if (directive == "end") {
                consume();
                consume();
                break;
            }
            if (directive == "property") {
                consume();
                consume();
                parse_objc_property(decl.entity, children);
                continue;
            }
            if (directive == "required") {
                consume();
                consume();
                current_optional = false;
                continue;
            }
            if (directive == "optional") {
                consume();
                consume();
                current_optional = true;
                continue;
            }
            diagnose(DiagnosticLevel::Error,
                     "unexpected '@" + directive + "' in @interface",
                     current_loc());
            consume();
            consume();
            continue;
        }
        if (check(TokenType::NEGATE) || check(TokenType::PLUS)) {
            std::optional<collect::ObjCMethodInput> method =
                parse_objc_method_signature(children);
            if (method.has_value()) {
                method->is_optional = current_optional;
                (void)collect_session_.declare_objc_method(decl.entity,
                                                           *method);
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after method declaration",
                         current_loc());
                skip_balanced_until_semicolon_or_brace();
            }
            continue;
        }
        if (match(TokenType::SEMICOLON)) {
            continue;
        }

        ParsedDecl inner = parse_external_declaration();
        children.push_back(inner.syntax);
    }
    if (pushed_type_params) {
        collect_session_.pop_objc_type_parameters();
    }
    collect_session_.finish_objc_interface(decl.entity, last_consumed_loc());
    return {make_node(NodeKind::ObjCInterfaceDecl, begin,
                      last_consumed_raw_end(), children, text_payload(name)),
            {}};
}

Parser::ParsedDecl Parser::parse_objc_implementation(size_t begin) {
    SrcLoc loc = current_loc();
    consume();
    consume();
    std::vector<NodeId> children;
    std::string name;
    if (!take_objc_selector_piece(name)) {
        diagnose(DiagnosticLevel::Error,
                 "expected a class name after '@implementation'",
                 current_loc());
        size_t end = skip_balanced_until_semicolon_or_brace();
        return {make_node(NodeKind::ObjCImplementationDecl, begin, end, {}, {},
                          NodeFlagHasError),
                {}};
    }
    cir::EntityId interface =
        collect_session_.begin_objc_implementation(name, loc);
    while (!at_end()) {
        if (check(TokenType::AT)) {
            std::string directive = objc_directive_spelling();
            if (directive == "end") {
                consume();
                consume();
                break;
            }
            if (directive == "synthesize" || directive == "dynamic") {
                bool is_dynamic = directive == "dynamic";
                SrcLoc directive_loc = current_loc();
                consume();
                consume();
                do {
                    std::string property_name;
                    if (!take_objc_selector_piece(property_name)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected a property name", current_loc());
                        break;
                    }
                    std::string backing;
                    if (!is_dynamic && match(TokenType::ASSIGN)) {
                        (void)take_objc_selector_piece(backing);
                    }
                    collect_session_.collect_objc_synthesize(
                        interface, property_name, backing, is_dynamic,
                        directive_loc);
                } while (match(TokenType::COMMA));
                if (!match(TokenType::SEMICOLON)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ';' after @" + directive,
                             current_loc());
                }
                continue;
            }
            if (directive == "property") {

                consume();
                consume();
                parse_objc_property(interface, children);
                continue;
            }
            diagnose(DiagnosticLevel::Error,
                     "unexpected '@" + directive + "' in @implementation",
                     current_loc());
            consume();
            consume();
            continue;
        }
        if (check(TokenType::NEGATE) || check(TokenType::PLUS)) {
            std::optional<collect::ObjCMethodInput> method =
                parse_objc_method_signature(children);
            if (!method.has_value()) {
                skip_balanced_until_semicolon_or_brace();
                continue;
            }
            if (match(TokenType::SEMICOLON)) {

                (void)collect_session_.declare_objc_method(interface, *method);
                continue;
            }
            if (!check(TokenType::LEFT_BRACE)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '{' to begin a method definition",
                         current_loc());
                skip_balanced_until_semicolon_or_brace();
                continue;
            }
            collect::FunctionDeclStart start =
                collect_session_.begin_objc_method_definition(
                    interface, *method, method->loc);
            ParsedStmt body = parse_compound_statement();
            children.push_back(body.syntax);
            body.sem = collect_session_.arc_finish_dealloc_body(
                std::move(body.sem), start, last_consumed_loc());
            collect_session_.finish_function(std::move(body.sem),
                                             last_consumed_loc());
            continue;
        }
        if (match(TokenType::SEMICOLON)) {
            continue;
        }

        ParsedDecl inner = parse_external_declaration();
        children.push_back(inner.syntax);
    }
    collect_session_.finish_objc_implementation(interface,
                                                last_consumed_loc());
    return {make_node(NodeKind::ObjCImplementationDecl, begin,
                      last_consumed_raw_end(), children, text_payload(name)),
            {}};
}

Parser::ParsedExpr Parser::parse_objc_at_expression() {
    size_t begin = current_raw_index();
    SrcLoc loc = current_loc();
    if (peek(1).type == TokenType::STRING_LITERAL) {
        consume();
        std::string bytes;
        std::string spelling = "@\"";

        while (true) {
            if (check(TokenType::STRING_LITERAL)) {
                bytes += std::string(current().value);
                consume();
                continue;
            }
            if (check(TokenType::AT) &&
                peek(1).type == TokenType::STRING_LITERAL) {
                consume();
                continue;
            }
            break;
        }
        spelling += bytes;
        spelling += '"';
        collect::ExprResult sem = collect_session_.collect_objc_string_literal(
            std::move(bytes), std::move(spelling), loc);
        return {make_node(NodeKind::ObjCStringLiteral, begin,
                          last_consumed_raw_end(), {}),
                std::move(sem)};
    }

    TokenType after = peek(1).type;
    if (after == TokenType::INTEGER_CONST ||
        after == TokenType::UNSIGNED_INTEGER_CONST ||
        after == TokenType::LONG_CONST ||
        after == TokenType::UNSIGNED_LONG_CONST ||
        after == TokenType::LONG_LONG_CONST ||
        after == TokenType::UNSIGNED_LONG_LONG_CONST ||
        after == TokenType::FLOAT_CONST ||
        after == TokenType::DOUBLE_CONST ||
        after == TokenType::LONG_DOUBLE_CONST ||
        after == TokenType::CHAR_LITERAL) {
        consume();
        ParsedExpr literal = parse_cast_expression();
        collect::ExprResult sem =
            collect_session_.collect_objc_box_expr(std::move(literal.sem), loc);
        return {make_node(NodeKind::ObjCBoxedExpr, begin,
                          last_consumed_raw_end(), {literal.syntax}),
                std::move(sem)};
    }
    std::string directive = objc_directive_spelling();
    if ((directive == "YES" || directive == "NO") &&
        (peek(1).type == TokenType::IDENTIFIER ||
         peek(1).type == TokenType::TRUE_KW ||
         peek(1).type == TokenType::FALSE_KW)) {
        consume();
        bool value = directive == "YES";
        consume();
        collect::ExprResult boolean = collect_session_.make_boolean_literal(
            value, directive, loc);
        collect::ExprResult sem =
            collect_session_.collect_objc_box_expr(std::move(boolean), loc);
        return {make_node(NodeKind::ObjCBoxedExpr, begin,
                          last_consumed_raw_end(), {}),
                std::move(sem)};
    }
    if (after == TokenType::LEFT_PAREN) {
        consume();
        consume();
        ParsedExpr inner = parse_expression(PrecLevel::ASSIGNMENT);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after '@('",
                     current_loc());
        }
        collect::ExprResult sem =
            collect_session_.collect_objc_box_expr(std::move(inner.sem), loc);
        return {make_node(NodeKind::ObjCBoxedExpr, begin,
                          last_consumed_raw_end(), {inner.syntax}),
                std::move(sem)};
    }
    if (after == TokenType::LEFT_BRACKET) {
        consume();
        consume();
        std::vector<NodeId> children;
        std::vector<collect::ExprResult> elements;
        while (!check(TokenType::RIGHT_BRACKET) && !at_end()) {
            ParsedExpr element = parse_expression(PrecLevel::ASSIGNMENT);
            children.push_back(element.syntax);
            elements.push_back(std::move(element.sem));
            if (!match(TokenType::COMMA)) {
                break;
            }
        }
        if (!match(TokenType::RIGHT_BRACKET)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ']' in array literal", current_loc());
        }
        collect::ExprResult sem = collect_session_.collect_objc_array_literal(
            std::move(elements), loc);
        return {make_node(NodeKind::ObjCArrayLiteral, begin,
                          last_consumed_raw_end(), children),
                std::move(sem)};
    }
    if (after == TokenType::LEFT_BRACE) {
        consume();
        consume();
        std::vector<NodeId> children;
        std::vector<std::pair<collect::ExprResult, collect::ExprResult>> entries;
        while (!check(TokenType::RIGHT_BRACE) && !at_end()) {
            ParsedExpr key = parse_expression(PrecLevel::ASSIGNMENT);
            children.push_back(key.syntax);
            if (!match(TokenType::COLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ':' in dictionary literal", current_loc());
                break;
            }
            ParsedExpr value = parse_expression(PrecLevel::ASSIGNMENT);
            children.push_back(value.syntax);
            entries.emplace_back(std::move(key.sem), std::move(value.sem));
            if (!match(TokenType::COMMA)) {
                break;
            }
        }
        if (!match(TokenType::RIGHT_BRACE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '}' in dictionary literal", current_loc());
        }
        collect::ExprResult sem =
            collect_session_.collect_objc_dictionary_literal(
                std::move(entries), loc);
        return {make_node(NodeKind::ObjCDictionaryLiteral, begin,
                          last_consumed_raw_end(), children),
                std::move(sem)};
    }
    if (directive == "encode") {
        consume();
        consume();
        if (!match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected '(' after '@encode'",
                     current_loc());
        }
        cir::TypeId type{};
        cir::TypeRef type_ref{};
        (void)parse_type_name(&type, nullptr, nullptr, &type_ref);
        if (!type_ref.type.valid() && type.valid()) {
            type_ref = collect_session_.type_ref(type);
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after '@encode'",
                     current_loc());
        }
        std::string encoding = aburi::objc_runtime::encode_type(
            collect_session_.file(), type_ref, {});
        collect::ExprResult sem = collect_session_.make_string_literal(
            encoding, "@encode(...)", loc);
        return {make_node(NodeKind::StringLiteral, begin,
                          last_consumed_raw_end(), {},
                          text_payload(encoding)),
                std::move(sem)};
    }
    if (directive == "protocol" && peek(2).type == TokenType::LEFT_PAREN) {
        consume();
        consume();
        consume();
        std::string name;
        if (!take_objc_selector_piece(name)) {
            diagnose(DiagnosticLevel::Error,
                     "expected a protocol name in '@protocol'",
                     current_loc());
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after protocol name", current_loc());
        }
        collect::ExprResult sem =
            collect_session_.collect_objc_protocol_expr(name, loc);
        return {make_node(NodeKind::ObjCSelectorExpr, begin,
                          last_consumed_raw_end(), {}, text_payload(name)),
                std::move(sem)};
    }
    if (directive == "selector") {
        consume();
        consume();
        if (!match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '(' after '@selector'", current_loc());
        }
        std::string selector;
        std::string piece;
        bool have_piece = take_objc_selector_piece(piece);
        if (have_piece && !check(TokenType::COLON)) {
            selector = std::move(piece);
        } else {
            while (true) {
                if (check(TokenType::COLON)) {
                    selector += piece;
                    selector += ':';
                    piece.clear();
                    consume();
                    if (take_objc_selector_piece(piece)) {
                        continue;
                    }
                    continue;
                }
                if (!piece.empty()) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ':' in selector name", current_loc());
                }
                break;
            }
        }
        if (selector.empty()) {
            diagnose(DiagnosticLevel::Error, "expected a selector name",
                     current_loc());
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after selector name", current_loc());
        }
        collect::ExprResult sem =
            collect_session_.collect_objc_selector_expr(selector, loc);
        return {make_node(NodeKind::ObjCSelectorExpr, begin,
                          last_consumed_raw_end(), {}, text_payload(selector)),
                std::move(sem)};
    }
    diagnose(DiagnosticLevel::Error,
             "unexpected '@" + directive + "' in expression", current_loc());
    consume();
    consume();
    return {make_node(NodeKind::Error, begin, last_consumed_raw_end(), {}, {},
                      NodeFlagHasError),
            {}};
}

Parser::ParsedExpr Parser::parse_objc_message_expression() {
    size_t begin = current_raw_index();
    SrcLoc loc = current_loc();
    consume();

    collect::ObjCMessageSendInput input;
    input.loc = loc;
    std::vector<NodeId> children;

    bool receiver_parsed = false;
    if (check(TokenType::IDENTIFIER)) {
        std::string_view head = current().value;
        if (head == "super") {
            input.is_super = true;
            consume();
            collect::ExprResult self_expr = collect_session_.lookup_name(
                "self", current_loc(), /*allow_unresolved_call_name=*/false);
            input.receiver = std::move(self_expr);
            receiver_parsed = true;
        } else if (collect_session_.is_objc_class_name(head)) {
            input.receiver_class = collect_session_.objc_class_entity(head);
            consume();
            receiver_parsed = true;
        }
    }
    if (!receiver_parsed) {
        ParsedExpr receiver = parse_expression(PrecLevel::ASSIGNMENT);
        children.push_back(receiver.syntax);
        input.receiver = std::move(receiver.sem);
    }

    std::string selector;
    std::string piece;
    bool have_piece = take_objc_selector_piece(piece);
    if (have_piece && !check(TokenType::COLON)) {
        selector = std::move(piece);
        piece.clear();
    } else {
        while (true) {
            if (check(TokenType::COLON)) {
                selector += piece;
                selector += ':';
                piece.clear();
                consume();
                ParsedExpr arg = parse_expression(PrecLevel::ASSIGNMENT);
                children.push_back(arg.syntax);
                input.args.push_back(std::move(arg.sem));
                have_piece = take_objc_selector_piece(piece);
                if (have_piece) {
                    continue;
                }

                while (match(TokenType::COMMA)) {
                    ParsedExpr extra = parse_expression(PrecLevel::ASSIGNMENT);
                    children.push_back(extra.syntax);
                    input.args.push_back(std::move(extra.sem));
                }
                continue;
            }
            if (have_piece) {
                diagnose(DiagnosticLevel::Error,
                         "expected ':' after selector fragment '" + piece +
                             "'",
                         current_loc());
            }
            break;
        }
    }
    if (selector.empty()) {
        diagnose(DiagnosticLevel::Error, "expected a selector in message send",
                 current_loc());
    }
    std::string selector_display = selector;
    input.selector = std::move(selector);
    if (!match(TokenType::RIGHT_BRACKET)) {
        diagnose(DiagnosticLevel::Error, "expected ']' after message send",
                 current_loc());
    }
    collect::ExprResult sem =
        collect_session_.collect_objc_message_send(std::move(input));
    return {make_node(NodeKind::ObjCMessageExpr, begin,
                      last_consumed_raw_end(), children,
                      text_payload(selector_display)),
            std::move(sem)};
}

Parser::ParsedDecl Parser::parse_objc_protocol(size_t begin) {
    SrcLoc loc = current_loc();
    consume();
    consume();
    std::vector<NodeId> children;
    std::string name;
    if (!take_objc_selector_piece(name)) {
        diagnose(DiagnosticLevel::Error,
                 "expected a protocol name after '@protocol'", current_loc());
        size_t end = skip_balanced_until_semicolon_or_brace();
        return {make_node(NodeKind::UnknownDecl, begin, end, {}, {},
                          NodeFlagHasError),
                {}};
    }
    if (check(TokenType::SEMICOLON) || check(TokenType::COMMA)) {
        (void)collect_session_.declare_objc_protocol_forward(name, loc);
        while (match(TokenType::COMMA)) {
            std::string more;
            if (!take_objc_selector_piece(more)) {
                diagnose(DiagnosticLevel::Error,
                         "expected a protocol name", current_loc());
                break;
            }
            (void)collect_session_.declare_objc_protocol_forward(more, loc);
        }
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after '@protocol'", current_loc());
        }
        return {make_node(NodeKind::ObjCClassForwardDecl, begin,
                          last_consumed_raw_end(), {}, text_payload(name)),
                {}};
    }

    std::vector<std::string> inherited;
    if (check(TokenType::LESS_THAN)) {
        inherited = parse_objc_angle_name_list(nullptr);
    }
    collect::ObjCInterfaceDeclResult decl =
        collect_session_.begin_objc_protocol(name, inherited, loc);

    bool current_optional = false;
    while (!at_end()) {
        if (check(TokenType::AT)) {
            std::string directive = objc_directive_spelling();
            if (directive == "end") {
                consume();
                consume();
                break;
            }
            if (directive == "property") {
                consume();
                consume();
                parse_objc_property(decl.entity, children);
                continue;
            }
            if (directive == "required") {
                consume();
                consume();
                current_optional = false;
                continue;
            }
            if (directive == "optional") {
                consume();
                consume();
                current_optional = true;
                continue;
            }
            diagnose(DiagnosticLevel::Error,
                     "unexpected '@" + directive + "' in @protocol",
                     current_loc());
            consume();
            consume();
            continue;
        }
        if (check(TokenType::NEGATE) || check(TokenType::PLUS)) {
            std::optional<collect::ObjCMethodInput> method =
                parse_objc_method_signature(children);
            if (method.has_value()) {
                method->is_optional = current_optional;
                (void)collect_session_.declare_objc_method(decl.entity,
                                                           *method);
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after method declaration",
                         current_loc());
                skip_balanced_until_semicolon_or_brace();
            }
            continue;
        }
        if (match(TokenType::SEMICOLON)) {
            continue;
        }
        ParsedDecl inner = parse_external_declaration();
        children.push_back(inner.syntax);
    }
    collect_session_.finish_objc_protocol(decl.entity, last_consumed_loc());
    return {make_node(NodeKind::ObjCInterfaceDecl, begin,
                      last_consumed_raw_end(), children, text_payload(name)),
            {}};
}

void Parser::parse_objc_property(cir::EntityId container,
                                 std::vector<NodeId>& children) {
    SrcLoc loc = current_loc();
    collect::ObjCPropertyInput input;
    input.loc = loc;
    if (match(TokenType::LEFT_PAREN)) {
        while (!check(TokenType::RIGHT_PAREN) && !at_end()) {
            if (match(TokenType::COMMA)) {

                continue;
            }
            std::string word;
            if (!take_objc_selector_piece(word)) {
                diagnose(DiagnosticLevel::Error,
                         "expected a property attribute", current_loc());
                break;
            }
            if (word == "readonly") {
                input.is_readonly = true;
            } else if (word == "readwrite") {
                input.is_readonly = false;
            } else if (word == "assign" || word == "unsafe_unretained") {
                input.ownership = cir::ObjCPropertyOwnership::UnsafeUnretained;
            } else if (word == "retain") {
                input.ownership = cir::ObjCPropertyOwnership::Retain;
            } else if (word == "strong") {
                input.ownership = cir::ObjCPropertyOwnership::Strong;
            } else if (word == "copy") {
                input.ownership = cir::ObjCPropertyOwnership::Copy;
            } else if (word == "weak") {
                input.ownership = cir::ObjCPropertyOwnership::Weak;
            } else if (word == "nonatomic") {
                input.is_nonatomic = true;
            } else if (word == "atomic") {
                input.is_nonatomic = false;
            } else if (word == "class") {
                input.is_class_property = true;
            } else if (word == "getter") {
                if (match(TokenType::ASSIGN)) {
                    (void)take_objc_selector_piece(input.getter);
                }
            } else if (word == "setter") {
                if (match(TokenType::ASSIGN)) {
                    (void)take_objc_selector_piece(input.setter);
                    if (match(TokenType::COLON)) {
                        input.setter += ':';
                    }
                }
            } else {

            }
            if (!match(TokenType::COMMA)) {
                break;
            }
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after property attributes", current_loc());
        }
    }

    DeclarationParser property_parser(*this, TypeParseContext{});
    cir::TypeRef base_ref =
        property_parser.parse_declaration(/*run_second_half=*/false);
    do {
        property_parser.reset_declarator_parsing_state();
        ParsedDeclarator declarator =
            property_parser.parse_declarator(base_ref,
                                             /*allow_abstract=*/false);
        collect::ObjCPropertyInput one = input;
        one.name = declarator.name;
        one.type = declarator.type_ref.type.valid()
                       ? declarator.type_ref
                       : collect_session_.type_ref(declarator.type);
        one.loc = declarator.loc;
        if (one.name.empty()) {
            diagnose(DiagnosticLevel::Error,
                     "expected a property name", current_loc());
            break;
        }
        while (check(TokenType::ATTRIBUTE_KW)) {
            ParsedAttributes trailing = parse_gnu_attribute_list();
            one.attrs.append(std::move(trailing.attrs));
        }
        (void)collect_session_.declare_objc_property(container, one);
        children.push_back(declarator.syntax);
    } while (match(TokenType::COMMA));
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after @property", current_loc());
        skip_balanced_until_semicolon_or_brace();
    }
}

Parser::ParsedStmt Parser::parse_objc_at_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current_loc();
    std::string directive = objc_directive_spelling();
    if (directive == "throw") {
        consume();
        consume();
        std::optional<collect::ExprResult> operand;
        std::vector<NodeId> children;
        if (!check(TokenType::SEMICOLON)) {
            ParsedExpr thrown = parse_expression(PrecLevel::ASSIGNMENT);
            children.push_back(thrown.syntax);
            operand = std::move(thrown.sem);
        }
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error, "expected ';' after '@throw'",
                     current_loc());
        }
        collect::StmtResult sem =
            collect_session_.collect_objc_throw_stmt(std::move(operand), loc);
        return {make_node(NodeKind::ThrowExpr, begin, last_consumed_raw_end(),
                          children),
                std::move(sem)};
    }
    if (directive == "autoreleasepool") {
        consume();
        consume();
        if (!check(TokenType::LEFT_BRACE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '{' after '@autoreleasepool'", current_loc());
        }
        ParsedStmt body = parse_compound_statement();
        collect::StmtResult sem = collect_session_.collect_objc_autoreleasepool(
            std::move(body.sem), loc);
        return {make_node(NodeKind::CompoundStmt, begin,
                          last_consumed_raw_end(), {body.syntax}),
                std::move(sem)};
    }
    if (directive == "synchronized") {
        consume();
        consume();
        if (!match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '(' after '@synchronized'", current_loc());
        }
        ParsedExpr object = parse_expression(PrecLevel::ASSIGNMENT);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after '@synchronized' object",
                     current_loc());
        }
        collect::ObjCSynchronizedControl control =
            collect_session_.begin_objc_synchronized(std::move(object.sem),
                                                     loc);
        if (!check(TokenType::LEFT_BRACE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '{' after '@synchronized'", current_loc());
        }
        ParsedStmt body = parse_compound_statement();
        collect::StmtResult sem = collect_session_.finish_objc_synchronized(
            control, std::move(body.sem), loc);
        return {make_node(NodeKind::CompoundStmt, begin,
                          last_consumed_raw_end(),
                          {object.syntax, body.syntax}),
                std::move(sem)};
    }

    consume();
    consume();
    collect::TryControl control = collect_session_.begin_try(loc);
    std::vector<NodeId> children;
    if (!check(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error, "expected '{' after '@try'",
                 current_loc());
    }
    ParsedStmt body = parse_compound_statement();
    children.push_back(body.syntax);
    collect_session_.finish_try_body(control, std::move(body.sem));

    bool saw_handler = false;
    while (check(TokenType::AT) && objc_directive_spelling() == "catch") {
        size_t catch_begin = current_raw_index();
        SrcLoc catch_loc = current_loc();
        consume();
        consume();
        std::vector<NodeId> catch_children;
        if (!match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected '(' after '@catch'",
                     current_loc());
        }
        collect_session_.enter_scope(collect::ScopeFlags::BlockScope);
        std::optional<cir::TypeRef> catch_type;
        std::string param_name;
        if (check(TokenType::ELLIPSIS)) {
            consume();
        } else {
            DeclarationParser catch_parser(*this);
            cir::TypeRef base = catch_parser.parse_declaration(false, true);
            ParsedDeclarator declarator =
                catch_parser.parse_declarator(base, true);
            catch_type = declarator.type_ref;
            if (declarator.has_name) {
                param_name = declarator.name;
            }
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after '@catch' declaration", current_loc());
        }
        collect_session_.begin_catch_handler(control, catch_type, param_name,
                                             catch_loc);
        ParsedStmt handler = parse_compound_statement();
        catch_children.push_back(handler.syntax);
        collect_session_.finish_catch_handler(control, std::move(handler.sem),
                                              catch_loc);
        collect_session_.leave_scope();
        children.push_back(make_node(NodeKind::CatchClause, catch_begin,
                                     last_consumed_raw_end(),
                                     catch_children));
        saw_handler = true;
    }

    bool saw_finally = check(TokenType::AT) &&
                       objc_directive_spelling() == "finally";
    if (saw_finally && !saw_handler) {
        collect_session_.begin_catch_handler(control, std::nullopt, "", loc);
        collect::StmtResult rethrow =
            collect_session_.collect_objc_throw_stmt(std::nullopt, loc);
        collect_session_.finish_catch_handler(control, std::move(rethrow),
                                              loc);
    }
    collect::StmtResult sem = collect_session_.finish_try(control, loc);
    if (saw_finally) {
        consume();
        consume();
        diagnose(DiagnosticLevel::Warning,
                 "'@finally' runs on normal exit only; exceptional-path "
                 "cleanup is not implemented yet",
                 loc);
        ParsedStmt normal_finally = parse_compound_statement();
        children.push_back(normal_finally.syntax);
        sem.fragment = collect_session_.chain(
            std::move(sem.fragment), std::move(normal_finally.sem.fragment),
            loc);
        sem.falls_through =
            sem.falls_through && normal_finally.sem.falls_through;
        sem.has_error = sem.has_error || normal_finally.sem.has_error;
    }
    if (!saw_handler && !saw_finally) {
        diagnose(DiagnosticLevel::Error,
                 "expected '@catch' or '@finally' after '@try' block",
                 current_loc());
    }
    return {make_node(NodeKind::TryStmt, begin, last_consumed_raw_end(),
                      children),
            std::move(sem)};
}

bool Parser::objc_for_in_ahead() const {
    if (peek(1).type != TokenType::LEFT_PAREN) {
        return false;
    }
    size_t depth = 1;
    for (size_t offset = 2; offset < 256; ++offset) {
        const Token& token = peek(offset);
        switch (token.type) {
        case TokenType::LEFT_PAREN:
        case TokenType::LEFT_BRACKET:
        case TokenType::LEFT_BRACE:
            ++depth;
            break;
        case TokenType::RIGHT_PAREN:
        case TokenType::RIGHT_BRACKET:
        case TokenType::RIGHT_BRACE:
            if (--depth == 0) {
                return false;
            }
            break;
        case TokenType::SEMICOLON:
            if (depth == 1) {
                return false;
            }
            break;
        case TokenType::Eof:
            return false;
        case TokenType::IDENTIFIER:
            if (depth == 1 && token.value == "in") {
                return true;
            }
            break;
        default:
            break;
        }
    }
    return false;
}

Parser::ParsedStmt Parser::parse_objc_for_in_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current_loc();
    consume();
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected '(' after for",
                 current_loc());
    }
    cir::TypeRef loop_var_type;
    std::string loop_var_name;
    if (check(TokenType::IDENTIFIER) &&
        peek(1).type == TokenType::IDENTIFIER && peek(1).value == "in") {

        diagnose(DiagnosticLevel::Error,
                 "declare the loop variable inside the for-in statement "
                 "(for (id x in collection))",
                 current_loc());
        consume();
    } else {
        DeclarationParser var_parser(*this);
        cir::TypeRef base = var_parser.parse_declaration(false, true);
        ParsedDeclarator declarator = var_parser.parse_declarator(base, true);
        loop_var_type = declarator.type_ref;
        if (declarator.has_name) {
            loop_var_name = declarator.name;
        } else {
            diagnose(DiagnosticLevel::Error,
                     "expected a named loop variable in for-in statement",
                     current_loc());
        }
    }
    if (!(check(TokenType::IDENTIFIER) && current().value == "in")) {
        diagnose(DiagnosticLevel::Error,
                 "expected 'in' after the for-in loop variable",
                 current_loc());
    } else {
        consume();
    }
    ParsedExpr collection = parse_expression(PrecLevel::ASSIGNMENT);
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after for-in collection", current_loc());
    }
    collect::ObjCForInControl control = collect_session_.begin_objc_for_in(
        loop_var_name, loop_var_type, std::move(collection.sem), loc);
    ParsedStmt body = parse_statement();
    collect::StmtResult sem =
        collect_session_.finish_objc_for_in(control, body.sem, loc);
    return {make_node(NodeKind::ForStmt, begin, last_consumed_raw_end(),
                      {collection.syntax, body.syntax}),
            std::move(sem)};
}

} // namespace aburi::syntax
