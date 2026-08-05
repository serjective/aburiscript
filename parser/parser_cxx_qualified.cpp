#include "parser.h"

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

collect::ExprResult make_invalid_template_disambiguator_expr(
    collect::Session& session,
    std::string_view name) {
    collect::ExprResult result;
    result.type = session.file().unknown_type();
    result.name = std::string(name);
    result.qualified_name = true;
    result.category = collect::ValueCategory::Dependent;
    result.has_error = true;
    return result;
}

std::optional<cir::OperatorFunctionSpelling> symbolic_operator_spelling(
    const Token& token) {
    using Spelling = cir::OperatorFunctionSpelling;
    switch (token.type) {
        case TokenType::ARROW: return Spelling::Arrow;
        case TokenType::ARROW_STAR: return Spelling::ArrowStar;
        case TokenType::BITWISE_NOT: return Spelling::BitwiseNot;
        case TokenType::LOGICAL_NOT: return Spelling::LogicalNot;
        case TokenType::PLUS: return Spelling::Plus;
        case TokenType::NEGATE: return Spelling::Minus;
        case TokenType::MULTIPLY: return Spelling::Multiply;
        case TokenType::DIVIDE: return Spelling::Divide;
        case TokenType::MODULO: return Spelling::Modulo;
        case TokenType::BITWISE_XOR: return Spelling::BitwiseXor;
        case TokenType::BITWISE_AND: return Spelling::BitwiseAnd;
        case TokenType::BITWISE_OR: return Spelling::BitwiseOr;
        case TokenType::ASSIGN: return Spelling::Assign;
        case TokenType::ASSIGN_ADD: return Spelling::AddAssign;
        case TokenType::ASSIGN_SUB: return Spelling::SubtractAssign;
        case TokenType::ASSIGN_MUL: return Spelling::MultiplyAssign;
        case TokenType::ASSIGN_DIV: return Spelling::DivideAssign;
        case TokenType::ASSIGN_MOD: return Spelling::ModuloAssign;
        case TokenType::ASSIGN_XOR: return Spelling::XorAssign;
        case TokenType::ASSIGN_AND: return Spelling::AndAssign;
        case TokenType::ASSIGN_OR: return Spelling::OrAssign;
        case TokenType::LEFT_SHIFT: return Spelling::LeftShift;
        case TokenType::RIGHT_SHIFT: return Spelling::RightShift;
        case TokenType::ASSIGN_LSHIFT: return Spelling::LeftShiftAssign;
        case TokenType::ASSIGN_RSHIFT: return Spelling::RightShiftAssign;
        case TokenType::EQUAL_TO: return Spelling::Equal;
        case TokenType::NOT_EQUAL: return Spelling::NotEqual;
        case TokenType::LESS_THAN: return Spelling::Less;
        case TokenType::GREATER_THAN: return Spelling::Greater;
        case TokenType::LESS_EQUAL_THAN: return Spelling::LessEqual;
        case TokenType::GREATER_EQUAL_THAN: return Spelling::GreaterEqual;
        case TokenType::THREE_WAY_COMPARE: return Spelling::ThreeWayCompare;
        case TokenType::LOGICAL_AND: return Spelling::LogicalAnd;
        case TokenType::LOGICAL_OR: return Spelling::LogicalOr;
        case TokenType::INCREMENT: return Spelling::Increment;
        case TokenType::DECREMENT: return Spelling::Decrement;
        case TokenType::COMMA: return Spelling::Comma;
        default: break;
    }
    if (token.type == TokenType::CO_AWAIT_KW ||
        (token.type == TokenType::IDENTIFIER && token.value == "co_await")) {

        return Spelling::CoAwait;
    }
    return std::nullopt;
}

} // namespace

std::optional<Parser::ParsedOperatorFunctionId>
Parser::parse_operator_function_id() {
    if (!lang_opts_.is_cxx_mode() || !check(TokenType::OPERATOR_KW)) {
        return std::nullopt;
    }

    ParsedOperatorFunctionId result;
    result.loc = current_loc();
    const bool conversion = starts_conversion_function_id();
    consume();

    if (conversion) {
        auto [target, syntax] = parse_conversion_type_id();
        result.identity.kind = cir::OperatorFunctionKind::Conversion;
        result.identity.conversion_type = target;
        result.type_syntax = syntax;
        result.name = "operator " + collect_session_.file().format_type(target);
        result.has_error = !target.type.valid();
        return result;
    }

    auto consume_empty_delimiters =
        [&](TokenType left,
            TokenType right,
            cir::OperatorFunctionSpelling spelling) {
            if (!check(left) || peek(1).type != right) {
                return false;
            }
            result.identity.kind = cir::OperatorFunctionKind::Symbolic;
            result.identity.spelling = spelling;
            result.name = "operator" + std::string(
                cir::operator_function_spelling_text(spelling));
            consume();
            consume();
            return true;
        };
    if (consume_empty_delimiters(TokenType::LEFT_PAREN,
                                 TokenType::RIGHT_PAREN,
                                 cir::OperatorFunctionSpelling::Call) ||
        consume_empty_delimiters(TokenType::LEFT_BRACKET,
                                 TokenType::RIGHT_BRACKET,
                                 cir::OperatorFunctionSpelling::Subscript)) {
        return result;
    }

    if (check(TokenType::STRING_LITERAL)) {
        Token literal = current();
        consume();
        result.identity.kind = cir::OperatorFunctionKind::Literal;
        if (literal.literal_prefix != LiteralPrefix::None ||
            !literal.value.empty()) {
            diagnose(DiagnosticLevel::Error,
                     "literal operator name requires an empty unprefixed string literal",
                     literal.loc);
            result.has_error = true;
        }
        if (!check(TokenType::IDENTIFIER) &&
            !check(TokenType::LITERAL_SUFFIX)) {
            diagnose(DiagnosticLevel::Error,
                     "expected identifier suffix in literal operator name",
                     current_loc());
            result.name = "operator\"\"";
            result.has_error = true;
            return result;
        }
        std::string suffix(current().value);
        result.identity.literal_suffix =
            collect_session_.file().intern_name(suffix);
        result.name = "operator\"\"" + suffix;
        consume();
        return result;
    }

    if (at_end()) {
        diagnose(DiagnosticLevel::Error,
                 "expected operator name after 'operator'",
                 result.loc);
        result.name = "operator";
        result.has_error = true;
        return result;
    }

    Token name_token = current();
    if (name_token.type == TokenType::NEW ||
        name_token.type == TokenType::DELETE) {
        const bool allocation = name_token.type == TokenType::NEW;
        result.identity.kind = allocation
            ? cir::OperatorFunctionKind::Allocation
            : cir::OperatorFunctionKind::Deallocation;
        consume();
        bool array = check(TokenType::LEFT_BRACKET) &&
            peek(1).type == TokenType::RIGHT_BRACKET;
        if (array) {
            result.identity.spelling = allocation
                ? cir::OperatorFunctionSpelling::NewArray
                : cir::OperatorFunctionSpelling::DeleteArray;
            consume();
            consume();
        } else {
            result.identity.spelling = allocation
                ? cir::OperatorFunctionSpelling::New
                : cir::OperatorFunctionSpelling::Delete;
        }
        result.name = "operator" + std::string(
            cir::operator_function_spelling_text(result.identity.spelling));
        return result;
    }

    std::optional<cir::OperatorFunctionSpelling> spelling =
        symbolic_operator_spelling(name_token);
    if (!spelling) {
        diagnose(DiagnosticLevel::Error,
                 "expected an overloadable operator name after 'operator'",
                 name_token.loc);
        result.name = "operator";
        result.has_error = true;
        consume();
        return result;
    }
    result.identity.kind = cir::OperatorFunctionKind::Symbolic;
    result.identity.spelling = *spelling;
    result.name = "operator" + std::string(
        cir::operator_function_spelling_text(*spelling));
    consume();
    return result;
}

bool Parser::starts_conversion_function_id(size_t offset) {
    if (!lang_opts_.is_cxx_mode() ||
        peek(offset).type != TokenType::OPERATOR_KW) {
        return false;
    }
    const Token& first = peek(offset + 1);
    if (is_type_start(first.type) ||
        first.type == TokenType::SCOPE_RESOLUTION) {
        return true;
    }
    if (!is_identifier_token(first.type)) {
        return false;
    }
    if (collect_session_.is_type_name(first.value)) {
        return true;
    }
    if (peek(offset + 2).type == TokenType::LESS_THAN) {
        const collect::Session::TemplateInfo* info =
            collect_session_.template_info_for_name(first.value);
        return info && (info->is_class_template || info->is_alias_template);
    }
    return false;
}

bool Parser::starts_qualified_conversion_function_id(size_t offset) {
    while (peek(offset).type == TokenType::LEFT_PAREN) {
        ++offset;
    }
    int angle_depth = 0;
    bool saw_scope = false;
    for (size_t index = offset; index < offset + 4096; ++index) {
        TokenType type = peek(index).type;
        if (type == TokenType::Eof || type == TokenType::SEMICOLON ||
            type == TokenType::LEFT_BRACE || type == TokenType::LEFT_PAREN) {
            return false;
        }
        if (type == TokenType::LESS_THAN) {
            ++angle_depth;
        } else if (type == TokenType::GREATER_THAN) {
            --angle_depth;
        } else if (type == TokenType::RIGHT_SHIFT) {
            angle_depth -= 2;
        } else if (angle_depth == 0 &&
                   type == TokenType::SCOPE_RESOLUTION) {
            saw_scope = true;
        } else if (angle_depth == 0 && type == TokenType::OPERATOR_KW) {
            return saw_scope && starts_conversion_function_id(index);
        }
    }
    return false;
}

std::pair<cir::TypeRef, NodeId> Parser::parse_conversion_type_id() {
    DeclarationParser conversion_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::ConversionTypeId));
    cir::TypeRef conversion_type =
        conversion_parser.parse_declaration(false, true);
    NodeId conversion_syntax = conversion_parser.type_syntax;

    auto parse_pointer_qualifiers = [&]() {
        uint8_t qualifiers = cir::QualNone;
        while (true) {
            if (match(TokenType::CONST)) {
                qualifiers |= cir::QualConst;
            } else if (match(TokenType::VOLATILE)) {
                qualifiers |= cir::QualVolatile;
            } else if (match(TokenType::RESTRICT)) {
                qualifiers |= cir::QualRestrict;
            } else if (match(TokenType::ATOMIC)) {
                qualifiers |= cir::QualAtomic;
            } else if (match(TokenType::NULLABILITY_QUALIFIER)) {
            } else if (check(TokenType::ATTRIBUTE_KW)) {
                (void)try_parse_attributes();
            } else {
                break;
            }
        }
        return qualifiers;
    };

    while (true) {
        if (check(TokenType::IDENTIFIER) &&
            peek(1).type == TokenType::SCOPE_RESOLUTION &&
            peek(2).type == TokenType::MULTIPLY) {
            Token owner = current();
            cir::TypeId owner_type =
                collect_session_.lookup_type_name(owner.value);
            consume();
            consume();
            consume();
            if (!owner_type.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "member pointer conversion target names an unknown class type",
                         owner.loc);
                conversion_type = collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            } else {
                cir::TypeId member_pointer =
                    collect_session_.member_pointer_type(
                        collect_session_.type_ref(owner_type),
                        conversion_type);
                conversion_type = cir::TypeRef{
                    member_pointer,
                    parse_pointer_qualifiers(),
                    conversion_type.memory_space};
            }
            continue;
        }
        if (match(TokenType::MULTIPLY)) {
            uint8_t pointer_qualifiers = parse_pointer_qualifiers();
            cir::TypeId pointer =
                collect_session_.pointer_type(conversion_type);
            conversion_type = cir::TypeRef{pointer,
                                           pointer_qualifiers,
                                           conversion_type.memory_space};
            continue;
        }
        if (match(TokenType::BITWISE_AND)) {
            cir::TypeId reference = collect_session_.reference_type(
                conversion_type, cir::ReferenceKind::LValue);
            conversion_type = collect_session_.type_ref(reference);
            continue;
        }
        if (match(TokenType::LOGICAL_AND)) {
            cir::TypeId reference = collect_session_.reference_type(
                conversion_type, cir::ReferenceKind::RValue);
            conversion_type = collect_session_.type_ref(reference);
            continue;
        }
        break;
    }
    cir::TypeId resolved =
        collect_session_.file().resolved_type(conversion_type.type);
    if (collect_session_.file().valid(resolved)) {
        cir::TypeKind kind = collect_session_.file().type(resolved).kind;
        if (kind == cir::TypeKind::Function) {
            diagnose(DiagnosticLevel::Error,
                     "conversion function cannot convert to a function type",
                     current_loc());
        } else if (kind == cir::TypeKind::Array) {
            diagnose(DiagnosticLevel::Error,
                     "conversion function cannot convert to an array type",
                     current_loc());
        }
    }
    return {conversion_type, conversion_syntax};
}

std::optional<Parser::ParsedConversionFunctionId>
Parser::parse_conversion_function_id() {
    if (!starts_conversion_function_id()) {
        return std::nullopt;
    }
    std::optional<ParsedOperatorFunctionId> parsed =
        parse_operator_function_id();
    if (!parsed || parsed->identity.kind !=
                       cir::OperatorFunctionKind::Conversion) {
        return std::nullopt;
    }
    ParsedConversionFunctionId result;
    result.name = std::move(parsed->name);
    result.identity = parsed->identity;
    result.target_type = parsed->identity.conversion_type;
    result.type_syntax = parsed->type_syntax;
    result.loc = parsed->loc;
    result.has_error = parsed->has_error;
    return result;
}

std::optional<Parser::ParsedConversionFunctionDeclarator>
Parser::parse_conversion_function_declarator(bool require_qualified) {
    size_t surrounding_parentheses = 0;
    while (match(TokenType::LEFT_PAREN)) {
        ++surrounding_parentheses;
    }
    ParsedNestedName nested;
    bool qualified = starts_qualified_conversion_function_id();
    if (qualified) {
        nested = parse_nested_name_specifier();
    } else if (require_qualified) {
        return std::nullopt;
    }
    std::optional<ParsedConversionFunctionId> conversion_id =
        parse_conversion_function_id();
    if (!conversion_id) {
        return std::nullopt;
    }

    bool grouping_error = false;
    for (size_t index = 0; index < surrounding_parentheses; ++index) {
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' around conversion-function-id",
                     current_loc());
            grouping_error = true;
            break;
        }
    }

    ParsedDeclarator prefix;
    prefix.name = conversion_id->name;
    prefix.operator_function = conversion_id->identity;
    prefix.type = conversion_id->target_type.type;
    prefix.type_ref = conversion_id->target_type;
    prefix.loc = conversion_id->loc;
    prefix.has_name = true;
    prefix.qualified_context = nested.scope.context;
    prefix.template_qualifier_info = nested.template_qualifier_info;
    prefix.template_qualifier_arguments =
        std::move(nested.template_qualifier_arguments);
    prefix.template_qualifier_loc = nested.template_qualifier_loc;
    prefix.dependent_qualifier_type = nested.scope.dependent_type;

    DeclarationParser suffix_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    suffix_parser.allow_cxx_member_declarator_ids = true;
    ParsedDeclarator declarator = suffix_parser.parse_declarator(
        conversion_id->target_type,
        /*allow_abstract=*/true,
        &prefix);

    ParsedConversionFunctionDeclarator result;
    result.declarator = std::move(declarator);
    result.target_type = conversion_id->target_type;
    result.target_syntax = conversion_id->type_syntax;
    result.has_error = nested.has_error || conversion_id->has_error ||
                       grouping_error ||
                       !result.declarator.is_function;
    if (!result.declarator.params.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "conversion function cannot have parameters",
                 conversion_id->loc);
        result.has_error = true;
    }
    if (result.declarator.has_trailing_return_type) {
        diagnose(DiagnosticLevel::Error,
                 "conversion function cannot use a trailing return type",
                 conversion_id->loc);
        result.has_error = true;
    }
    return result;
}

size_t Parser::template_id_scope_offset(size_t offset) {

    auto less_than_opens_nested_template_id =
        [&](size_t less_offset) {
            if (less_offset == offset + 1) {
                return true;
            }
            if (less_offset == 0 ||
                !is_identifier_token(peek(less_offset - 1).type)) {
                return false;
            }

            size_t name_offset = less_offset - 1;
            std::string_view name = peek(name_offset).value;
            if (name_offset > 0 &&
                peek(name_offset - 1).type == TokenType::TEMPLATE) {
                return true;
            }
            if (collect_session_.template_info_for_name(name)) {
                return true;
            }

            bool member_or_qualified =
                name_offset > 0 &&
                (peek(name_offset - 1).type ==
                     TokenType::SCOPE_RESOLUTION ||
                 peek(name_offset - 1).type == TokenType::DOT ||
                 peek(name_offset - 1).type == TokenType::ARROW);
            if (member_or_qualified) {
                if (peek(name_offset - 1).type ==
                    TokenType::SCOPE_RESOLUTION) {
                    std::vector<std::string_view> reversed_qualifiers;
                    size_t scope_offset = name_offset - 1;
                    while (scope_offset > 0) {
                        size_t qualifier_offset = scope_offset - 1;
                        if (!is_identifier_token(
                                peek(qualifier_offset).type)) {
                            break;
                        }
                        reversed_qualifiers.push_back(
                            peek(qualifier_offset).value);
                        if (qualifier_offset > 0 &&
                            peek(qualifier_offset - 1).type ==
                                TokenType::SCOPE_RESOLUTION) {
                            scope_offset = qualifier_offset - 1;
                            continue;
                        }
                        scope_offset = qualifier_offset;
                        break;
                    }
                    bool global_qualifier =
                        peek(scope_offset).type ==
                        TokenType::SCOPE_RESOLUTION;
                    std::reverse(reversed_qualifiers.begin(),
                                 reversed_qualifiers.end());
                    if (!reversed_qualifiers.empty() &&
                        collect_session_.peek_qualified_template_info(
                            global_qualifier,
                            reversed_qualifiers,
                            name)) {
                        return true;
                    }
                }
                return false;
            }

            const cir::File& file = collect_session_.file();
            const cir::Binding* binding =
                file.lookup_ordinary_binding(
                    collect_session_.current_decl_context(),
                    name,
                    /*include_parents=*/true);
            return !binding || file.binding_is_callable(*binding);
        };

    size_t i = offset + 1;
    int depth = 0;
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    size_t guard = 0;
    while (!at_end() && guard++ < 4096) {
        TokenType type = peek(i).type;
        if (type == TokenType::LEFT_PAREN) {
            ++paren_depth;
        } else if (type == TokenType::RIGHT_PAREN) {
            --paren_depth;
        } else if (type == TokenType::LEFT_BRACKET) {
            ++bracket_depth;
        } else if (type == TokenType::RIGHT_BRACKET) {
            --bracket_depth;
        } else if (type == TokenType::LEFT_BRACE) {
            ++brace_depth;
        } else if (type == TokenType::RIGHT_BRACE) {
            --brace_depth;
        } else if (paren_depth == 0 && bracket_depth == 0 &&
                   brace_depth == 0 &&
                   type == TokenType::LESS_THAN) {
            if (less_than_opens_nested_template_id(i)) {
                ++depth;
            }
        } else if (paren_depth == 0 && bracket_depth == 0 &&
                   brace_depth == 0 &&
                   type == TokenType::GREATER_THAN) {
            if (--depth == 0) {
                return peek(i + 1).type == TokenType::SCOPE_RESOLUTION ? i + 1
                                                                       : 0;
            }
        } else if (paren_depth == 0 && bracket_depth == 0 &&
                   brace_depth == 0 &&
                   type == TokenType::RIGHT_SHIFT) {
            depth -= 2;
            if (depth <= 0) {
                return depth == 0 &&
                               peek(i + 1).type == TokenType::SCOPE_RESOLUTION
                    ? i + 1
                    : 0;
            }
        } else if (paren_depth == 0 && bracket_depth == 0 &&
                   brace_depth == 0 &&
                   (type == TokenType::SEMICOLON ||
                    type == TokenType::Eof)) {
            return 0;
        }
        ++i;
    }
    return 0;
}

bool Parser::template_id_precedes_scope(size_t offset) {
    return template_id_scope_offset(offset) != 0;
}

bool Parser::starts_cxx_qualified_name(size_t offset) {
    return peek(offset).type == TokenType::SCOPE_RESOLUTION ||
        decltype_specifier_precedes_scope(offset) ||
        (is_identifier_token(peek(offset).type) &&
         (peek(offset + 1).type == TokenType::SCOPE_RESOLUTION ||
          (peek(offset + 1).type == TokenType::LESS_THAN &&
           template_id_precedes_scope(offset))));
}

bool Parser::decltype_specifier_precedes_scope(size_t offset) {
    if (peek(offset).type != TokenType::DECLTYPE_KW ||
        peek(offset + 1).type != TokenType::LEFT_PAREN) {
        return false;
    }
    size_t depth = 1;
    for (size_t index = offset + 2; index < offset + 4096; ++index) {
        TokenType type = peek(index).type;
        if (type == TokenType::LEFT_PAREN) {
            ++depth;
        } else if (type == TokenType::RIGHT_PAREN) {
            if (--depth == 0) {
                return peek(index + 1).type == TokenType::SCOPE_RESOLUTION;
            }
        } else if (type == TokenType::Eof) {
            return false;
        }
    }
    return false;
}

bool Parser::out_of_line_structor_declaration_ahead(size_t start_offset) {
    if (!lang_opts_.is_cxx_mode()) {
        return false;
    }
    size_t offset = start_offset;
    size_t surrounding_parentheses = 0;
    while (peek(offset).type == TokenType::LEFT_PAREN) {
        ++surrounding_parentheses;
        ++offset;
    }
    if (peek(offset).type == TokenType::SCOPE_RESOLUTION) {
        ++offset;
    }

    auto followed_by_parameter_list = [&](size_t terminal_end) {
        for (size_t index = 0; index < surrounding_parentheses; ++index) {
            if (peek(terminal_end + index).type != TokenType::RIGHT_PAREN) {
                return false;
            }
        }
        return peek(terminal_end + surrounding_parentheses).type ==
            TokenType::LEFT_PAREN;
    };

    std::string_view previous;
    bool saw_component = false;
    size_t guard = 0;
    while (guard++ < 64) {
        const Token& tok = peek(offset);
        if (!is_identifier_token(tok.type)) {
            break;
        }
        if (peek(offset + 1).type == TokenType::SCOPE_RESOLUTION) {
            previous = tok.value;
            saw_component = true;
            offset += 2;
            continue;
        }
        if (peek(offset + 1).type == TokenType::LESS_THAN) {
            size_t scope_offset = template_id_scope_offset(offset);
            if (scope_offset == 0) {
                return false;
            }
            previous = tok.value;
            saw_component = true;
            offset = scope_offset + 1;
            continue;
        }
        return saw_component && tok.value == previous &&
               followed_by_parameter_list(offset + 1);
    }
    return saw_component &&
           peek(offset).type == TokenType::BITWISE_NOT &&
           is_identifier_token(peek(offset + 1).type) &&
           peek(offset + 1).value == previous &&
           followed_by_parameter_list(offset + 2);
}

std::optional<Parser::TemplateIdQualifierLookahead>
Parser::peek_template_id_qualifier(size_t start_offset) {
    size_t offset = start_offset;
    bool global_qualifier = false;
    if (peek(offset).type == TokenType::SCOPE_RESOLUTION) {
        global_qualifier = true;
        ++offset;
    }

    std::vector<std::string_view> qualifiers;
    while (is_identifier_token(peek(offset).type) &&
           peek(offset + 1).type == TokenType::SCOPE_RESOLUTION &&
           peek(offset + 2).type != TokenType::MULTIPLY) {
        qualifiers.push_back(peek(offset).value);
        offset += 2;
    }

    if (!is_identifier_token(peek(offset).type) ||
        peek(offset + 1).type != TokenType::LESS_THAN ||
        !template_id_precedes_scope(offset)) {
        return std::nullopt;
    }

    const collect::Session::TemplateInfo* info = nullptr;
    if (qualifiers.empty() && !global_qualifier) {
        info = collect_session_.template_info_for_name(peek(offset).value);
    } else {
        info = collect_session_.peek_qualified_template_info(
            global_qualifier,
            qualifiers,
            peek(offset).value);
    }
    if (!info || (!info->is_class_template && !info->is_alias_template)) {
        return std::nullopt;
    }

    TemplateIdQualifierLookahead result;
    result.template_info = info;
    result.template_name = peek(offset).value;
    result.terminal_offset = template_id_scope_offset(offset) + 1;
    return result;
}

bool Parser::template_id_precedes_postfix(size_t offset,
                                          TokenType postfix) {
    size_t i = offset + 1;
    int depth = 0;
    size_t guard = 0;
    while (!at_end() && guard++ < 4096) {
        TokenType type = peek(i).type;
        if (type == TokenType::LESS_THAN) {
            ++depth;
        } else if (type == TokenType::GREATER_THAN) {
            if (--depth == 0) {
                return peek(i + 1).type == postfix;
            }
        } else if (type == TokenType::RIGHT_SHIFT) {
            depth -= 2;
            if (depth <= 0) {
                return depth == 0 && peek(i + 1).type == postfix;
            }
        } else if (type == TokenType::SEMICOLON ||
                   type == TokenType::LEFT_BRACE ||
                   type == TokenType::Eof) {
            return false;
        }
        ++i;
    }
    return false;
}

bool Parser::template_id_precedes_call(size_t offset) {

    return template_id_precedes_postfix(offset, TokenType::LEFT_PAREN);
}

bool Parser::template_id_precedes_type_conversion(size_t offset) {
    return template_id_precedes_call(offset) ||
           template_id_precedes_postfix(offset, TokenType::LEFT_BRACE);
}

Parser::ParsedNestedName Parser::parse_nested_name_specifier() {
    ParsedNestedName result;

    bool defer_class_template_qualifiers =
        defer_class_template_qualifier_instantiation_;
    defer_class_template_qualifier_instantiation_ = false;
    bool select_deferred_partial =
        select_partial_for_deferred_class_template_qualifier_;
    select_partial_for_deferred_class_template_qualifier_ = false;
    if (check(TokenType::SCOPE_RESOLUTION)) {
        consume();
        result.scope = collect_session_.resolve_qualifier_root();
        result.consumed_any = true;
        result.global_qualifier = true;
    }
    if (decltype_specifier_precedes_scope()) {
        SrcLoc decltype_loc = current_loc();
        DeclarationParser type_parser(
            *this,
            TypeParseContext::type_only(
                TypeParseContext::Origin::ClassOrDecltype));
        cir::TypeRef qualifier =
            type_parser.parse_declaration(false, true);
        result.consumed_any = true;
        result.last_component_name = "decltype";
        if (!match(TokenType::SCOPE_RESOLUTION)) {
            result.has_error = true;
            return result;
        }
        std::optional<collect::Session::QualifierResolution> resolved =
            collect_session_.resolve_type_qualifier(
                qualifier, decltype_loc, "decltype-specifier");
        if (!resolved.has_value()) {
            diagnose(
                DiagnosticLevel::Error,
                "decltype nested-name-specifier does not designate a class or enumeration type",
                decltype_loc);
            result.has_error = true;
            return result;
        }
        result.scope = *resolved;
        result.depends_on_template_parameter =
            result.scope.dependent_type.type.valid();
        result.has_error = result.scope.has_error;
    }
    while (is_identifier_token(current().type) ||
           (check(TokenType::TEMPLATE) &&
            is_identifier_token(peek(1).type) &&
            peek(2).type == TokenType::LESS_THAN &&
            template_id_precedes_scope(1))) {
        bool has_template_disambiguator = false;
        if (check(TokenType::TEMPLATE)) {
            consume();
            has_template_disambiguator = true;
        }
        const BuiltinInfo* builtin_type =
            current().type == TokenType::IDENTIFIER
                ? BuiltinRegistry::instance().lookup(current().value)
                : nullptr;
        if (builtin_type &&
            builtin_type->supported &&
            (builtin_type->syntax ==
                 BuiltinSyntaxKind::IntegerSequenceType ||
             builtin_type->syntax ==
                 BuiltinSyntaxKind::PackElementType) &&
            peek(1).type == TokenType::LESS_THAN &&
            template_id_precedes_scope(0)) {
            Token component = current();
            consume();
            std::vector<NodeId> ignored_children;
            cir::TypeRef component_type =
                builtin_type->syntax ==
                        BuiltinSyntaxKind::IntegerSequenceType
                    ? parse_builtin_make_integer_sequence_type(
                          component.loc,
                          ignored_children,
                          /*materialize_class_definition=*/true)
                    : parse_builtin_type_pack_element_type(
                          component.loc, ignored_children);
            result.consumed_any = true;
            result.last_component_name = component.value;
            if (!match(TokenType::SCOPE_RESOLUTION) ||
                !component_type.valid()) {
                result.has_error = true;
                break;
            }
            if (collect_session_.is_dependent_type(component_type.type)) {
                result.scope = {};
                result.scope.dependent_type = component_type;
                result.depends_on_template_parameter = true;
                continue;
            }
            cir::TypeId resolved = collect_session_.file().resolved_type(
                component_type.type);
            if (!collect_session_.file().valid(resolved) ||
                collect_session_.file().type(resolved).kind !=
                    cir::TypeKind::Record) {
                diagnose(DiagnosticLevel::Error,
                         "builtin type result is not a class type",
                         component.loc);
                result.has_error = true;
                break;
            }
            cir::EntityId entity =
                collect_session_.file().record_entity(resolved);
            if (!entity.valid() ||
                !collect_session_.file().valid(entity)) {
                result.has_error = true;
                break;
            }
            result.scope = {};
            result.scope.entity = entity;
            result.scope.context =
                collect_session_.file().entity(entity).semantic_context;
            result.scope.is_namespace = false;
            result.scope.has_error = !result.scope.context.valid();
            if (result.scope.has_error) {
                result.has_error = true;
                break;
            }
            continue;
        }
        if (peek(1).type == TokenType::SCOPE_RESOLUTION &&

            peek(2).type != TokenType::MULTIPLY) {
            Token component = current();
            bool directly_names_type_parameter =
                collect_session_.type_name_is_active_template_type_parameter(
                    component.value);
            bool component_from_template_parameter = false;
            if (in_constraint_substitution_failure_context()) {
                component_from_template_parameter =
                    directly_names_type_parameter;
            }
            consume();
            consume();
            result.consumed_any = true;
            result.last_component_name = component.value;
            if (result.scope.dependent_type.valid()) {
                cir::TypeId dependent_component =
                    collect_session_.file().dependent_name_type(
                        result.scope.dependent_type,
                        component.value);
                result.scope = {};
                result.scope.dependent_type =
                    collect_session_.type_ref(dependent_component);
            } else {
                result.scope = collect_session_.resolve_qualifier_component(
                    result.scope.context, component.value, component.loc);
            }
            result.depends_on_template_parameter =
                result.depends_on_template_parameter ||
                component_from_template_parameter ||
                result.scope.dependent_type.type.valid();
            if (directly_names_type_parameter &&
                result.scope.dependent_type.type.valid() &&
                collect_session_.type_contains_type_parameter_pack(
                    result.scope.dependent_type.type)) {
                if (!collect_session_.capture_type_parameter_pack_name(
                        component.value)) {
                    diagnose(DiagnosticLevel::Error,
                             "unexpanded template parameter pack '" +
                                 std::string(component.value) +
                                 "' is not supported yet",
                             component.loc);
                    result.has_error = true;
                    break;
                }
            }
            if (result.scope.has_error) {
                if (component_from_template_parameter) {
                    note_constraint_substitution_failure();
                }
                result.has_error = true;
                break;
            }
            continue;
        }
        if (lang_opts_.is_cxx_mode() &&
            peek(1).type == TokenType::LESS_THAN &&
            template_id_precedes_scope(0)) {

            // [temp.names]p4
            if (result.scope.dependent_type.valid() &&
                has_template_disambiguator) {
                Token name_token = current();
                consume();
                std::vector<collect::Session::TemplateArgument> arguments;
                bool parsed_arguments =
                    parse_dependent_type_template_argument_list(
                        arguments, name_token.loc);
                result.consumed_any = true;
                result.last_component_name = name_token.value;
                if (!parsed_arguments ||
                    !match(TokenType::SCOPE_RESOLUTION)) {
                    result.has_error = true;
                    break;
                }
                cir::TypeId dependent_component =
                    collect_session_.file().dependent_name_type(
                        result.scope.dependent_type,
                        name_token.value,
                        std::move(arguments));
                result.scope = {};
                result.scope.dependent_type =
                    collect_session_.type_ref(dependent_component);
                result.depends_on_template_parameter = true;
                continue;
            }
            const collect::Session::TemplateInfo* info = nullptr;
            if (result.consumed_any && result.scope.context.valid()) {
                info = collect_session_.template_info_in_context(
                    result.scope.context,
                    current().value,
                    /*include_parents=*/false);
            } else {
                info = collect_session_.template_info_for_name(current().value);
            }
            if (!info ||
                (!info->is_class_template && !info->is_alias_template)) {
                if (has_template_disambiguator) {
                    diagnose(DiagnosticLevel::Error,
                             "template disambiguator names a non-template",
                             current().loc);
                    result.has_error = true;
                }
                break;
            }
            Token name_token = current();
            consume();
            std::vector<collect::Session::TemplateArgument> arguments;
            uint64_t point_lookup_generation = 0;
            bool parsed_arguments =
                parse_and_canonicalize_template_argument_list(
                    *info,
                    arguments,
                    name_token.loc,
                    &point_lookup_generation);
            bool has_dependent_arguments =
                parsed_arguments &&
                template_arguments_are_dependent(arguments);
            result.consumed_any = true;
            result.last_component_name = name_token.value;
            if (!parsed_arguments) {
                result.has_error = true;
                break;
            }
            if (defer_class_template_qualifiers && info->is_class_template &&
                (has_dependent_arguments ||
                 !collect_session_.in_template_instantiation())) {
                consume();
                const collect::Session::TemplateInfo* qualifier_info = info;
                if (select_deferred_partial &&
                    !info->is_partial_specialization) {
                    collect::Session::PartialSpecializationSelection
                        selection =
                            select_template_partial_specialization(
                                *info,
                                arguments,
                                name_token.loc,
                                point_lookup_generation);
                    if (!selection.is_ambiguous && selection.info) {
                        qualifier_info = selection.info;
                    }
                }

                result.template_qualifier_info = info;
                result.template_qualifier_arguments = std::move(arguments);
                result.template_qualifier_loc = name_token.loc;
                if (qualifier_info->pattern_record.valid() &&
                    collect_session_.file().valid(
                        qualifier_info->pattern_record)) {
                    const cir::Entity& pattern =
                        collect_session_.file().entity(
                            qualifier_info->pattern_record);
                    result.scope.context = pattern.semantic_context;
                    result.scope.entity = qualifier_info->pattern_record;
                    result.scope.is_namespace = false;
                    result.scope.has_error = !result.scope.context.valid();
                    if (result.scope.has_error) {
                        result.has_error = true;
                        break;
                    }
                } else {

                    result.scope = {};
                    result.scope.dependent_type =
                        collect_session_.type_ref(
                            collect_session_.file().dependent_type(
                                "deferred class-template qualifier"));
                    result.depends_on_template_parameter = true;
                }
                continue;
            }
            cir::EntityId instantiated =
                instantiate_template_with_args(*info,
                                               std::move(arguments),
                                               name_token.loc,
                                               point_lookup_generation,
                                               false,
                                               true);
            consume();
            if (!instantiated.valid()) {
                result.has_error = true;
                break;
            }
            const cir::Entity& entity =
                collect_session_.file().entity(instantiated);
            if (entity.type.valid() &&
                (has_dependent_arguments ||
                 collect_session_.is_dependent_type(entity.type))) {

                result.scope = {};
                result.scope.entity = instantiated;
                result.scope.is_namespace = false;
                result.scope.dependent_type =
                    collect_session_.type_ref(entity.type);
                result.depends_on_template_parameter = true;
                continue;
            }

            cir::TypeId qualifier_type =
                collect_session_.file().resolved_type(entity.type);
            cir::EntityId qualifier_entity{};
            if (collect_session_.file().valid(qualifier_type) &&
                collect_session_.file().type(qualifier_type).kind ==
                    cir::TypeKind::Record) {
                (void)collect_session_.require_complete_class_type(
                    qualifier_type,
                    name_token.loc,
                    cir::InstantiationDemandKind::BaseMemberList);
                qualifier_entity =
                    collect_session_.file().record_entity(qualifier_type);
            } else if (collect_session_.file().valid(qualifier_type) &&
                       collect_session_.file().type(qualifier_type).kind ==
                           cir::TypeKind::Enum) {
                qualifier_entity =
                    std::get<cir::EnumTypePayload>(
                        collect_session_.file().type_payload(qualifier_type))
                        .entity;
            }
            if (!qualifier_entity.valid() ||
                !collect_session_.file().valid(qualifier_entity)) {
                diagnose(DiagnosticLevel::Error,
                         "template-id nested-name-specifier does not name a class or enumeration",
                         name_token.loc);
                result.has_error = true;
                break;
            }
            result.scope.entity = qualifier_entity;
            result.scope.context = collect_session_.file()
                                       .entity(qualifier_entity)
                                       .semantic_context;
            result.scope.is_namespace = false;
            result.scope.has_error = !result.scope.context.valid();
            if (result.scope.has_error) {
                result.has_error = true;
                break;
            }
            continue;
        }
        break;
    }
    return result;
}

Parser::ParsedExpr Parser::parse_cxx_qualified_id_expression() {
    size_t begin = current_raw_index();
    ParsedNestedName nested = parse_nested_name_specifier();

    bool has_template_keyword = false;
    if (lang_opts_.is_cxx_mode() && check(TokenType::TEMPLATE)) {
        has_template_keyword = true;
        consume();
    }

    if (check(TokenType::BITWISE_NOT)) {
        Token destructor_token = current();
        consume();
        std::string destructor_name = "~<destructor>";
        cir::TypeId named_type{};
        bool has_error = nested.has_error;
        if (is_identifier_token(current().type)) {
            Token name_token = current();
            destructor_name = "~" + std::string(name_token.value);
            named_type = nested.scope.context.valid()
                ? collect_session_.lookup_qualified_type_name_checked(
                      nested.scope.context, name_token.value,
                      name_token.loc)
                : collect_session_.lookup_type_name(name_token.value);
            if (!named_type.valid() && nested.scope.entity.valid() &&
                collect_session_.file().valid(nested.scope.entity)) {
                const cir::Entity& qualifier =
                    collect_session_.file().entity(nested.scope.entity);
                bool names_qualifier =
                    (qualifier.name.valid() &&
                     collect_session_.file().name(qualifier.name) ==
                         name_token.value) ||
                    nested.last_component_name == name_token.value;
                if (names_qualifier && qualifier.type.valid()) {
                    named_type = qualifier.type;
                }
            }
            if (!named_type.valid() &&
                nested.scope.dependent_type.type.valid()) {
                named_type = nested.scope.dependent_type.type;
            }
            if (!named_type.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "unknown type name in qualified destructor-id",
                         name_token.loc);
                has_error = true;
            }
            consume();
        } else {
            diagnose(DiagnosticLevel::Error,
                     "expected destructor name after '~'",
                     current_loc());
            has_error = true;
        }
        if (has_template_keyword) {
            diagnose(DiagnosticLevel::Error,
                     "template disambiguator cannot name a destructor",
                     destructor_token.loc);
            has_error = true;
        }
        collect::ExprResult sem;
        sem.type = named_type.valid()
            ? named_type
            : collect_session_.file().unknown_type();
        sem.name = destructor_name;
        sem.qualified_name = true;
        sem.destructor_designator = true;
        sem.category = collect::ValueCategory::Invalid;
        sem.has_error = has_error;
        NodeId syntax = make_node(
            NodeKind::Identifier, begin, last_consumed_raw_end(), {},
            text_payload(destructor_name),
            has_error ? NodeFlagHasError : NodeFlagNone);
        return {syntax, std::move(sem)};
    }

    if (check(TokenType::OPERATOR_KW)) {
        ParsedOperatorFunctionId operator_id =
            *parse_operator_function_id();
        bool has_error = operator_id.has_error || nested.has_error;
        if (has_template_keyword && !check(TokenType::LESS_THAN)) {
            diagnose(DiagnosticLevel::Error,
                     "template disambiguator requires a template argument list",
                     operator_id.loc);
            has_error = true;
        }

        const collect::Session::TemplateInfo* info = nullptr;
        if (!nested.has_error && nested.scope.context.valid() &&
            check(TokenType::LESS_THAN)) {
            info = collect_session_.template_info_in_context(
                nested.scope.context,
                operator_id.name,
                /*include_parents=*/false);
        }
        if (info) {
            std::vector<const collect::Session::TemplateInfo*>
                function_candidates =
                    collect_session_.function_template_infos_for_name(
                        nested.scope.context,
                        operator_id.name,
                        /*include_parents=*/false);
            std::vector<collect::Session::TemplateArgument> arguments;
            std::vector<collect::CandidateExplicitTemplateArguments>
                candidate_arguments;
            const collect::Session::TemplateInfo* selected_info = info;
            bool parsed_arguments =
                parse_function_template_argument_list_for_candidates(
                    *info,
                    function_candidates,
                    arguments,
                    candidate_arguments,
                    operator_id.loc,
                    &selected_info);
            collect::ExprResult sem = parsed_arguments
                ? instantiate_template_id_expression_result(
                      *selected_info,
                      std::move(arguments),
                      operator_id.loc,
                      /*qualified_name=*/true,
                      nullptr,
                      function_candidates.empty() ? nullptr
                                                  : &function_candidates,
                      candidate_arguments.empty()
                          ? nullptr
                          : &candidate_arguments)
                : collect::ExprResult{};
            sem.has_error = sem.has_error || has_error || !parsed_arguments;
            sem.unparenthesized_id_or_member = true;
            NodeId syntax = make_node(
                NodeKind::Identifier,
                begin,
                last_consumed_raw_end(),
                {},
                text_payload(operator_id.name),
                sem.has_error ? NodeFlagHasError : NodeFlagNone);
            return {syntax, std::move(sem)};
        }

        collect::ExprResult sem;
        if (!nested.has_error && nested.scope.dependent_type.type.valid()) {
            bool parsed = true;
            if (check(TokenType::LESS_THAN)) {
                if (!has_template_keyword) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "missing 'template' disambiguator before dependent template name",
                        operator_id.loc);
                    has_error = true;
                }
                parsed =
                    parse_dependent_expression_template_argument_list(
                        operator_id.loc);
            }
            collect::ExprResult dependent;
            dependent.type = collect_session_.file().dependent_type(
                "dependent qualified operator");
            dependent.name = operator_id.name;
            dependent.qualified_name = true;
            dependent.dependent_value_qualifier = nested.scope.dependent_type;
            dependent.dependent_value_name =
                collect_session_.file().intern_name(operator_id.name);
            dependent.category = collect::ValueCategory::Dependent;
            dependent.has_error = has_error || !parsed;
            sem = collect_session_.make_dependent_expr(
                std::move(dependent), operator_id.loc);
        } else {
            sem = collect_session_.lookup_qualified_name(
                nested.has_error ? cir::DeclContextId{}
                                 : nested.scope.context,
                operator_id.name, operator_id.loc);
        }
        sem.has_error = sem.has_error || has_error;
        sem.unparenthesized_id_or_member = true;
        NodeId syntax = make_node(
            NodeKind::Identifier, begin, last_consumed_raw_end(), {},
            text_payload(operator_id.name),
            sem.has_error ? NodeFlagHasError : NodeFlagNone);
        return {syntax, std::move(sem)};
    }

    if (!is_identifier_token(current().type)) {
        diagnose(DiagnosticLevel::Error,
                 "expected a name after the nested name specifier",
                 current_loc());
        collect::ExprResult sem;
        sem.has_error = true;
        NodeId syntax = make_node(NodeKind::Identifier,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("<qualified-name>"),
                                  NodeFlagHasError);
        return {syntax, std::move(sem)};
    }

    Token terminal = current();
    if (has_template_keyword && peek(1).type != TokenType::LESS_THAN) {
        diagnose(DiagnosticLevel::Error,
                 "template disambiguator requires a template argument list",
                 terminal.loc);
        consume();
        collect::ExprResult sem =
            make_invalid_template_disambiguator_expr(collect_session_,
                                                     terminal.value);
        sem.unparenthesized_id_or_member = true;
        NodeId syntax = make_node(NodeKind::Identifier,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload(std::string(terminal.value)),
                                  NodeFlagHasError);
        return {syntax, std::move(sem)};
    }
    if (peek(1).type == TokenType::LESS_THAN) {
        const collect::Session::TemplateInfo* info = nullptr;
        if (!nested.has_error && nested.scope.context.valid()) {
            info = collect_session_.template_info_in_context(
                nested.scope.context,
                terminal.value,
                /*include_parents=*/false);
        }
        if (info) {
            std::vector<const collect::Session::TemplateInfo*>
                function_candidates;
            if (!info->is_class_template && !info->is_alias_template &&
                !info->is_variable_template && !info->is_concept) {
                function_candidates =
                    collect_session_.function_template_infos_for_name(
                        nested.scope.context,
                        terminal.value,
                        /*include_parents=*/false);
            }
            consume();
            std::vector<collect::Session::TemplateArgument> arguments;
            std::vector<collect::CandidateExplicitTemplateArguments>
                candidate_arguments;
            const collect::Session::TemplateInfo* selected_info = info;
            bool parsed_arguments =
                parse_function_template_argument_list_for_candidates(
                    *info,
                    function_candidates,
                    arguments,
                    candidate_arguments,
                    terminal.loc,
                    &selected_info);
            std::vector<collect::Session::TemplateArgument>
                canonical_concept_arguments;
            collect::ExprResult sem = parsed_arguments
                ? instantiate_template_id_expression_result(
                      *selected_info,
                      std::move(arguments),
                      terminal.loc,
                      /*qualified_name=*/true,
                      info->is_concept ? &canonical_concept_arguments
                                       : nullptr,
                      function_candidates.empty() ? nullptr
                                                  : &function_candidates,
                      candidate_arguments.empty()
                          ? nullptr
                          : &candidate_arguments)
                : collect::ExprResult{};
            sem.has_error = sem.has_error || !parsed_arguments;
            sem.unparenthesized_id_or_member = true;
            NodeId syntax = make_node(NodeKind::Identifier,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload(std::string(terminal.value)),
                                      sem.has_error ? NodeFlagHasError
                                                    : NodeFlagNone);
            if (parsed_arguments && info->is_concept && !sem.has_error) {
                record_constraint_concept_id_syntax(
                    syntax,
                    *info,
                    std::move(canonical_concept_arguments),
                    /*qualified_name=*/true);
            }
            return {syntax, std::move(sem)};
        }
        bool dependent_qualified_template_id =
            !nested.has_error && nested.scope.dependent_type.type.valid();
        if (dependent_qualified_template_id &&
            !has_template_keyword &&
            template_id_precedes_call(0)) {
            diagnose(DiagnosticLevel::Error,
                     "missing 'template' disambiguator before dependent template name",
                     terminal.loc);
            consume();
            bool parsed =
                parse_dependent_expression_template_argument_list(terminal.loc);
            (void)parsed;
            collect::ExprResult dependent;
            dependent.type = collect_session_.file().dependent_type(
                "dependent qualified template-id");
            dependent.name = std::string(terminal.value);
            dependent.qualified_name = true;
            dependent.category = collect::ValueCategory::Dependent;
            dependent.has_error = true;
            collect::ExprResult sem =
                collect_session_.make_dependent_expr(std::move(dependent),
                                                     terminal.loc);
            sem.unparenthesized_id_or_member = true;
            NodeId syntax = make_node(NodeKind::Identifier,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload(std::string(terminal.value)),
                                      NodeFlagHasError);
            return {syntax, std::move(sem)};
        }
        if (has_template_keyword && dependent_qualified_template_id) {
            consume();
            size_t argument_list_begin = 0;
            size_t argument_list_end = 0;
            std::vector<collect::Session::TemplateArgument> arguments;
            bool parsed =
                parse_dependent_expression_template_argument_list(
                    terminal.loc,
                    &argument_list_begin,
                    &argument_list_end,
                    &arguments);
            collect::ExprResult dependent;
            dependent.type = collect_session_.file().dependent_type(
                "dependent qualified template-id");
            dependent.name = std::string(terminal.value);
            dependent.qualified_name = true;
            dependent.dependent_value_qualifier =
                nested.scope.dependent_type;
            dependent.dependent_value_name =
                collect_session_.file().intern_name(terminal.value);
            dependent.category = collect::ValueCategory::Dependent;
            dependent.has_explicit_template_arguments = true;
            dependent.explicit_template_arguments =
                std::move(arguments);
            dependent.has_error = !parsed;
            collect::ExprResult sem =
                collect_session_.make_dependent_expr(std::move(dependent),
                                                     terminal.loc);
            sem.unparenthesized_id_or_member = true;
            NodeId syntax = make_node(NodeKind::Identifier,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload(std::string(terminal.value)),
                                      sem.has_error ? NodeFlagHasError
                                                    : NodeFlagNone);
            if (parsed && !sem.has_error) {
                record_dependent_constraint_concept_id_syntax(
                    syntax,
                    nested.scope.dependent_type,
                    terminal.value,
                    /*qualified_name=*/true,
                    argument_list_begin,
                    argument_list_end);
            }
            return {syntax, std::move(sem)};
        }
        if (has_template_keyword) {
            if (!nested.has_error) {
                diagnose(DiagnosticLevel::Error,
                         "template disambiguator names a non-template",
                         terminal.loc);
            }
            consume();
            bool parsed =
                parse_dependent_expression_template_argument_list(terminal.loc);
            (void)parsed;
            collect::ExprResult sem =
                make_invalid_template_disambiguator_expr(collect_session_,
                                                         terminal.value);
            sem.unparenthesized_id_or_member = true;
            NodeId syntax = make_node(NodeKind::Identifier,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload(std::string(terminal.value)),
                                      NodeFlagHasError);
            return {syntax, std::move(sem)};
        }
    }
    if (!nested.has_error && nested.scope.context.valid() &&
        lang_opts_.is_cxx_mode() &&
        (peek(1).type == TokenType::LEFT_PAREN ||
         peek(1).type == TokenType::LEFT_BRACE)) {
        const collect::Session::TemplateInfo* info =
            collect_session_.template_info_in_context(
                nested.scope.context,
                terminal.value,
                /*include_parents=*/false);
        bool is_primary_class = info && info->is_class_template &&
            !info->is_partial_specialization;
        bool is_deducible_alias = info && info->is_alias_template &&
            info->alias_deduction_projection.has_value();
        cir::TypeRef qualified_type =
            collect_session_.lookup_qualified_type_name_ref(
                nested.scope.context,
                terminal.value);
        bool concrete_type_shadows_template =
            qualified_type.valid() &&
            collect_session_.qualified_type_name_denotes_concrete_type(
                nested.scope.context,
                terminal.value,
                info);
        if ((is_primary_class || is_deducible_alias) &&
            !concrete_type_shadows_template) {
            consume();
            collect::ExprResult sem;
            sem.name = info->name;
            sem.entity = info->entity;
            sem.category = collect::ValueCategory::Type;
            sem.qualified_name = true;
            sem.suppress_argument_dependent_lookup = true;
            sem.unparenthesized_id_or_member = true;
            NodeId syntax = make_node(
                NodeKind::Identifier,
                begin,
                last_consumed_raw_end(),
                {},
                text_payload(std::string(terminal.value)));
            return {syntax, std::move(sem)};
        }
    }
    const BuiltinInfo* builtin_info =
        BuiltinRegistry::instance().lookup(terminal.value);
    const bool reserved_builtin_name =
        terminal.value.rfind("__builtin_", 0) == 0;
    const bool globally_qualified_builtin_call =
        nested.global_qualifier && nested.last_component_name.empty() &&
        !nested.has_error && reserved_builtin_name && builtin_info &&
        builtin_info->supported &&
        builtin_info->syntax == BuiltinSyntaxKind::Call &&
        peek(1).type == TokenType::LEFT_PAREN;
    consume();

    collect::ExprResult sem;
    if (globally_qualified_builtin_call) {
        sem.name = std::string(terminal.value);
        sem.category = collect::ValueCategory::FunctionDesignator;
        sem.qualified_name = true;
        sem.suppress_argument_dependent_lookup = true;
        sem.builtin_call_designator = true;
    } else if (!nested.has_error && nested.scope.dependent_type.type.valid()) {
        collect::ExprResult dependent;
        dependent.type =
            collect_session_.file().dependent_type("dependent qualified value");
        dependent.name = std::string(terminal.value);
        dependent.qualified_name = true;
        dependent.dependent_value_qualifier = nested.scope.dependent_type;
        dependent.dependent_value_name =
            collect_session_.file().intern_name(terminal.value);
        dependent.category = collect::ValueCategory::Dependent;
        sem = collect_session_.make_dependent_expr(std::move(dependent),
                                                   terminal.loc);
    } else {
        sem = collect_session_.lookup_qualified_name(
            nested.has_error ? cir::DeclContextId{} : nested.scope.context,
            terminal.value,
            terminal.loc);
        if (sem.has_error && nested.depends_on_template_parameter &&
            in_constraint_substitution_failure_context()) {
            note_constraint_substitution_failure();
        }
        if (sem.entity.valid()) {
            materialize_deferred_static_data_member_expr(sem);
        }
    }
    sem.unparenthesized_id_or_member = true;
    NodeId syntax = make_node(NodeKind::Identifier,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload(std::string(terminal.value)),
                              sem.has_error ? NodeFlagHasError : NodeFlagNone);
    return {syntax, std::move(sem)};
}

std::optional<cir::TypeRef> Parser::parse_cxx_qualified_type_name(
    TypeParseContext context) {
    ParsedNestedName nested = parse_nested_name_specifier();
    if (!nested.consumed_any) {
        return std::nullopt;
    }
    bool saw_template_keyword = false;
    if (check(TokenType::TEMPLATE)) {
        consume();
        saw_template_keyword = true;
    }
    if (!is_identifier_token(current().type)) {
        diagnose(DiagnosticLevel::Error,
                 "expected a type name after the nested name specifier",
                 current_loc());
        return collect_session_.type_ref(
            collect_session_.file().unknown_type());
    }

    Token terminal = current();
    if (!nested.has_error && nested.scope.dependent_type.type.valid()) {
        consume();
        std::vector<collect::Session::TemplateArgument> template_arguments;
        if (check(TokenType::LESS_THAN)) {
            if (!parse_dependent_type_template_argument_list(
                    template_arguments,
                    terminal.loc)) {
                return collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            }
        } else if (saw_template_keyword) {
            diagnose(DiagnosticLevel::Error,
                     "template disambiguator requires a template argument list",
                     terminal.loc);
            return collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
        if (!context.is_type_only()) {
            diagnose(DiagnosticLevel::Error,
                     "missing 'typename' before dependent type name",
                     terminal.loc);
            return collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
        cir::TypeId dependent_name =
            collect_session_.file().dependent_name_type(
                nested.scope.dependent_type,
                terminal.value,
                std::move(template_arguments),
                false);
        return collect_session_.type_ref(dependent_name);
    }

    cir::TypeRef qualifier;
    if (nested.scope.entity.valid() &&
        collect_session_.file().valid(nested.scope.entity)) {
        qualifier = collect_session_.type_ref(
            collect_session_.file().entity(nested.scope.entity).type);
    }
    if (!qualifier.valid() && nested.scope.context.valid()) {
        cir::EntityId owner = collect_session_.file()
            .decl_context(nested.scope.context)
            .owner;
        if (owner.valid() && collect_session_.file().valid(owner) &&
            collect_session_.file().entity(owner).kind ==
                cir::EntityKind::Record) {
            qualifier = collect_session_.type_ref(
                collect_session_.file().entity(owner).type);
        }
    }

    if (!nested.has_error && nested.scope.context.valid() &&
        peek(1).type == TokenType::LESS_THAN) {
        const collect::Session::TemplateInfo* info =
            collect_session_.template_info_in_context(
                nested.scope.context,
                terminal.value,
                /*include_parents=*/false);
        if (info && (info->is_class_template || info->is_alias_template)) {
            consume();
            cir::TypeRef instantiated_or_dependent =
                instantiate_or_defer_qualified_type_template(
                    *info, qualifier, terminal.value, terminal.loc);
            if (instantiated_or_dependent.valid()) {
                return instantiated_or_dependent;
            }
            return collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
        if (collect_session_
                .current_instantiation_context_has_dependent_bases(
                    nested.scope.context) &&
            qualifier.valid()) {
            consume();
            std::vector<collect::Session::TemplateArgument>
                template_arguments;
            if (!parse_dependent_type_template_argument_list(
                    template_arguments,
                    terminal.loc)) {
                return collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            }
            return collect_session_.type_ref(
                collect_session_.file().dependent_name_type(
                    qualifier,
                    terminal.value,
                    std::move(template_arguments),
                    true));
        }
        diagnose(DiagnosticLevel::Error,
                 saw_template_keyword
                     ? "template disambiguator names a non-template"
                     : "qualified type name is not a template",
                 terminal.loc);
        consume();
        std::vector<collect::Session::TemplateArgument> ignored_arguments;
        (void)parse_dependent_type_template_argument_list(
            ignored_arguments,
            terminal.loc);
        return collect_session_.type_ref(
            collect_session_.file().unknown_type());
    }
    if (saw_template_keyword) {
        diagnose(DiagnosticLevel::Error,
                 "template disambiguator requires a template argument list",
                 terminal.loc);
        consume();
        return collect_session_.type_ref(
            collect_session_.file().unknown_type());
    }

    consume();
    cir::TypeRef type = !nested.has_error && nested.scope.context.valid()
        ? collect_session_.lookup_qualified_type_name_ref(
              nested.scope.context, terminal.value)
        : cir::TypeRef{};
    if (!type.valid() && !nested.has_error &&
        nested.scope.context.valid() && qualifier.valid() &&
        collect_session_
            .current_instantiation_context_has_dependent_bases(
                nested.scope.context)) {
        type = collect_session_.type_ref(
            collect_session_.file().dependent_name_type(
                qualifier,
                terminal.value,
                {},
                true));
    }
    if (!type.valid()) {
        diagnose(DiagnosticLevel::Error,
                 "no type named '" + std::string(terminal.value) +
                     (context.origin ==
                              TypeParseContext::Origin::ExplicitTypename
                          ? "' in typename qualifier"
                          : "' in nested-name-specifier"),
                 terminal.loc);
        type = collect_session_.type_ref(
            collect_session_.file().unknown_type());
    }
    return type;
}

std::optional<Parser::QualifiedTypeLookahead> Parser::peek_cxx_qualified_type(
    size_t start_offset) {
    size_t offset = start_offset;
    bool global_qualifier = false;
    if (peek(offset).type == TokenType::SCOPE_RESOLUTION) {
        global_qualifier = true;
        ++offset;
    }
    std::vector<std::string_view> qualifiers;
    while (is_identifier_token(peek(offset).type) &&
           peek(offset + 1).type == TokenType::SCOPE_RESOLUTION &&
           peek(offset + 2).type != TokenType::MULTIPLY) {
        qualifiers.push_back(peek(offset).value);
        offset += 2;
    }
    if (is_identifier_token(peek(offset).type) &&
        peek(offset + 1).type == TokenType::LESS_THAN &&
        template_id_precedes_scope(offset)) {
        const collect::Session::TemplateInfo* info = nullptr;
        if (qualifiers.empty() && !global_qualifier) {
            info = collect_session_.template_info_for_name(peek(offset).value);
        } else {
            info = collect_session_.peek_qualified_template_info(
                global_qualifier,
                qualifiers,
                peek(offset).value);
        }
        if (!info || !info->is_class_template ||
            !info->pattern_record.valid() ||
            !collect_session_.file().valid(info->pattern_record)) {
            return std::nullopt;
        }
        size_t scope_offset = template_id_scope_offset(offset);
        size_t terminal_offset = scope_offset + 1;
        if (!is_identifier_token(peek(terminal_offset).type)) {
            return std::nullopt;
        }

        if (peek(terminal_offset + 1).type ==
            TokenType::SCOPE_RESOLUTION) {
            return std::nullopt;
        }
        cir::DeclContextId context =
            collect_session_.file()
                .entity(info->pattern_record)
                .semantic_context;
        if (!context.valid()) {
            return std::nullopt;
        }
        cir::TypeRef type = collect_session_.lookup_qualified_type_name_ref(
            context,
            peek(terminal_offset).value);
        const collect::Session::TemplateInfo* terminal_info = nullptr;
        bool terminal_is_deduced_placeholder = false;
        if (peek(terminal_offset + 1).type != TokenType::LESS_THAN) {
            terminal_info = collect_session_.template_info_in_context(
                context,
                peek(terminal_offset).value,
                /*include_parents=*/false);
            terminal_is_deduced_placeholder =
                terminal_info &&
                ((terminal_info->is_class_template &&
                  !terminal_info->is_partial_specialization) ||
                 (terminal_info->is_alias_template &&
                  terminal_info->alias_deduction_projection.has_value()));
        }

        if (type.valid() &&
            peek(terminal_offset + 1).type != TokenType::LESS_THAN &&
            (!terminal_is_deduced_placeholder ||
             collect_session_.qualified_type_name_denotes_concrete_type(
                 context,
                 peek(terminal_offset).value,
                 terminal_info))) {
            QualifiedTypeLookahead result;
            result.type = type;
            result.tokens_to_consume =
                terminal_offset + 1 - start_offset;
            result.terminal_context = context;
            result.terminal_name =
                std::string(peek(terminal_offset).value);
            result.terminal_loc = peek(terminal_offset).loc;
            return result;
        }
        if (terminal_is_deduced_placeholder) {
            QualifiedTypeLookahead result;
            result.template_info = terminal_info;
            result.is_deduced_placeholder = true;
            result.tokens_to_consume =
                terminal_offset + 1 - start_offset;
            return result;
        }
        if (!type.valid() &&
            peek(terminal_offset + 1).type == TokenType::LESS_THAN) {
            const collect::Session::TemplateInfo* terminal_info =
                collect_session_.template_info_in_context(
                    context,
                    peek(terminal_offset).value,
                    /*include_parents=*/false);
            if (terminal_info &&
                (terminal_info->is_class_template ||
                 terminal_info->is_alias_template)) {
                QualifiedTypeLookahead result;
                result.template_info = terminal_info;
                result.tokens_to_consume =
                    terminal_offset + 1 - start_offset;
                return result;
            }
        }
        if (type.valid()) {
            QualifiedTypeLookahead result;
            result.type = type;
            result.tokens_to_consume = terminal_offset + 1 - start_offset;
            result.terminal_context = context;
            result.terminal_name =
                std::string(peek(terminal_offset).value);
            result.terminal_loc = peek(terminal_offset).loc;
            return result;
        }
        return std::nullopt;
    }
    if (qualifiers.empty() && !global_qualifier) {
        return std::nullopt;
    }
    if (!is_identifier_token(peek(offset).type)) {
        return std::nullopt;
    }
    cir::DeclContextId terminal_context;
    cir::TypeRef type = collect_session_.peek_qualified_type_ref(
        global_qualifier, qualifiers, peek(offset).value,
        &terminal_context);
    const collect::Session::TemplateInfo* exact_terminal_info =
        terminal_context.valid()
        ? collect_session_.template_info_in_context(
              terminal_context,
              peek(offset).value,
              /*include_parents=*/false)
        : nullptr;
    bool exact_terminal_is_deduced_placeholder =
        exact_terminal_info &&
        ((exact_terminal_info->is_class_template &&
          !exact_terminal_info->is_partial_specialization) ||
         (exact_terminal_info->is_alias_template &&
          exact_terminal_info->alias_deduction_projection.has_value()));
    if (type.valid() &&
        peek(offset + 1).type != TokenType::LESS_THAN &&
        (!exact_terminal_is_deduced_placeholder ||
         collect_session_.qualified_type_name_denotes_concrete_type(
             terminal_context,
             peek(offset).value,
             exact_terminal_info))) {
        QualifiedTypeLookahead result;
        result.type = type;
        result.tokens_to_consume = offset + 1 - start_offset;
        result.terminal_context = terminal_context;
        result.terminal_name = std::string(peek(offset).value);
        result.terminal_loc = peek(offset).loc;
        return result;
    }
    if (peek(offset + 1).type != TokenType::LESS_THAN) {
        const collect::Session::TemplateInfo* info =
            exact_terminal_is_deduced_placeholder
            ? exact_terminal_info
            : collect_session_.peek_qualified_template_info(
                  global_qualifier, qualifiers, peek(offset).value);
        bool is_primary_class = info && info->is_class_template &&
            !info->is_partial_specialization;
        bool is_deducible_alias = info && info->is_alias_template &&
            info->alias_deduction_projection.has_value();
        if (is_primary_class || is_deducible_alias) {
            QualifiedTypeLookahead result;
            result.template_info = info;
            result.is_deduced_placeholder = true;
            result.tokens_to_consume = offset + 1 - start_offset;
            return result;
        }
    }
    if (peek(offset + 1).type == TokenType::LESS_THAN) {
        const collect::Session::TemplateInfo* info =
            collect_session_.peek_qualified_template_info(
                global_qualifier, qualifiers, peek(offset).value);
        if (info &&
            (info->is_class_template || info->is_alias_template)) {
            QualifiedTypeLookahead result;
            result.template_info = info;
            result.tokens_to_consume = offset + 1 - start_offset;
            return result;
        }
    }
    if (!type.valid()) {

        if (peek(offset + 1).type == TokenType::LESS_THAN) {
            const collect::Session::TemplateInfo* info =
                collect_session_.peek_qualified_template_info(
                    global_qualifier, qualifiers, peek(offset).value);
            if (info &&
                (info->is_class_template || info->is_alias_template)) {
                QualifiedTypeLookahead result;
                result.template_info = info;
                result.tokens_to_consume = offset + 1 - start_offset;
                return result;
            }
        }
        return std::nullopt;
    }
    QualifiedTypeLookahead result;
    result.type = type;
    result.tokens_to_consume = offset + 1 - start_offset;
    result.terminal_context = terminal_context;
    result.terminal_name = std::string(peek(offset).value);
    result.terminal_loc = peek(offset).loc;
    return result;
}

} // namespace aburi::syntax
