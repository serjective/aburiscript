#include "parser.h"
#include "../abi/darwin_blocks.h"
#include "../helpers/auto_type_utils.h"
#include "../collect/collect_templates_internal.h"
#include "../collect/lookup_engine.h"

#include <cstdint>

// Parser expression helpers are defined in parser/parser.cpp.
std::vector<uint32_t> decode_utf8_codepoints(const std::string& text);
bool token_can_start_cast_operand(TokenType tok);
bool is_integer_literal(TokenType tok);
bool is_imaginary_integer_literal(TokenType tok);
TokenType imaginary_integer_to_real_token(TokenType tok);
bool is_floating_literal(TokenType tok);
bool is_assignment_token(TokenType tok);
bool is_unary_operator_token(TokenType tok);
std::shared_ptr<CType> getNumericTypeConstant(Token tok, TypeContext* type_ctx);

namespace {
struct TemplateArgumentGroupGuard {
    Parser& parser;
    bool active = false;

    explicit TemplateArgumentGroupGuard(Parser& parser)
        : parser(parser),
          active(parser.is_parsing_template_argument_expression()) {
        if (active) {
            parser.enter_template_argument_group();
        }
    }

    ~TemplateArgumentGroupGuard() {
        if (active) {
            parser.leave_template_argument_group();
        }
    }
};

bool try_get_fold_operator(const Token& token, BinOpTypes& op_out) {
    std::string spelling = token.value;
    op_out = string2bop(spelling);
    return op_out != BinOpTypes::UNKNOWN &&
           op_out != BinOpTypes::QUESTION;
}

std::unique_ptr<TemplateParameterDecl> clone_template_parameter_for_shape_check(
    ASTContext& ast_ctx,
    const TemplateParameterDecl* parameter) {
    if (!parameter) {
        return nullptr;
    }

    switch (parameter->get_kind()) {
        case DeclKind::TemplateTypeParmDecl: {
            auto* type_param =
                static_cast<const TemplateTypeParmDecl*>(parameter);
            auto cloned_type = std::make_shared<TemplateTypeParmType>(
                type_param->name,
                type_param->depth,
                type_param->index,
                type_param->is_parameter_pack);
            auto cloned = make_ast<TemplateTypeParmDecl>(
                ast_ctx,
                type_param->name,
                type_param->depth,
                type_param->index,
                cloned_type,
                type_param->is_parameter_pack,
                type_param->location);
            cloned_type->parameter_decl = cloned.get();
            return cloned;
        }
        case DeclKind::TemplateNonTypeParmDecl: {
            auto* non_type_param =
                static_cast<const TemplateNonTypeParmDecl*>(parameter);
            std::shared_ptr<Symbol> cloned_symbol = nullptr;
            if (non_type_param->sym) {
                cloned_symbol = std::make_shared<Symbol>(
                    non_type_param->sym->name,
                    non_type_param->sym->kind,
                    non_type_param->sym->type,
                    non_type_param->sym->storage_class,
                    non_type_param->sym->linkage,
                    non_type_param->sym->is_inline != 0);
                cloned_symbol->is_constexpr = non_type_param->sym->is_constexpr;
                cloned_symbol->set_language_linkage(
                    non_type_param->sym->get_language_linkage());
            }
            return make_ast<TemplateNonTypeParmDecl>(
                ast_ctx,
                non_type_param->name,
                non_type_param->depth,
                non_type_param->index,
                non_type_param->type,
                cloned_symbol,
                non_type_param->is_parameter_pack,
                non_type_param->location);
        }
        case DeclKind::TemplateTemplateParmDecl: {
            auto* template_param =
                static_cast<const TemplateTemplateParmDecl*>(parameter);
            TemplateParameterList cloned_parameters;
            cloned_parameters.reserve(template_param->parameters.size());
            for (const auto& inner_parameter : template_param->parameters) {
                cloned_parameters.push_back(
                    clone_template_parameter_for_shape_check(
                        ast_ctx,
                        inner_parameter.get()));
            }
            return make_ast<TemplateTemplateParmDecl>(
                ast_ctx,
                std::move(cloned_parameters),
                template_param->name,
                template_param->depth,
                template_param->index,
                template_param->uses_typename_keyword,
                template_param->is_parameter_pack,
                template_param->location);
        }
        default:
            return nullptr;
    }
}

TemplateParameterList clone_active_template_parameters_for_shape_check(
    ASTContext& ast_ctx,
    const std::vector<std::vector<const TemplateParameterDecl*>>&
        active_parameter_stack) {
    TemplateParameterList parameters;
    for (const auto& frame : active_parameter_stack) {
        for (const auto* parameter : frame) {
            if (auto cloned =
                    clone_template_parameter_for_shape_check(ast_ctx, parameter)) {
                parameters.push_back(std::move(cloned));
            }
        }
    }
    return parameters;
}

bool expr_references_active_parameter_pack(
    ASTContext* ast_ctx,
    const Expr* expr,
    const std::vector<std::vector<const TemplateParameterDecl*>>&
        active_parameter_stack) {
    if (!ast_ctx || !expr) {
        return false;
    }

    auto active_parameters = clone_active_template_parameters_for_shape_check(
        *ast_ctx,
        active_parameter_stack);
    template_sema_internal::TemplatePackExpansionShape shape;
    return template_sema_internal::collect_pack_expansion_shape_in_expr(
               expr,
               active_parameters,
               shape) &&
           !shape.has_unsupported_dependency &&
           !shape.referenced_parameters.empty();
}

} // namespace

bool Parser::skip_balanced_group_for_template_id_lookahead(
    size_t& offset,
    TokenType open_tok,
    TokenType close_tok) {
    if (peek_token_shortcut(offset).type != open_tok) {
        return false;
    }
    size_t depth = 0;
    while (peek_token_shortcut(offset).type != TokenType::Eof) {
        TokenType tok = peek_token_shortcut(offset).type;
        if (tok == open_tok) {
            ++depth;
        } else if (tok == close_tok) {
            --depth;
            ++offset;
            if (depth == 0) {
                return true;
            }
            continue;
        }
        ++offset;
    }
    return false;
}

bool Parser::skip_template_argument_list_for_expression_probe(size_t& offset) {
    if (peek_token_shortcut(offset).type != TokenType::LESS_THAN) {
        return false;
    }
    ++offset;
    size_t angle_depth = 1;
    while (peek_token_shortcut(offset).type != TokenType::Eof) {
        TokenType tok = peek_token_shortcut(offset).type;
        switch (tok) {
            case TokenType::LESS_THAN:
                ++angle_depth;
                ++offset;
                break;
            case TokenType::GREATER_THAN:
                --angle_depth;
                ++offset;
                if (angle_depth == 0) {
                    return true;
                }
                break;
            case TokenType::RIGHT_SHIFT:
                if (angle_depth <= 2) {
                    ++offset;
                    return true;
                }
                angle_depth -= 2;
                ++offset;
                break;
            case TokenType::LEFT_PAREN:
                if (!skip_balanced_group_for_template_id_lookahead(
                        offset,
                        TokenType::LEFT_PAREN,
                        TokenType::RIGHT_PAREN)) {
                    return false;
                }
                break;
            case TokenType::LEFT_BRACE:
                if (!skip_balanced_group_for_template_id_lookahead(
                        offset,
                        TokenType::LEFT_BRACE,
                        TokenType::RIGHT_BRACE)) {
                    return false;
                }
                break;
            case TokenType::LEFT_BRACKET:
                if (!skip_balanced_group_for_template_id_lookahead(
                        offset,
                        TokenType::LEFT_BRACKET,
                        TokenType::RIGHT_BRACKET)) {
                    return false;
                }
                break;
            default:
                ++offset;
                break;
        }
    }
    return false;
}

void Parser::retain_type_specifier_decl_if_needed(DeclarationParser& decl_parser) {
    if (!ast_ctx) {
        return;
    }
    if (decl_parser.cpp_record_obj) {
        ast_ctx->retain_external_decl(std::move(decl_parser.cpp_record_obj));
    }
    if (decl_parser.struct_obj) {
        ast_ctx->retain_external_decl(std::move(decl_parser.struct_obj));
    }
    if (decl_parser.enum_obj) {
        ast_ctx->retain_external_decl(std::move(decl_parser.enum_obj));
    }
    for (auto& param_parser : decl_parser.func_args) {
        if (!param_parser) {
            continue;
        }
        retain_type_specifier_decl_if_needed(*param_parser);
    }
}

TemplateParameterList Parser::lower_generic_lambda_parameter_placeholders(
    std::vector<std::unique_ptr<Decl>>& parameters,
    TemplateParameterList template_parameters,
    const std::string& closure_name,
    uint32_t parameter_depth,
    SrcLoc lambda_loc) {
    if (!ast_ctx) {
        error_custloc(
            "internal error: missing AST context for generic lambda",
            lambda_loc);
    }

    for (auto& parameter : parameters) {
        auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
        if (!param_decl || !param_decl->type ||
            !auto_type_utils::has_cxx_auto_type(param_decl->type.get_shared())) {
            continue;
        }

        auto rewritten_type = auto_type_utils::replace_cxx_auto_placeholders_with_callback(
            param_decl->type.get_shared(),
            [&](size_t) -> QualType {
                const uint32_t parameter_index =
                    static_cast<uint32_t>(template_parameters.size());
                std::string invented_name =
                    closure_name + "__T" + std::to_string(parameter_index);
                auto parameter_type = std::make_shared<TemplateTypeParmType>(
                    invented_name,
                    parameter_depth,
                    parameter_index,
                    false);
                auto parameter_decl = make_ast<TemplateTypeParmDecl>(
                    *ast_ctx,
                    invented_name,
                    parameter_depth,
                    parameter_index,
                    parameter_type,
                    false,
                    param_decl->location);
                parameter_type->parameter_decl = parameter_decl.get();
                template_parameters.push_back(std::move(parameter_decl));
                return QualType(parameter_type);
            });

        param_decl->type = QualType(
            rewritten_type,
            param_decl->type.get_qualifiers());
        if (param_decl->sym) {
            param_decl->sym->type = param_decl->type;
        }
    }

    return template_parameters;
}

bool Parser::is_lambda_declarator_parameter_clause_ahead() {
    if (!gentle_check(TokenType::LEFT_PAREN)) {
        return false;
    }

    size_t offset = 0;
    size_t depth = 0;
    while (true) {
        TokenType type = peek_token_shortcut(offset).type;
        if (type == TokenType::Eof) {
            return false;
        }
        if (type == TokenType::LEFT_PAREN) {
            ++depth;
        } else if (type == TokenType::RIGHT_PAREN) {
            if (depth == 0) {
                return false;
            }
            --depth;
            if (depth == 0) {
                ++offset;
                break;
            }
        }
        ++offset;
    }

    Token after = peek_token_shortcut(offset);
    if (after.type == TokenType::LEFT_BRACE ||
        after.type == TokenType::NOEXCEPT_KW ||
        after.type == TokenType::CONSTEXPR_KW ||
        after.type == TokenType::CONSTEVAL_KW ||
        after.type == TokenType::ARROW ||
        after.type == TokenType::MUTABLE_KW ||
        after.type == TokenType::REQUIRES_KW) {
        return true;
    }
    return after.type == TokenType::IDENTIFIER && after.value == "mutable";
}

std::unique_ptr<Expr> Parser::maybe_parse_pack_expansion_expression(
    std::unique_ptr<Expr> expr) {
    if (!gentle_check(TokenType::ELLIPSIS)) {
        return expr;
    }
    if (!is_in_template_pattern_context()) {
        error_custloc(
            "pack expansion is only supported in template patterns",
            current_token().loc);
    }
    SrcLoc expansion_loc = expr ? expr->location : current_token().loc;
    check_and_consume(TokenType::ELLIPSIS);
    return collect_->collect_pack_expansion_expression(
        std::move(expr),
        expansion_loc);
}

std::unique_ptr<Expr> Parser::parse_assignment_expression_with_optional_pack_expansion() {
    return maybe_parse_pack_expansion_expression(parse_assignment_expression());
}

std::unique_ptr<Expr> Parser::parse_call_argument_expression() {
    if (is_cxx_mode_active() && gentle_check(TokenType::LEFT_BRACE)) {
        return maybe_parse_pack_expansion_expression(parse_init_list());
    }
    return parse_assignment_expression_with_optional_pack_expansion();
}

std::unique_ptr<Expr> Parser::try_parse_fold_expression(SrcLoc lparen_loc) {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    RevertingTentativeParsingAction tentative(*this);
    try {
        auto build_fold =
            [&](BinOpTypes op,
                FoldDirection direction,
                std::unique_ptr<Expr> pattern,
                std::unique_ptr<Expr> init) -> std::unique_ptr<Expr> {
                if (!is_in_template_pattern_context()) {
                    error_custloc(
                        "fold expression is only supported in template patterns",
                        lparen_loc);
                }
                tentative.commit();
                return collect_->collect_fold_expression(
                    op,
                    direction,
                    std::move(pattern),
                    std::move(init),
                    lparen_loc);
            };

        if (gentle_check(TokenType::ELLIPSIS)) {
            advance();
            BinOpTypes op = BinOpTypes::UNKNOWN;
            if (!try_get_fold_operator(current_token(), op)) {
                return nullptr;
            }
            advance();

            auto pattern = parse_cast_expression();
            if (!pattern) {
                error_custloc(
                    "expected fold-expression pattern after fold operator",
                    current_token().loc);
            }
            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                error_custloc(
                    "expected ')' after fold-expression pattern",
                    current_token().loc);
            }

            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                return nullptr;
            }
            return build_fold(
                op,
                FoldDirection::Left,
                std::move(pattern),
                nullptr);
        }

        auto first_operand = parse_cast_expression();
        if (!first_operand) {
            return nullptr;
        }

        BinOpTypes op = BinOpTypes::UNKNOWN;
        if (!try_get_fold_operator(current_token(), op)) {
            return nullptr;
        }
        advance();

        if (!gentle_check(TokenType::ELLIPSIS)) {
            return nullptr;
        }
        advance();

        if (gentle_check(TokenType::RIGHT_PAREN)) {
            return build_fold(
                op,
                FoldDirection::Right,
                std::move(first_operand),
                nullptr);
        }

        BinOpTypes trailing_op = BinOpTypes::UNKNOWN;
        if (!try_get_fold_operator(current_token(), trailing_op)) {
            error_custloc(
                "expected fold operator after '...'",
                current_token().loc);
        }
        if (trailing_op != op) {
            error_custloc(
                "fold expression requires the same operator on both sides of '...'",
                current_token().loc);
        }
        advance();

        auto other_operand = parse_cast_expression();
        if (!other_operand) {
            error_custloc(
                "expected fold-expression initializer",
                current_token().loc);
        }
        if (!gentle_check(TokenType::RIGHT_PAREN)) {
            return nullptr;
        }
        bool first_is_pack = expr_references_active_parameter_pack(
            ast_ctx.get(),
            first_operand.get(),
            active_template_parameter_stack_);
        bool second_is_pack = expr_references_active_parameter_pack(
            ast_ctx.get(),
            other_operand.get(),
            active_template_parameter_stack_);
        if (first_is_pack == second_is_pack) {
            error_custloc(
                "binary fold expression requires exactly one operand to contain an unexpanded parameter pack",
                lparen_loc);
        }
        if (first_is_pack) {
            return build_fold(
                op,
                FoldDirection::Right,
                std::move(first_operand),
                std::move(other_operand));
        }
        return build_fold(
            op,
            FoldDirection::Left,
            std::move(other_operand),
            std::move(first_operand));
    } catch (const ParseError&) {
        return nullptr;
    } catch (const FatalErrorLimitReached&) {
        throw;
    }
}

std::unique_ptr<Expr> Parser::try_parse_cpp_type_construction_expression() {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    SrcLoc loc = current_token().loc;
    auto qualified_id_brace_scan = [&]() {
        struct Result {
            bool is_qualified = false;
            bool followed_by_left_brace = false;
            bool followed_by_left_paren = false;
        } result;

        auto skip_template_argument_list_at = [&](size_t& at) -> bool {
            if (peek_token_shortcut(at).type != TokenType::LESS_THAN) {
                return true;
            }

            std::vector<TokenType> close_stack;
            close_stack.push_back(TokenType::GREATER_THAN);
            ++at;
            while (!close_stack.empty()) {
                TokenType tok = peek_token_shortcut(at).type;
                if (tok == TokenType::Eof) {
                    return false;
                }

                TokenType expected_close = close_stack.back();
                if (expected_close == TokenType::GREATER_THAN) {
                    if (tok == TokenType::GREATER_THAN) {
                        close_stack.pop_back();
                        ++at;
                        continue;
                    }
                    if (tok == TokenType::RIGHT_SHIFT) {
                        close_stack.pop_back();
                        if (!close_stack.empty() &&
                            close_stack.back() == TokenType::GREATER_THAN) {
                            close_stack.pop_back();
                        }
                        ++at;
                        continue;
                    }
                    if (tok == TokenType::LESS_THAN) {
                        close_stack.push_back(TokenType::GREATER_THAN);
                        ++at;
                        continue;
                    }
                } else if (tok == expected_close) {
                    close_stack.pop_back();
                    ++at;
                    continue;
                }

                if (tok == TokenType::LEFT_PAREN) {
                    close_stack.push_back(TokenType::RIGHT_PAREN);
                } else if (tok == TokenType::LEFT_BRACKET) {
                    close_stack.push_back(TokenType::RIGHT_BRACKET);
                } else if (tok == TokenType::LEFT_BRACE) {
                    close_stack.push_back(TokenType::RIGHT_BRACE);
                }
                ++at;
            }
            return true;
        };

        size_t offset = 0;
        auto consume_scope_at = [&](size_t& at) -> bool {
            Token tok = peek_token_shortcut(at);
            if (tok.type == TokenType::SCOPE_RESOLUTION) {
                ++at;
                return true;
            }
            if (tok.type == TokenType::COLON &&
                peek_token_shortcut(at + 1).type == TokenType::COLON) {
                at += 2;
                return true;
            }
            return false;
        };

        bool saw_scope = consume_scope_at(offset);
        if (peek_token_shortcut(offset).type != TokenType::IDENTIFIER) {
            return result;
        }
        ++offset;
        if (!skip_template_argument_list_at(offset)) {
            return result;
        }
        while (consume_scope_at(offset)) {
            saw_scope = true;
            if (peek_token_shortcut(offset).type == TokenType::TEMPLATE) {
                ++offset;
            }
            if (peek_token_shortcut(offset).type != TokenType::IDENTIFIER) {
                return result;
            }
            ++offset;
            if (!skip_template_argument_list_at(offset)) {
                return result;
            }
        }
        result.is_qualified = saw_scope;
        TokenType following_token = peek_token_shortcut(offset).type;
        result.followed_by_left_brace = following_token == TokenType::LEFT_BRACE;
        result.followed_by_left_paren = following_token == TokenType::LEFT_PAREN;
        return result;
    };
    // Keep non-construction qualified-ids on the existing qualified-id expression
    // path. Tentative declaration parsing can diagnose or attach semantic
    // state even when reverted, so only probe qualified type construction
    // forms such as `N::T{}` and `N::T(...)`.
    auto qualified_scan = qualified_id_brace_scan();
    if (qualified_scan.is_qualified &&
        !qualified_scan.followed_by_left_brace &&
        !qualified_scan.followed_by_left_paren) {
        return nullptr;
    }
    if (!qualified_scan.is_qualified &&
        current_token().type == TokenType::IDENTIFIER &&
        !qualified_scan.followed_by_left_paren &&
        !qualified_scan.followed_by_left_brace) {
        return nullptr;
    }
    if (starts_with_cpp_dependent_qualified_call_expression()) {
        return nullptr;
    }

    RevertingTentativeParsingAction tentative(*this);
    try {
        DeclarationParser parse_decl(this);
        auto parsed_type = parse_decl.parse_declaration(false);
        if (!parsed_type ||
            !parse_decl.name.empty() ||
            parse_decl.str_class != StorageClass::NONE) {
            return nullptr;
        }

        QualType target_type(parsed_type, parse_decl.qualifiers);
        // Dependent qualified-ids are expressions unless `typename` made the
        // type interpretation explicit; otherwise calls like Box<T>::f() would
        // be misparsed as unresolved type construction.
        if (auto dependent_name =
                dyn_cast_shared<DependentNameType>(target_type.get_shared());
            dependent_name && !dependent_name->requires_typename_keyword) {
            return nullptr;
        }
        if (gentle_check(TokenType::LEFT_PAREN)) {
            advance(); // consume '('
            std::vector<std::unique_ptr<Expr>> args;
            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                TemplateArgumentGroupGuard group_guard(*this);
                do {
                    auto arg = parse_call_argument_expression();
                    args.push_back(std::move(arg));
                } while (gentle_check_and_consume(TokenType::COMMA));
            }
            check_and_consume(TokenType::RIGHT_PAREN);
            retain_type_specifier_decl_if_needed(parse_decl);
            tentative.commit();
            return collect_->collect_cpp_function_style_cast(
                target_type,
                std::move(args),
                loc);
        }

        if (gentle_check(TokenType::LEFT_BRACE)) {
            auto init_expr = parse_init_list();
            auto* init_list = dyn_cast<InitListExpr>(init_expr.get());
            if (!init_list) {
                return nullptr;
            }
            auto owned_init_list = std::unique_ptr<InitListExpr>(
                static_cast<InitListExpr*>(init_expr.release()));
            retain_type_specifier_decl_if_needed(parse_decl);
            tentative.commit();
            return collect_->collect_cpp_type_list_initialization_expression(
                target_type,
                std::move(owned_init_list),
                loc);
        }
    } catch (const ParseError&) {
    } catch (const FatalErrorLimitReached&) {
        throw;
    }

    return nullptr;
}

std::unique_ptr<Expr> Parser::parse_cpp_qualified_primary_expression() {
    SrcLoc qualified_loc = current_token().loc;
    auto current_scope = collect_->collect_current_scope();
    auto current_context = collect_->get_current_decl_context();

    auto parse_component =
        [&](bool preceded_by_template_keyword) -> CppQualifiedNameComponent {
            if (!gentle_check(TokenType::IDENTIFIER) &&
                !gentle_check(TokenType::OPERATOR_KW)) {
                error_custloc(
                    "expected identifier after '::' in qualified-id expression",
                    current_token().loc);
            }
            CppQualifiedNameComponent component;
            component.loc = current_token().loc;
            component.preceded_by_template_keyword = preceded_by_template_keyword;
            if (gentle_check(TokenType::OPERATOR_KW)) {
                auto operator_name = try_parse_cpp_operator_function_id_name();
                if (!operator_name) {
                    error_custloc(
                        "expected operator-function-id after '::' in qualified-id expression",
                        component.loc);
                }
                component.name = std::move(*operator_name);
                return component;
            }

            component.name = current_token().value;
            advance();
            if (gentle_check(TokenType::LESS_THAN)) {
                RevertingTentativeParsingAction tentative(*this);
                auto parsed_arguments = parse_cpp_template_argument_list();
                bool scope_after_template_id = is_cpp_scope_resolution_here();
                if (scope_after_template_id) {
                    tentative.commit();
                    component.has_template_argument_list = true;
                    component.template_arguments = std::move(parsed_arguments);
                }
            }
            return component;
        };

    bool has_global_qualifier = false;
    std::optional<CppQualifiedOwnerSeed> initial_owner;
    std::vector<CppQualifiedNameComponent> components;
    if (gentle_check(TokenType::DECLTYPE_KW)) {
        SrcLoc decltype_loc = current_token().loc;
        QualType owner_type = parse_cpp_decltype_type_specifier();
        if (!is_cpp_scope_resolution_here()) {
            error_custloc(
                "expected '::' after decltype-specifier in qualified-id expression",
                current_token().loc);
        }
        CppQualifiedOwnerSeed seed;
        seed.owner_type = owner_type;
        seed.spelling = "decltype(<expr>)";
        seed.loc = decltype_loc;
        seed.is_dependent =
            type_depends_on_template_parameters(owner_type, ast_ctx.get());
        seed.requires_class_or_enum = true;
        initial_owner = std::move(seed);

        consume_cpp_scope_resolution();
        bool preceded_by_template_keyword =
            gentle_check_and_consume(TokenType::TEMPLATE);
        components.push_back(parse_component(preceded_by_template_keyword));
        while (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            preceded_by_template_keyword =
                gentle_check_and_consume(TokenType::TEMPLATE);
            components.push_back(parse_component(preceded_by_template_keyword));
        }
    } else {
        has_global_qualifier = consume_cpp_scope_resolution();
        if (!gentle_check(TokenType::IDENTIFIER) &&
            !(has_global_qualifier && gentle_check(TokenType::OPERATOR_KW))) {
            error_custloc("expected identifier after '::' in qualified-id expression",
                current_token().loc);
        }

        components.push_back(parse_component(false));
        while (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            bool preceded_by_template_keyword =
                gentle_check_and_consume(TokenType::TEMPLATE);
            components.push_back(parse_component(preceded_by_template_keyword));
        }
    }

    std::vector<CppQualifiedNameComponent> qualifiers;
    CppQualifiedNameComponent terminal_component;
    if (!components.empty()) {
        qualifiers.assign(components.begin(), components.end() - 1);
        terminal_component = std::move(components.back());
    }
    SrcLoc terminal_loc = terminal_component.loc;
    std::string terminal_name = terminal_component.name;
    bool saw_terminal_template_keyword =
        terminal_component.preceded_by_template_keyword;

    auto lookup_record_type_in_context =
        [&](const DeclContext* start_context,
            const std::string& name,
            bool allow_enclosing_lookup) -> QualType {
            if (!start_context || name.empty()) {
                return QualType();
            }
            auto try_ctx = [&](const DeclContext* ctx) -> QualType {
                if (!ctx) {
                    return QualType();
                }
                auto* tag_binding = ctx->lookup_local(name, LookupNamespace::Tag);
                if (!tag_binding) {
                    return QualType();
                }
                return tag_binding->type;
            };

            if (!allow_enclosing_lookup) {
                return try_ctx(start_context);
            }
            for (auto* ctx = start_context; ctx; ctx = ctx->semantic_parent()) {
                if (auto record_type = try_ctx(ctx)) {
                    return record_type;
                }
            }
            return QualType();
        };
    Parser::CppQualifiedOwnerChainResolution owner_chain;
    bool used_single_qualifier_record_compat = false;
    if (!initial_owner &&
        !has_global_qualifier &&
        qualifiers.size() == 1 &&
        !qualifiers.front().has_template_argument_list &&
        current_context) {
        QualType compatibility_owner_type = lookup_record_type_in_context(
            current_context.get(),
            qualifiers.front().name,
            /*allow_enclosing_lookup=*/true);
        if (compatibility_owner_type) {
            owner_chain.owner_type = compatibility_owner_type;
            owner_chain.is_current_instantiation =
                cpp_qualifier_is_current_instantiation(
                    qualifiers.front().name,
                    compatibility_owner_type);
            owner_chain.is_dependent =
                type_depends_on_template_parameters(
                    compatibility_owner_type,
                    ast_ctx.get());
            owner_chain.qualifier_spellings = {qualifiers.front().spelling()};
            owner_chain.qualifier_chain_spelling =
                qualifiers.front().spelling();
            owner_chain.lookup_scope = current_scope;
            owner_chain.lookup_context = current_context.get();
            used_single_qualifier_record_compat = true;
        }
    }
    if (!used_single_qualifier_record_compat) {
        owner_chain = resolve_cpp_qualified_owner_chain(
            qualifiers,
            has_global_qualifier,
            qualified_loc,
            /*diagnose_dependent_names=*/true,
            initial_owner);
    }
    auto current_function_owner_type =
        [&]() -> QualType {
            auto fn_type = dyn_cast_shared<FunctionType>(func_type);
            if (!fn_type || fn_type->parameters.empty()) {
                return QualType();
            }
            auto this_ptr_type =
                desugar_type(fn_type->parameters.front(), ast_ctx.get())
                    .as_shared<PointerType>();
            if (!this_ptr_type) {
                return QualType();
            }
            return this_ptr_type->pointed_type;
        };
    if (owner_chain.lookup_failed &&
        !has_global_qualifier &&
        qualifiers.size() == 1 &&
        !qualifiers.front().has_template_argument_list) {
        QualType function_owner_type = current_function_owner_type();
        if (function_owner_type) {
            auto semantic_owner_type =
                desugar_type(function_owner_type, ast_ctx.get());
            bool owner_matches = false;
            if (auto owner_record = semantic_owner_type.as_shared<ObjectType>()) {
                if (const auto* owner_decl =
                        dyn_cast<ObjectDecl>(owner_record->get_decl())) {
                    owner_matches =
                        owner_decl->tag == qualifiers.front().name;
                }
            } else if (auto owner_specialization =
                           semantic_owner_type.as<TemplateSpecializationType>()) {
                owner_matches =
                    owner_specialization->template_name ==
                    qualifiers.front().name;
            }
            if (owner_matches) {
                owner_chain.lookup_failed = false;
                owner_chain.failed_prefix_spelling.clear();
                owner_chain.owner_type = function_owner_type;
                owner_chain.is_current_instantiation = true;
                owner_chain.is_dependent =
                    type_depends_on_template_parameters(
                        function_owner_type,
                        ast_ctx.get());
                owner_chain.qualifier_spellings = {
                    qualifiers.front().spelling()
                };
                owner_chain.qualifier_chain_spelling =
                    qualifiers.front().spelling();
                owner_chain.lookup_scope = collect_->collect_current_scope();
                auto current_context = collect_->get_current_decl_context();
                owner_chain.lookup_context =
                    current_context ? current_context.get() : nullptr;
            }
        }
    }

    auto set_qualified_expr_info =
        [&](std::unique_ptr<Expr>& expr,
            QualType qualifier_type = QualType(),
            bool is_type_qualified = false,
            bool current_instantiation = false) {
            if (!expr || !isa<VarRef>(expr.get())) {
                return;
            }
            expr = attach_cpp_qualified_info_to_expr(
                std::move(expr),
                build_cpp_qualified_expr_info(
                    has_global_qualifier,
                    owner_chain.qualifier_spellings,
                    qualifier_type,
                    is_type_qualified,
                    current_instantiation));
        };

    if (saw_terminal_template_keyword &&
        !gentle_check(TokenType::LESS_THAN)) {
        error_custloc(
            "expected template-id after 'template' keyword",
            terminal_loc);
    }

    if (!saw_terminal_template_keyword &&
        gentle_check(TokenType::LESS_THAN) &&
        owner_chain.requires_template_keyword()) {
        if (!owner_chain.qualifier_chain_spelling.empty()) {
            diagnose_missing_cpp_template_keyword(
                owner_chain.qualifier_chain_spelling,
                terminal_name,
                terminal_loc);
        }
    }

    if (saw_terminal_template_keyword) {
        QualType qualifier_type;
        bool current_instantiation = false;
        bool is_type_qualified = false;
        if (owner_chain.has_owner_type()) {
            qualifier_type = owner_chain.owner_type;
            current_instantiation = owner_chain.is_current_instantiation;
            is_type_qualified = true;
        }
        auto qualified_expr = collect_->collect_identifier_reference(
            terminal_name, nullptr, qualified_loc);
        set_qualified_expr_info(
            qualified_expr,
            qualifier_type,
            is_type_qualified,
            current_instantiation);
        return qualified_expr;
    }

    bool looks_like_call = gentle_check(TokenType::LEFT_PAREN);
    bool might_be_template_id = looks_like_call;
        if (!looks_like_call &&
            is_cxx_mode_active() &&
            gentle_check(TokenType::LESS_THAN)) {
            size_t offset = 0;
            if (skip_template_argument_list_for_expression_probe(offset)) {
                might_be_template_id = true;
                looks_like_call =
                    peek_token_shortcut(offset).type == TokenType::LEFT_PAREN;
            }
        }

    auto lookup_scope = owner_chain.lookup_scope;
    const DeclContext* lookup_context = owner_chain.lookup_context;
    bool qualifier_lookup_failed = owner_chain.lookup_failed;
    std::shared_ptr<ObjectType> qualified_owner_type = nullptr;
    const ObjectDecl* qualified_owner_record_decl = nullptr;
    std::shared_ptr<EnumType> qualified_owner_enum_type = nullptr;
    const EnumDecl* qualified_owner_enum_decl = nullptr;
    if (owner_chain.has_owner_type() &&
        !owner_chain.is_dependent_context()) {
        QualType qualified_owner_canonical =
            desugar_type(
                remove_reference(owner_chain.owner_type, ast_ctx.get()),
                ast_ctx.get());
        qualified_owner_type = qualified_owner_canonical.as_shared<ObjectType>();
        qualified_owner_record_decl =
            dyn_cast<ObjectDecl>(
                qualified_owner_type
                    ? qualified_owner_type->get_decl()
                    : nullptr);
        if (!qualified_owner_record_decl) {
            qualified_owner_enum_type = qualified_owner_canonical.as_shared<EnumType>();
            qualified_owner_enum_decl =
                dyn_cast<EnumDecl>(
                    qualified_owner_enum_type
                        ? qualified_owner_enum_type->get_decl()
                        : nullptr);
        }
        qualifier_lookup_failed =
            qualifier_lookup_failed ||
            ((!qualified_owner_type || !qualified_owner_record_decl) &&
             (!qualified_owner_enum_type || !qualified_owner_enum_decl));
    }

    if (qualified_owner_type && qualified_owner_record_decl) {
        std::vector<std::pair<const RecordSemanticState::Method*, const ObjectDecl*>>
            method_matches;
        std::vector<std::pair<const RecordSemanticState::MethodTemplate*,
                              const ObjectDecl*>>
            method_template_matches;
        std::vector<std::pair<const RecordSemanticState::StaticDataMember*,
                              const ObjectDecl*>>
            static_data_matches;
        std::vector<std::shared_ptr<Symbol>> enumerator_matches;
        std::unordered_set<const ObjectDecl*> visited;
        // Search owner + bases until we find the first level that defines the name.
        // If a level matches, stop descending so hidden base members stay hidden.
        std::function<void(const ObjectDecl*)> collect_methods =
            [&](const ObjectDecl* current_decl) {
            if (!current_decl || visited.contains(current_decl)) {
                return;
            }
            visited.insert(current_decl);
            const RecordSemanticState* state =
                collect_
                    ? collect_->ensure_record_semantics_available(
                          QualType(current_decl->get_record_type()),
                          qualified_loc)
                    : record_semantics_cache_lookup(current_decl);
            if (!state) {
                return;
            }
            bool matched_here = false;
            for (const auto& static_data : state->static_data_members) {
                if (static_data.name == terminal_name) {
                    static_data_matches.emplace_back(
                        &static_data, current_decl);
                    matched_here = true;
                }
            }
            for (const auto& enumerator : state->enumerator_members) {
                if (enumerator.name == terminal_name) {
                    enumerator_matches.push_back(enumerator.symbol);
                    matched_here = true;
                }
            }
            for (const auto& method : state->methods) {
                if (method.name == terminal_name) {
                    method_matches.emplace_back(&method, current_decl);
                    matched_here = true;
                }
            }
            for (const auto& method_template : state->method_templates) {
                if (method_template.name == terminal_name) {
                    method_template_matches.emplace_back(
                        &method_template,
                        current_decl);
                    matched_here = true;
                }
            }
            if (matched_here) {
                return;
            }
            for (const auto& base : state->bases) {
                collect_methods(base.record_decl);
            }
        };
        collect_methods(qualified_owner_record_decl);

        size_t static_method_matches = 0;
        size_t nonstatic_method_matches = 0;
        for (const auto& method_match : method_matches) {
            if (method_match.first && method_match.first->is_static) {
                ++static_method_matches;
            } else {
                ++nonstatic_method_matches;
            }
        }
        size_t static_method_template_matches = 0;
        size_t nonstatic_method_template_matches = 0;
        for (const auto& method_template_match : method_template_matches) {
            if (method_template_match.first &&
                method_template_match.first->is_static) {
                ++static_method_template_matches;
            } else {
                ++nonstatic_method_template_matches;
            }
        }
        size_t static_callable_matches =
            static_method_matches + static_method_template_matches;
        size_t total_matches =
            method_matches.size() +
            method_template_matches.size() +
            static_data_matches.size() +
            enumerator_matches.size();
        bool callable_only_matches =
            looks_like_call &&
            (method_matches.size() + method_template_matches.size()) > 0 &&
            static_data_matches.empty() &&
            enumerator_matches.empty();
        if (looks_like_call &&
            static_callable_matches > 0 &&
            nonstatic_method_matches == 0 &&
            nonstatic_method_template_matches == 0 &&
            static_data_matches.empty()) {
            std::shared_ptr<Symbol> selected_symbol = nullptr;
            if (static_method_matches == 1 &&
                static_method_template_matches == 0 &&
                method_matches.size() == 1 &&
                method_matches.front().first &&
                method_matches.front().first->is_static) {
                selected_symbol = method_matches.front().first->symbol;
            }
            auto qualified_ref = collect_->collect_identifier_reference(
                terminal_name,
                std::move(selected_symbol),
                qualified_loc);
            set_qualified_expr_info(
                qualified_ref,
                QualType(qualified_owner_type),
                true,
                false);
            return qualified_ref;
        }
        if (total_matches > 1 && !callable_only_matches) {
            diag_engine->report_error(
                "member '" + terminal_name + "' is ambiguous",
                qualified_loc);
            return collect_->collect_error_expression(
                "ambiguous member reference", qualified_loc);
        }
        if (total_matches == 0) {
            diag_engine->report_error(
                "no member named '" + terminal_name + "' in '" +
                    qualified_owner_type->to_string() + "'",
                qualified_loc);
            return collect_->collect_error_expression(
                "missing qualified member", qualified_loc);
        }

        if (static_data_matches.size() == 1) {
            const auto* static_data = static_data_matches.front().first;
            if (!static_data || !static_data->symbol) {
                diag_engine->report_error(
                    "internal error: unresolved static data member symbol '" +
                        terminal_name + "'",
                    qualified_loc);
                return collect_->collect_error_expression(
                    "unresolved static data member symbol",
                    qualified_loc);
            }
                auto qualified_ref = collect_->collect_identifier_reference(
                    terminal_name, static_data->symbol, qualified_loc);
                set_qualified_expr_info(
                    qualified_ref,
                    QualType(qualified_owner_type),
                    true,
                    false);
                return qualified_ref;
        }

        if (enumerator_matches.size() == 1) {
            auto qualified_ref = collect_->collect_identifier_reference(
                terminal_name, enumerator_matches.front(), qualified_loc);
            set_qualified_expr_info(
                qualified_ref,
                QualType(qualified_owner_type),
                true,
                false);
            return qualified_ref;
        }

        if (method_matches.size() == 1) {
            const auto* method = method_matches.front().first;
            if (method && method->is_static) {
                if (!method->symbol) {
                    diag_engine->report_error(
                        "internal error: unresolved member function symbol '" +
                            terminal_name + "'",
                        qualified_loc);
                    return collect_->collect_error_expression(
                        "unresolved member function symbol", qualified_loc);
                }
                auto qualified_ref = collect_->collect_identifier_reference(
                    terminal_name, method->symbol, qualified_loc);
                set_qualified_expr_info(
                    qualified_ref,
                    QualType(qualified_owner_type),
                    true,
                    false);
                return qualified_ref;
            }
        }

        // Non-static member access through a qualified-id still needs an object;
        // build `this`, cast it to the qualified owner, then form member access.
        auto this_expr = collect_->collect_cpp_this_expression(qualified_loc);
        if (isa<ErrorExpr>(this_expr.get())) {
            return this_expr;
        }
        auto this_ptr_type = desugar_type(this_expr->get_type())
            .as_shared<PointerType>();
        uint8_t owner_quals = this_ptr_type
            ? this_ptr_type->pointed_type.get_qualifiers()
            : QUAL_NONE;
        QualType owner_qt(qualified_owner_type, owner_quals);
        QualType owner_ptr_type(std::make_shared<PointerType>(owner_qt));
        auto owner_this_expr =
            collect_->collect_cpp_named_cast(
                Collect::CppNamedCastKind::Static,
                std::move(this_expr),
                owner_ptr_type,
                qualified_loc);
        return collect_->collect_member_expression(
            std::move(owner_this_expr),
            terminal_name,
            true,
            qualified_loc,
            looks_like_call,
            true,
            owner_chain.requires_template_keyword());
    }

    if (qualified_owner_enum_type && qualified_owner_enum_decl) {
        auto enumerator_symbol =
            collect_->collect_lookup_enum_enumerator(
                owner_chain.owner_type,
                terminal_name);
        if (!enumerator_symbol) {
            diag_engine->report_error(
                "use of undeclared identifier '" + terminal_name + "'",
                qualified_loc);
            return collect_->collect_error_expression("undeclared identifier",
                qualified_loc);
        }
        auto qualified_ref = collect_->collect_identifier_reference(
            terminal_name,
            enumerator_symbol,
            qualified_loc);
        set_qualified_expr_info(
            qualified_ref,
            QualType(qualified_owner_enum_type),
            true,
            false);
        return qualified_ref;
    }

    if (owner_chain.is_dependent_context()) {
        auto qualifier = build_dependent_lookup_qualifier(
            build_cpp_qualified_expr_info(
                has_global_qualifier,
                owner_chain.qualifier_spellings,
                owner_chain.owner_type,
                /*is_type_qualified=*/true,
                owner_chain.is_current_instantiation));
        return collect_->collect_unresolved_lookup_expression(
            terminal_name,
            std::move(qualifier),
            /*requires_template_keyword=*/false,
            qualified_loc);
    }

    if (!qualifier_lookup_failed) {
        std::shared_ptr<Symbol> sym = nullptr;
        const DeclBinding* binding = nullptr;
        if (lookup_context) {
            auto qualified_lookup = LookupEngine::lookup_qualified(
                terminal_name,
                lookup_context,
                LookupNamespace::Ordinary);
            binding =
                qualified_lookup.status == LookupEngine::QualifiedLookupStatus::Found
                    ? qualified_lookup.binding
                    : nullptr;
            if (binding) {
                sym = qualified_lookup.symbol;
                if (!sym && binding->symbol) {
                    sym = binding->symbol;
                } else if (!sym &&
                           binding->has_overload_set() &&
                           !binding->overload_candidates.empty()) {
                    sym = binding->overload_candidates.front();
                }
            }
        }

        if (!sym &&
            might_be_template_id &&
            binding &&
            (binding->template_decl || binding->has_template_overload_set())) {
            auto qualified_ref = collect_->collect_identifier_reference(
                terminal_name, nullptr, qualified_loc);
            set_qualified_expr_info(qualified_ref);
            return qualified_ref;
        }

        if (!sym && !looks_like_call) {
            diag_engine->report_error(
                "use of undeclared identifier '" + terminal_name + "'",
                qualified_loc);
            return collect_->collect_error_expression("undeclared identifier",
                qualified_loc);
        }

        auto qualified_ref = collect_->collect_identifier_reference(
            terminal_name, std::move(sym), qualified_loc);
        set_qualified_expr_info(qualified_ref);
        return qualified_ref;
    }
    if (qualifier_lookup_failed && !qualifiers.empty()) {
        diag_engine->report_error(
            "use of undeclared identifier '" +
                (owner_chain.failed_prefix_spelling.empty()
                     ? qualifiers.front().spelling()
                     : owner_chain.failed_prefix_spelling) +
                "'",
            qualified_loc);
        return collect_->collect_error_expression("undeclared identifier",
            qualified_loc);
    }

    if (might_be_template_id) {
        auto qualified_ref = collect_->collect_identifier_reference(
            terminal_name, nullptr, qualified_loc);
        set_qualified_expr_info(qualified_ref);
        return qualified_ref;
    }

    if (!looks_like_call) {
        diag_engine->report_error(
            "use of undeclared identifier '" + terminal_name + "'",
            qualified_loc);
        return collect_->collect_error_expression("undeclared identifier",
            qualified_loc);
    }
    auto qualified_ref = collect_->collect_identifier_reference(
        terminal_name, nullptr, qualified_loc);
    set_qualified_expr_info(qualified_ref);
    return qualified_ref;
}

std::unique_ptr<Expr> Parser::parse_cpp_lambda_expression() {
    if (!is_cxx_mode_active() || !gentle_check(TokenType::LEFT_BRACKET)) {
        return nullptr;
    }

    SrcLoc lambda_loc = current_token().loc;
    LambdaClosureInfo closure_info;
    CppThisContext enclosing_this_context =
        collect_->collect_current_cpp_this_context();

    auto parse_simple_capture =
        [&](std::vector<CppLambdaCapture>& captures) {
            CppLambdaCapture capture;
            capture.location = current_token().loc;
            if (gentle_check_and_consume(TokenType::BITWISE_AND)) {
                capture.by_reference = true;
                capture.location = current_token().loc;
                if (gentle_check(TokenType::ELLIPSIS)) {
                    fail_cpp_future_work(
                        "lambda capture pack",
                        "lambda_capture_pack",
                        current_token().loc);
                }
                if (gentle_check(TokenType::THIS_KW)) {
                    error_custloc(
                        "lambda capture '&this' is not valid",
                        current_token().loc);
                }
            }

            if (gentle_check(TokenType::THIS_KW)) {
                if (!enclosing_this_context.is_member_function ||
                    enclosing_this_context.is_static_member_function ||
                    !enclosing_this_context.this_type) {
                    error_custloc(
                        "lambda capture 'this' is only valid in a non-static member function",
                        current_token().loc);
                }
                capture.captures_this = true;
                capture.name = "this";
                advance();
                captures.push_back(std::move(capture));
                return;
            }

            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc("expected lambda capture", current_token().loc);
            }

            capture.name = current_token().value;
            capture.location = current_token().loc;
            advance();
            if (gentle_check(TokenType::ASSIGN)) {
                capture.is_init_capture = true;
                advance();
                auto initializer = parse_assignment_expression();
                if (!initializer) {
                    error_custloc(
                        "lambda init-capture requires an initializer expression",
                        capture.location);
                }
                capture.initializer =
                    std::shared_ptr<Expr>(initializer.release());
            } else if (gentle_check(TokenType::LEFT_BRACE) ||
                       gentle_check(TokenType::LEFT_PAREN)) {
                fail_cpp_future_work(
                    "lambda init-capture initializer form",
                    "lambda_init_capture_initializer",
                    current_token().loc);
            } else {
                capture.symbol =
                    collect_->collect_lookup_variable_symbol(capture.name, true);
            }
            if (gentle_check(TokenType::ELLIPSIS)) {
                fail_cpp_future_work(
                    "lambda capture pack",
                    "lambda_capture_pack",
                    current_token().loc);
            }
            captures.push_back(std::move(capture));
        };

    check_and_consume(TokenType::LEFT_BRACKET);
    if (!gentle_check(TokenType::RIGHT_BRACKET)) {
        bool parsed_default_capture = false;
        if ((gentle_check(TokenType::BITWISE_AND) || gentle_check(TokenType::ASSIGN)) &&
            (peek_token().type == TokenType::COMMA ||
             peek_token().type == TokenType::RIGHT_BRACKET)) {
            closure_info.default_capture =
                gentle_check(TokenType::BITWISE_AND)
                    ? CppLambdaCaptureDefault::ByReference
                    : CppLambdaCaptureDefault::ByCopy;
            advance();
            parsed_default_capture = true;
        }

        if (!gentle_check(TokenType::RIGHT_BRACKET)) {
            if (parsed_default_capture) {
                check_and_consume(TokenType::COMMA);
            }
            while (true) {
                parse_simple_capture(closure_info.captures);
                if (!gentle_check_and_consume(TokenType::COMMA)) {
                    break;
                }
            }
        }
    }
    check_and_consume(TokenType::RIGHT_BRACKET);

    bool has_parameter_clause = false;
    bool is_mutable = false;
    bool is_constexpr = false;
    bool is_consteval = false;
    bool has_trailing_return = false;
    bool is_generic = false;
    bool has_auto_template_parameters = false;
    uint32_t lambda_template_parameter_depth =
        static_cast<uint32_t>(active_template_parameter_stack_.size());
    TemplateParameterList call_operator_template_parameters;
    std::unique_ptr<Expr> template_requires_clause = nullptr;
    std::unique_ptr<Expr> trailing_requires_clause = nullptr;
    std::vector<std::unique_ptr<Decl>> parameters;
    auto semantic_info = make_lambda_semantic_info(*ast_ctx, lambda_loc);
    semantic_info.lexical_this_context = enclosing_this_context;
    auto lambda_function_type = std::make_shared<FunctionType>();
    lambda_function_type->ret_type =
        QualType(std::make_shared<AutoType>(AutoTypeFlavor::Cxx));

    struct LambdaTemplateScopeGuard {
        Collect* collect = nullptr;
        std::vector<std::vector<const TemplateParameterDecl*>>* stack = nullptr;
        std::shared_ptr<Scope> scope;
        bool scope_active = false;
        bool stack_active = false;

        void leave_now() {
            if (scope_active && collect && scope) {
                collect->collect_set_current_scope(scope);
                collect->collect_leave_scope();
                scope_active = false;
            }
            if (stack_active && stack && !stack->empty()) {
                stack->pop_back();
                stack_active = false;
            }
        }

        ~LambdaTemplateScopeGuard() {
            leave_now();
        }
    } lambda_template_scope_guard;

    if (gentle_check(TokenType::LESS_THAN)) {
        if (!lang_opts.is_cxx20_or_later()) {
            error_custloc(
                "lambda template parameter list requires C++20",
                current_token().loc);
        }
        is_generic = true;
        auto entered_template_scope =
            collect_->collect_enter_scope(ScopeFlags::TemplateParameterScope);
        lambda_template_scope_guard.collect = collect_.get();
        lambda_template_scope_guard.stack = &active_template_parameter_stack_;
        lambda_template_scope_guard.scope = entered_template_scope.scope;
        lambda_template_scope_guard.scope_active = true;
        active_template_parameter_stack_.emplace_back();
        lambda_template_scope_guard.stack_active = true;

        call_operator_template_parameters =
            parse_cpp_template_parameter_list(lambda_template_parameter_depth);
        if (call_operator_template_parameters.empty()) {
            error_custloc(
                "lambda template parameter list cannot be empty",
                lambda_loc);
        }

        if (gentle_check(TokenType::REQUIRES_KW)) {
            advance(); // 'requires'
            ++lambda_template_requires_clause_depth_;
            struct TemplateRequiresParseGuard {
                uint32_t& depth;
                ~TemplateRequiresParseGuard() { --depth; }
            } template_requires_guard{lambda_template_requires_clause_depth_};
            template_requires_clause = parse_cpp_constraint_expression();
            if (!template_requires_clause) {
                error_custloc(
                    "invalid lambda template requires-clause",
                    current_token().loc);
            }
        }
    }

    auto saved_scope = collect_->collect_current_scope();
    auto saved_func_type = func_type;
    auto saved_seen_stmt_labels = seen_stmt_labels;
    auto saved_stmt_labels = stmt_labels;
    auto saved_local_label_scopes = local_label_scopes_;
    uint64_t saved_local_label_unique_id = local_label_unique_id_;

    auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
    auto lambda_scope = entered_scope.scope;

    seen_stmt_labels.clear();
    stmt_labels.clear();
    local_label_scopes_.clear();
    local_label_unique_id_ = 0;

    auto restore_lambda_parse_state = [&]() {
        collect_->collect_set_current_scope(saved_scope);
        func_type = saved_func_type;
        seen_stmt_labels = saved_seen_stmt_labels;
        stmt_labels = saved_stmt_labels;
        local_label_scopes_ = saved_local_label_scopes;
        local_label_unique_id_ = saved_local_label_unique_id;
    };

    auto bind_lambda_init_capture_symbols =
        [&]() {
            for (auto& capture : closure_info.captures) {
                if (!capture.is_init_capture) {
                    continue;
                }
                if (!capture.initializer) {
                    error_custloc(
                        "lambda init-capture requires an initializer expression",
                        capture.location);
                }

                QualType declared_type(
                    std::make_shared<AutoType>(AutoTypeFlavor::Cxx));
                if (capture.by_reference) {
                    declared_type = QualType(
                        std::make_shared<ReferenceType>(
                            QualType(
                                std::make_shared<AutoType>(
                                    AutoTypeFlavor::Cxx)),
                            ReferenceKind::LValue));
                }

                auto capture_symbol = collect_->collect_declare_variable_symbol(
                    capture.name,
                    declared_type,
                    StorageClass::NONE,
                    false,
                    false,
                    capture.location);
                collect_->collect_resolve_auto_variable_type_from_expr(
                    declared_type,
                    capture.initializer.get(),
                    capture_symbol,
                    capture.name,
                    capture.location);
                if (capture.by_reference && capture_symbol) {
                    capture_symbol->type =
                        remove_reference(declared_type, ast_ctx.get());
                }
                capture.symbol = std::move(capture_symbol);
            }
        };

    try {
        bind_lambda_init_capture_symbols();

        if (gentle_check(TokenType::LEFT_PAREN)) {
            has_parameter_clause = true;
            advance();
            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                while (true) {
                    auto parameter = parse_parameter_declaration();
                    auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
                    if (!param_decl) {
                        error_custloc(
                            "internal error: lambda parameter did not produce ParamDecl",
                            lambda_loc);
                    }
                    if (param_decl->is_parameter_pack) {
                        fail_cpp_future_work(
                            "lambda parameter pack",
                            "lambda_parameter_pack",
                            param_decl->location);
                    }
                    if (auto_type_utils::has_cxx_auto_type(
                            param_decl->type.get_shared())) {
                        is_generic = true;
                        has_auto_template_parameters = true;
                    }
                    parameters.push_back(std::move(parameter));
                    if (!gentle_check_and_consume(TokenType::COMMA)) {
                        break;
                    }
                }
            }
            check_and_consume(TokenType::RIGHT_PAREN);
        }

        if (has_auto_template_parameters) {
            call_operator_template_parameters =
                lower_generic_lambda_parameter_placeholders(
                    parameters,
                    std::move(call_operator_template_parameters),
                    semantic_info.closure_name(),
                    lambda_template_parameter_depth,
                    lambda_loc);
        }

        lambda_function_type->clear_parameters();
        lambda_function_type->parameters.reserve(parameters.size());
        lambda_function_type->parameter_pack_flags.reserve(parameters.size());
        for (const auto& parameter : parameters) {
            auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
            if (!param_decl) {
                error_custloc(
                    "internal error: lambda parameter did not produce ParamDecl",
                    lambda_loc);
            }
            lambda_function_type->push_parameter(
                param_decl->type,
                param_decl->is_parameter_pack);
        }

        while (true) {
            if (gentle_check(TokenType::MUTABLE_KW)) {
                if (is_mutable) {
                    error_custloc(
                        "duplicate 'mutable' in lambda declarator",
                        current_token().loc);
                }
                is_mutable = true;
                advance();
                continue;
            }
            if (gentle_check(TokenType::CONSTEXPR_KW)) {
                if (!lang_opts.is_cxx17_or_later()) {
                    error_custloc(
                        "lambda 'constexpr' specifier requires C++17",
                        current_token().loc);
                }
                if (is_constexpr) {
                    error_custloc(
                        "duplicate 'constexpr' in lambda declarator",
                        current_token().loc);
                }
                is_constexpr = true;
                advance();
                continue;
            }
            if (gentle_check(TokenType::CONSTEVAL_KW)) {
                if (!lang_opts.is_cxx20_or_later()) {
                    error_custloc(
                        "lambda 'consteval' specifier requires C++20",
                        current_token().loc);
                }
                if (is_consteval) {
                    error_custloc(
                        "duplicate 'consteval' in lambda declarator",
                        current_token().loc);
                }
                is_consteval = true;
                advance();
                continue;
            }
            break;
        }

        if (is_constexpr && is_consteval) {
            error_custloc(
                "'constexpr' cannot be combined with 'consteval' on a lambda",
                lambda_loc);
        }

        if (gentle_check(TokenType::NOEXCEPT_KW)) {
            parse_cpp_optional_noexcept_spec(*lambda_function_type);
        }

        DeclarationParser return_parser(this);
        if (auto return_type = return_parser.parse_cpp_trailing_return_type()) {
            if (return_parser.is_parameter_pack ||
                auto_type_utils::has_cxx_auto_type(return_type->get_shared())) {
                fail_cpp_future_work(
                    "generic lambda trailing return",
                    "generic_lambda",
                    lambda_loc);
            }
            lambda_function_type->ret_type = *return_type;
            has_trailing_return = true;
        }

        if (lang_opts.is_cxx20_or_later() &&
            gentle_check(TokenType::REQUIRES_KW)) {
            advance(); // 'requires'
            trailing_requires_clause = parse_cpp_constraint_expression();
            if (!trailing_requires_clause) {
                error_custloc(
                    "invalid lambda trailing requires-clause",
                    current_token().loc);
            }
            if (!is_generic) {
                error_custloc(
                    "non-generic lambda cannot have a trailing requires-clause",
                    trailing_requires_clause->location.isInvalid()
                        ? lambda_loc
                        : trailing_requires_clause->location);
            }
        }

        auto call_operator_type = std::make_shared<FunctionType>(*lambda_function_type);
        call_operator_type->has_prototype = true;
        auto closure_owner_type = semantic_info.closure_type();
        if (!closure_owner_type) {
            error_custloc(
                "internal error: lambda closure semantic owner has no object type",
                lambda_loc);
        } else {
            uint8_t this_object_quals = is_mutable ? QUAL_NONE : QUAL_CONST;
            QualType qualified_owner_type(
                closure_owner_type.get_shared(),
                this_object_quals);
            QualType this_type(
                std::make_shared<PointerType>(qualified_owner_type));
            call_operator_type->insert_parameter(0, this_type);
        }

        func_type = QualType(call_operator_type).get_shared();
        collect_->collect_start_function_definition(
            semantic_info.closure_name() + "::operator()",
            QualType(call_operator_type),
            enclosing_this_context);

        std::unique_ptr<CompoundStmt> body;
        std::unordered_set<std::string> lambda_stmt_labels;
        try {
            auto body_stmt = parse_compound_stmt(lambda_scope);
            body = std::unique_ptr<CompoundStmt>(
                dyn_cast<CompoundStmt>(body_stmt.release()));
            if (!body) {
                error_custloc(
                    "expected lambda compound-statement body",
                    lambda_loc);
            }
            lambda_stmt_labels = stmt_labels;
            collect_->collect_finish_function_definition(lambda_scope);
            lambda_function_type->ret_type = call_operator_type->ret_type;
        } catch (...) {
            collect_->collect_abort_function_definition();
            throw;
        }

        restore_lambda_parse_state();
        lambda_template_scope_guard.leave_now();
        auto lambda_expr = collect_->collect_cpp_lambda_expression(
            std::move(closure_info),
            std::move(semantic_info),
            QualType(lambda_function_type),
            std::move(call_operator_template_parameters),
            std::move(template_requires_clause),
            std::move(trailing_requires_clause),
            std::move(parameters),
            std::move(body),
            std::move(lambda_stmt_labels),
            call_operator_type->ret_type,
            has_parameter_clause,
            is_mutable,
            is_constexpr,
            is_consteval,
            lambda_function_type->has_explicit_exception_spec,
            has_trailing_return,
            is_generic,
            lambda_loc);
        return lambda_expr;
    } catch (...) {
        restore_lambda_parse_state();
        throw;
    }
}

std::unique_ptr<Expr> Parser::parse_block_literal_expression() {
    if (!gentle_check(TokenType::BITWISE_XOR)) {
        return nullptr;
    }
    if (!type_ctx || !type_ctx->target ||
        !darwin_blocks::blocks_enabled_for_langopts(lang_opts, *type_ctx->target)) {
        return nullptr;
    }

    SrcLoc block_loc = current_token().loc;
    advance(); // consume '^'

    bool has_parameter_clause = false;
    bool has_explicit_return_type = false;
    QualType explicit_return_type = nullptr;
    std::vector<std::unique_ptr<Decl>> parameters;
    auto block_function_type = std::make_shared<FunctionType>();
    block_function_type->ret_type =
        QualType(std::make_shared<AutoType>(AutoTypeFlavor::Cxx));
    block_function_type->has_prototype = true;

    auto parse_block_parameter_clause =
        [&]() {
            has_parameter_clause = true;
            check_and_consume(TokenType::LEFT_PAREN);
            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                while (true) {
                    auto parameter = parse_parameter_declaration();
                    auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
                    if (!param_decl) {
                        error_custloc(
                            "internal error: block parameter did not produce ParamDecl",
                            block_loc);
                    }
                    parameters.push_back(std::move(parameter));
                    if (!gentle_check_and_consume(TokenType::COMMA)) {
                        break;
                    }
                }
            }
            check_and_consume(TokenType::RIGHT_PAREN);
        };

    if (gentle_check(TokenType::LEFT_PAREN)) {
        parse_block_parameter_clause();
    } else if (isTokenDeclarationSpec(current_token())) {
        DeclarationParser return_parser(this);
        explicit_return_type = QualType(return_parser.parse_declaration(false));
        retain_type_specifier_decl_if_needed(return_parser);
        if (!explicit_return_type) {
            error_custloc("expected block return type after '^'", block_loc);
        }
        has_explicit_return_type = true;
        block_function_type->ret_type = explicit_return_type;
        if (gentle_check(TokenType::LEFT_PAREN)) {
            parse_block_parameter_clause();
        }
    }

    block_function_type->clear_parameters();
    if (parameters.empty()) {
        block_function_type->push_parameter(
            QualType(type_ctx->get_builtin(BuiltinTypes::Void)));
    } else {
        block_function_type->parameters.reserve(parameters.size());
        block_function_type->parameter_pack_flags.reserve(parameters.size());
        for (const auto& parameter : parameters) {
            auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
            if (!param_decl) {
                error_custloc(
                    "internal error: block parameter did not produce ParamDecl",
                    block_loc);
            }
            block_function_type->push_parameter(
                param_decl->type,
                param_decl->is_parameter_pack);
        }
    }

    auto saved_scope = collect_->collect_current_scope();
    auto saved_func_type = func_type;
    auto saved_seen_stmt_labels = seen_stmt_labels;
    auto saved_stmt_labels = stmt_labels;
    auto saved_local_label_scopes = local_label_scopes_;
    uint64_t saved_local_label_unique_id = local_label_unique_id_;

    auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
    auto block_scope = entered_scope.scope;

    seen_stmt_labels.clear();
    stmt_labels.clear();
    local_label_scopes_.clear();
    local_label_unique_id_ = 0;

    auto restore_block_parse_state = [&]() {
        collect_->collect_set_current_scope(saved_scope);
        func_type = saved_func_type;
        seen_stmt_labels = saved_seen_stmt_labels;
        stmt_labels = saved_stmt_labels;
        local_label_scopes_ = saved_local_label_scopes;
        local_label_unique_id_ = saved_local_label_unique_id;
    };

    try {
        func_type = QualType(block_function_type).get_shared();
        collect_->collect_start_function_definition(
            make_block_internal_name(block_loc) + "::__invoke",
            QualType(block_function_type),
            Collect::CppThisContext{});

        std::unique_ptr<CompoundStmt> body;
        std::unordered_set<std::string> block_stmt_labels;
        try {
            auto body_stmt = parse_compound_stmt(block_scope);
            body = std::unique_ptr<CompoundStmt>(
                dyn_cast<CompoundStmt>(body_stmt.release()));
            if (!body) {
                error_custloc(
                    "expected block compound-statement body",
                    block_loc);
            }
            block_stmt_labels = stmt_labels;
            collect_->collect_finish_function_definition(block_scope);
            if (has_explicit_return_type) {
                block_function_type->ret_type = explicit_return_type;
            }
        } catch (...) {
            collect_->collect_abort_function_definition();
            throw;
        }

        restore_block_parse_state();

        if (parameters.empty()) {
            parameters.push_back(collect_->collect_parameter_declaration(
                QualType(type_ctx->get_builtin(BuiltinTypes::Void)),
                "",
                nullptr,
                StorageClass::NONE,
                block_loc));
        }

        QualType block_type(
            std::make_shared<BlockPointerType>(QualType(block_function_type)));
        return collect_->collect_block_expression(
            make_block_semantic_info(*ast_ctx, block_loc),
            block_type,
            std::move(parameters),
            std::move(body),
            std::move(block_stmt_labels),
            explicit_return_type,
            has_parameter_clause,
            has_explicit_return_type,
            block_loc);
    } catch (...) {
        restore_block_parse_state();
        throw;
    }
}

std::unique_ptr<Expr> Parser::parse_primary_expression() {
    Token tok = current_token();
    if (is_cxx_mode_active()) {
        if (auto type_construction = try_parse_cpp_type_construction_expression()) {
            return type_construction;
        }
        TPResult qualified_id_probe = try_parse_cpp_qualified_id();
        if (qualified_id_probe == TPResult::True) {
            return parse_cpp_qualified_primary_expression();
        }
        if (lang_opts.is_cxx20_or_later() &&
            tok.type == TokenType::REQUIRES_KW) {
            return parse_cpp_requires_expression();
        }
        if (tok.type == TokenType::IDENTIFIER) {
            const std::string& ident = tok.value;
            if (ident == "typeid") {
                return parse_cpp_typeid_expression();
            }
            if (ident == "dynamic_cast" || ident == "static_cast" ||
                ident == "reinterpret_cast" || ident == "const_cast") {
                return parse_cpp_named_cast_expression();
            }
        }
        if (tok.type == TokenType::LEFT_BRACKET) {
            return parse_cpp_lambda_expression();
        }
    }
    if (is_imaginary_integer_literal(tok.type)) {
        advance();
        Token real_tok = tok;
        real_tok.type = imaginary_integer_to_real_token(tok.type);
        std::shared_ptr<CType> int_type = getNumericTypeConstant(real_tok, type_ctx.get());
        if (!int_type) {
            error_custloc("int const doesn't fit", tok.loc);
            return nullptr;
        }
        auto int_builtin = dyn_cast_shared<BuiltinType>(int_type);
        if (!int_builtin) {
            error_custloc("imaginary integer literal requires builtin integer type", tok.loc);
            return nullptr;
        }
        auto complex_type = type_ctx->get_complex(int_builtin->builtin_kind);
        if (!complex_type) {
            error_custloc("imaginary integer literal has unsupported type", tok.loc);
            return nullptr;
        }
        return collect_->collect_floating_literal(tok.value, complex_type, true, tok.loc);
    }
    if (is_integer_literal(tok.type)) {
        advance();
        std::shared_ptr<CType> int_type;
        TokenType tt = tok.type;
        int_type = getNumericTypeConstant(tok, type_ctx.get());
        if (int_type == nullptr) {
            error_custloc("int const doesn't fit", tok.loc);
            return nullptr;
        }
        return collect_->collect_integer_literal(tok.value, int_type, tok.loc);
    }
    if (is_floating_literal(tok.type)) {
        advance();
        if (tok.type == TokenType::IMAG_FLOAT_CONST ||
            tok.type == TokenType::IMAG_DOUBLE_CONST ||
            tok.type == TokenType::IMAG_LONG_DOUBLE_CONST) {
            std::shared_ptr<CType> complex_type;
            if (tok.type == TokenType::IMAG_FLOAT_CONST) {
                complex_type = type_ctx->get_complex(BuiltinTypes::Float);
            } else if (tok.type == TokenType::IMAG_LONG_DOUBLE_CONST) {
                complex_type = type_ctx->get_complex(BuiltinTypes::LongDouble);
            } else {
                complex_type = type_ctx->get_complex(BuiltinTypes::Double);
            }
            return collect_->collect_floating_literal(tok.value, complex_type, true, tok.loc);
        }
        std::shared_ptr<CType> float_type;
        if (tok.type == TokenType::FLOAT_CONST) {
            float_type = type_ctx->get_builtin(BuiltinTypes::Float);
        } else if (tok.type == TokenType::LONG_DOUBLE_CONST) {
            float_type = type_ctx->get_builtin(BuiltinTypes::LongDouble);
        } else {
            float_type = type_ctx->get_builtin(BuiltinTypes::Double);
        }
        return collect_->collect_floating_literal(tok.value, float_type, false, tok.loc);
    }
    if (tok.type == TokenType::TRUE_KW || tok.type == TokenType::FALSE_KW) {
        advance();
        auto bool_type = type_ctx->get_builtin(BuiltinTypes::Bool);
        const std::string bool_value = (tok.type == TokenType::TRUE_KW) ? "1" : "0";
        return collect_->collect_integer_literal(bool_value, bool_type, tok.loc);
    }
    if (tok.type == TokenType::NULLPTR_KW) {
        advance();
        auto int_type = type_ctx->get_builtin(BuiltinTypes::Int);
        auto zero = collect_->collect_integer_literal("0", int_type, tok.loc);
        auto nullptr_type = type_ctx->get_builtin(BuiltinTypes::NullPtr);
        return collect_->collect_explicit_cast(
            std::move(zero), QualType(nullptr_type), tok.loc);
    }
    if (tok.type == TokenType::THIS_KW) {
        advance();
        if (!is_cxx_mode_active()) {
            error_custloc("'this' is only valid in C++ mode", tok.loc);
            return nullptr;
        }
        return collect_->collect_cpp_this_expression(tok.loc);
    }
    if (tok.type == TokenType::CHAR_LITERAL) {
        advance();
        // Character literals have type int in C
        bool cxx_mode = is_cxx_mode_active();
        int32_t fin_val = 0;
        bool is_unicode_prefixed = (tok.literal_prefix == LiteralPrefix::L ||
                                    tok.literal_prefix == LiteralPrefix::u ||
                                    tok.literal_prefix == LiteralPrefix::U);
        if (is_unicode_prefixed) {
            auto cps = decode_utf8_codepoints(tok.value);
            fin_val = cps.empty() ? 0 : static_cast<int32_t>(cps[0]);
        } else {
            for (char &c: tok.value) {
                // if there is more than one char it is undefined, mainstream compilers just add extra chars to int
                fin_val <<= 8;
                fin_val |= static_cast<int32_t>(static_cast<unsigned char>(c));
            }
        }
        std::shared_ptr<CType> char_type;
        switch (tok.literal_prefix) {
            case LiteralPrefix::u:
                char_type = type_ctx->get_builtin(
                    cxx_mode ? BuiltinTypes::Char16 : BuiltinTypes::UShort);
                break;
            case LiteralPrefix::U:
                char_type = type_ctx->get_builtin(
                    cxx_mode ? BuiltinTypes::Char32 : BuiltinTypes::UInt);
                break;
            case LiteralPrefix::L:
                char_type = type_ctx->get_builtin(
                    cxx_mode ? BuiltinTypes::WChar : BuiltinTypes::Int);
                break;
            case LiteralPrefix::U8:
            case LiteralPrefix::None:
            default:
                char_type = type_ctx->get_builtin(
                    cxx_mode ? BuiltinTypes::Char : BuiltinTypes::Int);
                break;
        }
        return collect_->collect_character_literal(tok.value, fin_val, QualType(char_type), tok.loc);
    }
    if (tok.type == TokenType::STRING_LITERAL) {
        advance();
        bool cxx_mode = is_cxx_mode_active();
        bool is_unicode_prefixed = (tok.literal_prefix == LiteralPrefix::L ||
                                    tok.literal_prefix == LiteralPrefix::u ||
                                    tok.literal_prefix == LiteralPrefix::U);
        size_t length = (is_unicode_prefixed
            ? decode_utf8_codepoints(tok.value).size()
            : tok.value.length()) + 1; // +1 for null terminator
        std::shared_ptr<CType> charType;
        switch (tok.literal_prefix) {
            case LiteralPrefix::u:
                charType = type_ctx->get_builtin(
                    cxx_mode ? BuiltinTypes::Char16 : BuiltinTypes::UShort);
                break;
            case LiteralPrefix::U:
                charType = type_ctx->get_builtin(
                    cxx_mode ? BuiltinTypes::Char32 : BuiltinTypes::UInt);
                break;
            case LiteralPrefix::L:
                charType = type_ctx->get_builtin(
                    cxx_mode ? BuiltinTypes::WChar : BuiltinTypes::Int);
                break;
            case LiteralPrefix::U8:
            case LiteralPrefix::None:
            default:
                charType = type_ctx->get_builtin(BuiltinTypes::Char);
                break;
        }
        auto arrayType = std::make_shared<ArrayType>(QualType(charType), length);
        return collect_->collect_string_literal(tok.value, QualType(arrayType), tok.loc);
    }
    if (tok.type == TokenType::LEFT_PAREN) {
        advance();
        if (gentle_check(TokenType::LEFT_BRACE)) {
            auto compound_stmt = parse_compound_stmt();
            check_and_consume(TokenType::RIGHT_PAREN);
            auto cs_ptr = std::unique_ptr<CompoundStmt>(static_cast<CompoundStmt*>(compound_stmt.release()));
            return collect_->collect_statement_expression(std::move(cs_ptr), tok.loc);
        }
        if (auto fold = try_parse_fold_expression(tok.loc)) {
            check_and_consume(TokenType::RIGHT_PAREN);
            return fold;
        }
        TemplateArgumentGroupGuard group_guard(*this);
        std::unique_ptr<Expr> exp = parse_expression();
        check_and_consume(TokenType::RIGHT_PAREN);
        return std::move(exp);
    }
    // Handle _Generic selection expression
    // Grammar: _Generic ( assignment-expression , generic-assoc-list )
    if (tok.type == TokenType::GENERIC) {
        advance(); // consume '_Generic'
        check_and_consume(TokenType::LEFT_PAREN);
        auto controlling = parse_assignment_expression();
        if (!controlling) {
            error_custloc("Error parsing controlling expression in _Generic", tok.loc);
            return nullptr;
        }
        check_and_consume(TokenType::COMMA);
        std::vector<GenericAssociation> associations;
        // Parse generic-assoc-list
        do {
            GenericAssociation assoc;
            assoc.loc = current_token().loc;
            if (gentle_check(TokenType::DEFAULT)) {
                advance(); // consume 'default'
                assoc.is_default = true;
                assoc.type = QualType();
            } else {
                // Parse type-name
                auto parse_decl = DeclarationParser(this);
                auto assoc_type = parse_decl.parse_declaration();
                if (assoc_type == nullptr) {
                    error_custloc("Error parsing type in _Generic association", assoc.loc);
                    return nullptr;
                }
                retain_type_specifier_decl_if_needed(parse_decl);
                assoc.type = assoc_type;
                assoc.is_default = false;
            }
            check_and_consume(TokenType::COLON);
            assoc.expr = parse_assignment_expression();
            if (!assoc.expr) {
                error_custloc("Error parsing expression in _Generic association", assoc.loc);
                return nullptr;
            }
            associations.push_back(std::move(assoc));
        } while (gentle_check_and_consume(TokenType::COMMA));
        check_and_consume(TokenType::RIGHT_PAREN);
        return collect_->collect_generic_expression(std::move(controlling), std::move(associations), tok.loc);
    }
    // C++ style functional casts: int(67), std::string("Accra and Belgrade")
    if (is_cxx_mode_active() && isTokenDeclarationSpec(tok)) {
        TentativeParsingAction tentative(*this);
        try {
            DeclarationParser parse_decl(this);
            auto parsed_type = parse_decl.parse_declaration(false);
            if (parsed_type &&
                parse_decl.name.empty() &&
                parse_decl.str_class == StorageClass::NONE &&
                gentle_check(TokenType::LEFT_PAREN)) {
                QualType target_type(parsed_type, parse_decl.qualifiers);
                retain_type_specifier_decl_if_needed(parse_decl);
                advance(); // consume '('
                std::vector<std::unique_ptr<Expr>> args;
                if (!gentle_check(TokenType::RIGHT_PAREN)) {
                    TemplateArgumentGroupGuard group_guard(*this);
                    do {
                        auto arg = parse_call_argument_expression();
                        args.push_back(std::move(arg));
                    } while (gentle_check_and_consume(TokenType::COMMA));
                }
                check_and_consume(TokenType::RIGHT_PAREN);
                tentative.commit();
                return collect_->collect_cpp_function_style_cast(
                    target_type,
                    std::move(args),
                    tok.loc);
            }
        } catch (const ParseError&) {
        } catch (const FatalErrorLimitReached&) {
            throw;
        }
    }

    if (tok.type == TokenType::IDENTIFIER) {
        if (const auto* builtin_info =
                BuiltinRegistry::instance().lookup(tok.value);
            builtin_info &&
            is_builtin_type_trait_kind(builtin_info->kind)) {
            advance(); // consume builtin trait identifier
            check_and_consume(TokenType::LEFT_PAREN);

            std::vector<QualType> type_args;
            while (!gentle_check(TokenType::RIGHT_PAREN) &&
                   !gentle_check(TokenType::Eof)) {
                auto parse_decl = DeclarationParser(this);
                auto type_arg = parse_decl.parse_declaration();
                if (type_arg == nullptr) {
                    error_custloc(
                        "Error parsing type operand in " +
                            std::string(builtin_info->name),
                        tok.loc);
                    return nullptr;
                }
                retain_type_specifier_decl_if_needed(parse_decl);
                if (gentle_check(TokenType::ELLIPSIS)) {
                    advance(); // consume pack expansion marker; the type already carries pack-ness
                }
                type_args.emplace_back(type_arg, parse_decl.qualifiers);
                if (!gentle_check_and_consume(TokenType::COMMA)) {
                    break;
                }
            }
            check_and_consume(TokenType::RIGHT_PAREN);

            int arg_count = static_cast<int>(type_args.size());
            if (arg_count < builtin_info->min_args ||
                (builtin_info->max_args >= 0 &&
                 arg_count > builtin_info->max_args)) {
                error_custloc(
                    std::string(builtin_info->name) + " requires " +
                        std::to_string(builtin_info->min_args) +
                        " type argument(s)",
                    tok.loc);
                return nullptr;
            }

            return collect_->collect_builtin_type_trait_expression(
                builtin_info->kind,
                std::move(type_args),
                tok.loc);
        }
        // Handle __builtin_convertvector(expr, type)
        if (tok.value == "__builtin_convertvector") {
            advance(); // consume '__builtin_convertvector'
            check_and_consume(TokenType::LEFT_PAREN);
            auto source_expr = parse_assignment_expression();
            check_and_consume(TokenType::COMMA);
            auto parse_decl = DeclarationParser(this);
            auto target_type = parse_decl.parse_declaration();
            if (target_type == nullptr) {
                error_custloc("Error parsing type in __builtin_convertvector", tok.loc);
                return nullptr;
            }
            retain_type_specifier_decl_if_needed(parse_decl);
            check_and_consume(TokenType::RIGHT_PAREN);
            return collect_->collect_builtin_convertvector_expression(
                std::move(source_expr), target_type, tok.loc);
        }
        // Handle __builtin_va_arg(ap, type) - second arg is a type name
        if (tok.value == "__builtin_va_arg") {
            advance(); // consume '__builtin_va_arg'
            check_and_consume(TokenType::LEFT_PAREN);
            auto va_list_expr = parse_assignment_expression();
            check_and_consume(TokenType::COMMA);
            auto parse_decl = DeclarationParser(this);
            auto arg_type = parse_decl.parse_declaration();
            if (arg_type == nullptr) {
                error_custloc("Error parsing type in __builtin_va_arg", tok.loc);
                return nullptr;
            }
            retain_type_specifier_decl_if_needed(parse_decl);
            check_and_consume(TokenType::RIGHT_PAREN);
            return collect_->collect_va_arg_expression(std::move(va_list_expr), arg_type, tok.loc);
        }
        // Handle __builtin_types_compatible_p(type1, type2)
        if (tok.value == "__builtin_types_compatible_p") {
            advance(); // consume '__builtin_types_compatible_p'
            check_and_consume(TokenType::LEFT_PAREN);
            auto parse_decl1 = DeclarationParser(this);
            auto type1 = parse_decl1.parse_declaration();
            if (type1 == nullptr) {
                error_custloc("Error parsing first type in __builtin_types_compatible_p", tok.loc);
                return nullptr;
            }
            retain_type_specifier_decl_if_needed(parse_decl1);
            check_and_consume(TokenType::COMMA);
            auto parse_decl2 = DeclarationParser(this);
            auto type2 = parse_decl2.parse_declaration();
            if (type2 == nullptr) {
                error_custloc("Error parsing second type in __builtin_types_compatible_p", tok.loc);
                return nullptr;
            }
            retain_type_specifier_decl_if_needed(parse_decl2);
            check_and_consume(TokenType::RIGHT_PAREN);
            return collect_->collect_builtin_types_compatible_expression(type1, type2, tok.loc);
        }
        // Handle __builtin_choose_expr(const_expr, expr1, expr2)
        if (tok.value == "__builtin_choose_expr") {
            advance(); // consume '__builtin_choose_expr'
            check_and_consume(TokenType::LEFT_PAREN);
            auto const_expr = parse_assignment_expression();
            check_and_consume(TokenType::COMMA);
            auto expr1 = parse_assignment_expression();
            check_and_consume(TokenType::COMMA);
            auto expr2 = parse_assignment_expression();
            check_and_consume(TokenType::RIGHT_PAREN);
            return collect_->collect_builtin_choose_expression(
                std::move(const_expr), std::move(expr1), std::move(expr2), tok.loc);
        }
        // Handle __builtin_offsetof(type, member)
        if (tok.value == "__builtin_offsetof") {
            advance(); // consume '__builtin_offsetof'
            check_and_consume(TokenType::LEFT_PAREN);
            auto parse_decl = DeclarationParser(this);
            auto offset_type = parse_decl.parse_declaration();
            if (offset_type == nullptr) {
                error_custloc("Error parsing type in __builtin_offsetof", tok.loc);
                return nullptr;
            }
            retain_type_specifier_decl_if_needed(parse_decl);
            check_and_consume(TokenType::COMMA);
            // Parse member designator: field, field[N], field.sub, field[N].sub, etc.
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc("Expected member name in __builtin_offsetof", current_token().loc);
                return nullptr;
            }
            std::string member_name = current_token().value;
            advance();
            std::vector<OffsetOfComponent> designator_path;
            // Parse optional designator path extensions: [N] and .field
            while (gentle_check(TokenType::LEFT_BRACKET) || gentle_check(TokenType::DOT)
                   || gentle_check(TokenType::ARROW)) {
                if (gentle_check_and_consume(TokenType::LEFT_BRACKET)) {
                    auto idx_expr = parse_assignment_expression();
                    auto idx_val = try_evaluate_with_consteval_compat(
                        idx_expr.get(), ConstEvalMode::c_ice());
                    OffsetOfComponent comp;
                    if (idx_val.has_value()) {
                        comp.array_index = *idx_val;
                    } else {
                        comp.array_index_expr = std::move(idx_expr);
                    }
                    designator_path.push_back(std::move(comp));
                    check_and_consume(TokenType::RIGHT_BRACKET);
                } else {
                    advance(); // consume . or ->
                    if (!gentle_check(TokenType::IDENTIFIER)) {
                        error_custloc("Expected member name after field access in __builtin_offsetof", current_token().loc);
                        return nullptr;
                    }
                    OffsetOfComponent comp;
                    comp.field_name = current_token().value;
                    designator_path.push_back(std::move(comp));
                    advance();
                }
            }
            check_and_consume(TokenType::RIGHT_PAREN);
            return collect_->collect_offsetof_expression(
                offset_type, member_name, std::move(designator_path), tok.loc);
        }
        // Handle __builtin_available(...) as a compatibility parse builtin.
        // We currently treat availability checks as always true.
        if (tok.value == "__builtin_available") {
            advance(); // consume '__builtin_available'
            if (!gentle_check(TokenType::LEFT_PAREN)) {
                error_custloc("Expected '(' after __builtin_available", tok.loc);
                return collect_->collect_error_expression("invalid __builtin_available invocation", tok.loc);
            }
            advance(); // consume '('
            int depth = 1;
            while (depth > 0) {
                if (gentle_check(TokenType::Eof)) {
                    error_custloc("Unterminated __builtin_available invocation", tok.loc);
                    return collect_->collect_error_expression("unterminated __builtin_available", tok.loc);
                }
                if (gentle_check(TokenType::LEFT_PAREN)) {
                    depth++;
                } else if (gentle_check(TokenType::RIGHT_PAREN)) {
                    depth--;
                }
                advance();
            }
            return collect_->collect_integer_literal("1", type_ctx->get_builtin(BuiltinTypes::Int), tok.loc);
        }
        bool looks_like_call = (peek_token().type == TokenType::LEFT_PAREN);
        bool might_be_template_id = looks_like_call;
        if (!looks_like_call &&
            is_cxx_mode_active() &&
            peek_token().type == TokenType::LESS_THAN) {
            size_t offset = 1;
            if (skip_template_argument_list_for_expression_probe(offset)) {
                might_be_template_id = true;
                looks_like_call =
                    peek_token_shortcut(offset).type == TokenType::LEFT_PAREN;
            }
        }
        // todo: when we get typedefs this can be ambgioous. But we should realize that at cast_expression not here
        advance();
        return collect_->collect_unqualified_identifier_expression(
            tok.value, looks_like_call, might_be_template_id, tok.loc);
    }
    diag_engine->report_error("unexpected token \"" + tok.value +
          "\" in parse_primary_expression", tok.loc);
    if (!gentle_check(TokenType::Eof)) advance();
    return collect_->collect_error_expression("unexpected token", tok.loc);
}
std::unique_ptr<Expr> Parser::parse_postfix_expression() {
    // Check for compound literal: (type-name) { initializer-list }
    // This is a postfix-expression in the C grammar
    std::unique_ptr<Expr> expr = nullptr;
    Token start_tok = current_token();

    if (gentle_check(TokenType::LEFT_PAREN)) {
        TentativeParsingAction tentative(*this);
        try {
            advance(); // consume '('
            // __extension__ after ( is an expression prefix, not a type specifier
            if (current_token().type != TokenType::EXTENSION_KW && isTokenDeclarationSpec(current_token())) {
                DeclarationParser parse_decl(this);
                auto new_type = parse_decl.parse_declaration();
                if (new_type &&
                    parse_decl.name.empty() &&
                    gentle_check_and_consume(TokenType::RIGHT_PAREN) &&
                    gentle_check(TokenType::LEFT_BRACE)) {
                    retain_type_specifier_decl_if_needed(parse_decl);
                    auto init_list = parse_init_list();
                    expr = collect_->collect_compound_literal_expression(
                        new_type, std::move(init_list), start_tok.loc);
                    tentative.commit();
                }
            }
        } catch (const ParseError&) {
        } catch (const FatalErrorLimitReached&) {
        }
    }

    if (!expr) {
        expr = parse_primary_expression();
    }
    auto base_requires_template_keyword =
        [&](QualType base_type, bool is_arrow) -> bool {
            return analyze_cpp_member_access_base(base_type, is_arrow)
                .requires_template_keyword();
        };
    struct ParsedMemberAccessName {
        std::string name;
        SrcLoc loc;
    };
    auto parse_member_access_name =
        [&](std::string_view access_operator) -> ParsedMemberAccessName {
            if (is_cxx_mode_active() &&
                gentle_check(TokenType::OPERATOR_KW)) {
                SrcLoc member_loc = current_token().loc;
                auto operator_name = try_parse_cpp_operator_function_id_name();
                if (!operator_name) {
                    error(
                        "Expected member name after '" +
                        std::string(access_operator) + "'");
                }
                return ParsedMemberAccessName{
                    std::move(*operator_name),
                    member_loc};
            }

            if (!gentle_check(TokenType::IDENTIFIER)) {
                error(
                    "Expected member name after '" +
                    std::string(access_operator) + "'");
            }
            ParsedMemberAccessName parsed{
                current_token().value,
                current_token().loc};
            advance();
            return parsed;
        };
    auto unqualified_var_ref_names_template = [&](const VarRef* ref) {
        if (!ref || ref->symref || ref->has_cpp_qualified_info() || !collect_) {
            return false;
        }
        auto scope = collect_->collect_current_scope();
        if (!scope || ref->get_name().empty()) {
            return false;
        }
        auto lookup = LookupEngine::lookup_unqualified_template_binding_result(
            ref->get_name(),
            scope,
            /*allow_enclosing_lookup=*/true,
            LookupNamespace::Ordinary);
        return lookup.binding &&
               (lookup.binding->template_decl ||
                lookup.binding->has_template_overload_set());
    };
    while (true) {
        SrcLoc loc = expr->location;
        if (is_cxx_mode_active() &&
            gentle_check(TokenType::LESS_THAN)) {
            auto* callee_ref = dyn_cast<VarRef>(expr.get());
            auto* member_callee = dyn_cast<MemberExpr>(expr.get());
            auto* unresolved_member_callee =
                dyn_cast<UnresolvedMemberExpr>(expr.get());
            auto* unresolved_lookup_callee =
                dyn_cast<UnresolvedLookupExpr>(expr.get());
            if (callee_ref || member_callee ||
                unresolved_member_callee || unresolved_lookup_callee) {
                size_t explicit_suffix_probe_offset = 0;
                bool parse_known_unqualified_template =
                    unqualified_var_ref_names_template(callee_ref) &&
                    skip_template_argument_list_for_expression_probe(
                        explicit_suffix_probe_offset);
                if (parse_known_unqualified_template) {
                    auto explicit_template_args =
                        parse_cpp_template_argument_list();
                    if (lambda_template_requires_clause_depth_ > 0 &&
                        is_lambda_declarator_parameter_clause_ahead()) {
                        expr = collect_->collect_explicit_template_id_expression(
                            std::move(expr),
                            std::move(explicit_template_args),
                            loc);
                        continue;
                    }
                    if (gentle_check(TokenType::LEFT_PAREN)) {
                        advance();
                        std::vector<std::unique_ptr<Expr>> args;
                        if (!gentle_check(TokenType::RIGHT_PAREN)) {
                            do {
                                auto arg = parse_call_argument_expression();
                                args.push_back(std::move(arg));
                            } while (gentle_check_and_consume(TokenType::COMMA));
                        }
                        check_and_consume(TokenType::RIGHT_PAREN);
                        expr = collect_->collect_explicit_function_template_call(
                            std::move(expr),
                            std::move(explicit_template_args),
                            std::move(args),
                            loc);
                        continue;
                    }
                    expr = collect_->collect_explicit_template_id_expression(
                        std::move(expr),
                        std::move(explicit_template_args),
                        loc);
                    continue;
                }
                TentativeParsingAction tentative(*this);
                try {
                    auto explicit_template_args =
                        parse_cpp_template_argument_list();
                    if (lambda_template_requires_clause_depth_ > 0 &&
                        is_lambda_declarator_parameter_clause_ahead()) {
                        tentative.commit();
                        expr = collect_->collect_explicit_template_id_expression(
                            std::move(expr),
                            std::move(explicit_template_args),
                            loc);
                        continue;
                    }
                    if (gentle_check(TokenType::LEFT_PAREN)) {
                        tentative.commit();
                        advance();
                        std::vector<std::unique_ptr<Expr>> args;
                        if (!gentle_check(TokenType::RIGHT_PAREN)) {
                            do {
                                auto arg = parse_call_argument_expression();
                                args.push_back(std::move(arg));
                            } while (gentle_check_and_consume(TokenType::COMMA));
                        }
                        check_and_consume(TokenType::RIGHT_PAREN);
                        expr = collect_->collect_explicit_function_template_call(
                            std::move(expr),
                            std::move(explicit_template_args),
                            std::move(args),
                            loc);
                        continue;
                    }
                    tentative.commit();
                    expr = collect_->collect_explicit_template_id_expression(
                        std::move(expr),
                        std::move(explicit_template_args),
                        loc);
                    continue;
                } catch (const ParseError&) {
                } catch (const FatalErrorLimitReached&) {
                    throw;
                }
            }
        }
        if (lambda_template_requires_clause_depth_ > 0 &&
            is_lambda_declarator_parameter_clause_ahead()) {
            break;
        }
        if (template_head_requires_clause_depth_ > 0 &&
            gentle_check(TokenType::LEFT_BRACKET) &&
            peek_token().type == TokenType::LEFT_BRACKET) {
            break;
        }
        if (gentle_check(TokenType::LEFT_PAREN)) {
            advance();
            std::vector<std::unique_ptr<Expr>> args;
            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                do {
                    auto arg = parse_call_argument_expression();
                    args.push_back(std::move(arg));
                } while (gentle_check_and_consume(TokenType::COMMA));
            }
            check_and_consume(TokenType::RIGHT_PAREN);
            expr = collect_->collect_function_call(std::move(expr), std::move(args), loc);
        } else if (gentle_check(TokenType::LEFT_BRACKET)) {
            advance();
            auto index = parse_expression();
            check_and_consume(TokenType::RIGHT_BRACKET);
            expr = collect_->collect_array_subscript(std::move(expr), std::move(index), loc);
        } else if (gentle_check_and_consume(TokenType::DOT)) {
            if (is_cxx_mode_active() &&
                gentle_check(TokenType::BITWISE_NOT)) {
                expr = parse_cpp_postfix_pseudo_destructor_expression(
                    std::move(expr),
                    false,
                    loc);
                continue;
            }
            // Member access: expr.member
            QualType base_type = expr ? expr->get_type() : QualType();
            bool saw_template_keyword = gentle_check_and_consume(TokenType::TEMPLATE);
            auto member_name = parse_member_access_name(".");
            if (saw_template_keyword) {
                if (!gentle_check(TokenType::LESS_THAN)) {
                    error_custloc(
                        "expected template-id after 'template' keyword",
                        member_name.loc);
                }
            }
            if (!saw_template_keyword &&
                gentle_check(TokenType::LESS_THAN) &&
                base_requires_template_keyword(base_type, false)) {
                diagnose_missing_cpp_template_keyword(
                    member_name.name,
                    member_name.loc);
            }
            bool allow_overloaded_method_set =
                gentle_check(TokenType::LEFT_PAREN) ||
                gentle_check(TokenType::LESS_THAN);
            expr = collect_->collect_member_expression(
                std::move(expr),
                member_name.name,
                false,
                loc,
                allow_overloaded_method_set,
                /*suppress_virtual_dispatch=*/false,
                saw_template_keyword);
        } else if (gentle_check_and_consume(TokenType::ARROW)) {
            if (is_cxx_mode_active() &&
                gentle_check(TokenType::BITWISE_NOT)) {
                expr = parse_cpp_postfix_pseudo_destructor_expression(
                    std::move(expr),
                    true,
                    loc);
                continue;
            }
            // Pointer member access: ptr->member
            QualType base_type = expr ? expr->get_type() : QualType();
            bool saw_template_keyword = gentle_check_and_consume(TokenType::TEMPLATE);
            auto member_name = parse_member_access_name("->");
            if (saw_template_keyword) {
                if (!gentle_check(TokenType::LESS_THAN)) {
                    error_custloc(
                        "expected template-id after 'template' keyword",
                        member_name.loc);
                }
            }
            if (!saw_template_keyword &&
                gentle_check(TokenType::LESS_THAN) &&
                base_requires_template_keyword(base_type, true)) {
                diagnose_missing_cpp_template_keyword(
                    member_name.name,
                    member_name.loc);
            }
            bool allow_overloaded_method_set =
                gentle_check(TokenType::LEFT_PAREN) ||
                gentle_check(TokenType::LESS_THAN);
            expr = collect_->collect_member_expression(
                std::move(expr),
                member_name.name,
                true,
                loc,
                allow_overloaded_method_set,
                /*suppress_virtual_dispatch=*/false,
                saw_template_keyword);
        } else if (gentle_check(TokenType::INCREMENT)) {
            expr = collect_->collect_unary_operation(UnaryOpTypes::INCREMENT_POSTFIX, std::move(expr), loc);
            advance();
        }  else if (gentle_check(TokenType::DECREMENT)) {
            expr = collect_->collect_unary_operation(UnaryOpTypes::DECREMENT_POSTFIX, std::move(expr), loc);
            advance();
        }
        else {
            break;
        }
    }
    return expr;

}

std::unique_ptr<Expr> Parser::parse_cpp_postfix_pseudo_destructor_expression(
    std::unique_ptr<Expr> base,
    bool is_arrow,
    SrcLoc operator_loc) {
    check_and_consume(TokenType::BITWISE_NOT);

    DeclarationParser parse_decl(this);
    auto destroyed_base_type = parse_decl.parse_declaration(false);
    if (!destroyed_base_type || !parse_decl.name.empty()) {
        error_custloc(
            "expected type-name after '~' in pseudo-destructor expression",
            current_token().loc);
    }
    QualType destroyed_type(
        destroyed_base_type,
        parse_decl.qualifiers);
    retain_type_specifier_decl_if_needed(parse_decl);

    check_and_consume(TokenType::LEFT_PAREN);
    check_and_consume(TokenType::RIGHT_PAREN);
    return collect_->collect_cpp_pseudo_destructor_expression(
        std::move(base),
        destroyed_type,
        is_arrow,
        operator_loc);
}

std::unique_ptr<Expr> Parser::parse_unary_expression() {
    Token tok = current_token();
    if (tok.type == TokenType::BITWISE_XOR) {
        if (auto block_expr = parse_block_literal_expression()) {
            return block_expr;
        }
    }
    if (is_cxx_mode_active()) {
        bool saw_global_scope = false;
        bool has_scope_resolution =
            gentle_check(TokenType::SCOPE_RESOLUTION) ||
            (gentle_check(TokenType::COLON) &&
             peek_token().type == TokenType::COLON);
        if (has_scope_resolution) {
            TokenType token_after_scope = gentle_check(TokenType::SCOPE_RESOLUTION)
                ? peek_token().type
                : peek_token(2).type;
            if (token_after_scope == TokenType::NEW ||
                token_after_scope == TokenType::DELETE) {
                consume_cpp_scope_resolution();
                saw_global_scope = true;
                tok = current_token();
            }
        }
        if (tok.type == TokenType::NEW) {
            return parse_cpp_new_expression(saw_global_scope);
        }
        if (tok.type == TokenType::DELETE) {
            return parse_cpp_delete_expression(saw_global_scope);
        }
    }

    // Handle __extension__ as a no-op prefix — parse a cast-expression so that
    // patterns like (__extension__ (Type)(expr)) work correctly.
    if (tok.type == TokenType::EXTENSION_KW) {
        advance(); // consume __extension__
        return parse_cast_expression();
    }

    // Handle _Alignof / __alignof__ operator
    // Grammar: _Alignof ( type-name ) | __alignof__ ( type-name ) | __alignof__ ( expression )
    if (tok.type == TokenType::ALIGNOF) {
        advance(); // consume '_Alignof' / '__alignof__'
        check_and_consume(TokenType::LEFT_PAREN);
        {
            TentativeParsingAction tentative(*this);
            try {
                if (current_token().type != TokenType::EXTENSION_KW) {
                    auto parse_decl = DeclarationParser(this);
                    auto type = parse_decl.parse_declaration();
                    if (type &&
                        parse_decl.name.empty() &&
                        gentle_check_and_consume(TokenType::RIGHT_PAREN) &&
                        !gentle_check(TokenType::LEFT_BRACE)) {
                        retain_type_specifier_decl_if_needed(parse_decl);
                        tentative.commit();
                        return collect_->collect_alignof_type(type, tok.loc);
                    }
                }
            } catch (const ParseError&) {
            } catch (const FatalErrorLimitReached&) {
            }
        }

        // GCC extension: __alignof__(expression)
        Collect::UnevaluatedContextScope unevaluated_scope(
            collect_.get(), "_Alignof");
        auto expr = parse_assignment_expression();
        check_and_consume(TokenType::RIGHT_PAREN);
        return collect_->collect_alignof_expression(std::move(expr), tok.loc);
    }

    if (is_cxx_mode_active() && tok.type == TokenType::NOEXCEPT_KW) {
        advance(); // consume 'noexcept'
        check_and_consume(TokenType::LEFT_PAREN);
        Collect::UnevaluatedContextScope unevaluated_scope(
            collect_.get(), "noexcept");
        auto expr = parse_expression();
        check_and_consume(TokenType::RIGHT_PAREN);
        return collect_->collect_cpp_noexcept_expression(
            std::move(expr),
            tok.loc);
    }

    // Handle sizeof operator
    // Grammar: sizeof unary-expression | sizeof ( type-name )
    if (tok.type == TokenType::SIZEOF) {
        advance(); // consume 'sizeof'

        if (gentle_check(TokenType::ELLIPSIS)) {
            advance(); // consume '...'
            check_and_consume(TokenType::LEFT_PAREN);
            Token pack_tok = current_token();
            check_and_consume(TokenType::IDENTIFIER);
            check_and_consume(TokenType::RIGHT_PAREN);

            const auto* parameter_pack =
                find_active_template_parameter_pack(pack_tok.value);
            if (!parameter_pack) {
                error_custloc(
                    "identifier '" + pack_tok.value +
                        "' is not a template parameter pack",
                    pack_tok.loc);
                return collect_->collect_error_expression(
                    "invalid sizeof... operand",
                    tok.loc);
            }
            return collect_->collect_sizeof_pack_expression(
                pack_tok.value,
                parameter_pack,
                tok.loc);
        }

        // Check if we have sizeof(type-name) rather than sizeof unary-expression.
        if (gentle_check(TokenType::LEFT_PAREN)) {
            {
                TentativeParsingAction tentative(*this);
                try {
                    advance(); // consume '('
                    // __extension__ after ( is an expression prefix, not a type specifier
                    if (current_token().type != TokenType::EXTENSION_KW &&
                        isTokenDeclarationSpec(current_token())) {
                        auto parse_decl = DeclarationParser(this);
                        auto type = parse_decl.parse_declaration();
                        if (type &&
                            parse_decl.name.empty() &&
                            gentle_check_and_consume(TokenType::RIGHT_PAREN) &&
                            !gentle_check(TokenType::LEFT_BRACE)) {
                            retain_type_specifier_decl_if_needed(parse_decl);
                            tentative.commit();
                            return collect_->collect_sizeof_type(type, tok.loc);
                        }
                    }
                } catch (const ParseError&) {
                } catch (const FatalErrorLimitReached&) {
                }
            }

            // Not a type-name form (or it's a compound literal) — parse as
            // sizeof unary-expression so postfix ops like -> are included.
            // e.g., sizeof ((Stab_Sym*)0)->n_value
            Collect::UnevaluatedContextScope unevaluated_scope(
                collect_.get(), "sizeof");
            auto expr = parse_unary_expression();
            return collect_->collect_sizeof_expression(std::move(expr), tok.loc);
        } else {
            // sizeof unary-expression (without parentheses)
            // e.g., sizeof x, sizeof *p, sizeof arr[0]
            Collect::UnevaluatedContextScope unevaluated_scope(
                collect_.get(), "sizeof");
            auto expr = parse_unary_expression();
            return collect_->collect_sizeof_expression(std::move(expr), tok.loc);
        }
    }

    // Handle labels-as-values: &&label
    if (tok.type == TokenType::LOGICAL_AND) {
        advance(); // consume '&&'
        if (!gentle_check(TokenType::IDENTIFIER)) {
            error("expected label after '&&'");
            return nullptr;
        }
        std::string label = resolve_local_label_name(current_token().value);
        advance();
        return collect_->collect_label_address_expression(label, tok.loc);
    }

    // Handle __real__ and __imag__ operators
    if (tok.type == TokenType::REAL_PART || tok.type == TokenType::IMAG_PART) {
        UnaryOpTypes uop = (tok.type == TokenType::REAL_PART) ? UnaryOpTypes::REAL_PART : UnaryOpTypes::IMAG_PART;
        advance();
        auto exp = parse_unary_expression();
        return collect_->collect_unary_operation(uop, std::move(exp), tok.loc);
    }

    if (is_cxx_mode_active() && tok.type == TokenType::BITWISE_AND) {
        auto consume_scope_resolution = [&](size_t& offset) -> bool {
            Token sep = peek_token_shortcut(offset);
            if (sep.type == TokenType::SCOPE_RESOLUTION) {
                ++offset;
                return true;
            }
            if (sep.type == TokenType::COLON &&
                peek_token_shortcut(offset + 1).type == TokenType::COLON) {
                offset += 2;
                return true;
            }
            return false;
        };

        size_t offset = 1; // token after '&'
        bool saw_scope_resolution = false;
        std::vector<std::string> qualified_components;

        if (consume_scope_resolution(offset)) {
            saw_scope_resolution = true;
        }
        if (peek_token_shortcut(offset).type == TokenType::IDENTIFIER) {
            qualified_components.push_back(peek_token_shortcut(offset).value);
            ++offset;
            while (consume_scope_resolution(offset)) {
                saw_scope_resolution = true;
                if (peek_token_shortcut(offset).type != TokenType::IDENTIFIER) {
                    qualified_components.clear();
                    break;
                }
                qualified_components.push_back(peek_token_shortcut(offset).value);
                ++offset;
            }
        }

        if (saw_scope_resolution && qualified_components.size() >= 2) {
            const std::string& owner_candidate =
                qualified_components[qualified_components.size() - 2];
            auto owner_type_raw = collect_->collect_lookup_tag_type(owner_candidate, true);
            if (owner_type_raw &&
                canonical_type_kind(owner_type_raw) == TypeKind::Object) {
                std::string member_name = qualified_components.back();

                advance(); // consume '&'
                size_t tokens_after_amp = offset - 1;
                for (size_t i = 0; i < tokens_after_amp; ++i) {
                    advance();
                }
                return collect_->collect_member_pointer_literal_expression(
                    owner_candidate,
                    member_name,
                    tok.loc);
            }
        }
    }

    // Handle other unary operators
    if (is_unary_operator_token(tok.type)) {
        UnaryOpTypes uop = string2uop(tok.value);
        if (uop == UnaryOpTypes::DECREMENT) uop = UnaryOpTypes::DECREMENT_PREFIX;
        if (uop == UnaryOpTypes::INCREMENT) uop = UnaryOpTypes::INCREMENT_PREFIX;
        advance();
        // C11 6.5.3: unary-operator cast-expression (not unary-expression)
        // This allows *(uint16_t *)buf to parse the cast correctly
        auto exp = parse_cast_expression();
        auto uast = collect_->collect_unary_operation(uop, std::move(exp), tok.loc);
        return std::move(uast);
    }
    return parse_postfix_expression();
}
std::unique_ptr<Expr> Parser::parse_cast_expression() {
    Token t = current_token();
    if (gentle_check(TokenType::LEFT_PAREN)) {
        TentativeParsingAction tentative(*this);
        try {
            advance(); // consume '('
            // __extension__ after ( is an expression prefix, not a type specifier
            if (current_token().type != TokenType::EXTENSION_KW && isTokenDeclarationSpec(current_token())) {
                auto parse_decl = DeclarationParser(this);
                auto new_type = parse_decl.parse_declaration();
                if (new_type &&
                    parse_decl.name.empty() &&
                    parse_decl.str_class == StorageClass::NONE &&
                    gentle_check_and_consume(TokenType::RIGHT_PAREN) &&
                    token_can_start_cast_operand(current_token().type) &&
                    !gentle_check(TokenType::LEFT_BRACE)) {
                    retain_type_specifier_decl_if_needed(parse_decl);
                    auto exp = parse_cast_expression();
                    auto cast_expr = collect_->collect_explicit_cast(std::move(exp), new_type, t.loc);
                    tentative.commit();
                    return cast_expr;
                }
            }
        } catch (const ParseError&) {
        } catch (const FatalErrorLimitReached&) {
        }
    }

    return parse_unary_expression();
}
bool Parser::is_init_designator_start() {
    if (gentle_check(TokenType::DOT) || gentle_check(TokenType::LEFT_BRACKET)) {
        return true;
    }
    if (current_token().type == TokenType::IDENTIFIER && peek_token().type == TokenType::COLON) {
        return true;
    }
    return false;
}

std::vector<Designator> Parser::parse_designator_list() {
    std::vector<Designator> designators;
    while (true) {
        if (gentle_check(TokenType::DOT)) {
            check_and_consume(TokenType::DOT);
            Token field_tok = current_token();
            check_and_consume(TokenType::IDENTIFIER);
            designators.push_back(Designator::field(field_tok.value, field_tok.loc));
            continue;
        }
        if (gentle_check(TokenType::LEFT_BRACKET)) {
            Token bracket_tok = current_token();
            check_and_consume(TokenType::LEFT_BRACKET);
            auto start_expr = parse_assignment_expression();
            if (gentle_check(TokenType::ELLIPSIS)) {
                check_and_consume(TokenType::ELLIPSIS);
                auto end_expr = parse_assignment_expression();
                check_and_consume(TokenType::RIGHT_BRACKET);
                designators.push_back(Designator::range_designator(std::move(start_expr), std::move(end_expr), bracket_tok.loc));
            } else {
                check_and_consume(TokenType::RIGHT_BRACKET);
                designators.push_back(Designator::index_designator(std::move(start_expr), bracket_tok.loc));
            }
            continue;
        }
        if (current_token().type == TokenType::IDENTIFIER && peek_token().type == TokenType::COLON) {
            Token field_tok = current_token();
            check_and_consume(TokenType::IDENTIFIER);
            check_and_consume(TokenType::COLON);
            designators.push_back(Designator::field(field_tok.value, field_tok.loc));
            continue;
        }
        break;
    }
    return designators;
}
std::unique_ptr<Expr> Parser::parse_init_list() {
    Token t = current_token();
    check_and_consume(TokenType::LEFT_BRACE);
    auto init_list = collect_->collect_initializer_list_expression(t.loc);
    size_t last_recovery_idx = std::numeric_limits<size_t>::max();
    while (!gentle_check(TokenType::RIGHT_BRACE) && !gentle_check(TokenType::Eof)) {
        try {
            InitElement elem;
            elem.loc = current_token().loc;
            if (is_init_designator_start()) {
                elem.designators = parse_designator_list();
                if (gentle_check(TokenType::ASSIGN)) {
                    check_and_consume(TokenType::ASSIGN);
                }
            }
            if (gentle_check(TokenType::LEFT_BRACE)) {
                elem.value = parse_init_list();
            } else {
                elem.value =
                    parse_assignment_expression_with_optional_pack_expansion();
            }
            init_list->elements.push_back(std::move(elem));
            diag_engine->sync_point_reached();
            last_recovery_idx = std::numeric_limits<size_t>::max();
            if (!gentle_check(TokenType::RIGHT_BRACE)) {
                check_and_consume(TokenType::COMMA);
            }
        } catch (ParseError& e) {
            if (is_in_tentative_context()) {
                throw;
            }
            size_t recover_start_idx = get_token_idx();
            skip_to_init_list_sync_point();
            if (get_token_idx() == recover_start_idx &&
                recover_start_idx == last_recovery_idx &&
                !gentle_check(TokenType::Eof)) {
                advance();
            }
            last_recovery_idx = get_token_idx();
            diag_engine->sync_point_reached();
            InitElement err_elem;
            err_elem.loc = e.location;
            err_elem.value = collect_->collect_error_expression(e.message, e.location);
            init_list->elements.push_back(std::move(err_elem));
        }
    }
    check_and_consume(TokenType::RIGHT_BRACE);
    return init_list;
}

std::unique_ptr<Expr> Parser::parse_paren_init_list() {
    Token t = current_token();
    check_and_consume(TokenType::LEFT_PAREN);
    auto init_list = collect_->collect_initializer_list_expression(t.loc);
    init_list->is_paren_init = true;

    if (gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
        return init_list;
    }

    while (true) {
        InitElement elem;
        elem.loc = current_token().loc;
        if (gentle_check(TokenType::LEFT_BRACE)) {
            elem.value = parse_init_list();
        } else {
            elem.value =
                parse_assignment_expression_with_optional_pack_expansion();
        }
        init_list->elements.push_back(std::move(elem));

        if (gentle_check_and_consume(TokenType::COMMA)) {
            continue;
        }
        check_and_consume(TokenType::RIGHT_PAREN);
        break;
    }

    return init_list;
}
std::unique_ptr<Expr> Parser::parse_binary_expression(int min_precedence) {
    std::unique_ptr<Expr> left = parse_cast_expression();
    while (is_binary_operator(current_token().value)) {
        TokenType op_type = current_token().type;
        if (is_at_top_level_template_argument_expression() &&
            (op_type == TokenType::GREATER_THAN ||
             op_type == TokenType::RIGHT_SHIFT ||
             op_type == TokenType::ASSIGN_RSHIFT)) {
            break;
        }
        std::string op = current_token().value;
        Token op_tok = current_token();
        int precedence = static_cast<int>(get_prec(op_type));
        if (precedence == static_cast<int>(PrecLevel::UNKNOWN)) {
            throw std::runtime_error("error in parse_binop");
        }
        if (precedence < min_precedence) {
            break;
        }
        advance();
        if (op_type == TokenType::QUESTION) {
            // conditional — GCC extension: omitted middle operand (a ?: b)
            std::unique_ptr<Expr> right1 = nullptr;
            if (current_token().type != TokenType::COLON) {
                right1 = parse_binary_expression();
            }
            check_and_consume(TokenType::COLON);
            auto right2 = parse_binary_expression(precedence);
            auto newLeft = collect_->collect_conditional_expression(std::move(left),
                std::move(right1), std::move(right2), QualType(), op_tok.loc);
            left = std::move(newLeft);
        } else if (is_assignment_token(op_type)) {
            // todo
            auto right = parse_binary_expression(precedence);
            if (op_type != TokenType::ASSIGN) {
                // compound assignment
                /* A compound assignment of the form E1 op= E2 is equivalent to the simple assignment expression E1 =
                 * E1 op (E2), except that the lvalue E1 is evaluated only once, and with respect to an indeterminately
                 * sequenced function call, the operation of a compound assignment is a single evaluation. */
                auto bop  = string2bop(op);
                left = collect_->collect_compound_assign_operation(std::move(left),
                    std::move(right), bop, op_tok.loc);
            } else {
                // Collect validates and types binary operations
                auto newLeft = collect_->collect_binary_operation(std::move(left), std::move(right),
                    string2bop(op), op_tok.loc);
                left = std::move(newLeft);
            }
            // same as below, except we dont
        } else {
            auto new_prec = precedence+1;
            auto right = parse_binary_expression(new_prec);

            // Collect validates and types binary operations
            auto newLeft = collect_->collect_binary_operation(std::move(left),
                std::move(right),
                string2bop(op), op_tok.loc);
            left = std::move(newLeft);
        }
    }
    return left;


}

std::unique_ptr<Expr> Parser::parse_expression() {
    auto left = parse_assignment_expression();
    while (gentle_check(TokenType::COMMA)) {
        Token op_tok = current_token();
        std::string op = current_token().value;
        advance();
        auto right = parse_assignment_expression();
        left = collect_->collect_binary_operation(
            std::move(left),
            std::move(right),
            string2bop(op),
            op_tok.loc);
    }
    return left;
}
std::unique_ptr<Expr> Parser::parse_assignment_expression() {
    if (is_cxx_mode_active() && gentle_check(TokenType::THROW_KW)) {
        return parse_cpp_throw_expression();
    }
    return parse_binary_expression(static_cast<int>(PrecLevel::ASSIGNMENT));
}

std::unique_ptr<Expr> Parser::parse_conditional_expression() {
    return parse_binary_expression(static_cast<int>(PrecLevel::CONDITIONAL));
}
