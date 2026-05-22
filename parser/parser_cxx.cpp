#include "parser.h"
#include "cpp_out_of_line_match.h"
#include "tentative_syntax_probe.h"
#include "../collect/lookup_engine.h"
#include "../collect/collect_templates_internal.h"
#include "../helpers/casting.h"
#include "../numeric_utils.h"
#include "../helpers/qualified_name_utils.h"
#include "../helpers/auto_type_utils.h"

// C++-only parser entrypoints and helpers belong here.
// Keep shared C/C++ parsing logic in parser.cpp.

#include <algorithm>
#include <cstdint>
#include <limits>
#include <optional>

namespace {
Token make_template_split_token(const Token& source,
                                TokenType type,
                                std::string value,
                                uint32_t offset_adjust = 0) {
    Token split = source;
    split.type = type;
    split.value = std::move(value);
    if (!split.loc.isInvalid()) {
        split.loc.offset += offset_adjust;
    }
    return split;
}

bool is_integer_pack_builtin_expr(const Expr* expr) {
    auto strip_implicit_casts_and_parens = [](const Expr* candidate) -> Expr* {
        auto* stripped =
            Collect::strip_implicit_casts(const_cast<Expr*>(candidate));
        while (auto* paren = dyn_cast<ParenExpr>(stripped)) {
            stripped = Collect::strip_implicit_casts(paren->subexpr.get());
        }
        return stripped;
    };

    auto* stripped = strip_implicit_casts_and_parens(expr);
    const auto* builtin = dyn_cast<BuiltinCallExpr>(stripped);
    if (builtin && builtin->kind == BuiltinKind::INTEGER_PACK) {
        return true;
    }
    if (const auto* dependent_call = dyn_cast<DependentCallExpr>(stripped)) {
        const auto* callee_ref = dyn_cast<VarRef>(
            strip_implicit_casts_and_parens(dependent_call->callee.get()));
        return callee_ref && callee_ref->get_name() == "__integer_pack";
    }
    if (const auto* call = dyn_cast<FuncCall>(stripped)) {
        const auto* callee_ref = dyn_cast<VarRef>(
            strip_implicit_casts_and_parens(call->func.get()));
        return callee_ref && callee_ref->get_name() == "__integer_pack";
    }
    return false;
}

bool cpp_in_class_definition_is_inline(bool explicitly_inline, bool is_definition) {
    return explicitly_inline || is_definition;
}

template <typename TemplateDeclT>
TemplateDeclT* canonical_primary_template_for_partial_registration(
    TemplateDeclT* primary_template) {
    if (!primary_template) {
        return nullptr;
    }
    const TemplateDecl* canonical_template =
        get_template_decl_canonical_decl(primary_template);
    auto* canonical_primary = dyn_cast<TemplateDeclT>(
        const_cast<TemplateDecl*>(canonical_template));
    return canonical_primary ? canonical_primary : primary_template;
}

const ClassTemplateDecl* canonical_class_template_decl(
    const ClassTemplateDecl* class_template) {
    if (!class_template) {
        return nullptr;
    }
    const TemplateDecl* canonical_template =
        get_template_decl_canonical_decl(class_template);
    auto* canonical_class_template = dyn_cast<ClassTemplateDecl>(
        const_cast<TemplateDecl*>(canonical_template));
    return canonical_class_template ? canonical_class_template : class_template;
}

const ClassTemplateDecl* class_template_decl_from_friend_type(
    QualType friend_type,
    const ASTContext* ast_ctx) {
    if (!friend_type) {
        return nullptr;
    }
    QualType desugared_friend_type = desugar_type(friend_type, ast_ctx);
    if (auto specialization_type =
            dyn_cast_shared<TemplateSpecializationType>(
                desugared_friend_type.get_shared())) {
        return canonical_class_template_decl(
            dyn_cast<ClassTemplateDecl>(
                const_cast<Decl*>(specialization_type->primary_template)));
    }
    if (auto object_type =
            dyn_cast_shared<ObjectType>(desugared_friend_type.get_shared())) {
        return canonical_class_template_decl(
            object_type->get_primary_class_template());
    }
    return nullptr;
}

} // namespace

bool Parser::is_cxx_mode_active() const {
    return lang_opts.is_cxx_mode();
}

bool Parser::can_parse_namespace_scope_template_declaration() const {
    if (!is_cxx_mode_active() || !collect_) {
        return false;
    }
    if (is_parsing_cpp_record_body()) {
        return false;
    }
    auto scope = collect_->collect_current_scope();
    while (scope &&
           scope_flags_contains(scope->flags, ScopeFlags::TemplateParameterScope)) {
        scope = scope->parent;
    }
    if (!scope) {
        return false;
    }
    if (scope_flags_contains(scope->flags, ScopeFlags::FunctionScope) ||
        scope_flags_contains(scope->flags, ScopeFlags::BlockScope) ||
        scope_flags_contains(scope->flags, ScopeFlags::PrototypeScope)) {
        return false;
    }
    return scope_flags_contains(scope->flags, ScopeFlags::FileScope) ||
           scope_flags_contains(scope->flags, ScopeFlags::NamespaceScope);
}

bool Parser::is_in_template_pattern_context() const {
    return template_pattern_depth_ > 0;
}

std::string Parser::make_cpp_unsupported_message(std::string_view feature) const {
    return "C++ parser unsupported syntax: " + std::string(feature);
}

void Parser::fail_cpp_unsupported(std::string_view feature, SrcLoc loc) {
    error_custloc(make_cpp_unsupported_message(feature), loc);
}

bool Parser::is_cpp_operator_function_name(std::string_view name) const {
    return name.rfind("operator", 0) == 0;
}

std::optional<std::string>
Parser::try_parse_cpp_overloadable_operator_function_id_name_after_operator_keyword() {
    auto make_operator_name = [](std::string_view suffix) {
        return std::string("operator") + std::string(suffix);
    };

    auto consume_paired_operator =
        [&](TokenType open_tok,
            TokenType close_tok,
            std::string_view suffix) -> std::optional<std::string> {
        if (!gentle_check(open_tok) || peek_token().type != close_tok) {
            return std::nullopt;
        }
        advance();
        advance();
        return make_operator_name(suffix);
    };

    if (auto name = consume_paired_operator(
            TokenType::LEFT_PAREN,
            TokenType::RIGHT_PAREN,
            "()")) {
        return name;
    }
    if (auto name = consume_paired_operator(
            TokenType::LEFT_BRACKET,
            TokenType::RIGHT_BRACKET,
            "[]")) {
        return name;
    }

    if (gentle_check(TokenType::STRING_LITERAL)) {
        Token literal_token = current_token();
        advance();
        if (literal_token.literal_prefix != LiteralPrefix::None ||
            !literal_token.value.empty()) {
            error_custloc(
                "literal operator name requires an empty string literal after 'operator'",
                literal_token.loc);
        }
        if (!gentle_check(TokenType::IDENTIFIER)) {
            error_custloc(
                "expected identifier suffix in literal operator name",
                current_token().loc);
            return make_operator_name("\"\"");
        }
        std::string literal_suffix = current_token().value;
        advance();
        return make_operator_name("\"\"" + literal_suffix);
    }

    if (gentle_check(TokenType::NEW)) {
        advance(); // consume 'new'
        if (auto name = consume_paired_operator(
                TokenType::LEFT_BRACKET,
                TokenType::RIGHT_BRACKET,
                "new[]")) {
            return name;
        }
        return make_operator_name("new");
    }
    if (gentle_check(TokenType::DELETE)) {
        advance(); // consume 'delete'
        if (auto name = consume_paired_operator(
                TokenType::LEFT_BRACKET,
                TokenType::RIGHT_BRACKET,
                "delete[]")) {
            return name;
        }
        return make_operator_name("delete");
    }

    std::string_view suffix;
    switch (current_token().type) {
        case TokenType::INCREMENT:
            suffix = "++";
            break;
        case TokenType::DECREMENT:
            suffix = "--";
            break;
        case TokenType::PLUS:
            suffix = "+";
            break;
        case TokenType::NEGATE:
            suffix = "-";
            break;
        case TokenType::MULTIPLY:
            suffix = "*";
            break;
        case TokenType::DIVIDE:
            suffix = "/";
            break;
        case TokenType::MODULO:
            suffix = "%";
            break;
        case TokenType::BITWISE_AND:
            suffix = "&";
            break;
        case TokenType::BITWISE_OR:
            suffix = "|";
            break;
        case TokenType::BITWISE_XOR:
            suffix = "^";
            break;
        case TokenType::BITWISE_NOT:
            suffix = "~";
            break;
        case TokenType::LOGICAL_NOT:
            suffix = "!";
            break;
        case TokenType::ASSIGN:
            suffix = "=";
            break;
        case TokenType::LESS_THAN:
            suffix = "<";
            break;
        case TokenType::GREATER_THAN:
            suffix = ">";
            break;
        case TokenType::ASSIGN_ADD:
            suffix = "+=";
            break;
        case TokenType::ASSIGN_SUB:
            suffix = "-=";
            break;
        case TokenType::ASSIGN_MUL:
            suffix = "*=";
            break;
        case TokenType::ASSIGN_DIV:
            suffix = "/=";
            break;
        case TokenType::ASSIGN_MOD:
            suffix = "%=";
            break;
        case TokenType::ASSIGN_AND:
            suffix = "&=";
            break;
        case TokenType::ASSIGN_OR:
            suffix = "|=";
            break;
        case TokenType::ASSIGN_XOR:
            suffix = "^=";
            break;
        case TokenType::LEFT_SHIFT:
            suffix = "<<";
            break;
        case TokenType::RIGHT_SHIFT:
            suffix = ">>";
            break;
        case TokenType::ASSIGN_LSHIFT:
            suffix = "<<=";
            break;
        case TokenType::ASSIGN_RSHIFT:
            suffix = ">>=";
            break;
        case TokenType::EQUAL_TO:
            suffix = "==";
            break;
        case TokenType::NOT_EQUAL:
            suffix = "!=";
            break;
        case TokenType::LESS_EQUAL_THAN:
            suffix = "<=";
            break;
        case TokenType::THREE_WAY_COMPARE:
            suffix = "<=>";
            break;
        case TokenType::GREATER_EQUAL_THAN:
            suffix = ">=";
            break;
        case TokenType::LOGICAL_AND:
            suffix = "&&";
            break;
        case TokenType::LOGICAL_OR:
            suffix = "||";
            break;
        case TokenType::COMMA:
            suffix = ",";
            break;
        case TokenType::ARROW:
            suffix = "->";
            break;
        case TokenType::ARROW_STAR:
            suffix = "->*";
            break;
        default:
            break;
    }

    if (!suffix.empty()) {
        advance();
        return make_operator_name(suffix);
    }

    return std::nullopt;
}

std::optional<std::string> Parser::try_parse_cpp_operator_function_id_name() {
    if (!is_cxx_mode_active() || !gentle_check(TokenType::OPERATOR_KW)) {
        return std::nullopt;
    }

    Token operator_kw_tok = current_token();
    advance(); // consume 'operator'

    if (auto name =
            try_parse_cpp_overloadable_operator_function_id_name_after_operator_keyword()) {
        return name;
    }

    error_custloc(
        "expected overloaded operator name after 'operator'",
        operator_kw_tok.loc);
    return std::nullopt;
}

bool Parser::is_cpp_member_only_operator_name(std::string_view name) const {
    return name == "operator=" ||
           name == "operator[]" ||
           name == "operator()" ||
           name == "operator->";
}

void Parser::validate_cpp_operator_function_declaration(
    std::string_view name,
    bool in_class_member_context,
    bool is_static_member,
    SrcLoc loc) {
    if (!is_cxx_mode_active() || !is_cpp_operator_function_name(name)) {
        return;
    }
    if (is_cpp_member_only_operator_name(name) &&
        (!in_class_member_context || is_static_member)) {
        error_custloc(
            "overloaded '" + std::string(name) +
                "' must be a non-static member function",
            loc);
    }
}

bool Parser::is_cpp_scope_resolution_here() {
    if (gentle_check(TokenType::SCOPE_RESOLUTION)) {
        return true;
    }
    return gentle_check(TokenType::COLON) && peek_token().type == TokenType::COLON;
}

bool Parser::consume_cpp_scope_resolution() {
    if (gentle_check(TokenType::SCOPE_RESOLUTION)) {
        advance();
        return true;
    }
    if (gentle_check(TokenType::COLON) && peek_token().type == TokenType::COLON) {
        advance();
        advance();
        return true;
    }
    return false;
}

bool Parser::is_parsing_cpp_record_body() const {
    return !cxx_record_parse_stack_.empty();
}

std::string Parser::current_cpp_record_qualifier_prefix() const {
    std::string qualifier;
    for (const auto& frame : cxx_record_parse_stack_) {
        std::string component =
            frame.semantic_owner ? frame.semantic_owner->tag : frame.name;
        if (component.empty()) {
            continue;
        }
        if (!qualifier.empty()) {
            qualifier += "::";
        }
        qualifier += component;
    }
    return qualifier;
}

std::shared_ptr<Scope> Parser::nearest_cpp_friend_namespace_scope() const {
    if (!collect_) {
        return nullptr;
    }
    auto scope = collect_->collect_current_scope();
    while (scope &&
           !scope_flags_contains(scope->flags, ScopeFlags::FileScope) &&
           !scope_flags_contains(scope->flags, ScopeFlags::NamespaceScope)) {
        scope = scope->parent;
    }
    return scope ? scope : collect_->collect_current_scope();
}

const ObjectDecl* Parser::ensure_cpp_specialized_record_semantic_owner(
    CppRecordKind record_kind,
    const std::string& name,
    const std::vector<TemplateArgument>& specialization_arguments,
    SrcLoc loc,
    const ClassTemplateDecl* primary_class_template,
    bool has_specialization_argument_list) {
    if (!collect_ ||
        name.empty() ||
        !has_specialization_argument_list) {
        return nullptr;
    }

    for (const auto& argument : specialization_arguments) {
        switch (argument.kind) {
            case TemplateArgumentKind::Type:
                if (!argument.type ||
                    type_depends_on_template_parameters(
                        argument.type,
                        ast_ctx.get())) {
                    return nullptr;
                }
                break;
            case TemplateArgumentKind::Value:
                if (!argument.value_type ||
                    type_depends_on_template_parameters(
                        argument.value_type,
                        ast_ctx.get())) {
                    return nullptr;
                }
                break;
            case TemplateArgumentKind::Template:
                if (!argument.template_decl) {
                    return nullptr;
                }
                break;
        }
    }

    std::string specialization_name(name);
    specialization_name += "<";
    for (size_t idx = 0; idx < specialization_arguments.size(); ++idx) {
        if (idx != 0) {
            specialization_name += ", ";
        }
        specialization_name += specialization_arguments[idx].to_string();
    }
    specialization_name += ">";

    if (auto* existing_tag_decl =
            collect_->collect_lookup_tag_decl(specialization_name, false)) {
        auto* existing_owner = dyn_cast<ObjectDecl>(existing_tag_decl);
        if (!existing_owner) {
            error_custloc(
                "tag '" + specialization_name +
                    "' was previously declared with a different kind",
                loc);
        }
        return existing_owner;
    }

    const ClassTemplateDecl* resolved_primary = primary_class_template;
    if (!resolved_primary) {
        auto lookup_scope = collect_->collect_current_scope();
        while (lookup_scope &&
               scope_flags_contains(
                   lookup_scope->flags,
                   ScopeFlags::TemplateParameterScope)) {
            lookup_scope = lookup_scope->parent;
        }
        const DeclBinding* template_binding =
            LookupEngine::lookup_unqualified_template_binding(
                name,
                lookup_scope ? lookup_scope : collect_->collect_current_scope(),
                true,
                LookupNamespace::Tag);
        const Decl* primary_template_decl = nullptr;
        if (template_binding) {
            primary_template_decl = template_binding->template_decl;
            if (!primary_template_decl &&
                template_binding->template_overload_candidates.size() == 1) {
                primary_template_decl =
                    template_binding->template_overload_candidates.front();
            }
        }
        resolved_primary =
            dyn_cast<ClassTemplateDecl>(primary_template_decl);
    }

    bool is_union = record_kind == CppRecordKind::Union;
    auto specialization_type = std::make_shared<ObjectType>(
        specialization_name,
        is_union,
        true);
    if (resolved_primary) {
        specialization_type->set_class_template_specialization_info(
            resolved_primary,
            specialization_arguments);
    }

    auto placeholder_decl = collect_->collect_record_declaration(
        specialization_name,
        specialization_type,
        is_union,
        loc);
    if (!placeholder_decl) {
        return nullptr;
    }

    collect_->query_publish_record_semantics(
        placeholder_decl.get(),
        RecordSemanticState{});
    collect_->collect_add_tag_decl(specialization_name, placeholder_decl.get());
    auto* semantic_owner = placeholder_decl.get();
    cpp_transient_semantic_decls_.push_back(std::move(placeholder_decl));
    return semantic_owner;
}

std::optional<TemplateArgument> Parser::try_parse_cpp_template_name_argument() {
    if (!collect_) {
        return std::nullopt;
    }

    auto current_scope = collect_->collect_current_scope();
    auto current_context = collect_->get_current_decl_context();
    if (!current_scope || !current_context) {
        return std::nullopt;
    }

    RevertingTentativeParsingAction tentative(*this);
    bool has_global_qualifier = consume_cpp_scope_resolution();
    if (!gentle_check(TokenType::IDENTIFIER)) {
        return std::nullopt;
    }

    auto parse_component = [&](bool preceded_by_template_keyword)
        -> CppQualifiedNameComponent {
        if (!gentle_check(TokenType::IDENTIFIER)) {
            return {};
        }
        CppQualifiedNameComponent component;
        component.name = current_token().value;
        component.loc = current_token().loc;
        component.preceded_by_template_keyword = preceded_by_template_keyword;
        advance();
        if (gentle_check(TokenType::LESS_THAN)) {
            RevertingTentativeParsingAction template_args(*this);
            auto parsed_arguments = parse_cpp_template_argument_list();
            if (is_cpp_scope_resolution_here()) {
                template_args.commit();
                component.has_template_argument_list = true;
                component.template_arguments = std::move(parsed_arguments);
            }
        }
        return component;
    };

    std::vector<CppQualifiedNameComponent> components;
    components.push_back(parse_component(false));
    while (is_cpp_scope_resolution_here()) {
        consume_cpp_scope_resolution();
        bool preceded_by_template_keyword =
            gentle_check_and_consume(TokenType::TEMPLATE);
        if (!gentle_check(TokenType::IDENTIFIER)) {
            return std::nullopt;
        }
        components.push_back(parse_component(preceded_by_template_keyword));
    }

    if (components.empty()) {
        return std::nullopt;
    }

    if (!is_cpp_template_argument_boundary_here() &&
        !gentle_check(TokenType::ELLIPSIS)) {
        return std::nullopt;
    }

    const auto& terminal_component = components.back();
    if (terminal_component.has_template_argument_list) {
        return std::nullopt;
    }

    if (!has_global_qualifier && components.size() == 1 &&
        !terminal_component.preceded_by_template_keyword) {
        if (collect_->collect_lookup_typedef_symbol(
                terminal_component.name,
                true)) {
            return std::nullopt;
        }
        QualType current_record_type =
            collect_->collect_current_cpp_record_lookup_type();
        if (current_record_type &&
            collect_->collect_lookup_record_nested_type(
                current_record_type,
                terminal_component.name)) {
            return std::nullopt;
        }
    }

    auto format_template_name_argument =
        [&](const std::vector<CppQualifiedNameComponent>& parts) {
            std::string spelled;
            if (has_global_qualifier) {
                spelled += "::";
            }
            for (size_t idx = 0; idx < parts.size(); ++idx) {
                if (idx > 0) {
                    spelled += "::";
                }
                if (parts[idx].preceded_by_template_keyword) {
                    spelled += "template ";
                }
                spelled += parts[idx].spelling();
            }
            return spelled;
        };

    auto resolve_single_template = [](const DeclBinding* binding) -> const Decl* {
        if (!binding) {
            return nullptr;
        }
        if (binding->template_decl) {
            return binding->template_decl;
        }
        if (binding->template_overload_candidates.size() == 1) {
            return binding->template_overload_candidates.front();
        }
        return nullptr;
    };

    std::vector<std::string> plain_qualifiers;
    plain_qualifiers.reserve(components.size() > 0 ? components.size() - 1 : 0);
    bool qualifiers_need_owner_chain = false;
    for (size_t idx = 0; idx + 1 < components.size(); ++idx) {
        const auto& component = components[idx];
        if (component.preceded_by_template_keyword ||
            component.has_template_argument_list) {
            qualifiers_need_owner_chain = true;
            break;
        }
        plain_qualifiers.push_back(component.name);
    }

    const Decl* resolved_template = nullptr;
    if (!has_global_qualifier && components.size() == 1 &&
        !terminal_component.preceded_by_template_keyword) {
        resolved_template = resolve_single_template(
            LookupEngine::lookup_unqualified_template_binding(
                terminal_component.name,
                current_scope,
                true,
                LookupNamespace::Ordinary));
        if (!resolved_template) {
            resolved_template = resolve_single_template(
                LookupEngine::lookup_unqualified_template_binding(
                    terminal_component.name,
                    current_scope,
                    true,
                    LookupNamespace::Tag));
        }
    } else if (!qualifiers_need_owner_chain &&
               !terminal_component.preceded_by_template_keyword) {
        LookupEngine::QualifiedNameSpec name_spec;
        name_spec.has_global_qualifier = has_global_qualifier;
        name_spec.qualifiers = plain_qualifiers;
        name_spec.terminal_name = terminal_component.name;

        auto ordinary_lookup = LookupEngine::lookup_qualified_name(
            name_spec,
            current_context.get(),
            LookupNamespace::Ordinary);
        resolved_template = resolve_single_template(ordinary_lookup.binding);
        if (!resolved_template) {
            auto tag_lookup = LookupEngine::lookup_qualified_name(
                name_spec,
                current_context.get(),
                LookupNamespace::Tag);
            resolved_template = resolve_single_template(tag_lookup.binding);
        }
    } else {
        if (components.size() < 2) {
            return std::nullopt;
        }

        std::vector<CppQualifiedNameComponent> qualifiers(
            components.begin(),
            components.end() - 1);
        auto owner_chain = resolve_cpp_qualified_owner_chain(
            qualifiers,
            has_global_qualifier,
            terminal_component.loc,
            /*diagnose_dependent_names=*/false);
        if (owner_chain.lookup_failed || !owner_chain.owner_type) {
            return std::nullopt;
        }
        if (owner_chain.requires_template_keyword() &&
            !terminal_component.preceded_by_template_keyword) {
            return std::nullopt;
        }

        std::string template_name =
            format_template_name_argument(components);

        if (owner_chain.is_dependent_context()) {
            tentative.commit();
            TemplateArgument argument =
                TemplateArgument::dependent_template_argument(
                    template_name);
            argument.dependent_template_qualifier_type =
                owner_chain.owner_type;
            argument.dependent_template_member_name =
                terminal_component.name;
            return argument;
        }

        const auto* nested_template =
            collect_->collect_lookup_record_nested_template(
                owner_chain.owner_type,
                terminal_component.name);
        auto* template_decl =
            nested_template
                ? nested_template->decl
                : nullptr;
        if (!template_decl) {
            return std::nullopt;
        }
        tentative.commit();
        return TemplateArgument::template_argument(
            template_decl,
            template_name);
    }

    if (!resolved_template) {
        return std::nullopt;
    }

    std::string template_name =
        format_template_name_argument(components);
    tentative.commit();

    if (auto* template_parameter = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<Decl*>(resolved_template))) {
        return TemplateArgument::dependent_template_argument(
            template_name,
            template_parameter);
    }
    const TemplateDecl* template_decl = nullptr;
        switch (resolved_template->get_kind()) {
        case DeclKind::AliasTemplateDecl:
        case DeclKind::FunctionTemplateDecl:
        case DeclKind::VariableTemplateDecl:
        case DeclKind::ClassTemplateDecl:
        case DeclKind::VariableTemplatePartialSpecializationDecl:
        case DeclKind::ClassTemplatePartialSpecializationDecl:
            template_decl =
                static_cast<const TemplateDecl*>(resolved_template);
            break;
        default:
            break;
    }
    if (template_decl) {
        return TemplateArgument::template_argument(template_decl, template_name);
    }
    return std::nullopt;
}

void Parser::consume_cpp_template_argument_list_close() {
    if (gentle_check(TokenType::GREATER_THAN)) {
        advance();
        return;
    }
    if (gentle_check(TokenType::RIGHT_SHIFT)) {
        Token tok = current_token();
        tok_mgnt.replace_current_token_sequence({
            make_template_split_token(tok, TokenType::GREATER_THAN, ">"),
            make_template_split_token(tok, TokenType::GREATER_THAN, ">", 1)
        });
        advance();
        return;
    }
    if (gentle_check(TokenType::ASSIGN_RSHIFT)) {
        Token tok = current_token();
        tok_mgnt.replace_current_token_sequence({
            make_template_split_token(tok, TokenType::GREATER_THAN, ">"),
            make_template_split_token(tok, TokenType::GREATER_THAN, ">", 1),
            make_template_split_token(tok, TokenType::ASSIGN, "=", 2)
        });
        advance();
        return;
    }
    error_custloc("expected '>' to close template argument list",
                  current_token().loc);
}

bool Parser::try_consume_cpp_decltype_specifier_for_lookahead() {
    if (!gentle_check(TokenType::DECLTYPE_KW)) {
        return false;
    }
    advance(); // 'decltype'
    if (!gentle_check_and_consume(TokenType::LEFT_PAREN)) {
        return false;
    }

    size_t paren_depth = 1;
    while (paren_depth > 0) {
        TokenType type = current_token().type;
        if (type == TokenType::Eof) {
            return false;
        }
        if (type == TokenType::LEFT_PAREN) {
            ++paren_depth;
        } else if (type == TokenType::RIGHT_PAREN) {
            --paren_depth;
        }
        advance();
    }
    return true;
}

bool Parser::can_start_cpp_named_type_specifier_for_lookahead() {
    if (!is_cxx_mode_active() || !collect_) {
        return false;
    }

    struct ProbeComponent {
        std::string name;
        bool has_template_argument_list = false;
        bool preceded_by_template_keyword = false;
    };

    auto token_at = [&](size_t offset) {
        return peek_token_shortcut(offset);
    };

    auto consume_scope_resolution_at = [&](size_t& offset) {
        if (token_at(offset).type == TokenType::SCOPE_RESOLUTION) {
            ++offset;
            return true;
        }
        if (token_at(offset).type == TokenType::COLON &&
            token_at(offset + 1).type == TokenType::COLON) {
            offset += 2;
            return true;
        }
        return false;
    };

    auto skip_balanced_group_at =
        [&](size_t& offset,
            TokenType open_tok,
            TokenType close_tok) -> bool {
        if (token_at(offset).type != open_tok) {
            return false;
        }
        size_t depth = 0;
        while (token_at(offset).type != TokenType::Eof) {
            TokenType tok = token_at(offset).type;
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
    };

    auto skip_template_argument_list_at = [&](size_t& offset) -> bool {
        if (token_at(offset).type != TokenType::LESS_THAN) {
            return false;
        }
        ++offset;
        size_t angle_depth = 1;
        while (token_at(offset).type != TokenType::Eof) {
            TokenType tok = token_at(offset).type;
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
                    if (!skip_balanced_group_at(
                            offset,
                            TokenType::LEFT_PAREN,
                            TokenType::RIGHT_PAREN)) {
                        return false;
                    }
                    break;
                case TokenType::LEFT_BRACE:
                    if (!skip_balanced_group_at(
                            offset,
                            TokenType::LEFT_BRACE,
                            TokenType::RIGHT_BRACE)) {
                        return false;
                    }
                    break;
                case TokenType::LEFT_BRACKET:
                    if (!skip_balanced_group_at(
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
    };

    auto parse_component_at =
        [&](size_t& offset,
            bool allow_template_keyword) -> std::optional<ProbeComponent> {
        ProbeComponent component;
        if (allow_template_keyword &&
            token_at(offset).type == TokenType::TEMPLATE) {
            component.preceded_by_template_keyword = true;
            ++offset;
        }
        if (token_at(offset).type != TokenType::IDENTIFIER) {
            return std::nullopt;
        }
        component.name = token_at(offset).value;
        ++offset;
        if (token_at(offset).type == TokenType::LESS_THAN) {
            component.has_template_argument_list = true;
            if (!skip_template_argument_list_at(offset)) {
                return std::nullopt;
            }
        }
        return component;
    };

    auto can_follow_named_type_specifier = [](TokenType tok) {
        switch (tok) {
            case TokenType::IDENTIFIER:
            case TokenType::MULTIPLY:
            case TokenType::BITWISE_AND:
            case TokenType::LOGICAL_AND:
            case TokenType::LEFT_PAREN:
            case TokenType::RIGHT_PAREN:
            case TokenType::LEFT_BRACKET:
            case TokenType::COMMA:
            case TokenType::ELLIPSIS:
            case TokenType::CONST:
            case TokenType::VOLATILE:
            case TokenType::RESTRICT:
            case TokenType::ATTRIBUTE_KW:
            case TokenType::ALIGNAS:
                return true;
            default:
                return false;
        }
    };

    auto single_template_decl_from_binding =
        [](const DeclBinding* binding) -> const Decl* {
        if (!binding) {
            return nullptr;
        }
        if (binding->template_decl) {
            return binding->template_decl;
        }
        if (binding->template_overload_candidates.size() == 1) {
            return binding->template_overload_candidates.front();
        }
        return nullptr;
    };

    auto is_type_template_decl = [](const Decl* decl) {
        return isa<AliasTemplateDecl>(decl) ||
               isa<ClassTemplateDecl>(decl) ||
               isa<TemplateTemplateParmDecl>(decl);
    };

    auto lookup_qualified_type_template =
        [&](const LookupEngine::QualifiedNameSpec& name_spec) -> const Decl* {
        auto ordinary_lookup = LookupEngine::lookup_qualified_name(
            name_spec,
            collect_->get_current_decl_context().get(),
            LookupNamespace::Ordinary);
        if (const Decl* decl =
                single_template_decl_from_binding(ordinary_lookup.binding);
            is_type_template_decl(decl)) {
            return decl;
        }

        auto tag_lookup = LookupEngine::lookup_qualified_name(
            name_spec,
            collect_->get_current_decl_context().get(),
            LookupNamespace::Tag);
        if (const Decl* decl =
                single_template_decl_from_binding(tag_lookup.binding);
            is_type_template_decl(decl)) {
            return decl;
        }
        return nullptr;
    };

    auto lookup_type_template_at =
        [&](const std::vector<ProbeComponent>& components,
            bool has_global_qualifier,
            size_t component_idx) -> const Decl* {
        if (!has_global_qualifier && component_idx == 0) {
            auto scope = collect_->collect_current_scope();
            if (const Decl* primary_template =
                    lookup_cpp_unqualified_type_template_decl(
                        components[component_idx].name,
                        scope,
                        /*allow_enclosing_lookup=*/true)) {
                return primary_template;
            }
            if (const auto* nested_template =
                    lookup_cpp_current_record_nested_type_template(
                        components[component_idx].name)) {
                return nested_template->decl;
            }
            return nullptr;
        }

        LookupEngine::QualifiedNameSpec name_spec;
        name_spec.has_global_qualifier = has_global_qualifier;
        for (size_t idx = 0; idx < component_idx; ++idx) {
            if (components[idx].has_template_argument_list ||
                components[idx].preceded_by_template_keyword) {
                return nullptr;
            }
            name_spec.qualifiers.push_back(components[idx].name);
        }
        name_spec.terminal_name = components[component_idx].name;
        return lookup_qualified_type_template(name_spec);
    };

    auto lookup_unqualified_type_template_at =
        [&](const ProbeComponent& component) -> const Decl* {
        auto scope = collect_->collect_current_scope();
        if (const Decl* primary_template =
                lookup_cpp_unqualified_type_template_decl(
                    component.name,
                    scope,
                    /*allow_enclosing_lookup=*/true)) {
            return primary_template;
        }
        if (const auto* nested_template =
                lookup_cpp_current_record_nested_type_template(component.name)) {
            return nested_template->decl;
        }
        return nullptr;
    };

    auto qualified_terminal_names_type =
        [&](const std::vector<ProbeComponent>& components,
            bool has_global_qualifier) {
        if (components.empty()) {
            return false;
        }

        const size_t terminal_idx = components.size() - 1;
        const auto& terminal = components.back();
        LookupEngine::QualifiedNameSpec name_spec;
        name_spec.has_global_qualifier = has_global_qualifier;
        for (size_t idx = 0; idx < terminal_idx; ++idx) {
            if (components[idx].has_template_argument_list ||
                components[idx].preceded_by_template_keyword) {
                return false;
            }
            name_spec.qualifiers.push_back(components[idx].name);
        }
        name_spec.terminal_name = terminal.name;

        if (terminal.has_template_argument_list) {
            if (!has_global_qualifier && terminal_idx == 0) {
                return lookup_unqualified_type_template_at(terminal) != nullptr;
            }
            return lookup_qualified_type_template(name_spec) != nullptr;
        }

        auto ordinary_lookup = LookupEngine::lookup_qualified_name(
            name_spec,
            collect_->get_current_decl_context().get(),
            LookupNamespace::Ordinary,
            LookupEngine::OrdinaryFilter::TypedefOnly);
        if (ordinary_lookup.binding && ordinary_lookup.symbol &&
            ordinary_lookup.symbol->kind == SymbolKind::TYPE) {
            return true;
        }

        auto tag_lookup = LookupEngine::lookup_qualified_name(
            name_spec,
            collect_->get_current_decl_context().get(),
            LookupNamespace::Tag);
        return tag_lookup.binding != nullptr;
    };

    size_t offset = 0;
    bool has_global_qualifier = consume_scope_resolution_at(offset);

    auto first_component = parse_component_at(
        offset,
        /*allow_template_keyword=*/false);
    if (!first_component) {
        return false;
    }

    std::vector<ProbeComponent> components;
    components.push_back(std::move(*first_component));
    while (consume_scope_resolution_at(offset)) {
        auto component = parse_component_at(
            offset,
            /*allow_template_keyword=*/true);
        if (!component) {
            return false;
        }
        components.push_back(std::move(*component));
    }

    TokenType follow = token_at(offset).type;
    if (!can_follow_named_type_specifier(follow)) {
        return false;
    }

    if (qualified_terminal_names_type(components, has_global_qualifier)) {
        return true;
    }

    if (!components.empty() && components.back().has_template_argument_list &&
        follow == TokenType::LEFT_PAREN) {
        return false;
    }

    for (size_t idx = 0; idx + 1 < components.size(); ++idx) {
        if (!components[idx].has_template_argument_list) {
            continue;
        }
        if (lookup_type_template_at(components, has_global_qualifier, idx)) {
            return true;
        }
        return false;
    }

    return false;
}

QualType Parser::parse_cpp_decltype_type_specifier() {
    Token decltype_tok = current_token();
    if (!is_cxx_mode_active()) {
        error_custloc("'decltype' is only available in C++ mode",
                      decltype_tok.loc);
    }
    check_and_consume(TokenType::DECLTYPE_KW);
    check_and_consume(TokenType::LEFT_PAREN);
    bool use_declared_type_rule =
        current_token().type != TokenType::LEFT_PAREN;
    Collect::UnevaluatedContextScope unevaluated_scope(
        collect_.get(),
        "decltype");
    auto decltype_expr = parse_expression();
    if (!decltype_expr) {
        error("Error parsing expression in decltype");
    }
    QualType decltype_type(std::make_shared<DecltypeExprType>(
        std::shared_ptr<Expr>(decltype_expr.release()),
        use_declared_type_rule));
    check_and_consume(TokenType::RIGHT_PAREN);
    return decltype_type;
}

bool Parser::is_cpp_template_argument_boundary_here() {
    return gentle_check(TokenType::COMMA) ||
           gentle_check(TokenType::GREATER_THAN) ||
           gentle_check(TokenType::RIGHT_SHIFT) ||
           gentle_check(TokenType::ASSIGN_RSHIFT);
}

const TemplateParameterDecl*
Parser::find_active_template_parameter(std::string_view name) const {
    if (name.empty()) {
        return nullptr;
    }
    for (auto stack_it = active_template_parameter_stack_.rbegin();
         stack_it != active_template_parameter_stack_.rend();
         ++stack_it) {
        for (auto param_it = stack_it->rbegin();
             param_it != stack_it->rend();
             ++param_it) {
            const auto* parameter = *param_it;
            if (!parameter || parameter->name != name) {
                continue;
            }
            return parameter;
        }
    }
    return nullptr;
}

const TemplateParameterDecl*
Parser::find_active_template_parameter_pack(std::string_view name) const {
    const auto* parameter = find_active_template_parameter(name);
    if (!parameter || !parameter->is_parameter_pack) {
        return nullptr;
    }
    return parameter;
}

const TemplateNonTypeParmDecl*
Parser::find_active_non_type_template_parameter(const Symbol* sym) const {
    if (!sym) {
        return nullptr;
    }
    for (auto stack_it = active_template_parameter_stack_.rbegin();
         stack_it != active_template_parameter_stack_.rend();
         ++stack_it) {
        for (auto param_it = stack_it->rbegin();
             param_it != stack_it->rend();
             ++param_it) {
            auto* non_type_param =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(*param_it));
            if (non_type_param && non_type_param->sym.get() == sym) {
                return non_type_param;
            }
        }
    }
    return nullptr;
}

bool Parser::expr_depends_on_active_template_parameter(const Expr* expr) const {
    if (!expr) {
        return false;
    }
    if (auto* var_ref = dyn_cast<VarRef>(expr)) {
        if (find_active_non_type_template_parameter(var_ref->symref.get()) !=
            nullptr) {
            return true;
        }
    }
    return collect_ &&
           collect_->expression_depends_on_template_parameters(expr);
}

std::unique_ptr<Expr> Parser::try_parse_cpp_typed_braced_template_argument_expr() {
    RevertingTentativeParsingAction tentative(*this);
    try {
        DeclarationParser type_parser(this);
        auto parsed_type = type_parser.parse_declaration();
        if (!parsed_type || !type_parser.name.empty() ||
            type_parser.str_class != StorageClass::NONE ||
            !gentle_check(TokenType::LEFT_BRACE)) {
            return nullptr;
        }

        tentative.commit();
        QualType target_type(parsed_type, type_parser.qualifiers);
        SrcLoc literal_loc = current_token().loc;
        auto initializer_expr = parse_init_list();
        auto* initializer = dyn_cast<InitListExpr>(initializer_expr.get());
        if (!initializer) {
            return nullptr;
        }
        auto owned_initializer = std::unique_ptr<InitListExpr>(
            static_cast<InitListExpr*>(initializer_expr.release()));
        if (type_depends_on_template_parameters(target_type, ast_ctx.get())) {
            if (!owned_initializer->actions.empty() ||
                !owned_initializer->mappings.empty()) {
                error_custloc(
                    "dependent braced template argument does not support lowered initializer actions",
                    literal_loc);
                return collect_->collect_error_expression(
                    "unsupported dependent braced template argument",
                    literal_loc);
            }
            std::vector<std::unique_ptr<Expr>> args;
            args.reserve(owned_initializer->elements.size());
            for (auto& element : owned_initializer->elements) {
                if (!element.designators.empty()) {
                    error_custloc(
                        "dependent braced template argument does not support designators",
                        element.loc);
                    return collect_->collect_error_expression(
                        "unsupported dependent braced template argument",
                        element.loc);
                }
                args.push_back(std::move(element.value));
            }
            auto deferred =
                collect_->collect_cpp_function_style_cast(
                    target_type,
                    std::move(args),
                    literal_loc);
            if (auto* cast = dyn_cast<CppFunctionStyleCastExpr>(deferred.get())) {
                cast->is_list_init = true;
            }
            return deferred;
        }
        return collect_->collect_cpp_type_list_initialization_expression(
            target_type,
            std::move(owned_initializer),
            literal_loc);
    } catch (const ParseError&) {
    } catch (const FatalErrorLimitReached&) {
        throw;
    }
    return nullptr;
}

TemplateArgument Parser::parse_cpp_template_argument() {
    auto finalize_template_argument =
        [&](TemplateArgument argument) -> TemplateArgument {
        const bool is_integer_pack_argument =
            argument.kind == TemplateArgumentKind::Value &&
            argument.value_expr &&
            is_integer_pack_builtin_expr(argument.value_expr.get());
        if (gentle_check(TokenType::ELLIPSIS)) {
            if (!is_in_template_pattern_context()) {
                error_custloc(
                    "pack expansion is only supported in template patterns",
                    current_token().loc);
            }
            advance();
            argument = argument.as_pack_expansion();
        }
        if (is_integer_pack_argument && !argument.expands_parameter_pack) {
            error_custloc(
                "__integer_pack must be expanded with '...'",
                current_token().loc);
        }
        if (!is_cpp_template_argument_boundary_here()) {
            error_custloc("expected template argument", current_token().loc);
        }
        return argument;
    };

    auto build_expression_argument =
        [&](std::unique_ptr<Expr> parsed_expr) -> TemplateArgument {
        if (!parsed_expr) {
            error_custloc("expected template argument", current_token().loc);
        }

        QualType argument_type = parsed_expr->get_type();
        if (!argument_type) {
            error_custloc("template argument has invalid type",
                          parsed_expr->location);
        }

        if (is_integer_pack_builtin_expr(parsed_expr.get())) {
            std::shared_ptr<Expr> shared_expr(parsed_expr.release());
            return TemplateArgument::dependent_value_argument(
                argument_type,
                std::move(shared_expr),
                "__integer_pack");
        }

        if (expr_depends_on_active_template_parameter(parsed_expr.get())) {
            std::string argument_spelling;
            const TemplateParameterDecl* referenced_parameter = nullptr;
            if (auto* var_ref = dyn_cast<VarRef>(parsed_expr.get())) {
                argument_spelling = var_ref->get_name();
                if (const auto* non_type_parameter =
                        find_active_non_type_template_parameter(
                            var_ref->symref.get())) {
                    referenced_parameter = non_type_parameter;
                }
            }
            std::shared_ptr<Expr> shared_expr(parsed_expr.release());
            return TemplateArgument::dependent_value_argument(
                argument_type,
                std::move(shared_expr),
                std::move(argument_spelling),
                referenced_parameter);
        }

        ConstEvalResult eval = evaluate_with_consteval_compat(
            parsed_expr.get(),
            ConstEvalMode::cpp_non_type_template_argument());
        if (eval.status == ConstEvalStatus::Constant &&
            eval.value.has_value() &&
            eval.value->kind != ConstValueKind::Invalid) {
            std::shared_ptr<Expr> concrete_expr = nullptr;
            if (eval.value->kind == ConstValueKind::Object) {
                if (auto* var_ref =
                        dyn_cast<VarRef>(Collect::strip_implicit_casts(parsed_expr.get()))) {
                    concrete_expr =
                        template_sema_internal::clone_constexpr_variable_initializer_expr(
                            var_ref->symref.get(),
                            ast_ctx.get());
                }
                if (!concrete_expr) {
                    concrete_expr = std::shared_ptr<Expr>(parsed_expr.release());
                }
            }
            return TemplateArgument::value_argument(
                argument_type,
                *eval.value,
                {},
                std::move(concrete_expr));
        }

        error_custloc(
            "non-type template argument must be a constant expression",
            parsed_expr->location);
        return TemplateArgument();
    };

    auto try_parse_injected_current_instantiation_type_argument =
        [&]() -> std::optional<TemplateArgument> {
            if (!is_in_template_pattern_context() ||
                cxx_record_parse_stack_.empty() ||
                current_token().type != TokenType::IDENTIFIER) {
                return std::nullopt;
            }

            Token name_tok = current_token();
            const auto& current_record = cxx_record_parse_stack_.back();
            if (current_record.name.empty() ||
                name_tok.value != current_record.name) {
                return std::nullopt;
            }

            TokenType after_name = peek_token().type;
            if (after_name != TokenType::COMMA &&
                after_name != TokenType::GREATER_THAN &&
                after_name != TokenType::RIGHT_SHIFT &&
                after_name != TokenType::ASSIGN_RSHIFT &&
                after_name != TokenType::ELLIPSIS) {
                return std::nullopt;
            }

            RevertingTentativeParsingAction tentative(*this);
            try {
                DeclarationParser type_parser(this);
                auto parsed_type = type_parser.parse_declaration();
                if (!parsed_type ||
                    !type_parser.name.empty() ||
                    type_parser.str_class != StorageClass::NONE ||
                    !(is_cpp_template_argument_boundary_here() ||
                      gentle_check(TokenType::ELLIPSIS))) {
                    return std::nullopt;
                }

                QualType parsed_argument_type(
                    parsed_type,
                    type_parser.qualifiers);
                if (!cpp_qualifier_is_current_instantiation(
                        name_tok.value,
                        parsed_argument_type)) {
                    return std::nullopt;
                }
                if (current_record.current_instantiation_type &&
                    !parsed_argument_type.equals_unqualified(
                        current_record.current_instantiation_type)) {
                    return std::nullopt;
                }

                tentative.commit();
                return TemplateArgument(parsed_argument_type);
            } catch (const ParseError&) {
            } catch (const FatalErrorLimitReached&) {
                throw;
            }
            return std::nullopt;
        };

    if (auto current_instantiation_argument =
            try_parse_injected_current_instantiation_type_argument()) {
        return finalize_template_argument(
            std::move(*current_instantiation_argument));
    }

    if (auto template_argument = try_parse_cpp_template_name_argument()) {
        return finalize_template_argument(std::move(*template_argument));
    }

    if (gentle_check(TokenType::NULLPTR_KW)) {
        advance();
        return finalize_template_argument(TemplateArgument::value_argument(
            QualType(type_ctx->get_builtin(BuiltinTypes::NullPtr)),
            ConstValue::null_pointer(),
            "nullptr"));
    }

    bool parsed_type_argument = false;
    QualType parsed_argument_type;
    {
        RevertingTentativeParsingAction tentative(*this);
        try {
            DeclarationParser type_parser(this);
            auto parsed_type = type_parser.parse_declaration();
            if (parsed_type &&
                type_parser.name.empty() &&
                type_parser.str_class == StorageClass::NONE &&
                (is_cpp_template_argument_boundary_here() ||
                 gentle_check(TokenType::ELLIPSIS))) {
                tentative.commit();
                parsed_argument_type = QualType(parsed_type, type_parser.qualifiers);
                parsed_type_argument = true;
            }
        } catch (const ParseError&) {
        } catch (const FatalErrorLimitReached&) {
            throw;
        }
    }

    if (parsed_type_argument) {
        return finalize_template_argument(TemplateArgument(parsed_argument_type));
    }

    if (auto typed_braced_expr =
            try_parse_cpp_typed_braced_template_argument_expr()) {
        return finalize_template_argument(
            build_expression_argument(std::move(typed_braced_expr)));
    }

    struct TemplateArgumentExpressionGuard {
        Parser& parser;

        explicit TemplateArgumentExpressionGuard(Parser& parser)
            : parser(parser) {
            parser.enter_template_argument_expression();
        }

        ~TemplateArgumentExpressionGuard() {
            parser.leave_template_argument_expression();
        }
    } expr_guard(*this);

    return finalize_template_argument(
        build_expression_argument(parse_assignment_expression()));
}

std::vector<TemplateArgument> Parser::parse_cpp_template_argument_list() {
    std::vector<TemplateArgument> arguments;
    check_and_consume(TokenType::LESS_THAN);
    if (gentle_check(TokenType::GREATER_THAN)) {
        consume_cpp_template_argument_list_close();
        return arguments;
    }

    while (true) {
        arguments.push_back(parse_cpp_template_argument());
        if (!gentle_check_and_consume(TokenType::COMMA)) {
            break;
        }
    }

    consume_cpp_template_argument_list_close();
    return arguments;
}

std::optional<Parser::ParsedCppTypeNameSpecifier>
Parser::try_parse_cpp_named_type_specifier(CppTypeNameParseContext context) {
    if (!is_cxx_mode_active()) {
        return std::nullopt;
    }
    const bool allow_implicit_typename =
        context == CppTypeNameParseContext::BaseSpecifier;
    const bool is_type_requirement =
        context == CppTypeNameParseContext::TypeRequirement;

    Token start_tok = current_token();
    if (!(start_tok.type == TokenType::TYPENAME ||
          start_tok.type == TokenType::DECLTYPE_KW ||
          start_tok.type == TokenType::IDENTIFIER ||
          start_tok.type == TokenType::SCOPE_RESOLUTION ||
          (start_tok.type == TokenType::COLON &&
           peek_token().type == TokenType::COLON))) {
        return std::nullopt;
    }

    size_t saved_idx = get_token_idx();
    auto saved_split_state = tok_mgnt.get_split_token_state();
    auto restore = [&]() {
        set_token_idx(saved_idx);
        tok_mgnt.set_split_token_state(saved_split_state);
    };

    auto current_scope = collect_->collect_current_scope();
    auto current_context = collect_->get_current_decl_context();
    if (!current_scope || !current_context) {
        error_custloc("internal error: missing C++ type-name lookup context",
                      start_tok.loc);
    }

    auto try_parse_concrete_named_type = [&]() -> std::optional<ParsedCppTypeNameSpecifier> {
        bool has_global_qualifier = consume_cpp_scope_resolution();
        if (!gentle_check(TokenType::IDENTIFIER)) {
            restore();
            return std::nullopt;
        }

        auto parse_component = [&]() -> CppQualifiedNameComponent {
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc("expected identifier after '::' in qualified type name",
                              current_token().loc);
            }
            CppQualifiedNameComponent component;
            component.name = current_token().value;
            component.loc = current_token().loc;
            advance();
            if (gentle_check(TokenType::LESS_THAN)) {
                component.has_template_argument_list = true;
                component.template_arguments = parse_cpp_template_argument_list();
            }
            return component;
        };

        std::vector<CppQualifiedNameComponent> components;
        components.push_back(parse_component());
        while (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            if (gentle_check(TokenType::TEMPLATE) && allow_implicit_typename) {
                restore();
                return std::nullopt;
            }
            components.push_back(parse_component());
        }

        auto tu_context = collect_->get_translation_unit_decl_context();
        if (!tu_context) {
            error_custloc("internal error: missing translation-unit declaration context",
                          start_tok.loc);
        }

        auto global_scope = current_scope;
        while (global_scope && global_scope->parent) {
            global_scope = global_scope->parent;
        }
        if (!global_scope) {
            error_custloc("internal error: missing global scope", start_tok.loc);
        }

        auto template_arguments_are_dependent =
            [&](const std::vector<TemplateArgument>& arguments) {
                for (const auto& argument : arguments) {
                    if (template_argument_depends_on_template_parameters(
                            argument,
                            ast_ctx.get())) {
                        return true;
                    }
                }
                return false;
            };

        auto lookup_typedef_type_in_scope =
            [&](const std::shared_ptr<Scope>& scope,
                bool allow_enclosing_lookup,
                const std::string& name,
                std::shared_ptr<Symbol>* typedef_symbol_out) -> QualType {
                if (typedef_symbol_out) {
                    *typedef_symbol_out = nullptr;
                }
                auto typedef_symbol =
                    LookupEngine::lookup_unqualified_ordinary(
                        name,
                        scope,
                        allow_enclosing_lookup,
                        LookupEngine::OrdinaryFilter::TypedefOnly);
                if (typedef_symbol && typedef_symbol->kind == SymbolKind::TYPE) {
                    if (typedef_symbol_out) {
                        *typedef_symbol_out = typedef_symbol;
                    }
                    return typedef_symbol->type;
                }
                return QualType();
            };

        auto lookup_tag_type_in_scope =
            [&](const std::shared_ptr<Scope>& scope,
                bool allow_enclosing_lookup,
                const std::string& name) -> QualType {
                if (auto tag_type = LookupEngine::lookup_tag_type(
                        name, scope, allow_enclosing_lookup)) {
                    return QualType(tag_type);
                }
                return QualType();
            };

        auto lookup_type_template_in_scope =
            [&](const std::shared_ptr<Scope>& scope,
                bool allow_enclosing_lookup,
                const std::string& name) -> const Decl* {
                return lookup_cpp_unqualified_type_template_decl(
                    name,
                    scope,
                    allow_enclosing_lookup);
            };

        auto complete_template_id_arguments_for_named_type =
            [&](const TemplateDecl* template_decl,
                const std::vector<TemplateArgument>& arguments,
                SrcLoc loc)
                -> std::optional<std::vector<TemplateArgument>> {
            std::string template_argument_error;
            auto normalized_arguments = complete_cpp_template_id_arguments(
                template_decl,
                arguments,
                loc,
                &template_argument_error);
            if (!normalized_arguments &&
                !template_argument_error.empty() &&
                !is_in_tentative_context()) {
                restore();
                error_custloc(template_argument_error, loc);
            }
            return normalized_arguments;
        };

        std::shared_ptr<Scope> lookup_scope =
            has_global_qualifier ? global_scope : current_scope;
        const DeclContext* lookup_context =
            has_global_qualifier ? tu_context.get() : current_context.get();
        std::vector<std::string> resolved_prefix;
        std::shared_ptr<Symbol> terminal_typedef_symbol = nullptr;
        QualType resolved_type;

        for (size_t idx = 0; idx < components.size(); ++idx) {
            bool is_last_component = idx + 1 == components.size();
            bool allow_enclosing_lookup = !has_global_qualifier && idx == 0;
            const auto& component = components[idx];

            if (!resolved_type) {
                if (!component.has_template_argument_list) {
                    auto namespace_scope = resolve_named_namespace_scope(
                        lookup_context,
                        component.name,
                        allow_enclosing_lookup);
                    if (namespace_scope && namespace_scope->associated_decl_context) {
                        if (is_last_component) {
                            restore();
                            return std::nullopt;
                        }
                        lookup_scope = namespace_scope;
                        lookup_context = namespace_scope->associated_decl_context;
                        resolved_prefix.push_back(component.name);
                        continue;
                    }

                    std::shared_ptr<Symbol> typedef_symbol = nullptr;
                    if (!resolved_type) {
                        resolved_type = lookup_typedef_type_in_scope(
                            lookup_scope,
                            allow_enclosing_lookup,
                            component.name,
                            &typedef_symbol);
                    }
                    if (!resolved_type && !has_global_qualifier && idx == 0) {
                        resolved_type =
                            try_build_cpp_injected_current_instantiation_type(
                                component.name,
                                component.loc);
                    }
                    if (!resolved_type) {
                        resolved_type =
                            lookup_cpp_current_record_nested_type(component.name);
                    }
                    if (!resolved_type &&
                        is_last_component &&
                        lang_opts.is_cxx17_or_later()) {
                        const Decl* primary_template =
                            lookup_type_template_in_scope(
                                lookup_scope,
                                allow_enclosing_lookup,
                                component.name);
                        const auto* class_template =
                            dyn_cast<ClassTemplateDecl>(
                                primary_template);
                        if (class_template) {
                            resolved_type =
                                QualType(std::make_shared<TemplateSpecializationType>(
                                    qualified_name_utils::format_cpp_qualified_name(
                                        has_global_qualifier,
                                        resolved_prefix,
                                        component.name),
                                    class_template,
                                    std::vector<TemplateArgument>{},
                                    false,
                                    true));
                        }
                    }
                    if (!resolved_type) {
                        resolved_type = lookup_tag_type_in_scope(
                            lookup_scope,
                            allow_enclosing_lookup,
                            component.name);
                    }
                    if (!resolved_type) {
                        restore();
                        return std::nullopt;
                    }
                    if (is_last_component) {
                        terminal_typedef_symbol = typedef_symbol;
                    }
                } else {
                    const Decl* primary_template = lookup_type_template_in_scope(
                        lookup_scope,
                        allow_enclosing_lookup,
                        component.name);
                    if (!primary_template && collect_) {
                        QualType owner_lookup_type;
                        const auto* nested_template =
                            lookup_cpp_current_record_nested_type_template(
                                component.name,
                                &owner_lookup_type);
                        if (nested_template && nested_template->decl) {
                            auto normalized_arguments =
                                complete_template_id_arguments_for_named_type(
                                    nested_template->decl,
                                    component.template_arguments,
                                    component.loc);
                            if (!normalized_arguments) {
                                restore();
                                return std::nullopt;
                            }
                            bool is_dependent =
                                type_depends_on_template_parameters(
                                    owner_lookup_type,
                                    ast_ctx.get()) ||
                                template_arguments_are_dependent(
                                    *normalized_arguments);
                            if (is_dependent) {
                                resolved_type = QualType(
                                    std::make_shared<TemplateSpecializationType>(
                                        component.name,
                                        nested_template->decl,
                                        *normalized_arguments,
                                        true));
                            } else {
                                bool matched_nested_template = false;
                                resolved_type =
                                    collect_->collect_lookup_record_nested_template_type(
                                        owner_lookup_type,
                                        component.name,
                                        *normalized_arguments,
                                        component.loc,
                                        &matched_nested_template);
                            }
                        }
                    }
                    if (!primary_template && !resolved_type) {
                        restore();
                        return std::nullopt;
                    }

                    if (primary_template) {
                        auto normalized_arguments =
                            complete_template_id_arguments_for_named_type(
                                cpp_template_decl_for_default_arguments(
                                    primary_template),
                                component.template_arguments,
                                component.loc);
                        if (!normalized_arguments) {
                            restore();
                            return std::nullopt;
                        }
                        bool is_dependent =
                            isa<TemplateTemplateParmDecl>(primary_template) ||
                            template_arguments_are_dependent(
                                *normalized_arguments);
                        QualType specialization_type =
                            QualType(std::make_shared<TemplateSpecializationType>(
                                qualified_name_utils::format_cpp_qualified_name(
                                    has_global_qualifier,
                                    resolved_prefix,
                                    component.name),
                                primary_template,
                                *normalized_arguments,
                                is_dependent));
                        if (is_last_component || is_dependent) {
                            resolved_type = specialization_type;
                        } else {
                            auto concrete_specialization =
                                collect_->collect_try_realize_deferred_semantic_type(
                                    specialization_type);
                            if (!concrete_specialization ||
                                type_depends_on_template_parameters(
                                    concrete_specialization,
                                    ast_ctx.get())) {
                                restore();
                                return std::nullopt;
                            }
                            resolved_type = concrete_specialization;
                        }
                    }
                }
            } else {
                if (component.has_template_argument_list) {
                    bool matched_nested_template = false;
                    resolved_type =
                        collect_->collect_lookup_record_nested_template_type(
                            resolved_type,
                            component.name,
                            component.template_arguments,
                            component.loc,
                            &matched_nested_template);
                } else {
                    resolved_type =
                        collect_->collect_lookup_record_nested_type(
                            resolved_type,
                            component.name);
                }
                if (!resolved_type) {
                    restore();
                    return std::nullopt;
                }
            }

            if (!is_last_component) {
                resolved_type =
                    prepare_cpp_qualified_type_owner(resolved_type);
                if (!resolved_type) {
                    restore();
                    return std::nullopt;
                }
                if (type_depends_on_template_parameters(
                        resolved_type,
                        ast_ctx.get())) {
                    restore();
                    return std::nullopt;
                }
                resolved_prefix.push_back(component.spelling());
            }
        }

        ParsedCppTypeNameSpecifier result;
        result.typedef_symbol = terminal_typedef_symbol;
        result.type = resolved_type;
        result.spelling = qualified_name_utils::format_cpp_qualified_name(
            has_global_qualifier,
            resolved_prefix,
            components.empty() ? std::string() : components.back().spelling());
        return result;
    };

    auto try_parse_decltype_qualified_type =
        [&](bool saw_typename_keyword)
            -> std::optional<ParsedCppTypeNameSpecifier> {
        if (!gentle_check(TokenType::DECLTYPE_KW)) {
            return std::nullopt;
        }
        {
            RevertingTentativeParsingAction tentative(*this);
            if (!try_consume_cpp_decltype_specifier_for_lookahead() ||
                !is_cpp_scope_resolution_here()) {
                return std::nullopt;
            }
        }

        SrcLoc decltype_loc = current_token().loc;
        QualType owner_type = parse_cpp_decltype_type_specifier();
        if (!is_cpp_scope_resolution_here()) {
            restore();
            return std::nullopt;
        }

        CppQualifiedOwnerSeed seed;
        seed.owner_type = owner_type;
        seed.spelling = "decltype(<expr>)";
        seed.loc = decltype_loc;
        seed.is_dependent =
            type_depends_on_template_parameters(owner_type, ast_ctx.get());
        seed.requires_class_or_enum = true;

        auto parse_component =
            [&](bool preceded_by_template_keyword)
                -> CppQualifiedNameComponent {
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected identifier after '::' in qualified type name",
                    current_token().loc);
            }
            CppQualifiedNameComponent component;
            component.name = current_token().value;
            component.loc = current_token().loc;
            component.preceded_by_template_keyword =
                preceded_by_template_keyword;
            advance();
            if (gentle_check(TokenType::LESS_THAN)) {
                component.has_template_argument_list = true;
                component.template_arguments =
                    parse_cpp_template_argument_list();
            }
            if (component.preceded_by_template_keyword &&
                !component.has_template_argument_list) {
                error_custloc(
                    "expected template-id after 'template' keyword",
                    component.loc);
            }
            return component;
        };

        std::vector<CppQualifiedNameComponent> components;
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

        if (components.empty()) {
            restore();
            return std::nullopt;
        }

        std::vector<CppQualifiedNameComponent> qualifiers(
            components.begin(),
            components.end() - 1);
        const auto& terminal_component = components.back();
        auto owner_chain = resolve_cpp_qualified_owner_chain(
            qualifiers,
            /*has_global_qualifier=*/false,
            decltype_loc,
            /*diagnose_dependent_names=*/true,
            seed);
        if (owner_chain.lookup_failed || !owner_chain.owner_type) {
            restore();
            return std::nullopt;
        }

        if (terminal_component.has_template_argument_list &&
            owner_chain.requires_template_keyword() &&
            !terminal_component.preceded_by_template_keyword) {
            diagnose_missing_cpp_template_keyword(
                owner_chain.qualifier_chain_spelling,
                terminal_component.name,
                terminal_component.loc);
        }

        QualType resolved_type;
        const bool terminal_is_known_type =
            saw_typename_keyword || allow_implicit_typename ||
            is_type_requirement;
        if (terminal_component.has_template_argument_list) {
            if (owner_chain.is_dependent_context()) {
                resolved_type = QualType(std::make_shared<DependentNameType>(
                    owner_chain.owner_type,
                    terminal_component.name,
                    terminal_component.template_arguments,
                    owner_chain.is_current_instantiation,
                    terminal_is_known_type,
                    true));
            } else {
                resolved_type =
                    collect_->collect_lookup_record_nested_template_type(
                        owner_chain.owner_type,
                        terminal_component.name,
                        terminal_component.template_arguments,
                        terminal_component.loc);
            }
        } else {
            if (owner_chain.is_dependent_context()) {
                if (!terminal_is_known_type &&
                    owner_chain.requires_typename_keyword()) {
                    diagnose_missing_cpp_typename_keyword(
                        owner_chain.qualifier_chain_spelling,
                        terminal_component.name,
                        terminal_component.loc);
                }
                resolved_type = QualType(std::make_shared<DependentNameType>(
                    owner_chain.owner_type,
                    terminal_component.name,
                    std::vector<TemplateArgument>{},
                    owner_chain.is_current_instantiation,
                    terminal_is_known_type,
                    false));
            } else {
                resolved_type =
                    collect_->collect_lookup_record_nested_type(
                        owner_chain.owner_type,
                        terminal_component.name);
            }
        }

        if (!resolved_type) {
            restore();
            return std::nullopt;
        }

        ParsedCppTypeNameSpecifier result;
        result.type = resolved_type;
        result.spelling =
            owner_chain.qualifier_chain_spelling + "::" +
            terminal_component.spelling();
        return result;
    };

    if (start_tok.type != TokenType::TYPENAME) {
        if (auto decltype_qualified =
                try_parse_decltype_qualified_type(false)) {
            return decltype_qualified;
        }
        if (auto concrete = try_parse_concrete_named_type()) {
            return concrete;
        }
        restore();
    }

    bool saw_typename_keyword = gentle_check_and_consume(TokenType::TYPENAME);
    if (saw_typename_keyword) {
        if (auto decltype_qualified =
                try_parse_decltype_qualified_type(true)) {
            return decltype_qualified;
        }
        if (is_type_requirement) {
            size_t after_typename_idx = get_token_idx();
            auto after_typename_split_state = tok_mgnt.get_split_token_state();
            if (auto concrete = try_parse_concrete_named_type()) {
                return concrete;
            }
            set_token_idx(after_typename_idx);
            tok_mgnt.set_split_token_state(after_typename_split_state);
        }
    }
    if (consume_cpp_scope_resolution()) {
        if (saw_typename_keyword) {
            error_custloc(
                "'typename' is only allowed before qualified dependent type names",
                start_tok.loc);
        }
        restore();
        return std::nullopt;
    }
    if (!gentle_check(TokenType::IDENTIFIER)) {
        restore();
        return std::nullopt;
    }

    auto format_component_spelling =
        [](std::string_view name,
           const std::vector<TemplateArgument>& arguments,
           bool has_template_argument_list) -> std::string {
            std::string spelled(name);
            if (!has_template_argument_list) {
                return spelled;
            }
            spelled += "<";
            for (size_t idx = 0; idx < arguments.size(); ++idx) {
                if (idx > 0) {
                    spelled += ", ";
                }
                spelled += arguments[idx].to_string();
            }
            spelled += ">";
            return spelled;
        };

    struct DependentTypeLookupState {
        QualType qualifier_type = nullptr;
        bool is_dependent = false;
        bool is_current_instantiation = false;

        bool is_dependent_context() const {
            return is_dependent || is_current_instantiation;
        }

        bool requires_template_keyword() const {
            return is_dependent && !is_current_instantiation;
        }

        bool requires_typename_keyword() const {
            return is_dependent && !is_current_instantiation;
        }
    };

    std::string qualifier_name = current_token().value;
    SrcLoc qualifier_loc = current_token().loc;
    advance();

    std::vector<TemplateArgument> qualifier_arguments;
    bool qualifier_has_template_argument_list = false;
    if (gentle_check(TokenType::LESS_THAN)) {
        qualifier_has_template_argument_list = true;
        qualifier_arguments = parse_cpp_template_argument_list();
    }

    if (!is_cpp_scope_resolution_here()) {
        if (saw_typename_keyword && is_type_requirement) {
            auto resolution = resolve_cpp_unqualified_type_component(
                qualifier_name,
                qualifier_arguments,
                qualifier_has_template_argument_list,
                qualifier_loc);
            if (!resolution || !resolution.type) {
                restore();
                return std::nullopt;
            }
            ParsedCppTypeNameSpecifier result;
            result.type = resolution.type;
            result.typedef_symbol = resolution.typedef_symbol;
            result.spelling = format_component_spelling(
                qualifier_name,
                qualifier_arguments,
                qualifier_has_template_argument_list);
            return result;
        }
        if (saw_typename_keyword) {
            error_custloc("expected qualified type name after 'typename'",
                          qualifier_loc);
        }
        restore();
        return std::nullopt;
    }

    consume_cpp_scope_resolution();
    bool saw_template_keyword = gentle_check_and_consume(TokenType::TEMPLATE);
    if (!gentle_check(TokenType::IDENTIFIER)) {
        error_custloc("expected identifier after '::' in qualified type name",
                      current_token().loc);
    }

    std::string member_name = current_token().value;
    SrcLoc member_loc = current_token().loc;
    advance();

    std::vector<TemplateArgument> member_arguments;
    bool member_has_template_argument_list = false;
    if (gentle_check(TokenType::LESS_THAN)) {
        member_has_template_argument_list = true;
        member_arguments = parse_cpp_template_argument_list();
    }

    auto qualifier_analysis = analyze_cpp_qualified_type_owner(
        qualifier_name,
        qualifier_arguments,
        qualifier_has_template_argument_list,
        qualifier_loc);
    if (!qualifier_analysis || !qualifier_analysis->owner_type) {
        restore();
        return std::nullopt;
    }
    DependentTypeLookupState state;
    state.qualifier_type = qualifier_analysis->owner_type;
    state.is_dependent = qualifier_analysis->is_dependent;
    state.is_current_instantiation =
        qualifier_analysis->is_current_instantiation;

    std::string current_qualifier_spelling = format_component_spelling(
        qualifier_name,
        qualifier_arguments,
        qualifier_has_template_argument_list);

    while (true) {
        bool has_more_qualifiers = is_cpp_scope_resolution_here();

        if (saw_template_keyword && !member_has_template_argument_list) {
            error_custloc(
                "expected template-id after 'template' keyword",
                member_loc);
        }

        const bool is_terminal_component = !has_more_qualifiers;
        const bool terminal_is_known_type =
            saw_typename_keyword || allow_implicit_typename ||
            is_type_requirement;
        if (!member_has_template_argument_list && is_terminal_component) {
            if (saw_typename_keyword &&
                !is_type_requirement &&
                !state.is_dependent &&
                !state.is_current_instantiation) {
                error_custloc(
                    "'typename' is only allowed before qualified dependent type names",
                    start_tok.loc);
            }
            if (!terminal_is_known_type &&
                state.requires_typename_keyword() &&
                gentle_check(TokenType::LEFT_PAREN)) {
                restore();
                return std::nullopt;
            }
            if (!terminal_is_known_type &&
                state.requires_typename_keyword()) {
                diagnose_missing_cpp_typename_keyword(
                    current_qualifier_spelling,
                    member_name,
                    start_tok.loc);
            }
        }

        std::string member_spelling = format_component_spelling(
            member_name,
            member_arguments,
            member_has_template_argument_list);

        if (member_has_template_argument_list) {
            if (state.is_dependent_context()) {
                if (!saw_template_keyword) {
                    if (state.requires_template_keyword()) {
                        diagnose_missing_cpp_template_keyword(
                            current_qualifier_spelling,
                            member_name,
                            member_loc);
                    }
                }
                state.qualifier_type = QualType(std::make_shared<DependentNameType>(
                    state.qualifier_type,
                    member_name,
                    std::move(member_arguments),
                    state.is_current_instantiation,
                    is_terminal_component && terminal_is_known_type,
                    true));
                state.is_dependent = true;
                state.is_current_instantiation = false;
            } else {
                auto nested_template_type =
                    collect_->collect_lookup_record_nested_template_type(
                        state.qualifier_type,
                        member_name,
                        member_arguments,
                        member_loc);
                if (!nested_template_type) {
                    restore();
                    return std::nullopt;
                }
                state.qualifier_type = nested_template_type;
                state.is_dependent = type_depends_on_template_parameters(
                    nested_template_type,
                    ast_ctx.get());
                state.is_current_instantiation = false;
                if (is_terminal_component && saw_typename_keyword &&
                    !state.is_dependent) {
                    error_custloc(
                        "'typename' is only allowed before qualified dependent type names",
                        start_tok.loc);
                }
            }
        } else {
            if (state.is_dependent_context()) {
                state.qualifier_type = QualType(std::make_shared<DependentNameType>(
                    state.qualifier_type,
                    member_name,
                    std::vector<TemplateArgument>{},
                    state.is_current_instantiation,
                    is_terminal_component && terminal_is_known_type,
                    false));
                state.is_dependent = true;
                state.is_current_instantiation = false;
            } else {
                auto nested_type =
                    collect_->collect_lookup_record_nested_type(
                        state.qualifier_type,
                        member_name);
                if (!nested_type) {
                    restore();
                    return std::nullopt;
                }
                state.qualifier_type = nested_type;
                state.is_dependent = type_depends_on_template_parameters(
                    nested_type,
                    ast_ctx.get());
                state.is_current_instantiation = false;
            }
        }

        if (!is_terminal_component && !state.is_dependent_context()) {
            state.qualifier_type =
                prepare_cpp_qualified_type_owner(state.qualifier_type);
            if (!state.qualifier_type) {
                restore();
                return std::nullopt;
            }
        }

        if (is_terminal_component) {
            ParsedCppTypeNameSpecifier result;
            result.type = state.qualifier_type;
            result.spelling = current_qualifier_spelling + "::" + member_spelling;
            return result;
        }

        current_qualifier_spelling += "::";
        current_qualifier_spelling += member_spelling;

        consume_cpp_scope_resolution();
        saw_template_keyword = gentle_check_and_consume(TokenType::TEMPLATE);
        if (!gentle_check(TokenType::IDENTIFIER)) {
            error_custloc(
                "expected identifier after '::' in qualified type name",
                current_token().loc);
        }

        member_name = current_token().value;
        member_loc = current_token().loc;
        advance();

        member_arguments.clear();
        member_has_template_argument_list = false;
        if (gentle_check(TokenType::LESS_THAN)) {
            member_has_template_argument_list = true;
            member_arguments = parse_cpp_template_argument_list();
        }
    }
}

std::vector<std::unique_ptr<Decl>>
Parser::parse_cpp_explicit_specialization_declaration(
    Token template_tok,
    bool member_template_declaration,
    bool angle_brackets_already_consumed) {
    std::vector<std::unique_ptr<Decl>> explicit_decls;
    pending_cpp_explicit_specialization_info_.reset();
    if (!angle_brackets_already_consumed) {
        check_and_consume(TokenType::LESS_THAN);
        check_and_consume(TokenType::GREATER_THAN);
    }

    if (member_template_declaration) {
        fail_cpp_future_work(
            "explicit specialization",
            "class-scope explicit specialization ownership",
            template_tok.loc);
    }

    auto resolve_primary_class_template =
        [&](const std::string& name,
            SrcLoc loc) -> const ClassTemplateDecl* {
        auto lookup_scope = collect_->collect_current_scope();
        while (lookup_scope &&
               scope_flags_contains(
                   lookup_scope->flags,
                   ScopeFlags::TemplateParameterScope)) {
            lookup_scope = lookup_scope->parent;
        }
        const DeclBinding* template_binding =
            LookupEngine::lookup_unqualified_template_binding(
                name,
                lookup_scope ? lookup_scope : collect_->collect_current_scope(),
                true,
                LookupNamespace::Tag);
        const Decl* primary_template = nullptr;
        if (template_binding) {
            primary_template = template_binding->template_decl;
            if (!primary_template &&
                template_binding->template_overload_candidates.size() == 1) {
                primary_template =
                    template_binding->template_overload_candidates.front();
            }
        }
        auto* class_template = dyn_cast<ClassTemplateDecl>(primary_template);
        if (!class_template) {
            error_custloc(
                "explicit specialization requires a prior primary template '" +
                    name + "'",
                loc);
        }
        const TemplateDecl* canonical =
            get_template_decl_canonical_decl(class_template);
        auto* canonical_class_template =
            dyn_cast<ClassTemplateDecl>(const_cast<TemplateDecl*>(canonical));
        return canonical_class_template ? canonical_class_template : class_template;
    };

    auto resolve_primary_function_template =
        [&](const FuncDecl* specialized_function,
            std::vector<TemplateArgument>& deduced_arguments_out)
        -> const FunctionTemplateDecl* {
        deduced_arguments_out.clear();
        if (!specialized_function || specialized_function->name.empty()) {
            error_custloc(
                "explicit specialization requires a named function declaration",
                specialized_function ? specialized_function->location : template_tok.loc);
        }

        auto lookup_scope = collect_->collect_current_scope();
        while (lookup_scope &&
               scope_flags_contains(
                   lookup_scope->flags,
                   ScopeFlags::TemplateParameterScope)) {
            lookup_scope = lookup_scope->parent;
        }
        const DeclBinding* template_binding =
            LookupEngine::lookup_unqualified_template_binding(
                specialized_function->name,
                lookup_scope ? lookup_scope : collect_->collect_current_scope(),
                true,
                LookupNamespace::Ordinary);
        if (!template_binding) {
            error_custloc(
                "explicit specialization requires a prior primary template '" +
                    specialized_function->name + "'",
                specialized_function->location);
        }

        std::vector<const FunctionTemplateDecl*> candidates;
        auto append_candidate = [&](const Decl* candidate) {
            auto* function_template = dyn_cast<FunctionTemplateDecl>(
                const_cast<Decl*>(candidate));
            if (!function_template) {
                return;
            }
            for (const auto* existing : candidates) {
                if (existing == function_template) {
                    return;
                }
            }
            candidates.push_back(function_template);
        };
        append_candidate(template_binding->template_decl);
        for (const auto* candidate : template_binding->template_overload_candidates) {
            append_candidate(candidate);
        }

        const FunctionTemplateDecl* matched_template = nullptr;
        std::vector<TemplateArgument> matched_arguments;
        for (const auto* candidate : candidates) {
            std::vector<TemplateArgument> deduced_arguments;
            if (!collect_->deduce_function_template_specialization_arguments(
                    candidate,
                    QualType(specialized_function->type),
                    deduced_arguments)) {
                continue;
            }
            if (matched_template && matched_template != candidate) {
                error_custloc(
                    "explicit specialization of function template '" +
                        specialized_function->name +
                        "' is ambiguous",
                    specialized_function->location);
            }
            matched_template = candidate;
            matched_arguments = std::move(deduced_arguments);
        }

        if (!matched_template) {
            error_custloc(
                "explicit specialization does not match any primary template '" +
                    specialized_function->name + "'",
                specialized_function->location);
        }

        const TemplateDecl* canonical =
            get_template_decl_canonical_decl(matched_template);
        auto* canonical_function_template =
            dyn_cast<FunctionTemplateDecl>(const_cast<TemplateDecl*>(canonical));
        deduced_arguments_out = std::move(matched_arguments);
        return canonical_function_template ? canonical_function_template : matched_template;
    };

    auto resolve_primary_variable_template =
        [&](const VariableDecl* specialized_variable,
            std::vector<TemplateArgument>& specialization_arguments_out)
        -> const VariableTemplateDecl* {
            specialization_arguments_out.clear();
            if (!specialized_variable || specialized_variable->name.empty()) {
                error_custloc(
                    "explicit specialization requires a named variable template",
                    template_tok.loc);
            }
            if (!specialized_variable->has_explicit_specialization_argument_list ||
                specialized_variable->explicit_specialization_arguments.empty()) {
                error_custloc(
                    "explicit specialization of variable template '" +
                        specialized_variable->name +
                        "' requires a template-id",
                    specialized_variable ? specialized_variable->location
                                         : template_tok.loc);
            }

            auto lookup_scope = collect_->collect_current_scope();
            while (lookup_scope &&
                   scope_flags_contains(
                       lookup_scope->flags,
                       ScopeFlags::TemplateParameterScope)) {
                lookup_scope = lookup_scope->parent;
            }
            const DeclBinding* template_binding =
                LookupEngine::lookup_unqualified_template_binding(
                    specialized_variable->name,
                    lookup_scope ? lookup_scope : collect_->collect_current_scope(),
                    true,
                    LookupNamespace::Ordinary);
            if (!template_binding) {
                error_custloc(
                    "explicit specialization requires a prior primary template '" +
                        specialized_variable->name + "'",
                    specialized_variable->location);
            }

            std::vector<const VariableTemplateDecl*> candidates;
            auto append_candidate = [&](const Decl* candidate) {
                auto* variable_template = dyn_cast<VariableTemplateDecl>(
                    const_cast<Decl*>(candidate));
                if (!variable_template) {
                    return;
                }
                for (const auto* existing : candidates) {
                    if (existing == variable_template) {
                        return;
                    }
                }
                candidates.push_back(variable_template);
            };
            append_candidate(template_binding->template_decl);
            for (const auto* candidate : template_binding->template_overload_candidates) {
                append_candidate(candidate);
            }

            const VariableTemplateDecl* matched_template = nullptr;
            for (const auto* candidate : candidates) {
                if (!candidate) {
                    continue;
                }
                if (matched_template && matched_template != candidate) {
                    error_custloc(
                        "explicit specialization of variable template '" +
                            specialized_variable->name +
                            "' is ambiguous",
                        specialized_variable->location);
                }
                matched_template = candidate;
            }

            if (!matched_template) {
                error_custloc(
                    "explicit specialization does not match any primary template '" +
                        specialized_variable->name + "'",
                    specialized_variable->location);
            }

            const TemplateDecl* canonical =
                get_template_decl_canonical_decl(matched_template);
            auto* canonical_variable_template =
                dyn_cast<VariableTemplateDecl>(
                    const_cast<TemplateDecl*>(canonical));
            specialization_arguments_out =
                specialized_variable->explicit_specialization_arguments;
            return canonical_variable_template ? canonical_variable_template
                                               : matched_template;
        };

    auto explicit_specialization_primary_name =
        [](const TemplateDecl* primary_template) -> std::string {
        if (!primary_template) {
            return "template";
        }
        if (const auto* class_template =
                dyn_cast<ClassTemplateDecl>(
                    const_cast<TemplateDecl*>(primary_template))) {
            const auto* record_decl = class_template->record_decl();
            if (record_decl && !record_decl->name.empty()) {
                return record_decl->name;
            }
        }
        if (const auto* function_template =
                dyn_cast<FunctionTemplateDecl>(
                    const_cast<TemplateDecl*>(primary_template))) {
            const auto* function_decl = function_template->function_decl();
            if (function_decl && !function_decl->name.empty()) {
                return function_decl->name;
            }
        }
        if (const auto* variable_template =
                dyn_cast<VariableTemplateDecl>(
                    const_cast<TemplateDecl*>(primary_template))) {
            const auto* variable_decl = variable_template->variable_decl();
            if (variable_decl && !variable_decl->name.empty()) {
                return variable_decl->name;
            }
        }
        if (const auto* alias_template =
                dyn_cast<AliasTemplateDecl>(
                    const_cast<TemplateDecl*>(primary_template))) {
            const auto* alias_decl = alias_template->alias_decl();
            if (alias_decl && !alias_decl->name.empty()) {
                return alias_decl->name;
            }
        }
        return "template";
    };

    auto format_class_specialization_name =
        [](std::string_view record_name,
            const std::vector<TemplateArgument>& specialization_arguments)
            -> std::string {
            std::string out(record_name);
            out += "<";
            for (size_t idx = 0; idx < specialization_arguments.size(); ++idx) {
                if (idx != 0) {
                    out += ", ";
                }
                out += specialization_arguments[idx].to_string();
            }
            out += ">";
            return out;
        };

    auto format_function_template_specialization_name =
        [](std::string_view function_name,
           const std::vector<TemplateArgument>& specialization_arguments)
            -> std::string {
            std::string out(function_name);
            out += "<";
            for (size_t idx = 0; idx < specialization_arguments.size(); ++idx) {
                if (idx != 0) {
                    out += ", ";
                }
                out += specialization_arguments[idx].to_string();
            }
            out += ">";
            return out;
        };

    auto explicit_specialization_display_name =
        [&](const TemplateDecl* primary_template,
            const ClassTemplateDecl* owner_primary_template,
            const TemplateExplicitSpecializationDecl* explicit_specialization)
            -> std::string {
            if (!explicit_specialization) {
                return explicit_specialization_primary_name(primary_template);
            }

            if (const auto* specialized_record =
                    dyn_cast<CppRecordDecl>(
                        const_cast<Decl*>(
                            explicit_specialization->get_specialized_decl()))) {
                if (explicit_specialization->has_explicit_argument_list ||
                    !explicit_specialization->specialization_arguments.empty()) {
                    return format_class_specialization_name(
                        specialized_record->name.empty()
                            ? explicit_specialization_primary_name(primary_template)
                            : specialized_record->name,
                        explicit_specialization->specialization_arguments);
                }
                if (!specialized_record->name.empty()) {
                    return specialized_record->name;
                }
            }

            if (const auto* specialized_function =
                    dyn_cast<FuncDecl>(
                        const_cast<Decl*>(
                            explicit_specialization->get_specialized_decl()))) {
                std::string out;
                if (const auto* qualifier_prefix =
                        get_func_decl_cxx_qualifier_prefix(specialized_function);
                    qualifier_prefix && !qualifier_prefix->empty()) {
                    out += *qualifier_prefix;
                    out += "::";
                } else if (explicit_specialization->primary_member_decl &&
                           owner_primary_template &&
                           !explicit_specialization->owner_specialization_arguments.empty()) {
                    out += format_class_specialization_name(
                        explicit_specialization_primary_name(owner_primary_template),
                        explicit_specialization->owner_specialization_arguments);
                    out += "::";
                }
                std::string function_name =
                    specialized_function->name.empty()
                        ? explicit_specialization_primary_name(primary_template)
                        : specialized_function->name;
                if (isa<FunctionTemplateDecl>(
                        const_cast<TemplateDecl*>(primary_template)) &&
                    !explicit_specialization->specialization_arguments.empty()) {
                    out += format_function_template_specialization_name(
                        function_name,
                        explicit_specialization->specialization_arguments);
                } else {
                    out += function_name;
                }
                return out;
            }

            if (const auto* specialized_variable =
                    dyn_cast<VariableDecl>(
                        const_cast<Decl*>(
                            explicit_specialization->get_specialized_decl()))) {
                std::string out;
                if (specialized_variable->sym) {
                    if (const auto* qualifier_prefix =
                            get_symbol_cxx_qualifier_prefix(
                                specialized_variable->sym.get());
                        qualifier_prefix && !qualifier_prefix->empty()) {
                        out += *qualifier_prefix;
                        out += "::";
                    }
                }
                std::string variable_name =
                    specialized_variable->name.empty()
                        ? explicit_specialization_primary_name(primary_template)
                        : specialized_variable->name;
                if (isa<VariableTemplateDecl>(
                        const_cast<TemplateDecl*>(primary_template)) &&
                    !explicit_specialization->specialization_arguments.empty()) {
                    out += format_function_template_specialization_name(
                        variable_name,
                        explicit_specialization->specialization_arguments);
                } else {
                    out += variable_name;
                }
                return out;
            }

            return explicit_specialization_primary_name(primary_template);
        };

    auto find_late_explicit_specialization_first_required_loc =
        [&](const TemplateDecl* primary_template,
            const ClassTemplateDecl* owner_primary_template,
            const TemplateExplicitSpecializationDecl* explicit_specialization)
            -> SrcLoc {
            if (!ast_ctx || !primary_template || !explicit_specialization) {
                return SrcLoc();
            }

            if (const auto* class_template =
                    dyn_cast<ClassTemplateDecl>(
                        const_cast<TemplateDecl*>(primary_template))) {
                const auto* entry =
                    ast_ctx->lookup_class_template_specialization(
                        class_template,
                        explicit_specialization->specialization_arguments);
                if (!entry) {
                    return SrcLoc();
                }
                if (explicit_specialization->primary_member_decl) {
                    return entry->lookup_primary_member_first_required_loc(
                        explicit_specialization->primary_member_decl);
                }
                return entry->first_required_loc;
            }

            const auto* function_template =
                dyn_cast<FunctionTemplateDecl>(
                    const_cast<TemplateDecl*>(primary_template));
            if (function_template) {
                const FunctionTemplateDecl* lookup_template = function_template;
                if (owner_primary_template &&
                    explicit_specialization->primary_member_decl &&
                    !explicit_specialization->owner_specialization_arguments.empty()) {
                    const auto* owner_entry =
                        ast_ctx->lookup_class_template_specialization(
                            owner_primary_template,
                            explicit_specialization->owner_specialization_arguments);
                    if (!owner_entry) {
                        return SrcLoc();
                    }
                    lookup_template =
                        owner_entry->lookup_owner_specialized_member_template(
                            explicit_specialization->primary_member_decl);
                    if (!lookup_template) {
                        return SrcLoc();
                    }
                }

                const auto* entry =
                    ast_ctx->lookup_function_template_specialization(
                        lookup_template,
                        explicit_specialization->specialization_arguments);
                return entry ? entry->first_required_loc : SrcLoc();
            }

            const auto* variable_template =
                dyn_cast<VariableTemplateDecl>(
                    const_cast<TemplateDecl*>(primary_template));
            if (!variable_template) {
                return SrcLoc();
            }

            const auto* entry =
                ast_ctx->lookup_variable_template_specialization(
                    variable_template,
                    explicit_specialization->specialization_arguments);
            return entry ? entry->first_required_loc : SrcLoc();
        };

    auto explicit_specialization_signature_matches =
        [&](const TemplateExplicitSpecializationDecl* existing,
            const TemplateExplicitSpecializationDecl* current) -> bool {
            if (!existing || !current) {
                return false;
            }
            const auto* existing_decl = existing->get_specialized_decl();
            const auto* current_decl = current->get_specialized_decl();
            if (!existing_decl || !current_decl ||
                existing_decl->get_kind() != current_decl->get_kind()) {
                return false;
            }

            if (const auto* existing_function =
                    dyn_cast<FuncDecl>(const_cast<Decl*>(existing_decl))) {
                const auto* current_function =
                    dyn_cast<FuncDecl>(const_cast<Decl*>(current_decl));
                return current_function &&
                       cpp_out_of_line_type_matches(
                           QualType(existing_function->type),
                           QualType(current_function->type),
                           true);
            }
            if (const auto* existing_record =
                    dyn_cast<CppRecordDecl>(const_cast<Decl*>(existing_decl))) {
                const auto* current_record =
                    dyn_cast<CppRecordDecl>(const_cast<Decl*>(current_decl));
                return current_record &&
                       existing_record->record_kind == current_record->record_kind &&
                       existing_record->name == current_record->name;
            }
            if (const auto* existing_variable =
                    dyn_cast<VariableDecl>(const_cast<Decl*>(existing_decl))) {
                const auto* current_variable =
                    dyn_cast<VariableDecl>(const_cast<Decl*>(current_decl));
                return current_variable &&
                       existing_variable->name == current_variable->name &&
                       cpp_out_of_line_type_matches(
                           existing_variable->type,
                           current_variable->type,
                           false);
            }
            return true;
        };

    auto normalize_explicit_specialization_arguments =
        [&](const TemplateDecl* primary_template,
            std::vector<TemplateArgument>& arguments,
            SrcLoc loc,
            const std::string& subject) -> bool {
            if (!collect_) {
                error_custloc(
                    "internal error: missing Collect during explicit specialization normalization",
                    loc);
                return false;
            }
            if (!primary_template) {
                error_custloc(
                    "internal error: missing primary template during explicit specialization normalization",
                    loc);
                return false;
            }

            TemplateArgumentBindings bindings;
            std::vector<TemplateArgument> normalized_arguments;
            std::string normalize_error;
            if (!collect_->collect_bind_and_normalize_template_arguments_for_specialization(
                    primary_template,
                    arguments,
                    bindings,
                    normalized_arguments,
                    loc,
                    &normalize_error)) {
                error_custloc(
                    subject + " argument list does not match primary template" +
                        (normalize_error.empty()
                             ? std::string()
                             : ": " + normalize_error),
                    loc);
                return false;
            }

            arguments = std::move(normalized_arguments);
            return true;
        };

    auto register_explicit_specialization =
        [&](const TemplateDecl* primary_template,
            const ClassTemplateDecl* owner_primary_template,
            std::unique_ptr<TemplateExplicitSpecializationDecl> explicit_specialization) {
            if (!primary_template || !explicit_specialization) {
                return;
            }

            if (!normalize_explicit_specialization_arguments(
                    primary_template,
                    explicit_specialization->specialization_arguments,
                    explicit_specialization->location,
                    "explicit specialization")) {
                explicit_decls.push_back(std::move(explicit_specialization));
                return;
            }
            if (owner_primary_template &&
                !explicit_specialization->owner_specialization_arguments.empty() &&
                !normalize_explicit_specialization_arguments(
                    owner_primary_template,
                    explicit_specialization->owner_specialization_arguments,
                    explicit_specialization->location,
                    "explicit specialization owner")) {
                explicit_decls.push_back(std::move(explicit_specialization));
                return;
            }

            auto* primary_template_mutable =
                const_cast<TemplateDecl*>(primary_template);
            auto* existing = primary_template_mutable->find_explicit_specialization(
                explicit_specialization->specialization_arguments,
                explicit_specialization->owner_specialization_arguments,
                explicit_specialization->primary_member_decl);
            if (!existing) {
                SrcLoc first_required_loc =
                    find_late_explicit_specialization_first_required_loc(
                        primary_template,
                        owner_primary_template,
                        explicit_specialization.get());
                if (!first_required_loc.isInvalid()) {
                    error_custloc(
                        "explicit specialization of '" +
                            explicit_specialization_display_name(
                                primary_template,
                                owner_primary_template,
                                explicit_specialization.get()) +
                            "' after instantiation",
                        explicit_specialization->location);
                    if (diag_engine) {
                        diag_engine->report_note(
                            "implicit instantiation first required here",
                            first_required_loc);
                    }
                    explicit_decls.push_back(std::move(explicit_specialization));
                    return;
                }
            }
            if (existing) {
                if (!explicit_specialization_signature_matches(
                        existing,
                        explicit_specialization.get())) {
                    error_custloc(
                        "explicit specialization of '" +
                            explicit_specialization_primary_name(primary_template) +
                            "' does not match the previous declaration",
                        explicit_specialization->location);
                }
                if (explicit_specialization->is_definition()) {
                    if (existing->is_definition()) {
                        error_custloc(
                            "redefinition of explicit specialization '" +
                                explicit_specialization_primary_name(primary_template) +
                                "'",
                            explicit_specialization->location);
                    }
                    primary_template_mutable->replace_explicit_specialization(
                        existing,
                        explicit_specialization.get());
                }
            } else {
                primary_template_mutable->add_explicit_specialization(
                    explicit_specialization.get());
            }
            explicit_decls.push_back(std::move(explicit_specialization));
        };

    if (gentle_check(TokenType::CLASS) ||
        gentle_check(TokenType::STRUCT) ||
        gentle_check(TokenType::UNION)) {
        std::vector<TemplateArgument> specialization_arguments;
        bool has_specialization_argument_list = false;
        auto specialized_record =
            parse_cpp_record_specifier(
                &specialization_arguments,
                &has_specialization_argument_list,
                true);
        check_and_consume(TokenType::SEMICOLON);

        auto* record_decl = dyn_cast<CppRecordDecl>(specialized_record.get());
        if (!record_decl) {
            error_custloc(
                "internal error: explicit specialization did not parse as a record declaration",
                template_tok.loc);
        }
        if (record_decl->name.empty()) {
            fail_cpp_unsupported(
                "anonymous explicit specialization",
                record_decl->location);
        }
        if (!has_specialization_argument_list) {
            error_custloc(
                "explicit specialization of class template '" +
                    record_decl->name +
                    "' requires a template-id",
                record_decl->location);
        }

        const ClassTemplateDecl* primary_template =
            resolve_primary_class_template(record_decl->name, record_decl->location);
        if (!normalize_explicit_specialization_arguments(
                primary_template,
                specialization_arguments,
                record_decl->location,
                "explicit class specialization")) {
            return explicit_decls;
        }
        std::unique_ptr<ObjectDecl> specialized_semantic_decl;
        if (auto semantic_decl = build_cpp_record_semantic_decl(
                *record_decl,
                format_class_specialization_name(
                    record_decl->name,
                    specialization_arguments))) {
            if (auto* semantic_record = dyn_cast<ObjectDecl>(semantic_decl.get())) {
                specialized_semantic_decl = std::unique_ptr<ObjectDecl>(
                    static_cast<ObjectDecl*>(semantic_decl.release()));
                if (auto record_type =
                        specialized_semantic_decl->get_record_type()) {
                    record_type->set_class_template_specialization_info(
                        primary_template,
                        specialization_arguments);
                }
            }
        }
        auto explicit_specialization =
            make_ast<TemplateExplicitSpecializationDecl>(
                *ast_ctx,
                primary_template,
                std::move(specialized_record),
                std::move(specialization_arguments),
                std::vector<TemplateArgument>{},
                nullptr,
                false,
                true,
                template_tok.loc);
        if (specialized_semantic_decl) {
            explicit_specialization->set_specialized_record_semantic_decl(
                std::move(specialized_semantic_decl));
        }
        register_explicit_specialization(
            primary_template,
            nullptr,
            std::move(explicit_specialization));
        return explicit_decls;
    }

    ++cpp_explicit_specialization_parse_depth_;
    struct ExplicitSpecializationParseGuard {
        uint32_t& depth;
        std::optional<PendingCppExplicitSpecializationInfo>* pending = nullptr;
        ~ExplicitSpecializationParseGuard() {
            if (depth > 0) {
                --depth;
            }
            if (pending) {
                pending->reset();
            }
        }
    } explicit_specialization_guard{
        cpp_explicit_specialization_parse_depth_,
        &pending_cpp_explicit_specialization_info_};

    auto specialized_decls = parse_declaration();
    if (specialized_decls.empty() ||
        specialized_decls.size() != 1 ||
        !specialized_decls.front()) {
        fail_cpp_future_work(
            "explicit specialization",
            "function/member explicit specialization ownership",
            template_tok.loc);
    }

    if (pending_cpp_explicit_specialization_info_.has_value()) {
        const auto pending_info =
            std::move(pending_cpp_explicit_specialization_info_.value());
        const TemplateDecl* primary_template =
            pending_info.primary_member_template
                ? static_cast<const TemplateDecl*>(
                      pending_info.primary_member_template)
                : static_cast<const TemplateDecl*>(
                      pending_info.owner_primary_template);
        if (!primary_template) {
            error_custloc(
                "internal error: missing primary template for member explicit specialization",
                specialized_decls.front()->location);
        }
        auto explicit_specialization =
            make_ast<TemplateExplicitSpecializationDecl>(
                *ast_ctx,
                primary_template,
                std::move(specialized_decls.front()),
                pending_info.specialization_arguments,
                pending_info.owner_specialization_arguments,
                pending_info.primary_member_decl,
                true,
                false,
                template_tok.loc);
        register_explicit_specialization(
            primary_template,
            pending_info.owner_primary_template,
            std::move(explicit_specialization));
        return explicit_decls;
    }

    if (specialized_decls.size() == 1 &&
        isa<TemplateExplicitSpecializationDecl>(specialized_decls.front().get())) {
        return specialized_decls;
    }

    if (auto* specialized_function =
            dyn_cast<FuncDecl>(specialized_decls.front().get())) {
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(specialized_function);
            qualifier_prefix && !qualifier_prefix->empty()) {
            fail_cpp_future_work(
                "explicit specialization",
                "qualified/member explicit specialization ownership",
                specialized_function->location);
        }

        std::vector<TemplateArgument> deduced_arguments;
        const FunctionTemplateDecl* primary_template =
            resolve_primary_function_template(
                specialized_function,
                deduced_arguments);
        std::vector<TemplateArgument> specialization_arguments =
            deduced_arguments;
        if (!normalize_explicit_specialization_arguments(
                primary_template,
                specialization_arguments,
                specialized_function->location,
                "explicit function specialization")) {
            return explicit_decls;
        }
        bool has_explicit_argument_list =
            specialized_function->has_explicit_specialization_argument_list;
        if (has_explicit_argument_list) {
            auto explicit_arguments =
                specialized_function->explicit_specialization_arguments;
            if (!normalize_explicit_specialization_arguments(
                    primary_template,
                    explicit_arguments,
                    specialized_function->location,
                    "explicit function specialization")) {
                return explicit_decls;
            }
            bool explicit_arguments_match =
                explicit_arguments.size() == specialization_arguments.size();
            size_t compare_count =
                explicit_arguments.size() < specialization_arguments.size()
                    ? explicit_arguments.size()
                    : specialization_arguments.size();
            for (size_t idx = 0; idx < compare_count; ++idx) {
                if (!explicit_arguments[idx].equals(specialization_arguments[idx])) {
                    explicit_arguments_match = false;
                }
            }
            if (!explicit_arguments_match) {
                error_custloc(
                    "explicit specialization argument list does not match specialized function declaration",
                    specialized_function->location);
                return explicit_decls;
            }
            specialization_arguments = std::move(explicit_arguments);
        }
        auto explicit_specialization =
            make_ast<TemplateExplicitSpecializationDecl>(
                *ast_ctx,
                primary_template,
                std::move(specialized_decls.front()),
                std::move(specialization_arguments),
                std::vector<TemplateArgument>{},
                nullptr,
                false,
                has_explicit_argument_list,
                template_tok.loc);
        register_explicit_specialization(
            primary_template,
            nullptr,
            std::move(explicit_specialization));
        return explicit_decls;
    }

    if (auto* specialized_variable =
            dyn_cast<VariableDecl>(specialized_decls.front().get())) {
        if (specialized_variable->storage_class == StorageClass::EXTERN &&
            !specialized_variable->init &&
            !specialized_variable->is_inline) {
            error_custloc(
                "explicit specialization of variable template '" +
                    specialized_variable->name +
                    "' requires a definition",
                specialized_variable->location);
        }

        std::vector<TemplateArgument> specialization_arguments;
        const VariableTemplateDecl* primary_template =
            resolve_primary_variable_template(
                specialized_variable,
                specialization_arguments);
        if (!normalize_explicit_specialization_arguments(
                primary_template,
                specialization_arguments,
                specialized_variable->location,
                "explicit variable specialization")) {
            return explicit_decls;
        }
        auto registered_specialization_arguments = specialization_arguments;
        SrcLoc specialization_loc = specialized_variable->location;
        auto explicit_specialization =
            make_ast<TemplateExplicitSpecializationDecl>(
                *ast_ctx,
                primary_template,
                std::move(specialized_decls.front()),
                std::move(specialization_arguments),
                std::vector<TemplateArgument>{},
                nullptr,
                false,
                true,
                template_tok.loc);
        register_explicit_specialization(
            primary_template,
            nullptr,
            std::move(explicit_specialization));
        if (collect_) {
            std::shared_ptr<Symbol> specialization_symbol;
            collect_->ensure_variable_template_specialization_symbol(
                primary_template,
                registered_specialization_arguments,
                specialization_loc,
                &specialization_symbol);
        }
        return explicit_decls;
    }

    fail_cpp_future_work(
        "explicit specialization",
        "function/member explicit specialization ownership",
        specialized_decls.front()->location);
    return explicit_decls;
}

std::optional<CppTypeConstraint>
Parser::parse_cpp_type_constraint(bool diagnose_on_failure) {
    Token start_tok = current_token();
    size_t saved_idx = get_token_idx();
    auto saved_split_state = tok_mgnt.get_split_token_state();
    auto restore = [&]() {
        set_token_idx(saved_idx);
        tok_mgnt.set_split_token_state(saved_split_state);
    };
    auto fail = [&](const std::string& message,
                    SrcLoc loc) -> std::optional<CppTypeConstraint> {
        restore();
        if (diagnose_on_failure) {
            error_custloc(message, loc);
        }
        return std::nullopt;
    };

    bool has_global_qualifier = consume_cpp_scope_resolution();
    if (!gentle_check(TokenType::IDENTIFIER)) {
        return fail("expected concept name in type-constraint", start_tok.loc);
    }

    std::vector<std::string> qualifier_components;
    std::string concept_name;
    SrcLoc concept_loc = current_token().loc;
    while (gentle_check(TokenType::IDENTIFIER)) {
        std::string component = current_token().value;
        SrcLoc component_loc = current_token().loc;
        advance();
        if (!is_cpp_scope_resolution_here()) {
            concept_name = std::move(component);
            concept_loc = component_loc;
            break;
        }
        qualifier_components.push_back(std::move(component));
        consume_cpp_scope_resolution();
    }

    if (concept_name.empty()) {
        return fail("expected concept name in type-constraint", start_tok.loc);
    }

    std::vector<TemplateArgument> written_arguments;
    if (gentle_check(TokenType::LESS_THAN)) {
        written_arguments = parse_cpp_template_argument_list();
    }

    CppQualifiedExprInfo qualified_info =
        build_cpp_qualified_expr_info(
            has_global_qualifier,
            qualifier_components);
    const CppQualifiedExprInfo* lookup_qualifier =
        qualified_info.has_qualifier() ? &qualified_info : nullptr;
    auto concepts =
        collect_->collect_lookup_concepts(concept_name, lookup_qualifier);
    if (concepts.empty()) {
        std::string display_name =
            qualified_name_utils::format_cpp_qualified_name(
                has_global_qualifier,
                qualifier_components,
                concept_name);
        return fail(
            "unknown concept '" + display_name + "' in type-constraint",
            concept_loc);
    }
    if (concepts.size() > 1) {
        std::string display_name =
            qualified_name_utils::format_cpp_qualified_name(
                has_global_qualifier,
                qualifier_components,
                concept_name);
        return fail(
            "ambiguous concept '" + display_name + "' in type-constraint",
            concept_loc);
    }

    CppTypeConstraint constraint;
    constraint.concept_decl = concepts.front();
    constraint.concept_name =
        qualified_name_utils::format_cpp_qualified_name(
            has_global_qualifier,
            qualifier_components,
            concept_name);
    constraint.template_arguments = std::move(written_arguments);
    constraint.location = concept_loc;
    return constraint;
}

bool Parser::can_start_cpp_constrained_placeholder_type_specifier_for_lookahead() {
    if (!is_cxx_mode_active() || !lang_opts.is_cxx20_or_later()) {
        return false;
    }

    RevertingTentativeParsingAction tentative(*this);
    std::optional<CppTypeConstraint> type_constraint;
    try {
        type_constraint =
            parse_cpp_type_constraint(/*diagnose_on_failure=*/false);
    } catch (const ParseError&) {
        return false;
    } catch (const FatalErrorLimitReached&) {
        throw;
    }
    if (!type_constraint) {
        return false;
    }
    if (gentle_check(TokenType::AUTO)) {
        return true;
    }
    if (gentle_check(TokenType::DECLTYPE_KW) &&
        peek_token(1).type == TokenType::LEFT_PAREN &&
        peek_token(2).type == TokenType::AUTO &&
        peek_token(3).type == TokenType::RIGHT_PAREN) {
        return true;
    }
    return false;
}

TemplateParameterList
Parser::parse_cpp_template_parameter_list(uint32_t depth) {
    TemplateParameterList parameters;
    check_and_consume(TokenType::LESS_THAN);
    if (gentle_check(TokenType::GREATER_THAN)) {
        advance();
        return parameters;
    }

    auto parse_template_parameter_default_argument =
        [&]() -> TemplateArgument {
        ++template_pattern_depth_;
        struct TemplateParameterDefaultPatternGuard {
            uint32_t& depth;
            ~TemplateParameterDefaultPatternGuard() { --depth; }
        } template_parameter_default_pattern_guard{template_pattern_depth_};
        return parse_cpp_template_argument();
    };

    auto is_scope_resolution_at = [&](size_t offset) {
        return peek_token_shortcut(offset).type == TokenType::SCOPE_RESOLUTION ||
               (peek_token_shortcut(offset).type == TokenType::COLON &&
                peek_token_shortcut(offset + 1).type == TokenType::COLON);
    };

    auto skip_template_argument_list_for_lookahead =
        [&](size_t& offset) -> bool {
        if (peek_token_shortcut(offset).type != TokenType::LESS_THAN) {
            return false;
        }

        int depth_count = 0;
        while (peek_token_shortcut(offset).type != TokenType::Eof) {
            TokenType tok = peek_token_shortcut(offset).type;
            if (tok == TokenType::LESS_THAN) {
                ++depth_count;
                ++offset;
                continue;
            }
            if (tok == TokenType::GREATER_THAN) {
                --depth_count;
                ++offset;
                if (depth_count == 0) {
                    return true;
                }
                continue;
            }
            if (tok == TokenType::RIGHT_SHIFT) {
                if (depth_count <= 0) {
                    return false;
                }
                depth_count -= depth_count >= 2 ? 2 : 1;
                ++offset;
                if (depth_count == 0) {
                    return true;
                }
                continue;
            }
            if (tok == TokenType::ASSIGN_RSHIFT) {
                if (depth_count <= 0) {
                    return false;
                }
                depth_count -= depth_count >= 2 ? 2 : 1;
                ++offset;
                if (depth_count == 0) {
                    return true;
                }
                continue;
            }
            ++offset;
        }
        return false;
    };

    auto typename_starts_qualified_type_specifier = [&]() -> bool {
        if (!gentle_check(TokenType::TYPENAME)) {
            return false;
        }

        size_t offset = 1;
        if (peek_token_shortcut(offset).type == TokenType::DECLTYPE_KW) {
            ++offset;
            if (!skip_balanced_tokens_for_lookahead(
                    offset,
                    TokenType::LEFT_PAREN,
                    TokenType::RIGHT_PAREN)) {
                return false;
            }
            return is_scope_resolution_at(offset);
        }

        if (peek_token_shortcut(offset).type != TokenType::IDENTIFIER) {
            return false;
        }
        ++offset;
        if (peek_token_shortcut(offset).type == TokenType::LESS_THAN &&
            !skip_template_argument_list_for_lookahead(offset)) {
            return false;
        }
        return is_scope_resolution_at(offset);
    };

    auto parse_non_type_template_parameter =
        [&](Token param_tok) -> std::unique_ptr<TemplateNonTypeParmDecl> {
        DeclarationParser param_parser(this);
        auto parsed_type = param_parser.parse_declaration();
        if (!parsed_type) {
            error_custloc(
                "expected non-type template parameter declaration",
                param_tok.loc);
        }
        if (param_parser.str_class != StorageClass::NONE) {
            error_custloc(
                "storage class specifier is not allowed in template parameter",
                param_tok.loc);
        }
        bool is_parameter_pack = param_parser.is_parameter_pack;
        if (gentle_check_and_consume(TokenType::ELLIPSIS)) {
            if (is_parameter_pack) {
                error_custloc(
                    "duplicate ellipsis in non-type template parameter pack",
                    current_token().loc);
            }
            is_parameter_pack = true;
            if (param_parser.name.empty() &&
                gentle_check(TokenType::IDENTIFIER)) {
                param_parser.name = current_token().value;
                if (param_parser.loc.isInvalid()) {
                    param_parser.loc = current_token().loc;
                }
                advance();
            }
        }
        std::optional<TemplateArgument> default_argument;
        if (gentle_check(TokenType::ASSIGN)) {
            if (is_parameter_pack) {
                fail_cpp_unsupported(
                    "default template argument on non-type template parameter pack",
                    current_token().loc);
            }
            advance();
            default_argument =
                parse_template_parameter_default_argument();
        }

        SrcLoc param_loc = param_parser.loc.isInvalid()
            ? param_tok.loc
            : param_parser.loc;
        QualType parameter_type(parsed_type, param_parser.qualifiers);
        parameter_type =
            collect_->collect_try_realize_deferred_semantic_type(
                parameter_type);
        if (!is_supported_non_type_template_parameter_type(
                parameter_type,
                ast_ctx.get())) {
            fail_cpp_unsupported("non-type template parameter type", param_loc);
        }
        if (auto_type_utils::has_cxx_auto_type(parameter_type.get_shared())) {
            parameter_type = QualType(
                auto_type_utils::retag_cxx_auto_placeholders(
                    parameter_type.get_shared(),
                    AutoTypeFlavor::TemplateNonType),
                parameter_type.get_qualifiers());
        }

        std::shared_ptr<Symbol> parameter_symbol = nullptr;
        if (!param_parser.name.empty()) {
            parameter_symbol = collect_->collect_declare_variable_symbol(
                param_parser.name,
                parameter_type,
                StorageClass::NONE,
                true,
                false,
                param_loc);
        }
        auto param_decl = make_ast<TemplateNonTypeParmDecl>(
            *ast_ctx,
            param_parser.name,
            depth,
            static_cast<uint32_t>(parameters.size()),
            parameter_type,
            parameter_symbol,
            is_parameter_pack,
            param_loc);
        if (default_argument.has_value()) {
            if (default_argument->kind != TemplateArgumentKind::Value) {
                error_custloc(
                    "non-type template parameter default must be a constant expression",
                    param_loc);
            }
            set_template_parameter_default_argument(
                param_decl.get(),
                std::move(default_argument));
        }
        return param_decl;
    };

    while (true) {
        Token param_tok = current_token();
        if (lang_opts.is_cxx20_or_later() &&
            (param_tok.type == TokenType::IDENTIFIER ||
             param_tok.type == TokenType::SCOPE_RESOLUTION ||
             (param_tok.type == TokenType::COLON &&
              peek_token().type == TokenType::COLON))) {
            auto try_parse_constrained_type_parameter =
                [&]() -> std::unique_ptr<TemplateTypeParmDecl> {
                    TentativeParsingAction tentative(*this);

                    auto type_constraint =
                        parse_cpp_type_constraint(
                            /*diagnose_on_failure=*/false);
                    if (!type_constraint) {
                        return nullptr;
                    }

                    bool is_parameter_pack =
                        gentle_check_and_consume(TokenType::ELLIPSIS);

                    std::string param_name;
                    SrcLoc param_loc = type_constraint->location;
                    if (gentle_check(TokenType::IDENTIFIER)) {
                        param_name = current_token().value;
                        param_loc = current_token().loc;
                        advance();
                    }

                    auto param_type = std::make_shared<TemplateTypeParmType>(
                        param_name,
                        depth,
                        static_cast<uint32_t>(parameters.size()),
                        is_parameter_pack);
                    auto param_decl = make_ast<TemplateTypeParmDecl>(
                        *ast_ctx,
                        param_name,
                        depth,
                        static_cast<uint32_t>(parameters.size()),
                        param_type,
                        is_parameter_pack,
                        param_loc);
                    param_type->parameter_decl = param_decl.get();

                    std::vector<TemplateArgument> concept_arguments;
                    concept_arguments.push_back(
                        TemplateArgument(QualType(param_type)));
                    concept_arguments.insert(
                        concept_arguments.end(),
                        type_constraint->template_arguments.begin(),
                        type_constraint->template_arguments.end());
                    param_decl->type_constraint =
                        collect_->collect_concept_specialization_expression(
                            type_constraint->concept_decl,
                            type_constraint->concept_name,
                            std::move(concept_arguments),
                            type_constraint->location);
                    tentative.commit();
                    return param_decl;
                };

            if (auto constrained_param = try_parse_constrained_type_parameter()) {
                std::optional<TemplateArgument> default_argument;
                if (gentle_check(TokenType::ASSIGN)) {
                    if (constrained_param->is_parameter_pack) {
                        fail_cpp_unsupported(
                            "default template argument on template parameter pack",
                            current_token().loc);
                    }
                    advance();
                    default_argument =
                        parse_template_parameter_default_argument();
                }
                if (default_argument.has_value()) {
                    if (default_argument->kind != TemplateArgumentKind::Type) {
                        error_custloc(
                            "type template parameter default must be a type-id",
                            constrained_param->location);
                    }
                    set_template_parameter_default_argument(
                        constrained_param.get(),
                        std::move(default_argument));
                }
                if (!constrained_param->name.empty()) {
                    collect_->collect_declare_type_name_symbol(
                        constrained_param->name,
                        QualType(constrained_param->type),
                        constrained_param->location);
                }
                parameters.push_back(std::move(constrained_param));
                if (!active_template_parameter_stack_.empty()) {
                    active_template_parameter_stack_.back().push_back(
                        parameters.back().get());
                }
                if (!gentle_check_and_consume(TokenType::COMMA)) {
                    break;
                }
                continue;
            }
        }

        if (param_tok.type == TokenType::TEMPLATE) {
            advance();
            TemplateParameterList nested_parameters;
            {
                collect_->collect_enter_scope(ScopeFlags::TemplateParameterScope);
                struct NestedTemplateParameterScopeGuard {
                    Collect* collect = nullptr;
                    bool active = true;
                    ~NestedTemplateParameterScopeGuard() {
                        if (active && collect) {
                            collect->collect_leave_scope();
                        }
                    }
                } nested_scope_guard{collect_.get(), true};

                active_template_parameter_stack_.push_back({});
                struct NestedTemplateParameterStackGuard {
                    std::vector<std::vector<const TemplateParameterDecl*>>& stack;
                    bool active = true;
                    ~NestedTemplateParameterStackGuard() {
                        if (active) {
                            stack.pop_back();
                        }
                    }
                } nested_stack_guard{active_template_parameter_stack_, true};

                nested_parameters =
                    parse_cpp_template_parameter_list(depth + 1);
            }
            if (!(gentle_check(TokenType::TYPENAME) ||
                  gentle_check(TokenType::CLASS))) {
                error_custloc(
                    "expected 'class' or 'typename' after template parameter list",
                    current_token().loc);
            }

            bool uses_typename_keyword =
                current_token().type == TokenType::TYPENAME;
            Token kind_tok = current_token();
            advance();

            bool is_parameter_pack =
                gentle_check_and_consume(TokenType::ELLIPSIS);

            std::string param_name;
            SrcLoc param_loc = kind_tok.loc;
            if (gentle_check(TokenType::IDENTIFIER)) {
                param_name = current_token().value;
                param_loc = current_token().loc;
                advance();
                if (gentle_check_and_consume(TokenType::ELLIPSIS)) {
                    if (is_parameter_pack) {
                        error_custloc(
                            "duplicate ellipsis in template-template parameter pack",
                            current_token().loc);
                    }
                    is_parameter_pack = true;
                }
            }

            std::optional<TemplateArgument> default_argument;
            if (gentle_check(TokenType::ASSIGN)) {
                if (is_parameter_pack) {
                    fail_cpp_unsupported(
                        "default template argument on template-template parameter pack",
                        current_token().loc);
                }
                advance();
                default_argument =
                    parse_template_parameter_default_argument();
            }

            auto param_decl = make_ast<TemplateTemplateParmDecl>(
                *ast_ctx,
                std::move(nested_parameters),
                param_name,
                depth,
                static_cast<uint32_t>(parameters.size()),
                uses_typename_keyword,
                is_parameter_pack,
                param_loc);
            if (default_argument.has_value()) {
                if (default_argument->kind != TemplateArgumentKind::Template) {
                    error_custloc(
                        "template-template parameter default must be a template-name",
                        param_loc);
                }
                set_template_parameter_default_argument(
                    param_decl.get(),
                    std::move(default_argument));
            }
            if (!param_name.empty()) {
                collect_->collect_bind_template_decl(
                    param_name,
                    param_decl.get(),
                    LookupNamespace::Ordinary);
            }
            parameters.push_back(std::move(param_decl));
            if (!active_template_parameter_stack_.empty()) {
                active_template_parameter_stack_.back().push_back(
                    parameters.back().get());
            }
        } else if (param_tok.type == TokenType::TYPENAME &&
                   typename_starts_qualified_type_specifier()) {
            auto param_decl = parse_non_type_template_parameter(param_tok);
            parameters.push_back(std::move(param_decl));
            if (!active_template_parameter_stack_.empty()) {
                active_template_parameter_stack_.back().push_back(
                    parameters.back().get());
            }
        } else if (param_tok.type == TokenType::TYPENAME ||
            param_tok.type == TokenType::CLASS) {
            advance();

            bool is_parameter_pack =
                gentle_check_and_consume(TokenType::ELLIPSIS);

            std::string param_name;
            SrcLoc param_loc = param_tok.loc;
            if (gentle_check(TokenType::IDENTIFIER)) {
                param_name = current_token().value;
                param_loc = current_token().loc;
                advance();
                if (gentle_check(TokenType::ELLIPSIS)) {
                    fail_cpp_unsupported("template parameter pack", current_token().loc);
                }
            }

            std::optional<TemplateArgument> default_argument;
            if (gentle_check(TokenType::ASSIGN)) {
                if (is_parameter_pack) {
                    fail_cpp_unsupported(
                        "default template argument on template parameter pack",
                        current_token().loc);
                }
                advance();
                default_argument =
                    parse_template_parameter_default_argument();
            }

            auto param_type = std::make_shared<TemplateTypeParmType>(
                param_name,
                depth,
                static_cast<uint32_t>(parameters.size()),
                is_parameter_pack);
            auto param_decl = make_ast<TemplateTypeParmDecl>(
                *ast_ctx,
                param_name,
                depth,
                static_cast<uint32_t>(parameters.size()),
                param_type,
                is_parameter_pack,
                param_loc);
            param_type->parameter_decl = param_decl.get();
            if (default_argument.has_value()) {
                if (default_argument->kind != TemplateArgumentKind::Type) {
                    error_custloc(
                        "type template parameter default must be a type-id",
                        param_loc);
                }
                set_template_parameter_default_argument(
                    param_decl.get(),
                    std::move(default_argument));
            }
            if (!param_name.empty()) {
                collect_->collect_declare_type_name_symbol(
                    param_name,
                    QualType(param_type),
                    param_loc);
            }
            parameters.push_back(std::move(param_decl));
            if (!active_template_parameter_stack_.empty()) {
                active_template_parameter_stack_.back().push_back(
                    parameters.back().get());
            }
        } else {
            auto param_decl = parse_non_type_template_parameter(param_tok);
            parameters.push_back(std::move(param_decl));
            if (!active_template_parameter_stack_.empty()) {
                active_template_parameter_stack_.back().push_back(
                    parameters.back().get());
            }
        }

        if (!gentle_check_and_consume(TokenType::COMMA)) {
            break;
        }
    }

    check_and_consume(TokenType::GREATER_THAN);
    return parameters;
}

bool Parser::is_cpp_deduction_guide_declaration_start() {
    if (!is_cxx_mode_active() || is_parsing_cpp_record_body()) {
        return false;
    }

    size_t offset = 0;
    skip_attribute_specifier_sequence_for_lookahead(offset);
    if (peek_token_shortcut(offset).type == TokenType::EXPLICIT_KW) {
        ++offset;
        if (peek_token_shortcut(offset).type == TokenType::LEFT_PAREN &&
            !skip_balanced_tokens_for_lookahead(
                offset,
                TokenType::LEFT_PAREN,
                TokenType::RIGHT_PAREN)) {
            return false;
        }
        skip_attribute_specifier_sequence_for_lookahead(offset);
    }
    skip_attribute_specifier_sequence_for_lookahead(offset);

    if (peek_token_shortcut(offset).type != TokenType::IDENTIFIER ||
        peek_token_shortcut(offset + 1).type != TokenType::LEFT_PAREN) {
        return false;
    }
    offset += 1;
    if (!skip_balanced_tokens_for_lookahead(
            offset,
            TokenType::LEFT_PAREN,
            TokenType::RIGHT_PAREN)) {
        return false;
    }
    return peek_token_shortcut(offset).type == TokenType::ARROW;
}

bool Parser::cpp_template_parameter_lists_match_for_redeclaration(
    const TemplateParameterList& lhs,
    const TemplateParameterList& rhs) const {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.size(); ++idx) {
        const auto* lhs_param = lhs[idx].get();
        const auto* rhs_param = rhs[idx].get();
        if (!lhs_param || !rhs_param ||
            lhs_param->get_kind() != rhs_param->get_kind() ||
            lhs_param->is_parameter_pack != rhs_param->is_parameter_pack) {
            return false;
        }
        if (auto* lhs_non_type = dyn_cast<TemplateNonTypeParmDecl>(lhs_param)) {
            auto* rhs_non_type = dyn_cast<TemplateNonTypeParmDecl>(rhs_param);
            if (!rhs_non_type ||
                !cpp_out_of_line_type_matches(
                    lhs_non_type->type,
                    rhs_non_type->type,
                    false)) {
                return false;
            }
        }
    }
    return true;
}

bool Parser::cpp_template_decls_match_for_redeclaration(
    const TemplateDecl* existing,
    const TemplateDecl* current,
    const std::string* current_template_name) const {
    if (!existing || !current ||
        existing->get_kind() != current->get_kind() ||
        !cpp_template_parameter_lists_match_for_redeclaration(
            existing->parameters,
            current->parameters)) {
        return false;
    }

    if (auto* existing_function =
            dyn_cast<FunctionTemplateDecl>(const_cast<TemplateDecl*>(existing))) {
        auto* current_function =
            dyn_cast<FunctionTemplateDecl>(const_cast<TemplateDecl*>(current));
        return current_function &&
               cpp_out_of_line_type_matches(
                   QualType(existing_function->function_decl()->type),
                   QualType(current_function->function_decl()->type),
                   true);
    }
    if (auto* existing_variable =
            dyn_cast<VariableTemplateDecl>(const_cast<TemplateDecl*>(existing))) {
        auto* current_variable =
            dyn_cast<VariableTemplateDecl>(const_cast<TemplateDecl*>(current));
        return current_variable &&
               existing_variable->variable_decl() &&
               current_variable->variable_decl() &&
               cpp_out_of_line_type_matches(
                   existing_variable->variable_decl()->type,
                   current_variable->variable_decl()->type,
                   false);
    }
    if (auto* existing_class =
            dyn_cast<ClassTemplateDecl>(const_cast<TemplateDecl*>(existing))) {
        auto* current_class =
            dyn_cast<ClassTemplateDecl>(const_cast<TemplateDecl*>(current));
        auto* existing_record = dyn_cast<CppRecordDecl>(
            const_cast<Decl*>(existing_class->get_templated_decl()));
        auto* current_record = current_class
            ? dyn_cast<CppRecordDecl>(
                  const_cast<Decl*>(current_class->get_templated_decl()))
            : nullptr;
        const std::string* current_name =
            current_record ? &current_record->name : current_template_name;
        return current_class &&
               existing_record &&
               current_name &&
               !existing_record->name.empty() &&
               existing_record->name == *current_name;
    }
    if (auto* existing_alias =
            dyn_cast<AliasTemplateDecl>(const_cast<TemplateDecl*>(existing))) {
        auto* current_alias =
            dyn_cast<AliasTemplateDecl>(const_cast<TemplateDecl*>(current));
        return current_alias &&
               existing_alias->alias_decl() &&
               current_alias->alias_decl() &&
               cpp_out_of_line_type_matches(
                   existing_alias->alias_decl()->type,
                   current_alias->alias_decl()->type,
                   false);
    }
    return false;
}

const TemplateDecl* Parser::resolve_matching_primary_template_redeclaration(
    const std::string& template_name,
    LookupNamespace lookup_namespace,
    const TemplateDecl* current_template) const {
    if (!collect_ || template_name.empty() || !current_template) {
        return nullptr;
    }
    auto current_scope = collect_->collect_current_scope();
    while (current_scope &&
           scope_flags_contains(
               current_scope->flags,
               ScopeFlags::TemplateParameterScope)) {
        current_scope = current_scope->parent;
    }
    if (!current_scope) {
        return nullptr;
    }

    const DeclBinding* binding =
        LookupEngine::lookup_unqualified_template_binding(
            template_name,
            current_scope,
            false,
            lookup_namespace);
    if (!binding) {
        return nullptr;
    }

    std::vector<const Decl*> candidates;
    auto append_candidate = [&](const Decl* candidate) {
        if (!candidate) {
            return;
        }
        for (const auto* existing : candidates) {
            if (existing == candidate) {
                return;
            }
        }
        candidates.push_back(candidate);
    };
    append_candidate(binding->template_decl);
    for (const auto* candidate : binding->template_overload_candidates) {
        append_candidate(candidate);
    }

    auto to_template_decl = [](const Decl* decl) -> const TemplateDecl* {
        if (!decl) {
            return nullptr;
        }
        switch (decl->get_kind()) {
            case DeclKind::AliasTemplateDecl:
            case DeclKind::FunctionTemplateDecl:
            case DeclKind::VariableTemplateDecl:
            case DeclKind::ClassTemplateDecl:
            case DeclKind::VariableTemplatePartialSpecializationDecl:
            case DeclKind::ClassTemplatePartialSpecializationDecl:
                return static_cast<const TemplateDecl*>(decl);
            default:
                return nullptr;
        }
    };

    for (const auto* candidate : candidates) {
        const TemplateDecl* candidate_template = to_template_decl(candidate);
        if (!candidate_template) {
            continue;
        }
        if (candidate_template == current_template) {
            continue;
        }
        if (!cpp_template_decls_match_for_redeclaration(
                candidate_template,
                current_template,
                &template_name)) {
            continue;
        }
        const TemplateDecl* canonical =
            get_template_decl_canonical_decl(candidate_template);
        return canonical ? canonical : candidate_template;
    }
    return nullptr;
}

void Parser::set_primary_template_canonical_identity(
    TemplateDecl* template_decl,
    const std::string& template_name,
    LookupNamespace lookup_namespace) {
    if (!template_decl) {
        return;
    }
    const TemplateDecl* canonical_template =
        resolve_matching_primary_template_redeclaration(
            template_name,
            lookup_namespace,
            template_decl);
    if (!canonical_template) {
        canonical_template = template_decl;
    }
    set_template_decl_canonical_decl(template_decl, canonical_template);
}

void Parser::validate_template_default_argument_rules(
    const TemplateDecl* template_decl) {
    if (!template_decl) {
        return;
    }
    bool require_trailing_defaults =
        isa<ClassTemplateDecl>(template_decl) ||
        isa<AliasTemplateDecl>(template_decl) ||
        isa<VariableTemplateDecl>(template_decl);
    if (!require_trailing_defaults) {
        return;
    }

    bool saw_default_argument = false;
    for (const auto& parameter : template_decl->parameters) {
        if (!parameter) {
            continue;
        }
        bool has_default_argument =
            get_template_parameter_default_argument(parameter.get()) != nullptr;
        if (has_default_argument) {
            saw_default_argument = true;
            continue;
        }
        if (saw_default_argument && !parameter->is_parameter_pack) {
            error_custloc(
                "template parameter without a default argument follows parameter with a default argument",
                parameter->location);
        }
    }
}

namespace {

bool primary_template_decl_is_definition(const TemplateDecl* template_decl) {
    if (!template_decl) {
        return false;
    }
    if (auto* class_template =
            dyn_cast<ClassTemplateDecl>(const_cast<TemplateDecl*>(template_decl))) {
        return class_template->record_decl() &&
               class_template->record_decl()->is_definition;
    }
    if (auto* function_template =
            dyn_cast<FunctionTemplateDecl>(const_cast<TemplateDecl*>(template_decl))) {
        return function_template->function_decl() &&
               function_decl_defines_entity(function_template->function_decl());
    }
    if (auto* variable_template =
            dyn_cast<VariableTemplateDecl>(const_cast<TemplateDecl*>(template_decl))) {
        auto* variable = variable_template->variable_decl();
        return variable_template->is_pattern_complete &&
               variable &&
               (variable->init ||
                variable->storage_class != StorageClass::EXTERN);
    }
    if (auto* concept_decl =
            dyn_cast<ConceptDecl>(const_cast<TemplateDecl*>(template_decl))) {
        return concept_decl->constraint_expr != nullptr;
    }
    return false;
}

} // namespace

void Parser::finalize_primary_template_decl(
    TemplateDecl* template_decl,
    const std::string& template_name,
    LookupNamespace lookup_namespace) {
    if (!template_decl) {
        return;
    }
    validate_template_default_argument_rules(template_decl);
    set_primary_template_canonical_identity(
        template_decl,
        template_name,
        lookup_namespace);
    if (primary_template_decl_is_definition(template_decl)) {
        const TemplateDecl* canonical_template =
            get_template_decl_canonical_decl(template_decl);
        set_template_decl_definition_decl(
            canonical_template ? canonical_template : template_decl,
            template_decl);
    }

    size_t conflict_index = std::numeric_limits<size_t>::max();
    if (merge_template_decl_default_arguments(
            template_decl,
            &conflict_index)) {
        return;
    }

    SrcLoc conflict_loc = template_decl->location;
    if (conflict_index < template_decl->parameters.size()) {
        if (const auto* parameter =
                template_decl->parameters[conflict_index].get()) {
            conflict_loc = parameter->location;
        }
    }
    error_custloc(
        "redefinition of default template argument",
        conflict_loc);
}

void Parser::register_cpp_friend_function_template_decl(FriendDecl* friend_decl) {
    auto* function_template =
        friend_decl ? friend_decl->function_template_decl() : nullptr;
    auto* function_decl =
        function_template ? function_template->function_decl() : nullptr;
    if (!friend_decl || !function_template || !function_decl ||
        function_decl->name.empty() || !collect_) {
        return;
    }

    auto friend_scope = nearest_cpp_friend_namespace_scope();
    bool has_visible_matching_namespace_decl = false;
    const FunctionTemplateDecl* visible_canonical_template = nullptr;
    if (friend_scope) {
        if (const DeclBinding* binding =
                LookupEngine::lookup_unqualified_template_binding(
                    function_decl->name,
                    friend_scope,
                    false,
                    LookupNamespace::Ordinary)) {
            auto consider_candidate = [&](const Decl* candidate) {
                auto* candidate_template =
                    dyn_cast<FunctionTemplateDecl>(
                        const_cast<Decl*>(candidate));
                if (!candidate_template ||
                    candidate_template->is_hidden_friend ||
                    !cpp_template_decls_match_for_redeclaration(
                        candidate_template,
                        function_template)) {
                    return;
                }
                has_visible_matching_namespace_decl = true;
                const TemplateDecl* canonical =
                    get_template_decl_canonical_decl(candidate_template);
                visible_canonical_template =
                    dyn_cast<FunctionTemplateDecl>(
                        const_cast<TemplateDecl*>(
                            canonical ? canonical : candidate_template));
            };
            consider_candidate(binding->template_decl);
            for (const auto* candidate :
                 binding->template_overload_candidates) {
                consider_candidate(candidate);
            }
        }
    }

    function_template->is_hidden_friend =
        !has_visible_matching_namespace_decl;
    if (visible_canonical_template) {
        set_template_decl_canonical_decl(
            function_template,
            visible_canonical_template);
    }
    if (has_visible_matching_namespace_decl && friend_scope) {
        collect_->collect_bind_template_decl_in_scope(
            friend_scope,
            function_decl->name,
            function_template,
            LookupNamespace::Ordinary);
    }
}

VariableTemplateDecl*
Parser::try_publish_pending_primary_variable_template_pattern(
    const std::string& name,
    QualType declared_type,
    const std::shared_ptr<Symbol>& declared_sym,
    StorageClass storage_class,
    bool is_inline,
    bool is_constexpr,
    bool is_thread_local,
    bool is_block_byref,
    const std::optional<std::string>& asm_label,
    LanguageLinkage language_linkage,
    SrcLoc loc) {
    auto* pending = pending_primary_variable_template_pattern_;
    if (!pending || pending->consumed || pending->member_template_declaration ||
        !pending->parameters || pending->parameters->empty() ||
        name.empty() || !collect_ || !ast_ctx ||
        !is_in_template_pattern_context() ||
        is_parsing_cpp_explicit_specialization()) {
        return nullptr;
    }
    auto declaration_scope = collect_->collect_current_scope();
    while (declaration_scope &&
           scope_flags_contains(
               declaration_scope->flags,
               ScopeFlags::TemplateParameterScope)) {
        declaration_scope = declaration_scope->parent;
    }
    if (!declaration_scope ||
        (!scope_flags_contains(declaration_scope->flags, ScopeFlags::FileScope) &&
         !scope_flags_contains(
             declaration_scope->flags,
             ScopeFlags::NamespaceScope))) {
        return nullptr;
    }

    QualType shell_type = declared_sym ? declared_sym->type : declared_type;
    QualType shell_original_type =
        is_constexpr && declared_type ? declared_type.with_const()
                                      : declared_type;
    auto shell_decl = make_ast<VariableDecl>(
        *ast_ctx,
        shell_type,
        name,
        std::unique_ptr<Expr>{},
        declared_sym,
        storage_class,
        is_inline,
        loc);
    shell_decl->original_type = shell_original_type;
    shell_decl->is_constexpr = is_constexpr;
    shell_decl->is_thread_local = is_thread_local;
    shell_decl->is_block_byref = is_block_byref;
    shell_decl->set_language_linkage(language_linkage);
    if (asm_label.has_value()) {
        shell_decl->set_asm_label(*asm_label);
    }

    auto template_decl = make_ast<VariableTemplateDecl>(
        *ast_ctx,
        std::move(*pending->parameters),
        std::move(shell_decl),
        pending->template_loc);
    template_decl->is_pattern_complete = false;
    if (pending->leading_requires_clause) {
        template_decl->associated_constraint =
            std::move(*pending->leading_requires_clause);
    }
    set_primary_template_canonical_identity(
        template_decl.get(),
        name,
        LookupNamespace::Ordinary);
    collect_->collect_add_variable_template_decl(name, template_decl.get());

    pending->name = name;
    pending->consumed = true;
    pending->provisional_template = std::move(template_decl);
    return pending->provisional_template.get();
}

std::unique_ptr<CppDeductionGuideDecl>
Parser::parse_cpp_deduction_guide_declaration(
    TemplateParameterList template_parameters,
    std::unique_ptr<Expr> leading_requires_clause,
    SrcLoc template_loc) {
    SrcLoc guide_loc = current_token().loc;
    if (!lang_opts.is_cxx17_or_later()) {
        error_custloc(
            "class template argument deduction guides require C++17",
            guide_loc);
    }

    const bool enter_template_pattern_context = !template_parameters.empty();
    if (enter_template_pattern_context) {
        ++template_pattern_depth_;
    }
    struct DeductionGuideTemplatePatternGuard {
        uint32_t& depth;
        bool active = false;
        ~DeductionGuideTemplatePatternGuard() {
            if (active) {
                --depth;
            }
        }
    } template_pattern_guard{
        template_pattern_depth_,
        enter_template_pattern_context};

    auto guide_attrs = try_parse_attributes();
    CppExplicitSpecifier explicit_specifier =
        parse_cpp_optional_explicit_specifier();
    auto post_explicit_attrs = try_parse_attributes();
    guide_attrs.insert(
        guide_attrs.end(),
        std::make_move_iterator(post_explicit_attrs.begin()),
        std::make_move_iterator(post_explicit_attrs.end()));
    Token guide_name_tok = current_token();
    check_and_consume(TokenType::IDENTIFIER);

    std::shared_ptr<Scope> lookup_scope = collect_->collect_current_scope();
    while (lookup_scope &&
           scope_flags_contains(
               lookup_scope->flags,
               ScopeFlags::TemplateParameterScope)) {
        lookup_scope = lookup_scope->parent;
    }
    const DeclBinding* template_binding =
        LookupEngine::lookup_unqualified_template_binding(
            guide_name_tok.value,
            lookup_scope ? lookup_scope : collect_->collect_current_scope(),
            true,
            LookupNamespace::Tag);
    const Decl* primary_template_decl = nullptr;
    if (template_binding) {
        primary_template_decl = template_binding->template_decl;
        if (!primary_template_decl &&
            template_binding->template_overload_candidates.size() == 1) {
            primary_template_decl =
                template_binding->template_overload_candidates.front();
        }
    }
    auto* primary_class_template =
        dyn_cast<ClassTemplateDecl>(
            const_cast<Decl*>(primary_template_decl));
    if (!primary_class_template) {
        error_custloc(
            "deduction guide requires a prior class template '" +
                guide_name_tok.value + "'",
            guide_name_tok.loc);
    }
    if (const auto* canonical_template =
            get_template_decl_canonical_decl(primary_class_template)) {
        primary_class_template =
            const_cast<ClassTemplateDecl*>(
                dyn_cast<ClassTemplateDecl>(
                    const_cast<TemplateDecl*>(canonical_template)));
    }
    if (!primary_class_template) {
        error_custloc(
            "deduction guide primary template is not a class template",
            guide_name_tok.loc);
    }

    std::vector<std::unique_ptr<Decl>> guide_parameters;
    auto function_type = std::make_shared<FunctionType>();
    function_type->has_prototype = true;

    check_and_consume(TokenType::LEFT_PAREN);
    if (!gentle_check(TokenType::RIGHT_PAREN)) {
        while (true) {
            auto parameter = parse_parameter_declaration();
            auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
            if (!param_decl) {
                error_custloc(
                    "internal error: deduction guide parameter did not produce ParamDecl",
                    guide_name_tok.loc);
            }
            function_type->push_parameter(
                param_decl->type,
                param_decl->is_parameter_pack);
            guide_parameters.push_back(std::move(parameter));
            if (!gentle_check_and_consume(TokenType::COMMA)) {
                break;
            }
        }
    }
    check_and_consume(TokenType::RIGHT_PAREN);
    check_and_consume(TokenType::ARROW);

    auto return_type_specifier = try_parse_cpp_named_type_specifier();
    if (!return_type_specifier.has_value() || !return_type_specifier->type) {
        error_custloc(
            "deduction guide requires a class-template-id return type",
            current_token().loc);
    }
    function_type->ret_type = return_type_specifier->type;
    auto return_specialization =
        dyn_cast_shared<TemplateSpecializationType>(
            desugar_typedefs(function_type->ret_type).get_shared());
    auto* return_primary_template =
        return_specialization
            ? dyn_cast<ClassTemplateDecl>(
                  const_cast<Decl*>(return_specialization->primary_template))
            : nullptr;
    if (const auto* canonical_return_template =
            get_template_decl_canonical_decl(return_primary_template)) {
        return_primary_template =
            dyn_cast<ClassTemplateDecl>(
                const_cast<TemplateDecl*>(canonical_return_template));
    }
    if (!return_specialization ||
        return_specialization->is_class_template_placeholder ||
        return_primary_template != primary_class_template) {
        error_custloc(
            "deduction guide return type must name '" +
                guide_name_tok.value + "' with explicit template arguments",
            guide_name_tok.loc);
    }
    check_and_consume(TokenType::SEMICOLON);

    auto guide = make_ast<CppDeductionGuideDecl>(
        *ast_ctx,
        std::move(template_parameters),
        guide_name_tok.value,
        primary_class_template,
        std::move(guide_parameters),
        std::move(function_type),
        template_loc.isInvalid() ? guide_loc : template_loc);
    guide->associated_constraint = std::move(leading_requires_clause);
    guide->explicit_specifier = std::move(explicit_specifier);
    ast_ctx->append_attrs(guide->node_id, std::move(guide_attrs));
    set_template_decl_canonical_decl(guide.get(), guide.get());
    primary_class_template->add_deduction_guide(guide.get());
    return guide;
}

std::vector<std::unique_ptr<Decl>> Parser::parse_cpp_template_declaration() {
    Token template_tok = current_token();
    bool member_template_declaration = is_parsing_cpp_record_body();
    if (!can_parse_namespace_scope_template_declaration()) {
        if (!member_template_declaration) {
            fail_cpp_unsupported("block-scope template-declaration", template_tok.loc);
        }
    }
    if (!collect_) {
        error_custloc("internal error: missing collection state for template declaration",
                      template_tok.loc);
    }

    advance(); // consume 'template'

    const uint32_t parameter_depth = template_parameter_depth_;
    ++template_parameter_depth_;
    struct TemplateDepthGuard {
        uint32_t& depth;
        ~TemplateDepthGuard() { --depth; }
    } template_depth_guard{template_parameter_depth_};

    collect_->collect_enter_scope(ScopeFlags::TemplateParameterScope);
    struct ScopeLeaveGuard {
        Collect* collect = nullptr;
        bool active = true;
        ~ScopeLeaveGuard() {
            if (active && collect) {
                collect->collect_leave_scope();
            }
        }
    } template_scope_guard{collect_.get(), true};

    active_template_parameter_stack_.emplace_back();
    struct ActiveTemplateParameterGuard {
        std::vector<std::vector<const TemplateParameterDecl*>>* stack = nullptr;
        ~ActiveTemplateParameterGuard() {
            if (stack && !stack->empty()) {
                stack->pop_back();
            }
        }
    } active_template_parameter_guard{&active_template_parameter_stack_};

    auto parameters = parse_cpp_template_parameter_list(parameter_depth);
    std::unique_ptr<Expr> leading_requires_clause = nullptr;
    if (lang_opts.is_cxx20_or_later() &&
        gentle_check(TokenType::REQUIRES_KW)) {
        advance(); // 'requires'
        ++template_head_requires_clause_depth_;
        struct TemplateHeadRequiresParseGuard {
            uint32_t& depth;
            ~TemplateHeadRequiresParseGuard() { --depth; }
        } template_head_requires_guard{template_head_requires_clause_depth_};
        leading_requires_clause = parse_cpp_template_constraint_expression();
    }
    if (parameters.empty()) {
        collect_->collect_leave_scope();
        template_scope_guard.active = false;
        return parse_cpp_explicit_specialization_declaration(
            template_tok,
            member_template_declaration,
            true);
    }
    if (is_cpp_deduction_guide_declaration_start()) {
        std::vector<std::unique_ptr<Decl>> ret_vec;
        ret_vec.push_back(parse_cpp_deduction_guide_declaration(
            std::move(parameters),
            std::move(leading_requires_clause),
            template_tok.loc));
        return ret_vec;
    }

    // Class-template pattern parsing needs temporary template-parameter scope
    // state, but the accepted pattern's semantic owner and published pattern
    // semantics are durable and must survive the rollback below.
    collect_->collect_begin_session_isolation();
    struct SessionIsolationRollbackGuard {
        Collect* collect = nullptr;
        bool active = true;
        ~SessionIsolationRollbackGuard() {
            if (active && collect) {
                collect->collect_rollback_session_isolation();
            }
        }
    } collect_rollback_guard{collect_.get(), true};

    ++template_pattern_depth_;
    struct TemplatePatternGuard {
        uint32_t& depth;
        ~TemplatePatternGuard() { --depth; }
    } template_pattern_guard{template_pattern_depth_};

    std::vector<std::unique_ptr<Decl>> templated_decls;
    std::vector<TemplateArgument> record_specialization_arguments;
    bool record_has_specialization_argument_list = false;
    bool parsing_record_template_declaration =
        gentle_check(TokenType::CLASS) ||
        gentle_check(TokenType::STRUCT) ||
        gentle_check(TokenType::UNION);
    PendingPrimaryVariableTemplatePattern pending_variable_template_pattern;
    pending_variable_template_pattern.parameters = &parameters;
    pending_variable_template_pattern.leading_requires_clause =
        &leading_requires_clause;
    pending_variable_template_pattern.template_loc = template_tok.loc;
    pending_variable_template_pattern.member_template_declaration =
        member_template_declaration;
    std::unique_ptr<ClassTemplateDecl> provisional_class_template;
    const ClassTemplateDecl* provisional_class_template_ptr = nullptr;
    if (parsing_record_template_declaration) {
        provisional_class_template = make_ast<ClassTemplateDecl>(
            *ast_ctx,
            std::move(parameters),
            make_ast<NopDecl>(*ast_ctx, template_tok.loc),
            template_tok.loc);
        provisional_class_template_ptr = provisional_class_template.get();
    }
    auto member_template_constructor_name_offset = [&]() -> std::optional<size_t> {
        if (!member_template_declaration ||
            cxx_record_parse_stack_.empty() ||
            cxx_record_parse_stack_.back().kind == CppRecordKind::Union ||
            cxx_record_parse_stack_.back().name.empty()) {
            return std::nullopt;
        }
        auto skip_balanced_tokens =
            [&](size_t& offset,
                TokenType open_tok,
                TokenType close_tok) -> bool {
            if (peek_token_shortcut(offset).type != open_tok) {
                return false;
            }
            int depth = 0;
            while (peek_token_shortcut(offset).type != TokenType::Eof) {
                TokenType tok = peek_token_shortcut(offset).type;
                if (tok == open_tok) {
                    ++depth;
                } else if (tok == close_tok) {
                    --depth;
                    if (depth == 0) {
                        ++offset;
                        return true;
                    }
                }
                ++offset;
            }
            return false;
        };
        auto skip_gnu_attribute = [&](size_t& offset) -> bool {
            if (!is_gnu_attribute_token(peek_token_shortcut(offset))) {
                return false;
            }
            ++offset;
            if (peek_token_shortcut(offset).type == TokenType::LEFT_PAREN) {
                skip_balanced_tokens(
                    offset,
                    TokenType::LEFT_PAREN,
                    TokenType::RIGHT_PAREN);
            }
            return true;
        };
        auto skip_cxx_attribute = [&](size_t& offset) -> bool {
            if (peek_token_shortcut(offset).type != TokenType::LEFT_BRACKET ||
                peek_token_shortcut(offset + 1).type != TokenType::LEFT_BRACKET) {
                return false;
            }
            offset += 2;
            while (peek_token_shortcut(offset).type != TokenType::Eof) {
                if (peek_token_shortcut(offset).type == TokenType::RIGHT_BRACKET &&
                    peek_token_shortcut(offset + 1).type == TokenType::RIGHT_BRACKET) {
                    offset += 2;
                    return true;
                }
                ++offset;
            }
            return false;
        };
        size_t offset = 0;
        while (true) {
            Token tok = peek_token_shortcut(offset);
            if (tok.type == TokenType::EXPLICIT_KW) {
                ++offset;
                if (peek_token_shortcut(offset).type == TokenType::LEFT_PAREN) {
                    skip_balanced_tokens(
                        offset,
                        TokenType::LEFT_PAREN,
                        TokenType::RIGHT_PAREN);
                }
                continue;
            }
            if (tok.type == TokenType::CONSTEXPR_KW ||
                tok.type == TokenType::CONSTEVAL_KW ||
                tok.type == TokenType::INLINE) {
                ++offset;
                continue;
            }
            if (skip_gnu_attribute(offset) || skip_cxx_attribute(offset)) {
                continue;
            }
            if (tok.type == TokenType::ALIGNAS) {
                ++offset;
                if (peek_token_shortcut(offset).type == TokenType::LEFT_PAREN) {
                    skip_balanced_tokens(
                        offset,
                        TokenType::LEFT_PAREN,
                        TokenType::RIGHT_PAREN);
                }
                continue;
            }
            break;
        }
        const std::string& record_name = cxx_record_parse_stack_.back().name;
        Token ctor_name_tok = peek_token_shortcut(offset);
        if (ctor_name_tok.type == TokenType::IDENTIFIER &&
            ctor_name_tok.value == record_name &&
            peek_token_shortcut(offset + 1).type == TokenType::LEFT_PAREN) {
            return offset;
        }
        return std::nullopt;
    };
    struct AbbreviatedFunctionTemplateContextGuard {
        Parser* parser = nullptr;
        ActiveAbbreviatedFunctionTemplateContext context;
        ActiveAbbreviatedFunctionTemplateContext* previous = nullptr;

        AbbreviatedFunctionTemplateContextGuard(Parser* parser,
                                                TemplateParameterList* parameters,
                                                uint32_t parameter_depth)
            : parser(parser),
              context{parameters, parameter_depth},
              previous(parser
                           ? parser->active_abbreviated_function_template_context_
                           : nullptr) {
            if (parser) {
                parser->active_abbreviated_function_template_context_ =
                    &context;
            }
        }

        ~AbbreviatedFunctionTemplateContextGuard() {
            if (parser) {
                parser->active_abbreviated_function_template_context_ =
                    previous;
            }
        }
    };

    if (member_template_constructor_name_offset().has_value()) {
        AbbreviatedFunctionTemplateContextGuard abbreviated_context_guard{
            this,
            &parameters,
            parameter_depth};
        templated_decls.push_back(parse_cpp_constructor_member());
    } else if (gentle_check(TokenType::CLASS) ||
        gentle_check(TokenType::STRUCT) ||
        gentle_check(TokenType::UNION)) {
        auto record_decl =
            parse_cpp_record_specifier(
                &record_specialization_arguments,
                &record_has_specialization_argument_list,
                false,
                provisional_class_template_ptr);
        check_and_consume(TokenType::SEMICOLON);
        templated_decls.push_back(std::move(record_decl));
    } else if (lang_opts.is_cxx20_or_later() &&
               gentle_check(TokenType::CONCEPT_KW)) {
        if (member_template_declaration) {
            fail_cpp_unsupported("member concept declaration", current_token().loc);
        }
        advance(); // 'concept'
        Token name_tok = current_token();
        check_and_consume(TokenType::IDENTIFIER);
        check_and_consume(TokenType::ASSIGN);
        auto constraint_expr = parse_cpp_constraint_expression();
        check_and_consume(TokenType::SEMICOLON);
        templated_decls.push_back(make_ast<NopDecl>(*ast_ctx, template_tok.loc));
        auto concept_decl = make_ast<ConceptDecl>(
            *ast_ctx,
            std::move(parameters),
            name_tok.value,
            std::move(constraint_expr),
            template_tok.loc);
        concept_decl->associated_constraint = std::move(leading_requires_clause);
        // Delayed finalization below, once the shared template-redeclaration helpers
        // are in scope.
        templated_decls.front() = std::move(concept_decl);
    } else if (member_template_declaration &&
               gentle_check(TokenType::USING)) {
        templated_decls = parse_cpp_using_alias_declaration();
    } else if (member_template_declaration) {
        AbbreviatedFunctionTemplateContextGuard abbreviated_context_guard{
            this,
            &parameters,
            parameter_depth};
        templated_decls = parse_struct_declaration(false);
    } else {
        struct PendingVariableTemplatePatternGuard {
            PendingPrimaryVariableTemplatePattern*& slot;
            PendingPrimaryVariableTemplatePattern* previous = nullptr;
            ~PendingVariableTemplatePatternGuard() {
                slot = previous;
            }
        } pending_variable_template_guard{
            pending_primary_variable_template_pattern_,
            pending_primary_variable_template_pattern_
        };
        pending_primary_variable_template_pattern_ =
            &pending_variable_template_pattern;
        AbbreviatedFunctionTemplateContextGuard abbreviated_context_guard{
            this,
            &parameters,
            parameter_depth};
        templated_decls = parse_declaration();
    }

    std::unique_ptr<ClassTemplateDecl> prepared_class_template;
    std::unique_ptr<ClassTemplatePartialSpecializationDecl>
        prepared_class_partial_specialization;
    std::unique_ptr<VariableTemplateDecl> prepared_variable_template;
    std::unique_ptr<VariableTemplatePartialSpecializationDecl>
        prepared_variable_partial_specialization;
    std::string prepared_class_template_name;
    std::string prepared_variable_template_name;
    if (templated_decls.size() == 1 && templated_decls.front()) {
        if (auto* record_decl = dyn_cast<CppRecordDecl>(templated_decls.front().get())) {
            if (record_decl->name.empty()) {
                fail_cpp_unsupported("anonymous class template", record_decl->location);
            }
            prepared_class_template_name = record_decl->name;
            if (!record_has_specialization_argument_list) {
                if (provisional_class_template) {
                    provisional_class_template->templated_decl =
                        std::move(templated_decls.front());
                    prepared_class_template =
                        std::move(provisional_class_template);
                } else {
                    prepared_class_template = make_ast<ClassTemplateDecl>(
                        *ast_ctx,
                        std::move(parameters),
                        std::move(templated_decls.front()),
                        template_tok.loc);
                }
                if (!member_template_declaration) {
                    collect_->collect_add_class_template_decl(
                        prepared_class_template_name,
                        prepared_class_template.get());
                }
                prepare_cpp_template_pattern_record(*prepared_class_template);
            } else {
                const Decl* primary_template = nullptr;
                if (member_template_declaration) {
                    QualType owner_lookup_type =
                        collect_->collect_current_cpp_record_lookup_type();
                    if (!owner_lookup_type &&
                        !cxx_record_parse_stack_.empty() &&
                        cxx_record_parse_stack_.back().semantic_owner) {
                        owner_lookup_type = QualType(
                            cxx_record_parse_stack_.back()
                                .semantic_owner
                                ->get_record_type());
                    }
                    const auto* nested_template =
                        collect_->collect_lookup_record_nested_template(
                            owner_lookup_type,
                            prepared_class_template_name);
                    if (nested_template &&
                        nested_template->kind ==
                            RecordSemanticState::NestedTemplateKind::Class) {
                        primary_template = nested_template->decl;
                    }
                } else {
                    auto lookup_scope = collect_->collect_current_scope();
                    while (lookup_scope &&
                           scope_flags_contains(
                               lookup_scope->flags,
                               ScopeFlags::TemplateParameterScope)) {
                        lookup_scope = lookup_scope->parent;
                    }
                    const DeclBinding* template_binding =
                        LookupEngine::lookup_unqualified_template_binding(
                            prepared_class_template_name,
                            lookup_scope ? lookup_scope : collect_->collect_current_scope(),
                            true,
                            LookupNamespace::Tag);
                    if (template_binding) {
                        primary_template = template_binding->template_decl;
                        if (!primary_template &&
                            template_binding->template_overload_candidates.size() == 1) {
                            primary_template =
                                template_binding->template_overload_candidates.front();
                        }
                    }
                }
                auto* primary_class_template =
                    dyn_cast<ClassTemplateDecl>(primary_template);
                if (!primary_class_template) {
                    error_custloc(
                        "class template partial specialization requires a prior primary template '" +
                            prepared_class_template_name + "'",
                        record_decl->location);
                }
                primary_class_template =
                    canonical_primary_template_for_partial_registration(
                        primary_class_template);
                prepared_class_partial_specialization =
                    make_ast<ClassTemplatePartialSpecializationDecl>(
                        *ast_ctx,
                        primary_class_template,
                        provisional_class_template
                            ? std::move(provisional_class_template->parameters)
                            : std::move(parameters),
                        std::move(record_specialization_arguments),
                        std::move(templated_decls.front()),
                        template_tok.loc);
                const_cast<ClassTemplateDecl*>(primary_class_template)
                    ->add_partial_specialization(
                    prepared_class_partial_specialization.get());
                prepare_cpp_template_pattern_record(
                    *prepared_class_partial_specialization);
            }
        } else if (auto* variable_decl =
                       dyn_cast<VariableDecl>(templated_decls.front().get())) {
            if (variable_decl->has_explicit_specialization_argument_list) {
                if (member_template_declaration) {
                    fail_cpp_unsupported(
                        "member variable template partial specialization",
                        variable_decl->location);
                }
                prepared_variable_template_name = variable_decl->name;
                auto lookup_scope = collect_->collect_current_scope();
                while (lookup_scope &&
                       scope_flags_contains(
                           lookup_scope->flags,
                           ScopeFlags::TemplateParameterScope)) {
                    lookup_scope = lookup_scope->parent;
                }
                const DeclBinding* template_binding =
                    LookupEngine::lookup_unqualified_template_binding(
                        prepared_variable_template_name,
                        lookup_scope ? lookup_scope : collect_->collect_current_scope(),
                        true,
                        LookupNamespace::Ordinary);
                const Decl* primary_template = nullptr;
                if (template_binding) {
                    primary_template = template_binding->template_decl;
                    if (!primary_template &&
                        template_binding->template_overload_candidates.size() == 1) {
                        primary_template =
                            template_binding->template_overload_candidates.front();
                    }
                }
                auto* primary_variable_template =
                    dyn_cast<VariableTemplateDecl>(primary_template);
                if (!primary_variable_template) {
                    error_custloc(
                        "variable template partial specialization requires a prior primary template '" +
                            prepared_variable_template_name + "'",
                        variable_decl->location);
                }
                primary_variable_template =
                    canonical_primary_template_for_partial_registration(
                        primary_variable_template);
                auto specialization_arguments =
                    std::move(variable_decl->explicit_specialization_arguments);
                variable_decl->explicit_specialization_arguments.clear();
                variable_decl->has_explicit_specialization_argument_list = false;
                prepared_variable_partial_specialization =
                    make_ast<VariableTemplatePartialSpecializationDecl>(
                        *ast_ctx,
                        primary_variable_template,
                        std::move(parameters),
                        std::move(specialization_arguments),
                        std::move(templated_decls.front()),
                        template_tok.loc);
                const_cast<VariableTemplateDecl*>(primary_variable_template)
                    ->add_partial_specialization(
                        prepared_variable_partial_specialization.get());
            } else if (pending_variable_template_pattern.consumed &&
                       pending_variable_template_pattern.provisional_template) {
                prepared_variable_template_name = variable_decl->name;
                if (prepared_variable_template_name !=
                    pending_variable_template_pattern.name) {
                    error_custloc(
                        "internal error: variable template provisional binding name mismatch",
                        variable_decl->location);
                }
                pending_variable_template_pattern.provisional_template
                    ->templated_decl = std::move(templated_decls.front());
                pending_variable_template_pattern.provisional_template
                    ->is_pattern_complete = true;
                prepared_variable_template =
                    std::move(
                        pending_variable_template_pattern.provisional_template);
            }
        }
    }

    collect_->collect_rollback_session_isolation();
    collect_rollback_guard.active = false;
    collect_->collect_leave_scope();
    template_scope_guard.active = false;

    if (!prepared_class_template &&
        !prepared_class_partial_specialization &&
        !prepared_variable_template &&
        !prepared_variable_partial_specialization &&
        (templated_decls.size() != 1 || !templated_decls.front())) {
        fail_cpp_unsupported("template-declaration form", template_tok.loc);
    }

    if (!prepared_class_template &&
        !prepared_class_partial_specialization &&
        !prepared_variable_template &&
        !prepared_variable_partial_specialization &&
        templated_decls.size() == 1 &&
        templated_decls.front()->get_kind() == DeclKind::NopDecl) {
        return templated_decls;
    }

    std::vector<std::unique_ptr<Decl>> wrapped_decls;
    if (prepared_class_template) {
        prepared_class_template->associated_constraint =
            std::move(leading_requires_clause);
        finalize_primary_template_decl(
            prepared_class_template.get(),
            prepared_class_template_name,
            LookupNamespace::Tag);
        if (!member_template_declaration) {
            collect_->collect_add_class_template_decl(
                prepared_class_template_name,
                prepared_class_template.get());
        }
        wrapped_decls.push_back(std::move(prepared_class_template));
        return wrapped_decls;
    }
    if (prepared_class_partial_specialization) {
        prepared_class_partial_specialization->associated_constraint =
            std::move(leading_requires_clause);
        wrapped_decls.push_back(std::move(prepared_class_partial_specialization));
        return wrapped_decls;
    }
    if (prepared_variable_template) {
        finalize_primary_template_decl(
            prepared_variable_template.get(),
            prepared_variable_template_name,
            LookupNamespace::Ordinary);
        collect_->collect_add_variable_template_decl(
            prepared_variable_template_name,
            prepared_variable_template.get());
        wrapped_decls.push_back(std::move(prepared_variable_template));
        return wrapped_decls;
    }
    if (prepared_variable_partial_specialization) {
        prepared_variable_partial_specialization->associated_constraint =
            std::move(leading_requires_clause);
        wrapped_decls.push_back(
            std::move(prepared_variable_partial_specialization));
        return wrapped_decls;
    }
    if (templated_decls.size() == 1 &&
        templated_decls.front() &&
        isa<ConceptDecl>(templated_decls.front().get())) {
        auto* concept_decl =
            static_cast<ConceptDecl*>(templated_decls.front().get());
        finalize_primary_template_decl(
            concept_decl,
            concept_decl->name,
            LookupNamespace::Ordinary);
        collect_->collect_add_concept_decl(concept_decl->name, concept_decl);
        wrapped_decls.push_back(std::move(templated_decls.front()));
        return wrapped_decls;
    }

    if (auto* friend_decl =
            dyn_cast<FriendDecl>(templated_decls.front().get())) {
        if (friend_decl->get_friend_kind() == CppFriendKind::Type) {
            const ClassTemplateDecl* friend_class_template =
                canonical_class_template_decl(friend_decl->friend_class_template);
            if (!friend_class_template) {
                friend_class_template = class_template_decl_from_friend_type(
                    friend_decl->friend_type,
                    ast_ctx.get());
            }
            if (!friend_class_template) {
                fail_cpp_unsupported(
                    "friend class template declaration without a class template target",
                    friend_decl->location);
            }
            if (!template_template_parameter_lists_are_compatible(
                    friend_class_template->parameters,
                    parameters)) {
                error_custloc(
                    "friend class template parameter list is not compatible with the target template",
                    friend_decl->location);
            }
            friend_decl->friend_class_template = friend_class_template;
            wrapped_decls.push_back(std::move(templated_decls.front()));
            return wrapped_decls;
        }
        auto* function_decl = friend_decl->function_decl();
        if (!function_decl) {
            fail_cpp_unsupported(
                "friend template declaration form",
                friend_decl->location);
        }
        if (isa<CppDestructorDecl>(function_decl)) {
            error_custloc(
                "destructor cannot be a template",
                function_decl->location);
        }
        if (function_decl->name.empty()) {
            fail_cpp_unsupported(
                "unnamed friend function template",
                function_decl->location);
        }

        std::string template_name = function_decl->name;
        auto function_pattern = std::move(friend_decl->target_decl);
        auto template_decl = make_ast<FunctionTemplateDecl>(
            *ast_ctx,
            std::move(parameters),
            std::move(function_pattern),
            template_tok.loc);
        template_decl->associated_constraint =
            std::move(leading_requires_clause);
        finalize_primary_template_decl(
            template_decl.get(),
            template_name,
            LookupNamespace::Ordinary);
        friend_decl->target_decl = std::move(template_decl);
        friend_decl->function_symbol.reset();
        register_cpp_friend_function_template_decl(friend_decl);
        wrapped_decls.push_back(std::move(templated_decls.front()));
        return wrapped_decls;
    }

    if (auto* function_decl = dyn_cast<FuncDecl>(templated_decls.front().get())) {
        if (isa<CppDestructorDecl>(function_decl)) {
            error_custloc(
                "destructor cannot be a template",
                function_decl->location);
        }
        if (function_decl->name.empty()) {
            fail_cpp_unsupported("unnamed function template", function_decl->location);
        }
        std::string template_name = function_decl->name;
        auto template_decl = make_ast<FunctionTemplateDecl>(
            *ast_ctx,
            std::move(parameters),
            std::move(templated_decls.front()),
            template_tok.loc);
        template_decl->associated_constraint = std::move(leading_requires_clause);
        finalize_primary_template_decl(
            template_decl.get(),
            template_name,
            LookupNamespace::Ordinary);
        if (!member_template_declaration) {
            collect_->collect_add_function_template_decl(
                template_name,
                template_decl.get());
        }
        wrapped_decls.push_back(std::move(template_decl));
        return wrapped_decls;
    }

    if (lang_opts.is_cxx20_or_later() &&
        gentle_check(TokenType::CONCEPT_KW)) {
        if (member_template_declaration) {
            fail_cpp_unsupported("member concept declaration", current_token().loc);
        }
        advance(); // 'concept'
        Token name_tok = current_token();
        check_and_consume(TokenType::IDENTIFIER);
        check_and_consume(TokenType::ASSIGN);
        auto constraint_expr = parse_cpp_constraint_expression();
        check_and_consume(TokenType::SEMICOLON);
        auto concept_decl = make_ast<ConceptDecl>(
            *ast_ctx,
            std::move(parameters),
            name_tok.value,
            std::move(constraint_expr),
            template_tok.loc);
        concept_decl->associated_constraint = std::move(leading_requires_clause);
        finalize_primary_template_decl(
            concept_decl.get(),
            name_tok.value,
            LookupNamespace::Ordinary);
        collect_->collect_add_concept_decl(name_tok.value, concept_decl.get());
        wrapped_decls.push_back(std::move(concept_decl));
        return wrapped_decls;
    }

    if (templated_decls.front()->get_kind() == DeclKind::TypedefDecl) {
        auto* alias_decl =
            static_cast<TypedefDecl*>(templated_decls.front().get());
        if (alias_decl->name.empty()) {
            fail_cpp_unsupported(
                "unnamed alias template",
                templated_decls.front()->location);
        }
        std::string template_name = alias_decl->name;
        auto template_decl = make_ast<AliasTemplateDecl>(
            *ast_ctx,
            std::move(parameters),
            std::move(templated_decls.front()),
            template_tok.loc);
        template_decl->associated_constraint = std::move(leading_requires_clause);
        finalize_primary_template_decl(
            template_decl.get(),
            template_name,
            LookupNamespace::Ordinary);
        if (!member_template_declaration) {
            collect_->collect_add_alias_template_decl(
                template_name,
                template_decl.get());
        }
        wrapped_decls.push_back(std::move(template_decl));
        return wrapped_decls;
    }
    if (templated_decls.front()->get_kind() == DeclKind::VariableDecl) {
        if (member_template_declaration) {
            fail_cpp_unsupported(
                "member variable template",
                templated_decls.front()->location);
        }
        auto* variable_decl =
            static_cast<VariableDecl*>(templated_decls.front().get());
        if (variable_decl->name.empty()) {
            fail_cpp_unsupported(
                "unnamed variable template",
                templated_decls.front()->location);
        }
        std::string template_name = variable_decl->name;
        auto template_decl = make_ast<VariableTemplateDecl>(
            *ast_ctx,
            std::move(parameters),
            std::move(templated_decls.front()),
            template_tok.loc);
        template_decl->associated_constraint = std::move(leading_requires_clause);
        finalize_primary_template_decl(
            template_decl.get(),
            template_name,
            LookupNamespace::Ordinary);
        collect_->collect_add_variable_template_decl(
            template_name,
            template_decl.get());
        wrapped_decls.push_back(std::move(template_decl));
        return wrapped_decls;
    }
    fail_cpp_unsupported("template-declaration form", templated_decls.front()->location);
    return wrapped_decls;
}

std::unique_ptr<Expr> Parser::parse_cpp_constraint_primary_expression() {
    if (gentle_check(TokenType::REQUIRES_KW)) {
        return parse_cpp_requires_expression();
    }
    return parse_primary_expression();
}

std::unique_ptr<Expr> Parser::parse_cpp_constraint_logical_or_expression() {
    return parse_conditional_expression();
}

std::unique_ptr<Expr> Parser::parse_cpp_constraint_expression() {
    return parse_cpp_constraint_logical_or_expression();
}

std::unique_ptr<Expr> Parser::parse_cpp_template_constraint_expression() {
    ++template_pattern_depth_;
    struct TemplateConstraintPatternGuard {
        uint32_t& depth;
        ~TemplateConstraintPatternGuard() { --depth; }
    } template_constraint_pattern_guard{template_pattern_depth_};

    return parse_cpp_constraint_expression();
}

std::unique_ptr<Expr> Parser::parse_cpp_requires_expression() {
    if (!is_cxx_mode_active() || !lang_opts.is_cxx20_or_later() ||
        !gentle_check(TokenType::REQUIRES_KW)) {
        return nullptr;
    }

    Token requires_tok = current_token();
    advance(); // 'requires'

    std::vector<std::unique_ptr<ParamDecl>> parameters;
    std::vector<ConstraintRequirement> requirements;

    bool entered_scope = false;
    if (gentle_check(TokenType::LEFT_PAREN)) {
        advance();
        collect_->collect_enter_scope(ScopeFlags::BlockScope);
        entered_scope = true;
        if (!gentle_check(TokenType::RIGHT_PAREN)) {
            while (true) {
                DeclarationParser param_parser(this);
                param_parser.in_function_parameter = true;
                auto param_base_type = param_parser.parse_declaration();
                if (!param_base_type) {
                    error_custloc(
                        "invalid requires-expression parameter declaration",
                        current_token().loc);
                }
                QualType parameter_type(param_base_type, param_parser.qualifiers);
                parameter_type =
                    collect_->collect_try_realize_deferred_semantic_type(
                        parameter_type);
                std::shared_ptr<Symbol> parameter_symbol = nullptr;
                if (!param_parser.name.empty()) {
                    parameter_symbol = collect_->collect_declare_variable_symbol(
                        param_parser.name,
                        parameter_type,
                        StorageClass::NONE,
                        false,
                        false,
                        param_parser.loc.isInvalid()
                            ? requires_tok.loc
                            : param_parser.loc);
                }
                auto parameter_decl = make_ast<ParamDecl>(
                    *ast_ctx,
                    parameter_type,
                    param_parser.name,
                    parameter_symbol,
                    StorageClass::NONE,
                    param_parser.loc.isInvalid()
                        ? requires_tok.loc
                        : param_parser.loc);
                parameters.push_back(std::move(parameter_decl));
                if (!gentle_check_and_consume(TokenType::COMMA)) {
                    break;
                }
            }
        }
        check_and_consume(TokenType::RIGHT_PAREN);
    }

    struct ScopeGuard {
        Collect* collect = nullptr;
        bool active = false;
        ~ScopeGuard() {
            if (active && collect) {
                collect->collect_leave_scope();
            }
        }
    } scope_guard{collect_.get(), entered_scope};

    check_and_consume(TokenType::LEFT_BRACE);
    while (!gentle_check(TokenType::RIGHT_BRACE) &&
           !gentle_check(TokenType::Eof)) {
        ConstraintRequirement requirement;
        requirement.location = current_token().loc;

        if (gentle_check(TokenType::TYPENAME)) {
            requirement.kind = ConstraintRequirementKind::Type;
            auto parsed_type = try_parse_cpp_named_type_specifier(
                CppTypeNameParseContext::TypeRequirement);
            if (!parsed_type) {
                error_custloc(
                    "expected type name in type requirement",
                    current_token().loc);
            }
            requirement.type_requirement = parsed_type->type;
            check_and_consume(TokenType::SEMICOLON);
        } else if (gentle_check(TokenType::REQUIRES_KW)) {
            requirement.kind = ConstraintRequirementKind::Nested;
            advance(); // nested 'requires'
            requirement.expr = parse_cpp_constraint_expression();
            check_and_consume(TokenType::SEMICOLON);
        } else if (gentle_check(TokenType::LEFT_BRACE)) {
            requirement.kind = ConstraintRequirementKind::Compound;
            advance();
            requirement.expr = parse_expression();
            check_and_consume(TokenType::RIGHT_BRACE);
            if (gentle_check(TokenType::NOEXCEPT_KW)) {
                requirement.is_noexcept = true;
                advance();
            }
            if (gentle_check_and_consume(TokenType::ARROW)) {
                requirement.return_type_constraint = parse_cpp_type_constraint();
            }
            check_and_consume(TokenType::SEMICOLON);
        } else {
            requirement.kind = ConstraintRequirementKind::Simple;
            requirement.expr = parse_expression();
            check_and_consume(TokenType::SEMICOLON);
        }
        requirements.push_back(std::move(requirement));
    }
    check_and_consume(TokenType::RIGHT_BRACE);
    return collect_->collect_requires_expression(
        std::move(parameters),
        std::move(requirements),
        requires_tok.loc);
}

bool Parser::is_cpp_qualified_id_start() {
    if (!is_cxx_mode_active()) {
        return false;
    }
    RevertingTentativeParsingAction tentative(*this);
    try {
        if (gentle_check(TokenType::DECLTYPE_KW)) {
            if (!try_consume_cpp_decltype_specifier_for_lookahead()) {
                return false;
            }
            return is_cpp_scope_resolution_here();
        }
        bool has_global_qualifier = consume_cpp_scope_resolution();
        if (!gentle_check(TokenType::IDENTIFIER) &&
            !(has_global_qualifier && gentle_check(TokenType::OPERATOR_KW))) {
            return false;
        }
        if (gentle_check(TokenType::OPERATOR_KW)) {
            return has_global_qualifier;
        }
        advance();
        if (gentle_check(TokenType::LESS_THAN)) {
            RevertingTentativeParsingAction template_args(*this);
            parse_cpp_template_argument_list();
            if (is_cpp_scope_resolution_here()) {
                template_args.commit();
            }
        }
        return has_global_qualifier || is_cpp_scope_resolution_here();
    } catch (const ParseError&) {
        return false;
    }
}

std::shared_ptr<Scope> Parser::resolve_named_namespace_scope(
    const DeclContext* start_context,
    const std::string& namespace_name,
    bool allow_enclosing_lookup) const {
    return qualified_name_utils::resolve_named_namespace_scope(
        start_context,
        namespace_name,
        allow_enclosing_lookup);
}

std::vector<std::unique_ptr<Decl>> Parser::parse_cpp_namespace_definition() {
    std::vector<std::unique_ptr<Decl>> parsed_decls;
    if (!is_cxx_mode_active()) {
        return parsed_decls;
    }

    bool leading_inline_namespace = false;
    if (gentle_check(TokenType::INLINE)) {
        if (peek_token().type != TokenType::NAMESPACE) {
            return parsed_decls;
        }
        leading_inline_namespace = true;
        advance(); // consume inline
    }
    if (!gentle_check(TokenType::NAMESPACE)) {
        return parsed_decls;
    }

    SrcLoc namespace_loc = current_token().loc;
    if (!collect_->collect_is_file_scope()) {
        error_custloc("namespace definition is only allowed at namespace scope",
                      namespace_loc);
    }
    advance(); // consume namespace

    std::vector<ParsedAttribute> namespace_head_attrs = try_parse_attributes();

    struct NamespacePathComponent {
        std::string name;
        SrcLoc loc;
        bool is_inline = false;
    };

    std::vector<NamespacePathComponent> namespace_path;
    bool is_anonymous_namespace = false;
    if (gentle_check(TokenType::IDENTIFIER)) {
        namespace_path.push_back(
            NamespacePathComponent{
                current_token().value,
                current_token().loc,
                leading_inline_namespace});
        advance();
        while (is_cpp_scope_resolution_here()) {
            if (namespace_path.back().is_inline) {
                error_custloc(
                    "inline namespace specifier is only allowed on the final component of a nested namespace definition",
                    namespace_path.back().loc);
            }
            consume_cpp_scope_resolution();
            bool component_is_inline = false;
            if (gentle_check(TokenType::INLINE)) {
                component_is_inline = true;
                advance();
            }
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected namespace name after '::' in namespace definition",
                    current_token().loc);
            }
            namespace_path.push_back(
                NamespacePathComponent{
                    current_token().value,
                    current_token().loc,
                    component_is_inline});
            advance();
        }
    } else if (gentle_check(TokenType::LEFT_BRACE)) {
        if (leading_inline_namespace) {
            error_custloc(
                "expected namespace name after 'inline'",
                namespace_loc);
        }
        is_anonymous_namespace = true;
    } else {
        if (leading_inline_namespace) {
            error_custloc("expected namespace name after 'inline'",
                          current_token().loc);
        }
        error_custloc("expected namespace name or '{' after 'namespace'",
                      current_token().loc);
    }

    auto current_scope = collect_->collect_current_scope();
    auto current_context = collect_->get_current_decl_context();
    auto translation_unit_context = collect_->get_translation_unit_decl_context();
    if (!current_scope || !current_context || !translation_unit_context) {
        error_custloc("internal error: missing namespace scope context",
                      namespace_loc);
    }
    auto global_scope = current_scope;
    while (global_scope && global_scope->parent) {
        global_scope = global_scope->parent;
    }
    if (!global_scope) {
        error_custloc("internal error: global namespace scope missing",
                      namespace_loc);
    }

    struct NamespaceDeclBuildInfo {
        std::string name;
        SrcLoc loc;
        DeclContext* semantic_context = nullptr;
        bool is_anonymous = false;
        bool is_inline = false;
        std::vector<ParsedAttribute> attrs;
    };
    std::vector<NamespaceDeclBuildInfo> namespace_decl_infos;

    if (gentle_check(TokenType::ASSIGN)) {
        if (is_anonymous_namespace || namespace_path.empty()) {
            error_custloc(
                "namespace alias definition requires an identifier before '='",
                namespace_loc);
        }
        if (namespace_path.size() != 1) {
            error_custloc(
                "namespace alias name must be a single identifier",
                namespace_loc);
        }

        for (const auto& component : namespace_path) {
            if (component.is_inline) {
                error_custloc(
                    "namespace alias definition cannot declare an inline namespace",
                    component.loc);
            }
        }

        const std::string& alias_name = namespace_path.front().name;
        if (current_context->lookup_local(alias_name, LookupNamespace::Ordinary) ||
            current_context->lookup_local(alias_name, LookupNamespace::Tag)) {
            error_custloc(
                "redefinition of '" + alias_name + "' as namespace alias",
                namespace_loc);
        }
        if (current_context->lookup_local_namespace(alias_name)) {
            error_custloc(
                "redefinition of '" + alias_name + "' as namespace alias",
                namespace_loc);
        }
        const auto* existing_alias =
            current_context->lookup_local_namespace_alias(alias_name);

        advance(); // consume '='

        bool rhs_has_global_qualifier = false;
        if (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            rhs_has_global_qualifier = true;
        }

        if (!gentle_check(TokenType::IDENTIFIER)) {
            error_custloc("expected namespace name in namespace alias definition",
                          current_token().loc);
        }

        std::vector<std::string> rhs_components;
        SrcLoc rhs_loc = current_token().loc;
        rhs_components.push_back(current_token().value);
        advance();
        while (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected namespace name after '::' in namespace alias definition",
                    current_token().loc);
            }
            rhs_components.push_back(current_token().value);
            advance();
        }

        check_and_consume(TokenType::SEMICOLON);

        const DeclContext* lookup_context =
            rhs_has_global_qualifier ? translation_unit_context.get()
                                     : current_context.get();
        std::shared_ptr<Scope> target_scope = nullptr;
        std::shared_ptr<DeclContext> target_context = nullptr;

        auto format_rhs_prefix = [&](size_t upto_index) {
            std::string formatted;
            if (rhs_has_global_qualifier) {
                formatted += "::";
            }
            for (size_t idx = 0; idx <= upto_index; ++idx) {
                if (idx > 0) {
                    formatted += "::";
                }
                formatted += rhs_components[idx];
            }
            return formatted;
        };

        for (size_t idx = 0; idx < rhs_components.size(); ++idx) {
            bool allow_enclosing_lookup =
                (!rhs_has_global_qualifier && idx == 0);
            auto namespace_scope = resolve_named_namespace_scope(
                lookup_context, rhs_components[idx], allow_enclosing_lookup);
            if (!namespace_scope || !namespace_scope->associated_decl_context) {
                error_custloc(
                    "namespace alias target '" + format_rhs_prefix(idx) +
                        "' does not name a namespace",
                    rhs_loc);
            }
            target_scope = namespace_scope;
            target_context =
                namespace_scope->associated_decl_context
                    ? namespace_scope->associated_decl_context->shared_from_this()
                    : nullptr;
            lookup_context = namespace_scope->associated_decl_context;
        }

        if (!target_scope || !target_context) {
            error_custloc("namespace alias target does not name a namespace",
                          rhs_loc);
        }

        if (existing_alias) {
            if (existing_alias->target_scope.get() != target_scope.get()) {
                error_custloc(
                    "redefinition of '" + alias_name +
                        "' as an alias for a different namespace",
                    namespace_loc);
            }
            std::vector<std::unique_ptr<Decl>> redecl_noop;
            redecl_noop.push_back(
                collect_->collect_nop_declaration(namespace_loc));
            return redecl_noop;
        }

        collect_->collect_register_namespace_alias(
            current_context,
            NamespaceBindingEntry{
                alias_name,
                target_context,
                target_scope});
        std::vector<std::unique_ptr<Decl>> alias_noop;
        alias_noop.push_back(collect_->collect_nop_declaration(namespace_loc));
        return alias_noop;
    }

    if (!is_anonymous_namespace && !namespace_path.empty()) {
        auto parent_context = collect_->get_current_decl_context();
        const std::string& outer_name = namespace_path.front().name;
        if (parent_context && parent_context->lookup_local_namespace_alias(outer_name)) {
            error_custloc(
                "redefinition of '" + outer_name + "' as namespace",
                namespace_loc);
        }
        if (parent_context &&
            (parent_context->lookup_local(outer_name, LookupNamespace::Ordinary) ||
             parent_context->lookup_local(outer_name, LookupNamespace::Tag))) {
            error_custloc(
                "redefinition of '" + outer_name + "' as namespace",
                namespace_loc);
        }
    }

    check_and_consume(TokenType::LEFT_BRACE);

    size_t entered_namespace_depth = 0;
    auto leave_entered_namespaces = [&]() {
        while (entered_namespace_depth > 0) {
            collect_->collect_leave_scope();
            --entered_namespace_depth;
        }
    };

    auto namespace_scope_flags = ScopeFlags::FileScope | ScopeFlags::NamespaceScope;
    auto enter_named_namespace = [&](const NamespacePathComponent& component) {
        const std::string& name = component.name;
        auto parent_scope = collect_->collect_current_scope();
        auto parent_context = collect_->get_current_decl_context();
        if (!parent_scope || !parent_context) {
            error_custloc("internal error: missing parent namespace context",
                          namespace_loc);
        }

        auto canonical_parent_context = parent_context;
        if (canonical_parent_context->primary_context() &&
            canonical_parent_context->primary_context() !=
                canonical_parent_context.get()) {
            canonical_parent_context =
                canonical_parent_context->primary_context()->shared_from_this();
        }

        if (parent_context->lookup_local(name, LookupNamespace::Ordinary) ||
            parent_context->lookup_local(name, LookupNamespace::Tag)) {
            error_custloc(
                "redefinition of '" + name + "' as namespace",
                component.loc);
        }
        if (parent_context->lookup_local_namespace_alias(name)) {
            error_custloc(
                "redefinition of '" + name + "' as namespace",
                component.loc);
        }

        auto ensure_inline_nomination =
            [&](const std::shared_ptr<DeclContext>& owner_context,
                const std::shared_ptr<DeclContext>& inline_context) {
            if (!owner_context || !inline_context) {
                return;
            }
            DeclContext* inline_primary =
                inline_context->primary_context()
                    ? inline_context->primary_context()
                    : inline_context.get();
            for (const auto& nomination : owner_context->namespace_nominations()) {
                if (nomination.kind != NamespaceNominationKind::InlineImplicit ||
                    !nomination.nominated_context) {
                    continue;
                }
                DeclContext* nominated_primary =
                    nomination.nominated_context->primary_context()
                        ? nomination.nominated_context->primary_context()
                        : nomination.nominated_context.get();
                if (nominated_primary == inline_primary) {
                    return;
                }
            }
            collect_->collect_register_namespace_nomination(
                owner_context,
                NamespaceNominationRecord{
                    NamespaceNominationKind::InlineImplicit,
                    inline_context,
                    component.loc,
                    0});
        };

        std::vector<std::string> scope_namespace_path =
            parent_scope ? parent_scope->cxx_namespace_path : std::vector<std::string>{};
        scope_namespace_path.push_back(name);
        const auto* existing_binding = parent_context->lookup_local_namespace(name);
        if (existing_binding &&
            existing_binding->target_scope &&
            existing_binding->target_scope->parent.get() == parent_scope.get()) {
            existing_binding->target_scope->cxx_namespace_path = scope_namespace_path;
            collect_->collect_enter_scope(namespace_scope_flags,
                                          existing_binding->target_scope);
            if (auto current_context = collect_->get_current_decl_context()) {
                current_context->set_lookup_name(name);
                auto canonical_namespace_context = current_context;
                if (canonical_namespace_context->primary_context() &&
                    canonical_namespace_context->primary_context() !=
                        canonical_namespace_context.get()) {
                    canonical_namespace_context =
                        canonical_namespace_context->primary_context()->shared_from_this();
                }
                if (component.is_inline &&
                    !canonical_namespace_context->is_inline_namespace()) {
                    error_custloc(
                        "extension of namespace '" + name +
                            "' with 'inline' requires the original namespace definition to be inline",
                        component.loc);
                }
                if (canonical_namespace_context->is_inline_namespace()) {
                    collect_->collect_set_namespace_inline_metadata(
                        canonical_namespace_context,
                        true,
                        canonical_parent_context.get());
                    ensure_inline_nomination(
                        canonical_parent_context,
                        canonical_namespace_context);
                } else if (component.is_inline) {
                    collect_->collect_set_namespace_inline_metadata(
                        canonical_namespace_context,
                        true,
                        canonical_parent_context.get());
                    ensure_inline_nomination(
                        canonical_parent_context,
                        canonical_namespace_context);
                }
                namespace_decl_infos.push_back(
                    NamespaceDeclBuildInfo{
                        name,
                        component.loc,
                        current_context.get(),
                        false,
                        component.is_inline,
                        {}});
            }
            ++entered_namespace_depth;
            return;
        }

        auto entered = collect_->collect_enter_scope(namespace_scope_flags);
        if (entered.scope) {
            entered.scope->cxx_namespace_path = scope_namespace_path;
        }
        if (auto current_context = collect_->get_current_decl_context()) {
            current_context->set_lookup_name(name);
            collect_->collect_register_namespace_binding(
                parent_context,
                NamespaceBindingEntry{
                    name,
                    current_context,
                    entered.scope});
            if (component.is_inline) {
                collect_->collect_set_namespace_inline_metadata(
                    current_context,
                    true,
                    canonical_parent_context.get());
                ensure_inline_nomination(
                    canonical_parent_context,
                    current_context);
            }
            namespace_decl_infos.push_back(
                NamespaceDeclBuildInfo{
                    name,
                    component.loc,
                    current_context.get(),
                    false,
                    component.is_inline,
                    {}});
        }
        ++entered_namespace_depth;
    };

    try {
        if (is_anonymous_namespace) {
            auto parent_scope = collect_->collect_current_scope();
            auto entered = collect_->collect_enter_scope(namespace_scope_flags);
            if (entered.scope && parent_scope) {
                entered.scope->cxx_namespace_path = parent_scope->cxx_namespace_path;
            }
            if (auto current_context = collect_->get_current_decl_context()) {
                namespace_decl_infos.push_back(
                    NamespaceDeclBuildInfo{
                        "",
                        namespace_loc,
                        current_context.get(),
                        true,
                        false,
                        {}});
            }
            ++entered_namespace_depth;
        } else {
            for (const auto& component : namespace_path) {
                enter_named_namespace(component);
            }
        }
        if (!namespace_decl_infos.empty() && !namespace_head_attrs.empty()) {
            auto& outermost_info = namespace_decl_infos.front();
            outermost_info.attrs.insert(
                outermost_info.attrs.end(),
                std::make_move_iterator(namespace_head_attrs.begin()),
                std::make_move_iterator(namespace_head_attrs.end()));
        }

        size_t last_recovery_idx = std::numeric_limits<size_t>::max();
        while (!gentle_check(TokenType::RIGHT_BRACE) &&
               !gentle_check(TokenType::Eof)) {
            try {
                auto decls = parse_declaration();
                if (decls.empty()) {
                    error("While parsing namespace definition, encountered a non-declaration");
                    return {};
                }
                parsed_decls.insert(
                    parsed_decls.end(),
                    std::make_move_iterator(decls.begin()),
                    std::make_move_iterator(decls.end()));
                diag_engine->sync_point_reached();
                last_recovery_idx = std::numeric_limits<size_t>::max();
            } catch (ParseError& e) {
                if (is_in_tentative_context()) {
                    throw;
                }
                size_t recover_start_idx = get_token_idx();
                skip_to_next_top_level_decl();
                if (get_token_idx() == recover_start_idx &&
                    recover_start_idx == last_recovery_idx &&
                    !gentle_check(TokenType::Eof) &&
                    !gentle_check(TokenType::RIGHT_BRACE)) {
                    advance();
                }
                last_recovery_idx = get_token_idx();
                diag_engine->sync_point_reached();
                parsed_decls.push_back(
                    collect_->collect_error_declaration(e.message, e.location));
            }
        }

        check_and_consume(TokenType::RIGHT_BRACE);
        gentle_check_and_consume(TokenType::SEMICOLON);
        if (parsed_decls.empty()) {
            parsed_decls.push_back(collect_->collect_nop_declaration(namespace_loc));
        }
        std::vector<std::unique_ptr<Decl>> namespace_wrappers_reversed;
        if (!namespace_decl_infos.empty()) {
            std::vector<Decl*> current_members;
            current_members.reserve(parsed_decls.size());
            for (const auto& parsed_decl : parsed_decls) {
                current_members.push_back(parsed_decl.get());
            }

            for (size_t idx = namespace_decl_infos.size(); idx > 0; --idx) {
                const auto& info = namespace_decl_infos[idx - 1];
                auto namespace_decl = std::make_unique<NamespaceDecl>(
                    info.name,
                    std::move(current_members),
                    info.semantic_context,
                    info.is_anonymous,
                    info.is_inline,
                    info.loc);
                auto* namespace_decl_ptr = namespace_decl.get();
                const DeclContext* context_key = info.semantic_context;
                if (context_key && context_key->primary_context()) {
                    context_key = context_key->primary_context();
                }
                if (context_key) {
                    auto canonical_it =
                        cxx_namespace_canonical_decl_cache_.find(context_key);
                    if (canonical_it == cxx_namespace_canonical_decl_cache_.end()) {
                        namespace_decl_ptr->canonical_decl = namespace_decl_ptr;
                        cxx_namespace_canonical_decl_cache_[context_key] =
                            namespace_decl_ptr;
                    } else {
                        namespace_decl_ptr->canonical_decl = canonical_it->second;
                    }

                    auto latest_it =
                        cxx_namespace_latest_decl_cache_.find(context_key);
                    if (latest_it != cxx_namespace_latest_decl_cache_.end()) {
                        namespace_decl_ptr->previous_decl = latest_it->second;
                    }
                    cxx_namespace_latest_decl_cache_[context_key] =
                        namespace_decl_ptr;
                } else {
                    namespace_decl_ptr->canonical_decl = namespace_decl_ptr;
                }

                if (ast_ctx && !info.attrs.empty()) {
                    ast_ctx->append_attrs(
                        namespace_decl_ptr->node_id,
                        std::vector<ParsedAttribute>(info.attrs));
                }

                current_members.clear();
                current_members.push_back(namespace_decl_ptr);
                namespace_wrappers_reversed.push_back(std::move(namespace_decl));
            }
        }
        leave_entered_namespaces();
        std::vector<std::unique_ptr<Decl>> result;
        result.reserve(
            namespace_wrappers_reversed.size() + parsed_decls.size());
        for (auto it = namespace_wrappers_reversed.rbegin();
             it != namespace_wrappers_reversed.rend();
             ++it) {
            result.push_back(std::move(*it));
        }
        result.insert(result.end(),
                      std::make_move_iterator(parsed_decls.begin()),
                      std::make_move_iterator(parsed_decls.end()));
        return result;
    } catch (...) {
        leave_entered_namespaces();
        throw;
    }
}

std::vector<std::unique_ptr<Decl>> Parser::parse_cpp_using_alias_declaration() {
    std::vector<std::unique_ptr<Decl>> parsed_decls;
    if (!is_cxx_mode_active() || !gentle_check(TokenType::USING)) {
        return parsed_decls;
    }

    Token using_tok = current_token();
    advance(); // consume using

    const bool in_class_scope =
        is_parsing_cpp_record_body() &&
        !collect_->collect_is_in_function_definition();

    auto current_scope = collect_->collect_current_scope();
    auto current_context = collect_->get_current_decl_context();
    auto translation_unit_context = collect_->get_translation_unit_decl_context();
    if (!current_scope || !current_context || !translation_unit_context) {
        error_custloc("internal error: missing namespace lookup context",
                      using_tok.loc);
    }
    auto global_scope = current_scope;
    while (global_scope && global_scope->parent) {
        global_scope = global_scope->parent;
    }
    if (!global_scope) {
        error_custloc("internal error: global namespace scope missing",
                      using_tok.loc);
    }

    auto format_namespace_prefix =
        [&](bool has_global_qualifier,
            const std::vector<std::string>& components,
            size_t upto_index) {
        std::vector<std::string> prefix_components;
        prefix_components.reserve(upto_index + 1);
        for (size_t idx = 0; idx <= upto_index; ++idx) {
            prefix_components.push_back(components[idx]);
        }
        if (prefix_components.empty()) {
            return std::string(has_global_qualifier ? "::" : "");
        }
        std::string terminal = prefix_components.back();
        prefix_components.pop_back();
        return qualified_name_utils::format_cpp_qualified_name(
            has_global_qualifier, prefix_components, terminal);
    };

    auto resolve_namespace_path =
        [&](bool has_global_qualifier,
            const std::vector<std::string>& components,
            SrcLoc error_loc,
            std::string_view target_kind) -> std::shared_ptr<Scope> {
        if (components.empty()) {
            error_custloc("expected namespace name after '" +
                              std::string(target_kind) + "'",
                          error_loc);
        }
        const DeclContext* lookup_context = has_global_qualifier
            ? translation_unit_context.get()
            : current_context.get();
        std::shared_ptr<Scope> resolved_scope = has_global_qualifier
            ? global_scope
            : current_scope;

        // Walk namespace components one-by-one so diagnostics can point at
        // the first segment that fails to resolve.
        for (size_t idx = 0; idx < components.size(); ++idx) {
            bool allow_enclosing_lookup =
                (!has_global_qualifier && idx == 0);
            auto namespace_scope = resolve_named_namespace_scope(
                lookup_context, components[idx], allow_enclosing_lookup);
            if (!namespace_scope || !namespace_scope->associated_decl_context) {
                error_custloc(
                    std::string(target_kind) + " target '" +
                        format_namespace_prefix(
                            has_global_qualifier, components, idx) +
                        "' does not name a namespace",
                    error_loc);
            }
            resolved_scope = namespace_scope;
            lookup_context = namespace_scope->associated_decl_context;
        }
        return resolved_scope;
    };

    if (gentle_check(TokenType::NAMESPACE)) {
        if (in_class_scope) {
            error_custloc("using-directive is not allowed in class scope",
                          using_tok.loc);
        }
        advance(); // consume namespace

        bool has_global_qualifier = false;
        if (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            has_global_qualifier = true;
        }

        if (!gentle_check(TokenType::IDENTIFIER)) {
            error_custloc("expected namespace name in using-directive",
                          current_token().loc);
        }

        std::vector<std::string> namespace_components;
        SrcLoc target_loc = current_token().loc;
        namespace_components.push_back(current_token().value);
        advance();
        while (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected namespace name after '::' in using-directive",
                    current_token().loc);
            }
            namespace_components.push_back(current_token().value);
            advance();
        }

        check_and_consume(TokenType::SEMICOLON);

        auto target_scope = resolve_namespace_path(
            has_global_qualifier,
            namespace_components,
            target_loc,
            "using-directive");
        auto* target_context = target_scope
            ? target_scope->associated_decl_context
            : nullptr;
        if (!target_context) {
            error_custloc("internal error: using-directive target context missing",
                          target_loc);
        }


        // Model using-directives as nomination relationships; unqualified lookup
        // walks these dynamically instead of materializing copied bindings.
        collect_->collect_register_namespace_nomination(
            current_context,
            NamespaceNominationRecord{
                NamespaceNominationKind::UsingDirective,
                target_context->shared_from_this(),
                using_tok.loc,
                0});

        parsed_decls.push_back(collect_->collect_nop_declaration(using_tok.loc));
        return parsed_decls;
    }

    if (gentle_check(TokenType::TYPENAME)) {
        fail_cpp_unsupported("using-declaration", using_tok.loc);
    }

    size_t payload_begin_idx = get_token_idx();
    if (gentle_check(TokenType::IDENTIFIER)) {
        std::string alias_name = current_token().value;
        SrcLoc alias_name_loc = current_token().loc;
        advance(); // alias identifier candidate

        auto alias_name_attrs = try_parse_attributes();
        if (gentle_check(TokenType::ASSIGN)) {
            advance(); // consume '='

            DeclarationParser alias_type_parser(this);
            auto alias_type = alias_type_parser.parse_declaration();
            if (!alias_type) {
                error_custloc("expected type-id in alias declaration", alias_name_loc);
            }
            if (!alias_type_parser.name.empty()) {
                error_custloc(
                    "alias declaration requires a type-id (unexpected declarator identifier '" +
                        alias_type_parser.name + "')",
                    alias_type_parser.loc);
            }
            if (alias_type_parser.str_class != StorageClass::NONE) {
                error_custloc(
                    "storage class specifier is not allowed in alias declaration",
                    alias_name_loc);
            }
            if (alias_type_parser.is_constexpr) {
                error_custloc(
                    "'constexpr' is not allowed in alias declaration",
                    alias_name_loc);
            }

            if (gentle_check(TokenType::COMMA)) {
                error_custloc("expected ';' after alias declaration", current_token().loc);
            }
            check_and_consume(TokenType::SEMICOLON);

            auto alias_underlying =
                QualType(alias_type, alias_type_parser.qualifiers);
            auto td_sym = collect_->collect_declare_typedef_symbol(
                alias_name, alias_underlying, using_tok.loc);
            if (td_sym) {
                for (const auto& attr : alias_type_parser.leading_attrs) {
                    td_sym->sym_attrs.attrs.push_back(attr);
                }
                for (const auto& attr : alias_name_attrs) {
                    td_sym->sym_attrs.attrs.push_back(attr);
                }
            }
            auto alias_decl = collect_->collect_typedef_declaration(
                alias_name,
                td_sym ? td_sym->type : alias_underlying,
                td_sym,
                using_tok.loc);
            if (td_sym && td_sym->type->kind == TypeKind::Typedef) {
                auto ttype = td_sym->type.as<TypedefType>();
                auto tdecl = dyn_cast<TypedefDecl>(alias_decl.get());
                ttype->typedef_decl = tdecl;
            }
            parsed_decls.push_back(std::move(alias_decl));
            return parsed_decls;
        }

        set_token_idx(payload_begin_idx);
    }

    struct ParsedUsingDeclarator {
        bool has_global_qualifier = false;
        std::vector<std::string> qualifiers;
        std::string terminal_name;
        SrcLoc terminal_loc;
    };

    auto parse_single_using_declarator =
        [&](std::string_view unsupported_feature) -> ParsedUsingDeclarator {
        ParsedUsingDeclarator declarator;
        if (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            declarator.has_global_qualifier = true;
        }

        if (!gentle_check(TokenType::IDENTIFIER)) {
            fail_cpp_unsupported(unsupported_feature, using_tok.loc);
        }

        declarator.terminal_name = current_token().value;
        declarator.terminal_loc = current_token().loc;
        advance();
        while (is_cpp_scope_resolution_here()) {
            consume_cpp_scope_resolution();
            declarator.qualifiers.push_back(std::move(declarator.terminal_name));
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected identifier after '::' in using-declaration",
                    current_token().loc);
            }
            declarator.terminal_name = current_token().value;
            declarator.terminal_loc = current_token().loc;
            advance();
        }

        return declarator;
    };

    std::vector<ParsedUsingDeclarator> using_declarators;
    std::string_view unsupported_feature =
        in_class_scope
            ? std::string_view("class-scope using-declaration")
            : std::string_view("using-declaration");
    while (true) {
        using_declarators.push_back(
            parse_single_using_declarator(unsupported_feature));
        if (!gentle_check_and_consume(TokenType::COMMA)) {
            break;
        }
    }
    check_and_consume(TokenType::SEMICOLON);

    if (in_class_scope) {
        for (const auto& declarator : using_declarators) {
            if (declarator.qualifiers.empty()) {
                fail_cpp_unsupported("class-scope using-declaration",
                                     declarator.terminal_loc);
            }
        }
        parsed_decls.push_back(collect_->collect_nop_declaration(using_tok.loc));
        return parsed_decls;
    }

    auto replayable_using_decl = collect_->collect_is_in_function_definition()
        ? make_ast<CppUsingDeclarationDecl>(*ast_ctx, using_tok.loc)
        : nullptr;

    auto using_import_namespace =
        [](LookupNamespace lookup_namespace) {
            return lookup_namespace == LookupNamespace::Tag
                ? CppUsingImportNamespace::Tag
                : CppUsingImportNamespace::Ordinary;
        };

    for (const auto& declarator : using_declarators) {
        if (!declarator.has_global_qualifier && declarator.qualifiers.empty()) {
            fail_cpp_unsupported("using-declaration", declarator.terminal_loc);
        }

        std::shared_ptr<Scope> target_scope;
        DeclContext* target_context = nullptr;
        if (declarator.has_global_qualifier &&
            declarator.qualifiers.empty()) {
            target_scope = global_scope;
            target_context = translation_unit_context.get();
        } else {
            target_scope = resolve_namespace_path(
                declarator.has_global_qualifier,
                declarator.qualifiers,
                declarator.terminal_loc,
                "using-declaration");
            target_context = target_scope
                ? target_scope->associated_decl_context
                : nullptr;
        }
        if (!target_context) {
            error_custloc("internal error: using-declaration target context missing",
                          declarator.terminal_loc);
        }

        CppUsingDeclarationDecl::ReplayTarget* replay_target = nullptr;
        if (replayable_using_decl) {
            replayable_using_decl->replay_targets.push_back(
                CppUsingDeclarationDecl::ReplayTarget{
                    declarator.terminal_name,
                    target_context});
            replay_target = &replayable_using_decl->replay_targets.back();
        }

        auto ordinary_lookup = LookupEngine::lookup_qualified(
            declarator.terminal_name,
            target_context,
            LookupNamespace::Ordinary);
        auto tag_lookup = LookupEngine::lookup_qualified(
            declarator.terminal_name,
            target_context,
            LookupNamespace::Tag);
        const DeclBinding* ordinary_binding =
            ordinary_lookup.status == LookupEngine::QualifiedLookupStatus::Found
                ? ordinary_lookup.binding
                : nullptr;
        const DeclBinding* tag_binding =
            tag_lookup.status == LookupEngine::QualifiedLookupStatus::Found
                ? tag_lookup.binding
                : nullptr;
        if (!ordinary_binding && !tag_binding) {
            error_custloc(
                "using-declaration target '" +
                    qualified_name_utils::format_cpp_qualified_name(
                        declarator.has_global_qualifier,
                        declarator.qualifiers,
                        declarator.terminal_name) +
                    "' does not name a member",
                declarator.terminal_loc);
        }

        std::vector<const Decl*> imported_template_decls;
        auto import_template_decl = [&](const Decl* template_decl,
                                        LookupNamespace lookup_namespace) {
            if (!template_decl) {
                return;
            }
            if (std::find(imported_template_decls.begin(),
                          imported_template_decls.end(),
                          template_decl) != imported_template_decls.end()) {
                return;
            }
            imported_template_decls.push_back(template_decl);
            collect_->collect_bind_template_decl(
                declarator.terminal_name, template_decl, lookup_namespace);
            if (replayable_using_decl) {
                CppUsingDeclarationDecl::ImportedTemplate imported{
                    declarator.terminal_name,
                    template_decl,
                    using_import_namespace(lookup_namespace)};
                replayable_using_decl->template_decls.push_back(imported);
                if (replay_target) {
                    replay_target->template_decls.push_back(std::move(imported));
                }
            }
        };

        auto import_template_binding = [&](const DeclBinding* binding,
                                           LookupNamespace lookup_namespace) {
            if (!binding) {
                return;
            }
            import_template_decl(binding->template_decl, lookup_namespace);
            for (const auto* template_candidate :
                 binding->template_overload_candidates) {
                import_template_decl(template_candidate, lookup_namespace);
            }
        };

        if (tag_binding &&
            !current_context->lookup_local(declarator.terminal_name,
                                           LookupNamespace::Tag)) {
            if (replay_target) {
                replay_target->import_tag = true;
            }
            if (auto* tag_decl = dyn_cast<TagDecl>(tag_binding->ast_decl)) {
                collect_->collect_add_tag_decl(
                    declarator.terminal_name, const_cast<TagDecl*>(tag_decl));
                if (replayable_using_decl) {
                    CppUsingDeclarationDecl::ImportedTag imported{
                        declarator.terminal_name,
                        const_cast<TagDecl*>(tag_decl)};
                    replayable_using_decl->tag_decls.push_back(imported);
                    if (replay_target) {
                        replay_target->tag_decls.push_back(imported);
                    }
                }
            }
            import_template_binding(tag_binding, LookupNamespace::Tag);
        }

        auto import_ordinary_symbol = [&](const std::shared_ptr<Symbol>& symbol) {
            if (!symbol) {
                return;
            }
            collect_->collect_bind_symbol_in_current_scope(
                declarator.terminal_name, symbol);
            if (replayable_using_decl) {
                CppUsingDeclarationDecl::ImportedSymbol imported{
                    declarator.terminal_name,
                    symbol};
                replayable_using_decl->ordinary_symbols.push_back(imported);
                if (replay_target) {
                    replay_target->ordinary_symbols.push_back(std::move(imported));
                }
            }
        };

        if (ordinary_binding) {
            if (replay_target) {
                replay_target->import_ordinary = true;
            }
            if (ordinary_binding->has_overload_set()) {
                for (const auto& candidate : ordinary_binding->overload_candidates) {
                    import_ordinary_symbol(candidate);
                }
            } else {
                import_ordinary_symbol(
                    ordinary_lookup.symbol ? ordinary_lookup.symbol
                                           : ordinary_binding->symbol);
            }
            import_template_binding(ordinary_binding, LookupNamespace::Ordinary);
        }
    }

    if (replayable_using_decl) {
        parsed_decls.push_back(std::move(replayable_using_decl));
    } else {
        parsed_decls.push_back(collect_->collect_nop_declaration(using_tok.loc));
    }
    return parsed_decls;
}

std::string Parser::make_cpp_future_work_message(
    std::string_view feature,
    std::string_view future_work_item) const {
    return "C++ parser TODO: " + std::string(feature) +
           " (future work item: " + std::string(future_work_item) + ")";
}

void Parser::fail_cpp_future_work(std::string_view feature,
                                  std::string_view future_work_item,
                                  SrcLoc loc) {
    error_custloc(make_cpp_future_work_message(feature, future_work_item), loc);
}

CppExplicitSpecifier Parser::parse_cpp_optional_explicit_specifier() {
    CppExplicitSpecifier specifier;
    if (!is_cxx_mode_active() || !gentle_check(TokenType::EXPLICIT_KW)) {
        return specifier;
    }

    Token explicit_tok = current_token();
    specifier.is_present = true;
    specifier.effective_value = true;
    specifier.location = explicit_tok.loc;
    advance(); // 'explicit'

    if (!gentle_check(TokenType::LEFT_PAREN)) {
        return specifier;
    }

    if (!lang_opts.is_cxx20_or_later()) {
        error_custloc(
            "conditional explicit specifier requires C++20",
            explicit_tok.loc);
    }

    specifier.is_conditional = true;
    SrcLoc lparen_loc = current_token().loc;
    advance(); // '('
    if (gentle_check(TokenType::RIGHT_PAREN)) {
        error_custloc(
            "explicit specifier requires a constant expression",
            lparen_loc);
    }

    auto condition = parse_conditional_expression();
    if (!condition) {
        error_custloc(
            "explicit specifier requires a constant expression",
            lparen_loc);
    }

    bool is_dependent =
        collect_ &&
        collect_->expression_is_value_dependent_for_constant_evaluation(
            condition.get(),
            is_in_template_pattern_context());

    specifier.condition = std::shared_ptr<Expr>(condition.release());
    if (is_dependent) {
        specifier.is_dependent = true;
        specifier.effective_value = true;
    } else {
        auto eval = collect_->try_evaluate_constant_expression_demand(
            specifier.condition.get(),
            ConstEvalMode::cpp_core_constant_expression(),
            lparen_loc);
        if (!eval.has_value()) {
            SrcLoc diag_loc = specifier.condition
                ? specifier.condition->location
                : lparen_loc;
            error_custloc(
                "explicit specifier expression must be an integer constant expression",
                diag_loc);
        }
        specifier.effective_value = *eval != 0;
    }

    check_and_consume(TokenType::RIGHT_PAREN);
    return specifier;
}

void Parser::parse_cpp_optional_noexcept_spec(
    FunctionType& function_type,
    const Collect::CppThisContext* cpp_this_context,
    QualType record_lookup_type) {
    if (!is_cxx_mode_active() || !gentle_check(TokenType::NOEXCEPT_KW)) {
        return;
    }

    function_type.has_explicit_exception_spec = true;
    function_type.exception_spec = FunctionExceptionSpecKind::PotentiallyThrowing;
    function_type.exception_spec_expr = nullptr;

    advance(); // 'noexcept'
    bool is_non_throwing = true;
    if (gentle_check(TokenType::LEFT_PAREN)) {
        SrcLoc lparen_loc = current_token().loc;
        advance(); // '('

        auto parse_noexcept_operand = [&]() {
            if (gentle_check(TokenType::RIGHT_PAREN)) {
                error_custloc("noexcept expression must be an integer constant expression",
                              lparen_loc);
            } else {
                auto noexcept_expr = parse_conditional_expression();
                bool is_dependent =
                    collect_ &&
                    collect_->expression_is_value_dependent_for_constant_evaluation(
                        noexcept_expr.get(),
                        is_in_template_pattern_context());
                if (is_dependent) {
                    function_type.exception_spec =
                        FunctionExceptionSpecKind::Dependent;
                    function_type.exception_spec_expr =
                        std::shared_ptr<Expr>(noexcept_expr.release());
                    is_non_throwing = false;
                } else {
                    auto eval = collect_->try_evaluate_constant_expression_demand(
                        noexcept_expr.get(),
                        ConstEvalMode::cpp_core_constant_expression(),
                        lparen_loc);
                    if (!eval.has_value()) {
                        SrcLoc diag_loc =
                            noexcept_expr ? noexcept_expr->location : current_token().loc;
                        error_custloc(
                            "noexcept expression must be an integer constant expression",
                            diag_loc);
                    } else {
                        is_non_throwing = *eval != 0;
                    }
                }
                if (!is_dependent && !noexcept_expr) {
                    SrcLoc diag_loc =
                        current_token().loc;
                    error_custloc(
                        "noexcept expression must be an integer constant expression",
                        diag_loc);
                }
            }
        };

        if (collect_ &&
            cpp_this_context &&
            cpp_this_context->is_member_function) {
            collect_->with_cpp_declarator_expression_context(
                *cpp_this_context,
                record_lookup_type,
                [&]() {
                    parse_noexcept_operand();
                    return true;
                });
        } else {
            parse_noexcept_operand();
        }
        check_and_consume(TokenType::RIGHT_PAREN);
    } else {
        function_type.exception_spec = FunctionExceptionSpecKind::NonThrowing;
    }

    if (function_type.exception_spec != FunctionExceptionSpecKind::Dependent) {
        function_type.exception_spec = is_non_throwing
            ? FunctionExceptionSpecKind::NonThrowing
            : FunctionExceptionSpecKind::PotentiallyThrowing;
    }
}

std::unique_ptr<Expr> Parser::parse_cpp_throw_expression() {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    Token throw_tok = current_token();
    if (!lang_opts.exceptions_enabled) {
        error_custloc("cannot use 'throw' with exceptions disabled", throw_tok.loc);
    }
    check_and_consume(TokenType::THROW_KW);

    std::unique_ptr<Expr> thrown_expr = nullptr;
    if (!gentle_check(TokenType::SEMICOLON) &&
        !gentle_check(TokenType::COMMA) &&
        !gentle_check(TokenType::COLON) &&
        !gentle_check(TokenType::RIGHT_PAREN) &&
        !gentle_check(TokenType::RIGHT_BRACKET) &&
        !gentle_check(TokenType::RIGHT_BRACE) &&
        !gentle_check(TokenType::Eof)) {
        thrown_expr = parse_assignment_expression();
    }

    return collect_->collect_cpp_throw_expression(std::move(thrown_expr), throw_tok.loc);
}

std::unique_ptr<Expr> Parser::parse_cpp_new_expression(bool is_global_allocation) {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    Token new_tok = current_token();
    check_and_consume(TokenType::NEW);

    std::vector<std::unique_ptr<Expr>> placement_args;
    QualType allocated_type = nullptr;
    bool parsed_type_id = false;

    auto try_parse_parenthesized_type_id = [&](QualType& out_type) -> bool {
        TentativeParsingAction tentative(*this);
        try {
            advance(); // '('
            DeclarationParser type_parser(this);
            auto parsed_type_raw = type_parser.parse_declaration();
            if (!parsed_type_raw ||
                !type_parser.name.empty() ||
                type_parser.str_class != StorageClass::NONE ||
                !gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                return false;
            }
            out_type = QualType(parsed_type_raw, type_parser.qualifiers);
            tentative.commit();
            return true;
        } catch (const ParseError&) {
            return false;
        } catch (const FatalErrorLimitReached&) {
            return false;
        }
    };

    if (gentle_check(TokenType::LEFT_PAREN) &&
        try_parse_parenthesized_type_id(allocated_type)) {
        parsed_type_id = true;
    }

    if (!parsed_type_id && gentle_check(TokenType::LEFT_PAREN)) {
        check_and_consume(TokenType::LEFT_PAREN);
        if (gentle_check(TokenType::RIGHT_PAREN)) {
            error_custloc("new placement arguments cannot be empty", current_token().loc);
        }
        do {
            placement_args.push_back(
                parse_assignment_expression_with_optional_pack_expansion());
        } while (gentle_check_and_consume(TokenType::COMMA));
        check_and_consume(TokenType::RIGHT_PAREN);
    }

    if (!parsed_type_id) {
        if (gentle_check(TokenType::LEFT_PAREN)) {
            check_and_consume(TokenType::LEFT_PAREN);
            DeclarationParser type_parser(this);
            auto parsed_type_raw = type_parser.parse_declaration();
            if (!parsed_type_raw ||
                !type_parser.name.empty() ||
                type_parser.str_class != StorageClass::NONE) {
                error_custloc("expected type-id in new-expression", new_tok.loc);
            }
            allocated_type = QualType(parsed_type_raw, type_parser.qualifiers);
            check_and_consume(TokenType::RIGHT_PAREN);
        } else {
            if (!isTokenDeclarationSpec(current_token())) {
                error_custloc("expected type-id in new-expression", current_token().loc);
            }
            DeclarationParser type_parser(this);
            type_parser.parse_new_type_id_context = true;
            auto parsed_type_raw = type_parser.parse_declaration();
            if (!parsed_type_raw ||
                !type_parser.name.empty() ||
                type_parser.str_class != StorageClass::NONE) {
                error_custloc("expected type-id in new-expression", new_tok.loc);
            }
            allocated_type = QualType(parsed_type_raw, type_parser.qualifiers);
        }
    }

    std::unique_ptr<Expr> initializer = nullptr;
    if (gentle_check(TokenType::LEFT_PAREN)) {
        initializer = parse_paren_init_list();
    } else if (gentle_check(TokenType::LEFT_BRACE)) {
        initializer = parse_init_list();
    }

    return collect_->collect_cpp_new_expression(
        allocated_type,
        std::move(placement_args),
        std::move(initializer),
        is_global_allocation,
        new_tok.loc);
}

std::unique_ptr<Expr> Parser::parse_cpp_delete_expression(bool is_global_delete) {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    Token delete_tok = current_token();
    check_and_consume(TokenType::DELETE);

    bool is_array_form = false;
    if (gentle_check(TokenType::LEFT_BRACKET) &&
        peek_token().type == TokenType::RIGHT_BRACKET) {
        advance(); // '['
        advance(); // ']'
        is_array_form = true;
    }

    auto operand = parse_cast_expression();
    return collect_->collect_cpp_delete_expression(
        std::move(operand),
        is_array_form,
        is_global_delete,
        delete_tok.loc);
}

CppCatchClause Parser::parse_cpp_catch_clause() {
    CppCatchClause clause;
    Token catch_tok = current_token();
    check_and_consume(TokenType::CATCH_KW);
    clause.location = catch_tok.loc;

    check_and_consume(TokenType::LEFT_PAREN);
    if (gentle_check(TokenType::ELLIPSIS)) {
        clause.is_catch_all = true;
        advance();
    } else {
        DeclarationParser decl_parser(this);
        auto exception_type = decl_parser.parse_declaration();
        if (!exception_type) {
            error_custloc("invalid catch parameter declaration", catch_tok.loc);
        }
        clause.exception_type = exception_type;
        clause.exception_name = decl_parser.name;
    }
    check_and_consume(TokenType::RIGHT_PAREN);

    if (!gentle_check(TokenType::LEFT_BRACE)) {
        error_custloc("expected '{' to start catch handler", current_token().loc);
    }

    auto entered_scope = collect_->collect_enter_scope(ScopeFlags::BlockScope);
    auto catch_scope = entered_scope.scope;
    struct CatchScopeGuard {
        Collect* collect = nullptr;
        bool active = false;
        ~CatchScopeGuard() {
            if (active && collect) {
                collect->collect_leave_scope();
            }
        }
    } catch_scope_guard{collect_.get(), true};

    if (!clause.is_catch_all && !clause.exception_name.empty() && clause.exception_type) {
        clause.exception_symbol = collect_->collect_declare_variable_symbol(
            clause.exception_name,
            clause.exception_type,
            StorageClass::NONE,
            false,
            false,
            catch_tok.loc);
    }

    clause.handler = parse_compound_stmt(catch_scope);

    collect_->collect_leave_scope();
    catch_scope_guard.active = false;
    return clause;
}

void Parser::skip_balanced_token_sequence_tokens(
    TokenType open_tok,
    TokenType close_tok,
    const std::string& missing_close_diag) {
    if (!gentle_check(open_tok)) {
        error("internal error: expected balanced token sequence start");
    }

    std::vector<TokenType> closer_stack;
    closer_stack.push_back(close_tok);
    advance(); // consume initial opener
    while (!gentle_check(TokenType::Eof) && !closer_stack.empty()) {
        TokenType tt = current_token().type;
        if (tt == TokenType::LEFT_PAREN) {
            closer_stack.push_back(TokenType::RIGHT_PAREN);
            advance();
            continue;
        }
        if (tt == TokenType::LEFT_BRACE) {
            closer_stack.push_back(TokenType::RIGHT_BRACE);
            advance();
            continue;
        }
        if (tt == TokenType::LEFT_BRACKET) {
            closer_stack.push_back(TokenType::RIGHT_BRACKET);
            advance();
            continue;
        }

        if (tt == closer_stack.back()) {
            closer_stack.pop_back();
            advance();
            continue;
        }
        advance();
    }
    if (!closer_stack.empty()) {
        error(missing_close_diag);
    }
}

void Parser::skip_cpp_constructor_mem_initializer_list_tokens() {
    if (!gentle_check(TokenType::COLON)) {
        return;
    }

    advance(); // ':'
    while (true) {
        bool saw_target_token = false;
        int angle_depth = 0;
        while (!gentle_check(TokenType::Eof)) {
            TokenType tt = current_token().type;
            if (angle_depth == 0 &&
                (tt == TokenType::LEFT_PAREN || tt == TokenType::LEFT_BRACE)) {
                break;
            }
            if (angle_depth == 0 &&
                (tt == TokenType::COMMA || tt == TokenType::SEMICOLON ||
                 tt == TokenType::RIGHT_BRACE)) {
                break;
            }
            if (tt == TokenType::DECLTYPE_KW &&
                peek_token().type == TokenType::LEFT_PAREN) {
                saw_target_token = true;
                advance(); // decltype
                skip_balanced_token_sequence_tokens(
                    TokenType::LEFT_PAREN,
                    TokenType::RIGHT_PAREN,
                    "expected ')' to close decltype in constructor mem-initializer");
                continue;
            }
            if (tt == TokenType::LESS_THAN) {
                ++angle_depth;
                saw_target_token = true;
                advance();
                continue;
            }
            if (tt == TokenType::GREATER_THAN && angle_depth > 0) {
                --angle_depth;
                saw_target_token = true;
                advance();
                continue;
            }
            if (tt == TokenType::RIGHT_SHIFT && angle_depth > 0) {
                angle_depth = angle_depth > 1 ? angle_depth - 2 : 0;
                saw_target_token = true;
                advance();
                continue;
            }
            if (tt == TokenType::ASSIGN_RSHIFT && angle_depth > 0) {
                angle_depth = 0;
                saw_target_token = true;
                advance();
                continue;
            }
            saw_target_token = true;
            advance();
        }
        if (!saw_target_token) {
            error("expected member name in constructor mem-initializer-list");
        }

        if (gentle_check(TokenType::LEFT_PAREN)) {
            skip_balanced_token_sequence_tokens(
                TokenType::LEFT_PAREN,
                TokenType::RIGHT_PAREN,
                "expected ')' to close constructor member initializer");
        } else if (gentle_check(TokenType::LEFT_BRACE)) {
            skip_balanced_token_sequence_tokens(
                TokenType::LEFT_BRACE,
                TokenType::RIGHT_BRACE,
                "expected '}' to close constructor member initializer");
        } else {
            error("expected '(' or '{' after constructor mem-initializer");
        }

        gentle_check_and_consume(TokenType::ELLIPSIS);

        if (!gentle_check_and_consume(TokenType::COMMA)) {
            break;
        }
    }
}

void Parser::skip_cpp_function_try_block_tail_tokens() {
    if (!gentle_check(TokenType::LEFT_BRACE)) {
        error_custloc("expected '{' to start function-try-block body",
                      current_token().loc);
    }
    skip_balanced_token_sequence_tokens(
        TokenType::LEFT_BRACE,
        TokenType::RIGHT_BRACE,
        "expected '}' to close function-try-block body");

    bool saw_handler = false;
    while (gentle_check(TokenType::CATCH_KW)) {
        saw_handler = true;
        advance(); // catch
        check_and_consume(TokenType::LEFT_PAREN);
        if (gentle_check(TokenType::ELLIPSIS)) {
            advance();
        } else {
            while (!gentle_check(TokenType::RIGHT_PAREN) &&
                   !gentle_check(TokenType::Eof)) {
                advance();
            }
        }
        check_and_consume(TokenType::RIGHT_PAREN);
        if (!gentle_check(TokenType::LEFT_BRACE)) {
            error_custloc("expected '{' to start catch handler",
                          current_token().loc);
        }
        skip_balanced_token_sequence_tokens(
            TokenType::LEFT_BRACE,
            TokenType::RIGHT_BRACE,
            "expected '}' to close catch handler");
    }
    if (!saw_handler) {
        error_custloc("expected at least one catch handler after try block",
                      current_token().loc);
    }
}

void Parser::skip_cpp_function_try_block_tokens(
    bool allow_ctor_mem_initializer_after_try) {
    check_and_consume(TokenType::TRY_KW);
    if (allow_ctor_mem_initializer_after_try) {
        skip_cpp_constructor_mem_initializer_list_tokens();
    }
    skip_cpp_function_try_block_tail_tokens();
}

std::unique_ptr<Stmt> Parser::parse_cpp_try_statement(
    std::shared_ptr<Scope> try_scope,
    bool allow_ctor_mem_initializer_after_try) {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    Token try_tok = current_token();
    if (!lang_opts.exceptions_enabled) {
        error_custloc("cannot use 'try' with exceptions disabled", try_tok.loc);
    }
    check_and_consume(TokenType::TRY_KW);
    if (allow_ctor_mem_initializer_after_try &&
        gentle_check(TokenType::COLON)) {
        skip_cpp_constructor_mem_initializer_list_tokens();
    }
    auto try_block = parse_compound_stmt(try_scope);

    if (!gentle_check(TokenType::CATCH_KW)) {
        error_custloc("expected at least one catch handler after try block",
            current_token().loc);
    }

    std::vector<CppCatchClause> handlers;
    while (gentle_check(TokenType::CATCH_KW)) {
        handlers.push_back(parse_cpp_catch_clause());
    }
    return collect_->collect_cpp_try_statement(
        std::move(try_block),
        std::move(handlers),
        try_tok.loc);
}

std::unique_ptr<Expr> Parser::parse_cpp_named_cast_expression() {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    Token cast_tok = current_token();
    if (cast_tok.type != TokenType::IDENTIFIER) {
        return nullptr;
    }

    Collect::CppNamedCastKind cast_kind;
    if (cast_tok.value == "static_cast") {
        cast_kind = Collect::CppNamedCastKind::Static;
    } else if (cast_tok.value == "const_cast") {
        cast_kind = Collect::CppNamedCastKind::Const;
    } else if (cast_tok.value == "reinterpret_cast") {
        cast_kind = Collect::CppNamedCastKind::Reinterpret;
    } else if (cast_tok.value == "dynamic_cast") {
        cast_kind = Collect::CppNamedCastKind::Dynamic;
    } else {
        return nullptr;
    }

    advance(); // consume cast keyword
    check_and_consume(TokenType::LESS_THAN);

    DeclarationParser type_parser(this);
    auto parsed_type = type_parser.parse_declaration();
    if (!parsed_type || !type_parser.name.empty()) {
        error_custloc("expected type-id in named cast", cast_tok.loc);
    }
    if (type_parser.str_class != StorageClass::NONE) {
        error_custloc(
            "storage class specifier is not allowed in named cast type-id",
            cast_tok.loc);
    }

    check_and_consume(TokenType::GREATER_THAN);
    check_and_consume(TokenType::LEFT_PAREN);
    auto expr = parse_expression();
    check_and_consume(TokenType::RIGHT_PAREN);

    return collect_->collect_cpp_named_cast(
        cast_kind,
        std::move(expr),
        QualType(parsed_type, type_parser.qualifiers),
        cast_tok.loc);
}

std::unique_ptr<Expr> Parser::parse_cpp_typeid_expression() {
    if (!is_cxx_mode_active()) {
        return nullptr;
    }

    Token typeid_tok = current_token();
    if (typeid_tok.type != TokenType::IDENTIFIER || typeid_tok.value != "typeid") {
        return nullptr;
    }

    advance(); // consume 'typeid'
    check_and_consume(TokenType::LEFT_PAREN);

    {
        TentativeParsingAction tentative(*this);
        try {
            DeclarationParser type_parser(this);
            auto parsed_type = type_parser.parse_declaration();
            if (parsed_type &&
                type_parser.name.empty() &&
                type_parser.str_class == StorageClass::NONE &&
                gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                tentative.commit();
                return collect_->collect_cpp_typeid_type(
                    QualType(parsed_type, type_parser.qualifiers),
                    typeid_tok.loc);
            }
        } catch (const FatalErrorLimitReached&) {
        } catch (const ParseError&) {
        }
    }

    auto expr = parse_expression();
    check_and_consume(TokenType::RIGHT_PAREN);
    return collect_->collect_cpp_typeid_expression(std::move(expr), typeid_tok.loc);
}

Parser::TPResult Parser::try_parse_cpp_qualified_id() {
    if (!is_cpp_qualified_id_start()) {
        return TPResult::False;
    }
    RevertingTentativeParsingAction tentative(*this);
    try {
        auto parse_component = [&]() -> bool {
            if (gentle_check(TokenType::OPERATOR_KW)) {
                return try_parse_cpp_operator_function_id_name().has_value();
            }
            if (!gentle_check(TokenType::IDENTIFIER)) {
                return false;
            }
            advance();
            if (gentle_check(TokenType::LESS_THAN)) {
                RevertingTentativeParsingAction template_args(*this);
                parse_cpp_template_argument_list();
                if (is_cpp_scope_resolution_here()) {
                    template_args.commit();
                }
            }
            return true;
        };

        bool saw_scope = false;
        if (gentle_check(TokenType::DECLTYPE_KW)) {
            if (!try_consume_cpp_decltype_specifier_for_lookahead() ||
                !consume_cpp_scope_resolution()) {
                return TPResult::Error;
            }
            saw_scope = true;
            gentle_check_and_consume(TokenType::TEMPLATE);
            if (!parse_component()) {
                return TPResult::Error;
            }
        } else {
            saw_scope = consume_cpp_scope_resolution();
            if (!parse_component()) {
                return TPResult::Error;
            }
        }

        while (consume_cpp_scope_resolution()) {
            saw_scope = true;
            gentle_check_and_consume(TokenType::TEMPLATE);
            if (!parse_component()) {
                return TPResult::Error;
            }
        }

        return saw_scope ? TPResult::True : TPResult::False;
    } catch (const FatalErrorLimitReached&) {
        return TPResult::Error;
    } catch (const ParseError&) {
        return TPResult::Error;
    }
}

Parser::TPResult Parser::try_parse_cpp_qualified_declarator() {
    if (!is_cxx_mode_active() || !isTokenDeclarationSpec(current_token())) {
        return TPResult::False;
    }
    RevertingTentativeParsingAction tentative(*this);
    size_t start_idx = tok_mgnt.get_token_idx();

    tentative_syntax_probe::Config probe_cfg{
        .cxx_mode = is_cxx_mode_active(),
        .blocks_enabled = type_ctx && type_ctx->target &&
            darwin_blocks::blocks_enabled_for_langopts(
                lang_opts, *type_ctx->target)
    };
    tentative_syntax_probe::Result syntax_probe_result =
        tentative_syntax_probe::probe_cpp_qualified_declarator(tok_mgnt, probe_cfg);
    if (syntax_probe_result == tentative_syntax_probe::Result::Match) {
        return TPResult::True;
    }
    if (syntax_probe_result == tentative_syntax_probe::Result::NoMatch) {
        return TPResult::False;
    }
    if (syntax_probe_result == tentative_syntax_probe::Result::Error) {
        return TPResult::Error;
    }

    tok_mgnt.set_token_idx(start_idx);
    try {
        DeclarationParser decl(this);
        auto parsed_type = decl.parse_declaration();
        if (!parsed_type) {
            return TPResult::Error;
        }
        if (is_cpp_scope_resolution_here()) {
            return TPResult::True;
        }
        return TPResult::False;
    } catch (const FatalErrorLimitReached&) {
        return TPResult::Error;
    } catch (const ParseError&) {
        return TPResult::Error;
    }
}

namespace {
bool is_cpp_record_key_token(TokenType tok) {
    return tok == TokenType::CLASS ||
           tok == TokenType::STRUCT ||
           tok == TokenType::UNION;
}

bool is_access_specifier_token(TokenType tok) {
    return tok == TokenType::PUBLIC_KW ||
           tok == TokenType::PRIVATE_KW ||
           tok == TokenType::PROTECTED_KW;
}

CppAccessSpecifier to_cpp_access_specifier(TokenType tok) {
    switch (tok) {
        case TokenType::PUBLIC_KW:
            return CppAccessSpecifier::Public;
        case TokenType::PRIVATE_KW:
            return CppAccessSpecifier::Private;
        case TokenType::PROTECTED_KW:
            return CppAccessSpecifier::Protected;
        default:
            return CppAccessSpecifier::None;
    }
}
} // namespace

CppCtorInitializer Parser::parse_cpp_ctor_mem_initializer(
    const std::string& record_name) {
    CppCtorInitializer mem_init;
    Token target_tok = current_token();
    mem_init.location = target_tok.loc;

    size_t saved_idx = get_token_idx();
    auto saved_split_state = tok_mgnt.get_split_token_state();
    auto restore_target_parse = [&]() {
        set_token_idx(saved_idx);
        tok_mgnt.set_split_token_state(saved_split_state);
    };

    if (auto parsed_target =
            try_parse_cpp_named_type_specifier(
                CppTypeNameParseContext::BaseSpecifier)) {
        if (gentle_check(TokenType::LEFT_PAREN) ||
            gentle_check(TokenType::LEFT_BRACE)) {
            mem_init.member_name = parsed_target->spelling;
            mem_init.target_spelling = parsed_target->spelling;
            mem_init.target_type = parsed_target->type;
        } else {
            restore_target_parse();
        }
    }

    if (mem_init.target_spelling.empty()) {
        if (!gentle_check(TokenType::IDENTIFIER)) {
            error("expected member name in constructor mem-initializer-list");
        }
        target_tok = current_token();
        mem_init.location = target_tok.loc;
        mem_init.member_name = target_tok.value;
        mem_init.target_spelling = target_tok.value;
        advance();
    }

    mem_init.is_delegating_initializer = mem_init.target_spelling == record_name;
    const std::string& target_name =
        mem_init.target_spelling.empty()
            ? mem_init.member_name
            : mem_init.target_spelling;

    if (gentle_check(TokenType::LEFT_PAREN)) {
        mem_init.is_list_init = false;
        mem_init.deferred_init_begin_token_idx = get_token_idx();
        skip_balanced_token_sequence_tokens(
            TokenType::LEFT_PAREN,
            TokenType::RIGHT_PAREN,
            "expected ')' to close constructor member initializer");
        mem_init.deferred_init_end_token_idx = get_token_idx();
    } else if (gentle_check(TokenType::LEFT_BRACE)) {
        mem_init.is_list_init = true;
        mem_init.deferred_init_begin_token_idx = get_token_idx();
        skip_balanced_token_sequence_tokens(
            TokenType::LEFT_BRACE,
            TokenType::RIGHT_BRACE,
            "expected '}' to close constructor member initializer");
        mem_init.deferred_init_end_token_idx = get_token_idx();
    } else {
        error("expected '(' or '{' after constructor mem-initializer '" +
              target_name + "'");
    }

    if (gentle_check_and_consume(TokenType::ELLIPSIS)) {
        mem_init.is_pack_expansion = true;
    }

    return mem_init;
}

std::vector<CppCtorInitializer>
Parser::parse_cpp_ctor_mem_initializer_list(const std::string& record_name) {
    check_and_consume(TokenType::COLON);
    std::vector<CppCtorInitializer> parsed_ctor_initializers;
    while (true) {
        parsed_ctor_initializers.push_back(
            parse_cpp_ctor_mem_initializer(record_name));
        if (!gentle_check_and_consume(TokenType::COMMA)) {
            break;
        }
    }
    return parsed_ctor_initializers;
}

std::unique_ptr<Decl> Parser::parse_cpp_constructor_member() {
    if (!is_cxx_mode_active() || cxx_record_parse_stack_.empty()) {
        error("internal error: constructor parser invoked outside C++ class scope");
    }
    const auto& record_frame = cxx_record_parse_stack_.back();
    if (record_frame.kind == CppRecordKind::Union || record_frame.name.empty()) {
        error("internal error: constructor parser requires a named class context");
    }
    const std::string& record_name = record_frame.name;

    CppExplicitSpecifier explicit_specifier;
    bool is_constexpr = false;
    bool is_consteval = false;
    bool is_inline = false;
    std::vector<ParsedAttribute> leading_attrs;
    while (true) {
        if (gentle_check(TokenType::EXPLICIT_KW)) {
            if (explicit_specifier.is_present) {
                error_custloc("duplicate 'explicit' specifier", current_token().loc);
            }
            explicit_specifier = parse_cpp_optional_explicit_specifier();
            continue;
        }
        if (gentle_check(TokenType::CONSTEXPR_KW)) {
            if (is_constexpr) {
                error_custloc("duplicate 'constexpr' specifier", current_token().loc);
            }
            if (is_consteval) {
                error_custloc(
                    "'constexpr' cannot be combined with 'consteval'",
                    current_token().loc);
            }
            is_constexpr = true;
            advance();
            continue;
        }
        if (gentle_check(TokenType::CONSTEVAL_KW)) {
            if (!lang_opts.is_cxx20_or_later()) {
                error_custloc("'consteval' is only available in C++20",
                              current_token().loc);
            }
            if (is_consteval) {
                error_custloc("duplicate 'consteval' specifier", current_token().loc);
            }
            if (is_constexpr) {
                error_custloc(
                    "'constexpr' cannot be combined with 'consteval'",
                    current_token().loc);
            }
            is_consteval = true;
            is_constexpr = true;
            is_inline = true;
            advance();
            continue;
        }
        if (gentle_check(TokenType::INLINE)) {
            if (is_inline) {
                error_custloc("duplicate 'inline' specifier", current_token().loc);
            }
            is_inline = true;
            advance();
            continue;
        }
        if (is_gnu_attribute_token(current_token()) ||
            gentle_check(TokenType::ALIGNAS) ||
            (gentle_check(TokenType::LEFT_BRACKET) &&
             peek_token().type == TokenType::LEFT_BRACKET)) {
            auto parsed_attrs = try_parse_attributes();
            leading_attrs.insert(
                leading_attrs.end(),
                std::make_move_iterator(parsed_attrs.begin()),
                std::make_move_iterator(parsed_attrs.end()));
            continue;
        }
        break;
    }

    Token ctor_name_tok = current_token();
    if (!gentle_check(TokenType::IDENTIFIER) ||
        current_token().value != record_name) {
        error("expected constructor name '" + record_name + "'");
    }
    advance(); // consume constructor name

    check_and_consume(TokenType::LEFT_PAREN);

    std::vector<std::unique_ptr<Decl>> params;
    std::vector<QualType> param_types;
    std::vector<uint8_t> parameter_pack_flags;
    bool is_variadic = false;
    bool has_prototype = true;
    bool saw_default_argument = false;
    if (!gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
        while (true) {
            if (gentle_check_and_consume(TokenType::ELLIPSIS)) {
                is_variadic = true;
                check_and_consume(TokenType::RIGHT_PAREN);
                break;
            }

            DeclarationParser param_parser(this);
            param_parser.in_function_parameter = true;
            auto param_type_raw = param_parser.parse_declaration();
            if (!param_type_raw) {
                error("invalid constructor parameter declaration");
            }
            if (param_parser.is_consteval) {
                error("'consteval' is not valid for function parameter declarations");
            }
            if (param_parser.is_constexpr) {
                error("'constexpr' is not valid for function parameter declarations");
            }

            QualType param_type(param_type_raw, param_parser.qualifiers);
            if (param_type && param_type->isVoid() && !param_parser.name.empty()) {
                error("Argument cannot have 'void' type");
            }

            auto param_decl = collect_->collect_parameter_declaration(
                param_type,
                param_parser.name,
                nullptr,
                param_parser.str_class,
                param_parser.begin_loc);
            if (auto* typed_param = dyn_cast<ParamDecl>(param_decl.get())) {
                typed_param->is_constexpr = param_parser.is_constexpr;
                typed_param->is_parameter_pack = param_parser.is_parameter_pack;
                set_param_decl_default_argument(
                    typed_param,
                    std::move(param_parser.default_argument));
            }

            params.push_back(std::move(param_decl));
            param_types.push_back(param_type);
            parameter_pack_flags.push_back(
                param_parser.is_parameter_pack ? 1 : 0);

            bool has_default_argument = false;
            if (gentle_check(TokenType::ASSIGN)) {
                advance(); // '='
                if (params.empty()) {
                    error("internal error: constructor parameter list state is inconsistent");
                }
                auto* typed_param = dyn_cast<ParamDecl>(params.back().get());
                if (!typed_param) {
                    error("internal error: constructor parameter was not parsed as ParamDecl");
                }
                auto default_argument = parse_assignment_expression();
                if (!default_argument) {
                    error("invalid default argument expression");
                }
                set_param_decl_default_argument(
                    typed_param,
                    std::move(default_argument));
                has_default_argument = true;
            }
            if (has_default_argument) {
                saw_default_argument = true;
            } else if (saw_default_argument) {
                error("parameter without a default argument follows parameter with a default argument");
            }

            if (gentle_check_and_consume(TokenType::COMMA)) {
                continue;
            }
            check_and_consume(TokenType::RIGHT_PAREN);
            break;
        }
    }

    bool has_void_param = params.size() == 1 &&
        isa<ParamDecl>(params.front().get()) &&
        cast<ParamDecl>(params.front().get())->type &&
        cast<ParamDecl>(params.front().get())->type->isVoid();
    if (has_void_param && is_variadic) {
        error("'void' parameter cannot be combined with '...'");
    }
    if (has_void_param && !is_variadic) {
        auto* void_param = cast<ParamDecl>(params.front().get());
        if (!void_param->has_name() &&
            !void_param->is_parameter_pack &&
            void_param->type.get_qualifiers() == QUAL_NONE &&
            !get_param_decl_default_argument(void_param)) {
            params.clear();
            param_types.clear();
            parameter_pack_flags.clear();
        }
    }

    bool saw_invalid_cvref = false;
    SrcLoc invalid_cvref_loc;
    while (true) {
        if (gentle_check(TokenType::CONST) || gentle_check(TokenType::VOLATILE)) {
            if (!saw_invalid_cvref) {
                invalid_cvref_loc = current_token().loc;
            }
            saw_invalid_cvref = true;
            advance();
            continue;
        }
        if (gentle_check(TokenType::BITWISE_AND)) {
            if (!saw_invalid_cvref) {
                invalid_cvref_loc = current_token().loc;
            }
            saw_invalid_cvref = true;
            advance();
            if (gentle_check(TokenType::BITWISE_AND)) {
                advance();
            }
            continue;
        }
        break;
    }
    if (saw_invalid_cvref) {
        error_custloc("constructor cannot have cv/ref qualifier", invalid_cvref_loc);
    }

    bool ctor_has_exception_spec = false;
    FunctionExceptionSpecKind ctor_exception_spec =
        FunctionExceptionSpecKind::PotentiallyThrowing;
    std::shared_ptr<Expr> ctor_exception_spec_expr = nullptr;
    if (gentle_check(TokenType::NOEXCEPT_KW)) {
        FunctionType spec_probe;
        Collect::CppThisContext noexcept_cpp_this_context;
        QualType noexcept_record_lookup_type;
        bool has_noexcept_cpp_this_context =
            build_cpp_current_record_declarator_expression_context(
                false,
                QUAL_NONE,
                noexcept_cpp_this_context,
                noexcept_record_lookup_type);
        parse_cpp_optional_noexcept_spec(
            spec_probe,
            has_noexcept_cpp_this_context ? &noexcept_cpp_this_context : nullptr,
            noexcept_record_lookup_type);
        ctor_has_exception_spec = spec_probe.has_explicit_exception_spec;
        ctor_exception_spec = spec_probe.exception_spec;
        ctor_exception_spec_expr = spec_probe.exception_spec_expr;
    }

    auto trailing_attrs = try_parse_attributes();
    std::unique_ptr<Expr> trailing_requires_clause = nullptr;
    if (lang_opts.is_cxx20_or_later() &&
        gentle_check(TokenType::REQUIRES_KW)) {
        advance(); // consume 'requires'
        trailing_requires_clause = parse_cpp_constraint_expression();
        if (!trailing_requires_clause) {
            error("invalid trailing requires-clause");
        }
    }
    bool is_function_try_block = false;
    size_t function_try_begin_token_idx = 0;
    if (gentle_check(TokenType::TRY_KW)) {
        is_function_try_block = true;
        function_try_begin_token_idx = get_token_idx();
        advance(); // 'try'
    }

    std::vector<CppCtorInitializer> parsed_ctor_initializers;
    if (gentle_check(TokenType::COLON)) {
        parsed_ctor_initializers =
            parse_cpp_ctor_mem_initializer_list(record_name);
    }

    bool is_deleted = false;
    bool is_defaulted = false;
    if (gentle_check(TokenType::ASSIGN)) {
        SrcLoc suffix_loc = current_token().loc;
        advance(); // '='
        if (gentle_check(TokenType::DEFAULT)) {
            is_defaulted = true;
            advance(); // 'default'
        } else if (gentle_check(TokenType::DELETE)) {
            is_deleted = true;
            advance(); // 'delete'
        } else {
            fail_cpp_unsupported("constructor declaration suffix", suffix_loc);
        }
    }

    auto ctor_fn_type = std::make_shared<FunctionType>();
    ctor_fn_type->ret_type = QualType(type_ctx->get_builtin(BuiltinTypes::Void));
    ctor_fn_type->parameters = param_types;
    ctor_fn_type->parameter_pack_flags = parameter_pack_flags;
    ctor_fn_type->normalize_parameter_pack_flags();
    ctor_fn_type->is_variadic = is_variadic;
    ctor_fn_type->has_prototype = has_prototype;
    ctor_fn_type->has_explicit_exception_spec = ctor_has_exception_spec;
    ctor_fn_type->exception_spec = ctor_exception_spec;
    ctor_fn_type->exception_spec_expr = ctor_exception_spec_expr;
    validate_function_parameter_auto_placeholders(
        ctor_fn_type,
        ctor_name_tok.loc);
    TemplateParameterList ctor_abbreviated_template_parameters;
    if (function_type_has_ordinary_cxx_auto_parameters(ctor_fn_type)) {
        TemplateParameterList local_abbreviated_template_parameters;
        TemplateParameterList* target_template_parameters =
            active_abbreviated_function_template_parameters();
        if (!target_template_parameters) {
            target_template_parameters =
                &local_abbreviated_template_parameters;
        }
        lower_cxx_auto_function_parameter_placeholders(
            params,
            ctor_fn_type,
            *target_template_parameters,
            active_abbreviated_function_template_parameter_depth(),
            ctor_name_tok.loc);
        if (!active_abbreviated_function_template_parameters()) {
            ctor_abbreviated_template_parameters =
                std::move(local_abbreviated_template_parameters);
        }
    }

    auto ctor_decl = make_ast<CppConstructorDecl>(
        *ast_ctx,
        record_name,
        ctor_fn_type,
        std::move(params),
        nullptr,
        std::unordered_set<std::string>{},
        StorageClass::NONE,
        is_inline,
        explicit_specifier.effective_value,
        ctor_name_tok.loc);
    ctor_decl->type = ctor_fn_type;
    ctor_decl->explicit_specifier = std::move(explicit_specifier);
    ctor_decl->is_constexpr = is_constexpr;
    ctor_decl->is_consteval = is_consteval;
    if (ctor_decl->is_consteval) {
        ctor_decl->is_constexpr = true;
        ctor_decl->is_inline = true;
    }
    ctor_decl->is_deleted = is_deleted;
    ctor_decl->is_defaulted = is_defaulted;
    ctor_decl->trailing_requires_clause =
        std::move(trailing_requires_clause);
    ctor_decl->is_defaulted_on_first_declaration =
        is_defaulted && is_parsing_cpp_record_body();
    ctor_decl->set_language_linkage(current_decl_language_linkage());
    ctor_decl->ctor_initializers = std::move(parsed_ctor_initializers);
    ast_ctx->append_attrs(ctor_decl->node_id, std::move(leading_attrs));

    std::string ctor_qualifier_prefix;
    if (auto* existing_prefix = get_func_decl_cxx_qualifier_prefix(ctor_decl.get())) {
        ctor_qualifier_prefix = *existing_prefix;
    }
    qualified_name_utils::ensure_namespace_qualifier_prefix_for_scope(
        collect_->collect_current_scope(), ctor_qualifier_prefix);
    std::string record_qualifier_prefix = current_cpp_record_qualifier_prefix();
    if (!record_qualifier_prefix.empty()) {
        if (!ctor_qualifier_prefix.empty()) {
            ctor_qualifier_prefix += "::";
        }
        ctor_qualifier_prefix += record_qualifier_prefix;
    }
    if (!ctor_qualifier_prefix.empty()) {
        set_func_decl_cxx_qualifier_prefix(ctor_decl.get(), ctor_qualifier_prefix);
    }

    auto owner_type =
        record_frame.semantic_owner
            ? record_frame.semantic_owner->get_record_type()
            : nullptr;
    if (!owner_type) {
        auto owner_type_raw = collect_->collect_lookup_tag_type(record_name, false);
        owner_type = dyn_cast_shared<ObjectType>(owner_type_raw);
    }
    if (owner_type) {
        QualType this_type(
            std::make_shared<PointerType>(QualType(owner_type)));
        auto this_param = collect_->collect_parameter_declaration(
            this_type, "this", nullptr, StorageClass::NONE, ctor_name_tok.loc);
        ctor_decl->parameters.insert(
            ctor_decl->parameters.begin(), std::move(this_param));
        auto fn_type = dyn_cast_shared<FunctionType>(ctor_decl->type);
        if (fn_type) {
            fn_type->insert_parameter(0, this_type);
            fn_type->has_prototype = true;
        }
    }

    if (is_deleted || is_defaulted) {
        ctor_decl->is_inline =
            cpp_in_class_definition_is_inline(ctor_decl->is_inline, true);
        if (!ctor_decl->ctor_initializers.empty()) {
            error("defaulted/deleted constructor cannot have a member initializer list");
        }
        if (is_defaulted) {
            ctor_decl->body = make_ast<CompoundStmt>(
                *ast_ctx,
                std::vector<std::unique_ptr<Stmt>>{},
                ctor_name_tok.loc);
        }
        check_and_consume(TokenType::SEMICOLON);
        ast_ctx->append_attrs(ctor_decl->node_id, std::move(trailing_attrs));
        std::unique_ptr<Decl> ctor_result = std::move(ctor_decl);
        return wrap_abbreviated_function_template_if_needed(
            std::move(ctor_result),
            std::move(ctor_abbreviated_template_parameters),
            ctor_name_tok.loc,
            false);
    }

    bool has_inline_body = gentle_check(TokenType::LEFT_BRACE);
    if (is_function_try_block) {
        ctor_decl->is_inline =
            cpp_in_class_definition_is_inline(ctor_decl->is_inline, true);
        if (!gentle_check(TokenType::LEFT_BRACE)) {
            error("constructor function-try-block requires a function body");
        }
        size_t body_begin_token_idx = function_try_begin_token_idx;
        skip_cpp_function_try_block_tail_tokens();
        size_t body_end_token_idx = get_token_idx();
        ctor_decl->set_deferred_inline_body_token_range(
            body_begin_token_idx, body_end_token_idx);
    } else if (has_inline_body) {
        ctor_decl->is_inline =
            cpp_in_class_definition_is_inline(ctor_decl->is_inline, true);
        size_t body_begin_token_idx = get_token_idx();
        skip_balanced_token_sequence_tokens(
            TokenType::LEFT_BRACE,
            TokenType::RIGHT_BRACE,
            "expected '}' to close constructor body");
        size_t body_end_token_idx = get_token_idx();
        ctor_decl->set_deferred_inline_body_token_range(
            body_begin_token_idx, body_end_token_idx);
    } else {
        if (!ctor_decl->ctor_initializers.empty()) {
            error("constructor with mem-initializer-list requires a function body");
        }
        check_and_consume(TokenType::SEMICOLON);
    }

    ast_ctx->append_attrs(ctor_decl->node_id, std::move(trailing_attrs));
    std::unique_ptr<Decl> ctor_result = std::move(ctor_decl);
    return wrap_abbreviated_function_template_if_needed(
        std::move(ctor_result),
        std::move(ctor_abbreviated_template_parameters),
        ctor_name_tok.loc,
        false);
}

std::unique_ptr<Decl> Parser::parse_cpp_destructor_member() {
    if (!is_cxx_mode_active() || cxx_record_parse_stack_.empty()) {
        error("internal error: destructor parser invoked outside C++ class scope");
    }
    const auto& record_frame = cxx_record_parse_stack_.back();
    if (record_frame.name.empty()) {
        error("internal error: destructor parser requires a named class context");
    }
    const std::string& record_name = record_frame.name;

    bool is_constexpr = false;
    bool is_inline = false;
    std::vector<ParsedAttribute> leading_attrs;
    while (true) {
        if (gentle_check(TokenType::CONSTEXPR_KW)) {
            if (!lang_opts.is_cxx20_or_later()) {
                error_custloc("'constexpr' destructor is only available in C++20",
                              current_token().loc);
            }
            if (is_constexpr) {
                error_custloc("duplicate 'constexpr' specifier", current_token().loc);
            }
            is_constexpr = true;
            advance();
            continue;
        }
        if (gentle_check(TokenType::CONSTEVAL_KW)) {
            error_custloc("destructor cannot be consteval", current_token().loc);
        }
        if (gentle_check(TokenType::INLINE)) {
            if (is_inline) {
                error_custloc("duplicate 'inline' specifier", current_token().loc);
            }
            is_inline = true;
            advance();
            continue;
        }
        if (is_gnu_attribute_token(current_token()) ||
            gentle_check(TokenType::ALIGNAS) ||
            (gentle_check(TokenType::LEFT_BRACKET) &&
             peek_token().type == TokenType::LEFT_BRACKET)) {
            auto parsed_attrs = try_parse_attributes();
            leading_attrs.insert(
                leading_attrs.end(),
                std::make_move_iterator(parsed_attrs.begin()),
                std::make_move_iterator(parsed_attrs.end()));
            continue;
        }
        break;
    }

    Token tilde_tok = current_token();
    if (!gentle_check(TokenType::BITWISE_NOT)) {
        error("expected '~' to begin destructor declaration");
    }
    advance(); // '~'

    Token dtor_name_tok = current_token();
    if (!gentle_check(TokenType::IDENTIFIER) ||
        current_token().value != record_name) {
        error("expected destructor name '~" + record_name + "'");
    }
    advance(); // consume destructor name

    check_and_consume(TokenType::LEFT_PAREN);
    if (!gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
        if (gentle_check(TokenType::VOID) &&
            peek_token().type == TokenType::RIGHT_PAREN) {
            advance(); // consume 'void'
            check_and_consume(TokenType::RIGHT_PAREN);
        } else {
            SrcLoc invalid_param_loc = current_token().loc;
            while (!gentle_check(TokenType::RIGHT_PAREN) &&
                   !gentle_check(TokenType::Eof)) {
                advance();
            }
            gentle_check_and_consume(TokenType::RIGHT_PAREN);
            error_custloc("destructor cannot have parameters", invalid_param_loc);
        }
    }

    bool saw_invalid_cvref = false;
    SrcLoc invalid_cvref_loc;
    while (true) {
        if (gentle_check(TokenType::CONST) || gentle_check(TokenType::VOLATILE)) {
            if (!saw_invalid_cvref) {
                invalid_cvref_loc = current_token().loc;
            }
            saw_invalid_cvref = true;
            advance();
            continue;
        }
        if (gentle_check(TokenType::BITWISE_AND)) {
            if (!saw_invalid_cvref) {
                invalid_cvref_loc = current_token().loc;
            }
            saw_invalid_cvref = true;
            advance();
            if (gentle_check(TokenType::BITWISE_AND)) {
                advance();
            }
            continue;
        }
        break;
    }
    if (saw_invalid_cvref) {
        error_custloc("destructor cannot have cv/ref qualifier", invalid_cvref_loc);
    }

    bool dtor_has_exception_spec = false;
    FunctionExceptionSpecKind dtor_exception_spec =
        FunctionExceptionSpecKind::PotentiallyThrowing;
    std::shared_ptr<Expr> dtor_exception_spec_expr = nullptr;
    if (gentle_check(TokenType::NOEXCEPT_KW)) {
        FunctionType spec_probe;
        Collect::CppThisContext noexcept_cpp_this_context;
        QualType noexcept_record_lookup_type;
        bool has_noexcept_cpp_this_context =
            build_cpp_current_record_declarator_expression_context(
                false,
                QUAL_NONE,
                noexcept_cpp_this_context,
                noexcept_record_lookup_type);
        parse_cpp_optional_noexcept_spec(
            spec_probe,
            has_noexcept_cpp_this_context ? &noexcept_cpp_this_context : nullptr,
            noexcept_record_lookup_type);
        dtor_has_exception_spec = spec_probe.has_explicit_exception_spec;
        dtor_exception_spec = spec_probe.exception_spec;
        dtor_exception_spec_expr = spec_probe.exception_spec_expr;
    }

    bool is_override = false;
    bool is_final = false;
    while (gentle_check(TokenType::IDENTIFIER)) {
        const std::string& spelling = current_token().value;
        if (spelling == "override") {
            if (is_override) {
                error("duplicate 'override' specifier");
            }
            is_override = true;
            advance();
            continue;
        }
        if (spelling == "final") {
            if (is_final) {
                error("duplicate 'final' specifier");
            }
            is_final = true;
            advance();
            continue;
        }
        break;
    }

    auto trailing_attrs = try_parse_attributes();
    std::unique_ptr<Expr> trailing_requires_clause = nullptr;
    if (lang_opts.is_cxx20_or_later() &&
        gentle_check(TokenType::REQUIRES_KW)) {
        advance(); // consume 'requires'
        trailing_requires_clause = parse_cpp_constraint_expression();
        if (!trailing_requires_clause) {
            error("invalid trailing requires-clause");
        }
    }

    bool is_deleted = false;
    bool is_defaulted = false;
    bool is_pure = false;
    if (gentle_check(TokenType::ASSIGN)) {
        SrcLoc suffix_loc = current_token().loc;
        advance(); // '='
        if (gentle_check(TokenType::DEFAULT)) {
            is_defaulted = true;
            advance(); // 'default'
        } else if (gentle_check(TokenType::DELETE)) {
            is_deleted = true;
            advance(); // 'delete'
        } else if (gentle_check(TokenType::INTEGER_CONST) &&
                   current_token().value == "0") {
            is_pure = true;
            advance(); // '0'
        } else {
            fail_cpp_unsupported("destructor declaration suffix", suffix_loc);
        }
    }

    auto dtor_fn_type = std::make_shared<FunctionType>();
    dtor_fn_type->ret_type = QualType(type_ctx->get_builtin(BuiltinTypes::Void));
    dtor_fn_type->is_variadic = false;
    dtor_fn_type->has_prototype = true;
    dtor_fn_type->has_explicit_exception_spec = dtor_has_exception_spec;
    dtor_fn_type->exception_spec = dtor_exception_spec;
    dtor_fn_type->exception_spec_expr = dtor_exception_spec_expr;

    std::vector<std::unique_ptr<Decl>> params;
    auto dtor_decl = make_ast<CppDestructorDecl>(
        *ast_ctx,
        "~" + record_name,
        dtor_fn_type,
        std::move(params),
        nullptr,
        std::unordered_set<std::string>{},
        StorageClass::NONE,
        is_inline,
        tilde_tok.loc);
    dtor_decl->type = dtor_fn_type;
    dtor_decl->is_constexpr = is_constexpr;
    dtor_decl->trailing_requires_clause =
        std::move(trailing_requires_clause);
    dtor_decl->is_deleted = is_deleted;
    dtor_decl->is_defaulted = is_defaulted;
    dtor_decl->is_defaulted_on_first_declaration =
        is_defaulted && is_parsing_cpp_record_body();
    dtor_decl->is_override = is_override;
    dtor_decl->is_final = is_final;
    dtor_decl->is_pure = is_pure;
    dtor_decl->set_language_linkage(current_decl_language_linkage());
    ast_ctx->append_attrs(dtor_decl->node_id, std::move(leading_attrs));

    std::string dtor_qualifier_prefix;
    if (auto* existing_prefix = get_func_decl_cxx_qualifier_prefix(dtor_decl.get())) {
        dtor_qualifier_prefix = *existing_prefix;
    }
    qualified_name_utils::ensure_namespace_qualifier_prefix_for_scope(
        collect_->collect_current_scope(), dtor_qualifier_prefix);
    std::string record_qualifier_prefix = current_cpp_record_qualifier_prefix();
    if (!record_qualifier_prefix.empty()) {
        if (!dtor_qualifier_prefix.empty()) {
            dtor_qualifier_prefix += "::";
        }
        dtor_qualifier_prefix += record_qualifier_prefix;
    }
    if (!dtor_qualifier_prefix.empty()) {
        set_func_decl_cxx_qualifier_prefix(dtor_decl.get(), dtor_qualifier_prefix);
    }

    auto owner_type =
        record_frame.semantic_owner
            ? record_frame.semantic_owner->get_record_type()
            : nullptr;
    if (!owner_type) {
        auto owner_type_raw = collect_->collect_lookup_tag_type(record_name, false);
        owner_type = dyn_cast_shared<ObjectType>(owner_type_raw);
    }
    if (owner_type) {
        QualType this_type(
            std::make_shared<PointerType>(QualType(owner_type)));
        auto this_param = collect_->collect_parameter_declaration(
            this_type, "this", nullptr, StorageClass::NONE, dtor_name_tok.loc);
        dtor_decl->parameters.insert(
            dtor_decl->parameters.begin(), std::move(this_param));
        auto fn_type = dyn_cast_shared<FunctionType>(dtor_decl->type);
        if (fn_type) {
            fn_type->insert_parameter(0, this_type);
            fn_type->has_prototype = true;
        }
    }

    if (is_deleted || is_defaulted || is_pure) {
        dtor_decl->is_inline =
            cpp_in_class_definition_is_inline(
                dtor_decl->is_inline,
                is_deleted || is_defaulted);
        if (is_defaulted) {
            dtor_decl->body = make_ast<CompoundStmt>(
                *ast_ctx,
                std::vector<std::unique_ptr<Stmt>>{},
                tilde_tok.loc);
        }
        check_and_consume(TokenType::SEMICOLON);
        ast_ctx->append_attrs(dtor_decl->node_id, std::move(trailing_attrs));
        return dtor_decl;
    }

    bool has_function_try_block = gentle_check(TokenType::TRY_KW);
    bool has_inline_body =
        has_function_try_block || gentle_check(TokenType::LEFT_BRACE);
    if (is_pure && has_inline_body) {
        error("pure virtual destructor cannot have a function body");
    }
    if (has_function_try_block) {
        dtor_decl->is_inline =
            cpp_in_class_definition_is_inline(dtor_decl->is_inline, true);
        size_t body_begin_token_idx = get_token_idx();
        skip_cpp_function_try_block_tokens(false);
        size_t body_end_token_idx = get_token_idx();
        dtor_decl->set_deferred_inline_body_token_range(
            body_begin_token_idx, body_end_token_idx);
    } else if (has_inline_body) {
        dtor_decl->is_inline =
            cpp_in_class_definition_is_inline(dtor_decl->is_inline, true);
        size_t body_begin_token_idx = get_token_idx();
        skip_balanced_token_sequence_tokens(
            TokenType::LEFT_BRACE,
            TokenType::RIGHT_BRACE,
            "expected '}' to close destructor body");
        size_t body_end_token_idx = get_token_idx();
        dtor_decl->set_deferred_inline_body_token_range(
            body_begin_token_idx, body_end_token_idx);
    } else {
        check_and_consume(TokenType::SEMICOLON);
    }

    ast_ctx->append_attrs(dtor_decl->node_id, std::move(trailing_attrs));
    return dtor_decl;
}

std::unique_ptr<Decl> Parser::parse_cpp_record_specifier(
    std::vector<TemplateArgument>* specialization_arguments_out,
    bool* has_specialization_argument_list_out,
    bool suppress_placeholder_type,
    const ClassTemplateDecl* current_primary_class_template) {
    Token key_tok = current_token();
    CppRecordKind record_kind = CppRecordKind::Class;
    switch (key_tok.type) {
        case TokenType::CLASS:
            record_kind = CppRecordKind::Class;
            break;
        case TokenType::STRUCT:
            record_kind = CppRecordKind::Struct;
            break;
        case TokenType::UNION:
            record_kind = CppRecordKind::Union;
            break;
        default:
            fail_cpp_unsupported("record declaration key", key_tok.loc);
    }
    advance(); // consume class/struct/union key

    auto head_attrs = try_parse_attributes();

    std::string name;
    if (gentle_check(TokenType::IDENTIFIER)) {
        name = current_token().value;
        advance();
    }

    if (has_specialization_argument_list_out) {
        *has_specialization_argument_list_out = false;
    }
    if (specialization_arguments_out && gentle_check(TokenType::LESS_THAN)) {
        if (has_specialization_argument_list_out) {
            *has_specialization_argument_list_out = true;
        }
        *specialization_arguments_out = parse_cpp_template_argument_list();
    }

    std::vector<CppBaseSpecifier> bases;
    if (gentle_check(TokenType::COLON)) {
        if (record_kind == CppRecordKind::Union) {
            error_custloc("union cannot have base classes", current_token().loc);
        }
        advance(); // ':'

        auto parse_base_type_name =
            [&]() -> ParsedCppTypeNameSpecifier {
                if (gentle_check(TokenType::TYPENAME)) {
                    error_custloc(
                        "'typename' is not allowed in a base-specifier",
                        current_token().loc);
                }
                size_t saved_idx = get_token_idx();
                auto saved_split_state = tok_mgnt.get_split_token_state();
                if (auto parsed = try_parse_cpp_named_type_specifier(
                        CppTypeNameParseContext::BaseSpecifier)) {
                    return *parsed;
                }
                set_token_idx(saved_idx);
                tok_mgnt.set_split_token_state(saved_split_state);

                if (gentle_check(TokenType::DECLTYPE_KW)) {
                    ParsedCppTypeNameSpecifier parsed;
                    parsed.type = parse_cpp_decltype_type_specifier();
                    parsed.spelling = parsed.type.to_string();
                    return parsed;
                }

                bool has_global_qualifier = consume_cpp_scope_resolution();
                auto parse_component =
                    [&](bool preceded_by_template_keyword)
                    -> CppQualifiedNameComponent {
                    if (!gentle_check(TokenType::IDENTIFIER)) {
                        error_custloc(
                            "expected identifier after '::' in base-specifier",
                            current_token().loc);
                    }
                    CppQualifiedNameComponent component;
                    component.name = current_token().value;
                    component.loc = current_token().loc;
                    component.preceded_by_template_keyword =
                        preceded_by_template_keyword;
                    advance();
                    if (gentle_check(TokenType::LESS_THAN)) {
                        component.has_template_argument_list = true;
                        component.template_arguments =
                            parse_cpp_template_argument_list();
                    }
                    if (component.preceded_by_template_keyword &&
                        !component.has_template_argument_list) {
                        error_custloc(
                            "expected template-id after 'template' keyword",
                            component.loc);
                    }
                    return component;
                };

                if (!gentle_check(TokenType::IDENTIFIER)) {
                    error("expected base class name");
                }

                std::vector<CppQualifiedNameComponent> components;
                components.push_back(parse_component(false));
                while (is_cpp_scope_resolution_here()) {
                    consume_cpp_scope_resolution();
                    bool preceded_by_template_keyword =
                        gentle_check_and_consume(TokenType::TEMPLATE);
                    components.push_back(
                        parse_component(preceded_by_template_keyword));
                }

                ParsedCppTypeNameSpecifier parsed;
                std::vector<std::string> qualifiers;
                qualifiers.reserve(components.size() > 0 ? components.size() - 1 : 0);
                for (size_t idx = 0; idx + 1 < components.size(); ++idx) {
                    qualifiers.push_back(components[idx].spelling());
                }
                parsed.spelling = qualified_name_utils::format_cpp_qualified_name(
                    has_global_qualifier,
                    qualifiers,
                    components.back().spelling());
                auto template_arguments_are_dependent =
                    [&](const std::vector<TemplateArgument>& arguments) {
                        for (const auto& argument : arguments) {
                            if (template_argument_depends_on_template_parameters(
                                    argument,
                                    ast_ctx.get())) {
                                return true;
                            }
                        }
                        return false;
                    };
                if (!has_global_qualifier &&
                    components.size() == 1 &&
                    current_primary_class_template &&
                    components.back().name == name &&
                    components.back().has_template_argument_list &&
                    template_arguments_are_dependent(
                        components.back().template_arguments)) {
                    parsed.type = QualType(
                        std::make_shared<TemplateSpecializationType>(
                            parsed.spelling,
                            current_primary_class_template,
                            components.back().template_arguments,
                            true));
                }
                return parsed;
            };

        while (true) {
            SrcLoc base_loc = current_token().loc;
            bool is_virtual_base = false;
            CppAccessSpecifier access = CppAccessSpecifier::None;

            bool consumed_prefix = true;
            while (consumed_prefix) {
                consumed_prefix = false;
                if (gentle_check(TokenType::VIRTUAL_KW) && !is_virtual_base) {
                    is_virtual_base = true;
                    advance();
                    consumed_prefix = true;
                    continue;
                }
                if (is_access_specifier_token(current_token().type) &&
                    access == CppAccessSpecifier::None) {
                    access = to_cpp_access_specifier(current_token().type);
                    advance();
                    consumed_prefix = true;
                    continue;
                }
            }

            ParsedCppTypeNameSpecifier base_spec = parse_base_type_name();
            bool is_pack_expansion =
                gentle_check_and_consume(TokenType::ELLIPSIS);
            if (is_pack_expansion && !is_in_template_pattern_context()) {
                error_custloc(
                    "pack expansion is only supported in template patterns",
                    current_token().loc);
            }
            if (access == CppAccessSpecifier::None) {
                access = (record_kind == CppRecordKind::Class)
                    ? CppAccessSpecifier::Private
                    : CppAccessSpecifier::Public;
            }
            bases.emplace_back(
                base_spec.spelling,
                base_spec.type,
                access,
                is_virtual_base,
                is_pack_expansion,
                base_loc);

            if (!gentle_check_and_consume(TokenType::COMMA)) {
                break;
            }
        }
    }

    if (record_kind != CppRecordKind::Union &&
        !name.empty() &&
        gentle_check(TokenType::LEFT_BRACE) &&
        !suppress_placeholder_type) {
        ensure_cpp_class_placeholder_type(name, key_tok.loc);
    }

    if (!gentle_check(TokenType::LEFT_BRACE)) {
        if (!bases.empty()) {
            error("base-clause requires a class definition");
        }
        auto record = make_ast<CppRecordDecl>(
            *ast_ctx,
            record_kind,
            std::move(name),
            std::move(bases),
            false,
            key_tok.loc);
        ast_ctx->append_attrs(record->node_id, std::move(head_attrs));
        return record;
    }

    check_and_consume(TokenType::LEFT_BRACE);

    const ObjectDecl* semantic_owner = nullptr;
    const ClassTemplateDecl* primary_class_template =
        current_primary_class_template;
    if (specialization_arguments_out &&
        has_specialization_argument_list_out &&
        *has_specialization_argument_list_out) {
        primary_class_template = nullptr;
        semantic_owner =
            ensure_cpp_specialized_record_semantic_owner(
                record_kind,
                name,
                *specialization_arguments_out,
                key_tok.loc,
                nullptr,
                true);
        if (!name.empty()) {
            auto lookup_scope = collect_->collect_current_scope();
            while (lookup_scope &&
                   scope_flags_contains(
                       lookup_scope->flags,
                       ScopeFlags::TemplateParameterScope)) {
                lookup_scope = lookup_scope->parent;
            }
            const DeclBinding* template_binding =
                LookupEngine::lookup_unqualified_template_binding(
                    name,
                    lookup_scope ? lookup_scope : collect_->collect_current_scope(),
                    true,
                    LookupNamespace::Tag);
            const Decl* primary_template = nullptr;
            if (template_binding) {
                primary_template = template_binding->template_decl;
                if (!primary_template &&
                    template_binding->template_overload_candidates.size() == 1) {
                    primary_template =
                        template_binding->template_overload_candidates.front();
                }
            }
            primary_class_template =
                dyn_cast<ClassTemplateDecl>(primary_template);
        }
    }
    if (!semantic_owner && collect_ && !name.empty()) {
        semantic_owner =
            dyn_cast<ObjectDecl>(collect_->collect_lookup_tag_decl(name, false));
    }
    if (semantic_owner &&
        primary_class_template &&
        primary_class_template == current_primary_class_template &&
        !primary_class_template->pattern_semantic_decl()) {
        auto owned_semantic_owner =
            take_cpp_transient_semantic_object_decl(name);
        if (owned_semantic_owner &&
            owned_semantic_owner.get() == semantic_owner) {
            const_cast<ClassTemplateDecl*>(primary_class_template)
                ->set_pattern_semantic_decl(std::move(owned_semantic_owner));
        } else if (owned_semantic_owner) {
            cpp_transient_semantic_decls_.push_back(
                std::move(owned_semantic_owner));
        }
    }
    QualType semantic_owner_record_type =
        semantic_owner ? QualType(semantic_owner->get_record_type()) : QualType();
    QualType current_instantiation_type;
    if (primary_class_template && !name.empty()) {
        if (primary_class_template == current_primary_class_template) {
            set_primary_template_canonical_identity(
                const_cast<ClassTemplateDecl*>(primary_class_template),
                name,
                LookupNamespace::Tag);
        }
        bool has_record_specialization_argument_list =
            has_specialization_argument_list_out &&
            *has_specialization_argument_list_out &&
            specialization_arguments_out;
        if (has_record_specialization_argument_list) {
            current_instantiation_type =
                build_cpp_current_instantiation_type(
                    primary_class_template,
                    name,
                    *specialization_arguments_out);
        } else {
            current_instantiation_type =
                build_cpp_primary_current_instantiation_type(
                    primary_class_template,
                    name,
                    key_tok.loc);
        }
    }
    cxx_record_parse_stack_.push_back(
        CppRecordParseFrame{
            record_kind,
            name,
            semantic_owner,
            primary_class_template,
            current_instantiation_type});
    struct CppRecordStackGuard {
        std::vector<Parser::CppRecordParseFrame>* stack = nullptr;
        ~CppRecordStackGuard() {
            if (stack && !stack->empty()) {
                stack->pop_back();
            }
        }
    } record_stack_guard{&cxx_record_parse_stack_};
    QualType previous_record_lookup_type =
        collect_ ? collect_->collect_current_cpp_record_lookup_type() : QualType();
    struct CppRecordLookupGuard {
        Collect* collect = nullptr;
        QualType previous_type = nullptr;
        ~CppRecordLookupGuard() {
            if (collect) {
                collect->collect_set_current_cpp_record_lookup_type(previous_type);
            }
        }
    } record_lookup_guard{collect_.get(), previous_record_lookup_type};
    if (collect_ && semantic_owner_record_type) {
        collect_->collect_set_current_cpp_record_lookup_type(
            semantic_owner_record_type);
    }
    if (collect_ && semantic_owner && semantic_owner_record_type &&
        !bases.empty()) {
        CppRecordDecl provisional_record(
            record_kind,
            name,
            bases,
            true,
            key_tok.loc);
        provisional_record.provisional_semantic_owner = semantic_owner;
        collect_->collect_publish_cpp_record_provisional_bases(
            provisional_record,
            const_cast<ObjectDecl*>(semantic_owner));
    }
    struct CppRecordScopeGuard {
        Collect* collect = nullptr;
        bool active = false;
        ~CppRecordScopeGuard() {
            if (collect && active) {
                collect->collect_leave_scope();
            }
        }
    } record_scope_guard{};
    if (collect_) {
        collect_->collect_enter_scope(ScopeFlags::RecordScope);
        record_scope_guard.collect = collect_.get();
        record_scope_guard.active = true;
    }

    auto encode_member_access = [](CppAccessSpecifier access) {
        switch (access) {
            case CppAccessSpecifier::Public:
                return RecordMemberAccess::Public;
            case CppAccessSpecifier::Protected:
                return RecordMemberAccess::Protected;
            case CppAccessSpecifier::Private:
                return RecordMemberAccess::Private;
            case CppAccessSpecifier::None:
                break;
        }
        return RecordMemberAccess::Public;
    };
    auto ensure_namespace_qualifier_prefix = [&](std::string& qualifier_prefix) {
        if (!collect_ || !is_cxx_mode_active()) {
            return;
        }
        qualified_name_utils::ensure_namespace_qualifier_prefix_for_scope(
            collect_->collect_current_scope(),
            qualifier_prefix);
    };
    /*
     * This is needed because:
     * class Ghana {
     *   static const int nkrumah = 1957;
     *   int accra[nkrumah];
     *   }
     *  is valid and we need to see
     */
    auto publish_transient_record_member_semantics =
        [&](Decl* member_decl, RecordMemberAccess member_access) {
            if (!collect_ || !semantic_owner || !semantic_owner_record_type ||
                !member_decl) {
                return;
            }

            RecordSemanticState state;
            if (const auto* cached =
                    collect_->query_lookup_record_semantics(semantic_owner)) {
                state = *cached;
            }

            auto build_member_qualifier_prefix = [&]() {
                std::string qualifier_prefix =
                    semantic_owner ? semantic_owner->tag : name;
                ensure_namespace_qualifier_prefix(qualifier_prefix);
                return qualifier_prefix;
            };
            bool changed = false;
            if (auto* nested_record = dyn_cast<CppRecordDecl>(member_decl)) {
                if (nested_record->name.empty()) {
                    return;
                }
                auto* nested_owner = const_cast<ObjectDecl*>(
                    nested_record->provisional_semantic_owner);
                if (!nested_owner) {
                    nested_owner = dyn_cast<ObjectDecl>(
                        collect_->collect_lookup_tag_decl(
                            nested_record->name,
                            false));
                }
                const RecordSemanticState* nested_state =
                    nested_owner
                        ? collect_->query_lookup_record_semantics(nested_owner)
                        : nullptr;
                if (nested_record->is_definition &&
                    (!nested_owner || !nested_state ||
                     nested_state->is_incomplete)) {
                    if (is_in_template_pattern_context()) {
                        nested_owner = const_cast<ObjectDecl*>(
                            ensure_cpp_template_pattern_nested_record_semantics(
                                *nested_record));
                    } else {
                        auto nested_semantic =
                            build_cpp_record_semantic_decl(*nested_record);
                        if (auto* semantic_object =
                                dyn_cast<ObjectDecl>(nested_semantic.get())) {
                            nested_record->provisional_semantic_owner =
                                semantic_object;
                            nested_owner = semantic_object;
                        }
                        if (nested_semantic) {
                            cpp_transient_semantic_decls_.push_back(
                                std::move(nested_semantic));
                        }
                    }
                }
                if (!nested_owner || !nested_owner->get_record_type()) {
                    return;
                }
                for (const auto& existing_type : state.nested_types) {
                    if (existing_type.decl == nested_owner) {
                        return;
                    }
                }

                RecordSemanticState::NestedType nested_type;
                nested_type.name = nested_record->name;
                nested_type.type = QualType(nested_owner->get_record_type());
                nested_type.declared_access = member_access;
                nested_type.decl = nested_owner;
                state.nested_types.push_back(std::move(nested_type));
                changed = true;
            } else if (auto* typedef_decl = dyn_cast<TypedefDecl>(member_decl)) {
                for (const auto& existing_type : state.nested_types) {
                    if (existing_type.decl == typedef_decl) {
                        return;
                    }
                }

                RecordSemanticState::NestedType nested_type;
                nested_type.name = typedef_decl->name;
                nested_type.type = typedef_decl->type;
                nested_type.declared_access = member_access;
                nested_type.decl = typedef_decl;
                nested_type.symbol = typedef_decl->sym;
                state.nested_types.push_back(std::move(nested_type));
                changed = true;
            } else if (auto* static_member_decl = dyn_cast<VariableDecl>(member_decl)) {
                // todo: we can't have non-const static variable in class decl
                if (static_member_decl->storage_class != StorageClass::STATIC) {
                    return;
                }
                for (const auto& existing_member : state.static_data_members) {
                    if (existing_member.decl == static_member_decl) {
                        return;
                    }
                }

                std::shared_ptr<Symbol> static_member_sym = static_member_decl->sym;
                if (!static_member_sym) {
                    static_member_sym = std::make_shared<Symbol>(
                        static_member_decl->name,
                        SymbolKind::VARIABLE,
                        desugar_type(static_member_decl->type),
                        StorageClass::STATIC,
                        VariableLinkage::EXTERNAL,
                        static_member_decl->is_inline != 0);
                    static_member_decl->sym = static_member_sym;
                } else {
                    static_member_sym->type = desugar_type(static_member_decl->type);
                    static_member_sym->storage_class = StorageClass::STATIC;
                    static_member_sym->linkage = VariableLinkage::EXTERNAL;
                    if (static_member_decl->is_inline) {
                        static_member_sym->is_inline = true;
                    } else {
                        static_member_sym->had_non_inline_declaration = true;
                    }
                }
                static_member_sym->is_constexpr = static_member_decl->is_constexpr;
                static_member_sym->set_language_linkage(
                    static_member_decl->get_language_linkage());

                std::string qualifier_prefix =
                    semantic_owner ? semantic_owner->tag : name;
                ensure_namespace_qualifier_prefix(qualifier_prefix);
                if (!qualifier_prefix.empty()) {
                    set_symbol_cxx_qualifier_prefix(
                        static_member_sym.get(),
                        qualifier_prefix);
                }
                set_symbol_owner_record_type(
                    static_member_sym.get(),
                    semantic_owner_record_type);

                RecordSemanticState::StaticDataMember semantic_member;
                semantic_member.name = static_member_decl->name;
                semantic_member.type = static_member_decl->type;
                semantic_member.declared_access = member_access;
                semantic_member.decl = static_member_decl;
                semantic_member.symbol = std::move(static_member_sym);
                state.static_data_members.push_back(std::move(semantic_member));
                changed = true;
            } else if (auto* method_template_decl =
                           dyn_cast<FunctionTemplateDecl>(member_decl)) {
                auto* templated_function =
                    method_template_decl->function_decl();
                auto* templated_method =
                    dyn_cast<CppMethodDecl>(templated_function);
                auto* templated_ctor =
                    dyn_cast<CppConstructorDecl>(templated_function);
                if (!templated_method && !templated_ctor) {
                    return;
                }
                for (const auto& existing_method_template :
                     state.method_templates) {
                    if (existing_method_template.decl == method_template_decl) {
                        return;
                    }
                }

                std::string qualifier_prefix = build_member_qualifier_prefix();
                if (!qualifier_prefix.empty()) {
                    set_func_decl_cxx_qualifier_prefix(
                        templated_function,
                        qualifier_prefix);
                }
                set_func_decl_owner_record_type(
                    templated_function,
                    semantic_owner_record_type);

                RecordSemanticState::MethodTemplate semantic_method_template;
                semantic_method_template.name = templated_function->name;
                semantic_method_template.declared_access = member_access;
                semantic_method_template.is_static =
                    templated_method &&
                    templated_method->storage_class == StorageClass::STATIC;
                semantic_method_template.decl = method_template_decl;
                state.method_templates.push_back(
                    std::move(semantic_method_template));
                if (templated_ctor) {
                    state.definition_data.has_user_declared_constructor = true;
                }
                changed = true;
            } else if (auto* class_template_decl =
                           dyn_cast<ClassTemplateDecl>(member_decl)) {
                auto* nested_record = class_template_decl->record_decl();
                if (!nested_record || nested_record->name.empty()) {
                    return;
                }
                for (const auto& existing_nested_template :
                     state.nested_templates) {
                    if (existing_nested_template.decl == class_template_decl) {
                        return;
                    }
                }

                RecordSemanticState::NestedTemplate nested_template;
                nested_template.name = nested_record->name;
                nested_template.declared_access = member_access;
                nested_template.kind =
                    RecordSemanticState::NestedTemplateKind::Class;
                nested_template.decl = class_template_decl;
                state.nested_templates.push_back(std::move(nested_template));
                changed = true;
            } else if (auto* alias_template_decl =
                           dyn_cast<AliasTemplateDecl>(member_decl)) {
                auto* alias_decl = alias_template_decl->alias_decl();
                if (!alias_decl || alias_decl->name.empty()) {
                    return;
                }
                for (const auto& existing_nested_template :
                     state.nested_templates) {
                    if (existing_nested_template.decl == alias_template_decl) {
                        return;
                    }
                }

                RecordSemanticState::NestedTemplate nested_template;
                nested_template.name = alias_decl->name;
                nested_template.declared_access = member_access;
                nested_template.kind =
                    RecordSemanticState::NestedTemplateKind::Alias;
                nested_template.decl = alias_template_decl;
                state.nested_templates.push_back(std::move(nested_template));
                changed = true;
            } else if (auto* method_decl = dyn_cast<CppMethodDecl>(member_decl)) {
                for (const auto& existing_method : state.methods) {
                    if (existing_method.decl == method_decl) {
                        return;
                    }
                }

                std::string qualifier_prefix = build_member_qualifier_prefix();
                if (!qualifier_prefix.empty()) {
                    set_func_decl_cxx_qualifier_prefix(
                        method_decl,
                        qualifier_prefix);
                }
                set_func_decl_owner_record_type(
                    method_decl,
                    semantic_owner_record_type);

                bool is_definition = function_decl_defines_entity(method_decl);
                auto method_sym = collect_->collect_declare_function_symbol(
                    method_decl->name,
                    method_decl->type,
                    method_decl->storage_class,
                    method_decl->is_constexpr,
                    method_decl->is_consteval,
                    method_decl->is_inline,
                    is_definition,
                    method_decl->location,
                    method_decl->get_language_linkage(),
                    true,
                    method_decl->is_deleted,
                    method_decl->is_defaulted,
                    semantic_owner_record_type,
                    qualifier_prefix,
                    method_decl->trailing_requires_clause.get());
                collect_->collect_record_register_function_default_arguments(
                    method_sym,
                    method_decl,
                    method_decl->location);
                if (method_sym) {
                    if (!qualifier_prefix.empty()) {
                        set_symbol_cxx_qualifier_prefix(
                            method_sym.get(),
                            qualifier_prefix);
                    }
                    set_symbol_owner_record_type(
                        method_sym.get(),
                        semantic_owner_record_type);
                    if (is_definition) {
                        method_sym->function_definition = method_decl;
                    }
                    method_sym->function_trailing_requires_clause =
                        method_decl->trailing_requires_clause.get();
                }

                RecordSemanticState::Method semantic_method;
                semantic_method.name = method_decl->name;
                semantic_method.type = method_decl->type;
                semantic_method.declared_access = member_access;
                semantic_method.is_static =
                    method_decl->storage_class == StorageClass::STATIC;
                semantic_method.is_deleted = method_decl->is_deleted;
                semantic_method.is_defaulted = method_decl->is_defaulted;
                semantic_method.is_constexpr = method_decl->is_constexpr;
                semantic_method.is_consteval = method_decl->is_consteval;
                semantic_method.is_explicit =
                    method_decl->is_explicit_conversion;
                semantic_method.is_virtual = method_decl->is_virtual;
                semantic_method.is_override = method_decl->is_override;
                semantic_method.is_final = method_decl->is_final;
                semantic_method.is_pure = method_decl->is_pure;
                semantic_method.is_conversion_function =
                    method_decl->is_conversion_function;
                semantic_method.conversion_target_type =
                    method_decl->conversion_target_type;
                semantic_method.decl = method_decl;
                semantic_method.symbol = std::move(method_sym);
                state.methods.push_back(std::move(semantic_method));
                changed = true;
            } else if (auto* enum_decl = dyn_cast<EnumDecl>(member_decl)) {
                if (enum_decl->is_scoped()) {
                    return;
                }
                for (const auto& constant : enum_decl->constants) {
                    if (!constant) {
                        continue;
                    }
                    bool already_published = false;
                    for (const auto& existing_enumerator :
                         state.enumerator_members) {
                        if (existing_enumerator.decl == constant.get()) {
                            already_published = true;
                            break;
                        }
                    }
                    if (already_published) {
                        continue;
                    }
                    RecordSemanticState::EnumeratorMember enumerator_member;
                    enumerator_member.name = constant->name;
                    enumerator_member.declared_access = member_access;
                    enumerator_member.enum_decl = enum_decl;
                    enumerator_member.decl = constant.get();
                    enumerator_member.symbol = constant->sym;
                    state.enumerator_members.push_back(
                        std::move(enumerator_member));
                    changed = true;
                }
            }

            if (changed) {
                collect_->query_publish_record_semantics(
                    semantic_owner,
                    std::move(state));
            }
        };
    std::vector<std::unique_ptr<Decl>> members;
    RecordMemberAccess current_member_access =
        record_kind == CppRecordKind::Class
            ? RecordMemberAccess::Private
            : RecordMemberAccess::Public;
    auto append_record_member = [&](std::unique_ptr<Decl> member) {
        if (!member) {
            return;
        }
        if (auto* access_spec = dyn_cast<CppAccessSpecDecl>(member.get())) {
            current_member_access = encode_member_access(access_spec->access);
        } else {
            publish_transient_record_member_semantics(
                member.get(),
                current_member_access);
        }
        members.push_back(std::move(member));
    };

    size_t last_recovery_idx = std::numeric_limits<size_t>::max();
    while (!gentle_check(TokenType::RIGHT_BRACE) && !gentle_check(TokenType::Eof)) {
        try {
            bool member_leading_virtual = false;
            if (gentle_check(TokenType::VIRTUAL_KW)) {
                member_leading_virtual = true;
                advance();
            }

            if (is_access_specifier_token(current_token().type) &&
                peek_token().type == TokenType::COLON) {
                if (member_leading_virtual) {
                    error_custloc("expected member declaration after 'virtual'",
                                  current_token().loc);
                }
                CppAccessSpecifier access = to_cpp_access_specifier(current_token().type);
                SrcLoc access_loc = current_token().loc;
                advance(); // public/private/protected
                check_and_consume(TokenType::COLON);
                append_record_member(
                    make_ast<CppAccessSpecDecl>(*ast_ctx, access, access_loc));
                diag_engine->sync_point_reached();
                last_recovery_idx = std::numeric_limits<size_t>::max();
                continue;
            }

            if (gentle_check(TokenType::TEMPLATE)) {
                if (member_leading_virtual) {
                    error_custloc("expected member declaration after 'virtual'",
                                  current_token().loc);
                }
                auto templated_members = parse_cpp_template_declaration();
                for (auto& member : templated_members) {
                    append_record_member(std::move(member));
                }
                diag_engine->sync_point_reached();
                last_recovery_idx = std::numeric_limits<size_t>::max();
                continue;
            }
            if (gentle_check(TokenType::USING)) {
                if (member_leading_virtual) {
                    error_custloc("expected member declaration after 'virtual'",
                                  current_token().loc);
                }
                auto using_members = parse_cpp_using_alias_declaration();
                for (auto& member : using_members) {
                    append_record_member(std::move(member));
                }
                diag_engine->sync_point_reached();
                last_recovery_idx = std::numeric_limits<size_t>::max();
                continue;
            }
            if (!cxx_record_parse_stack_.empty() &&
                !cxx_record_parse_stack_.back().name.empty()) {
                const std::string& record_name = cxx_record_parse_stack_.back().name;
                bool in_named_record =
                    cxx_record_parse_stack_.back().kind != CppRecordKind::Union;
                auto skip_balanced_tokens =
                    [&](size_t& offset, TokenType open_tok, TokenType close_tok)
                    -> bool {
                        if (peek_token_shortcut(offset).type != open_tok) {
                            return false;
                        }
                        int depth = 0;
                        while (peek_token_shortcut(offset).type != TokenType::Eof) {
                            TokenType tok = peek_token_shortcut(offset).type;
                            if (tok == open_tok) {
                                ++depth;
                            } else if (tok == close_tok) {
                                --depth;
                                if (depth == 0) {
                                    ++offset;
                                    return true;
                                }
                            }
                            ++offset;
                        }
                        return false;
                    };
                auto skip_gnu_attribute = [&](size_t& offset) -> bool {
                    if (!is_gnu_attribute_token(peek_token_shortcut(offset))) {
                        return false;
                    }
                    ++offset;
                    if (peek_token_shortcut(offset).type == TokenType::LEFT_PAREN) {
                        skip_balanced_tokens(
                            offset,
                            TokenType::LEFT_PAREN,
                            TokenType::RIGHT_PAREN);
                    }
                    return true;
                };
                auto skip_cxx_attribute = [&](size_t& offset) -> bool {
                    if (peek_token_shortcut(offset).type != TokenType::LEFT_BRACKET ||
                        peek_token_shortcut(offset + 1).type != TokenType::LEFT_BRACKET) {
                        return false;
                    }
                    offset += 2;
                    while (peek_token_shortcut(offset).type != TokenType::Eof) {
                        if (peek_token_shortcut(offset).type == TokenType::RIGHT_BRACKET &&
                            peek_token_shortcut(offset + 1).type == TokenType::RIGHT_BRACKET) {
                            offset += 2;
                            return true;
                        }
                        ++offset;
                    }
                    return false;
                };
                auto skip_special_member_prefix =
                    [&](bool allow_explicit) -> size_t {
                        size_t offset = 0;
                        while (true) {
                            Token tok = peek_token_shortcut(offset);
                            if (allow_explicit &&
                                tok.type == TokenType::EXPLICIT_KW) {
                                ++offset;
                                if (peek_token_shortcut(offset).type ==
                                    TokenType::LEFT_PAREN) {
                                    skip_balanced_tokens(
                                        offset,
                                        TokenType::LEFT_PAREN,
                                        TokenType::RIGHT_PAREN);
                                }
                                continue;
                            }
                            if (tok.type == TokenType::CONSTEXPR_KW ||
                                tok.type == TokenType::CONSTEVAL_KW ||
                                tok.type == TokenType::INLINE) {
                                ++offset;
                                continue;
                            }
                            if (skip_gnu_attribute(offset)) {
                                continue;
                            }
                            if (skip_cxx_attribute(offset)) {
                                continue;
                            }
                            if (tok.type == TokenType::ALIGNAS) {
                                ++offset;
                                if (peek_token_shortcut(offset).type == TokenType::LEFT_PAREN) {
                                    skip_balanced_tokens(
                                        offset,
                                        TokenType::LEFT_PAREN,
                                        TokenType::RIGHT_PAREN);
                                }
                                continue;
                            }
                            return offset;
                        }
                };
                if (in_named_record) {
                    size_t constructor_name_offset =
                        skip_special_member_prefix(/*allow_explicit=*/true);
                    Token ctor_name_tok = peek_token_shortcut(constructor_name_offset);
                    bool looks_like_constructor =
                        ctor_name_tok.type == TokenType::IDENTIFIER &&
                        ctor_name_tok.value == record_name &&
                        peek_token_shortcut(constructor_name_offset + 1).type ==
                            TokenType::LEFT_PAREN;
                    if (looks_like_constructor) {
                        if (member_leading_virtual) {
                            error_custloc(
                                "constructor cannot be declared 'virtual'",
                                current_token().loc);
                        }
                        auto ctor_member = parse_cpp_constructor_member();
                        if (ctor_member) {
                            append_record_member(std::move(ctor_member));
                            diag_engine->sync_point_reached();
                            last_recovery_idx = std::numeric_limits<size_t>::max();
                            continue;
                        }
                    }
                }
                size_t destructor_prefix_offset =
                    skip_special_member_prefix(/*allow_explicit=*/false);
                if (peek_token_shortcut(destructor_prefix_offset).type ==
                        TokenType::BITWISE_NOT &&
                    peek_token_shortcut(destructor_prefix_offset + 1).type ==
                        TokenType::IDENTIFIER &&
                    peek_token_shortcut(destructor_prefix_offset + 1).value ==
                        record_name &&
                    peek_token_shortcut(destructor_prefix_offset + 2).type ==
                        TokenType::LEFT_PAREN) {
                    auto dtor_member = parse_cpp_destructor_member();
                    if (member_leading_virtual) {
                        if (auto* dtor_decl = dyn_cast<CppDestructorDecl>(dtor_member.get())) {
                            dtor_decl->is_virtual = true;
                        }
                    }
                    if (dtor_member) {
                        append_record_member(std::move(dtor_member));
                        diag_engine->sync_point_reached();
                        last_recovery_idx = std::numeric_limits<size_t>::max();
                        continue;
                    }
                }
            }

            if (is_cxx_mode_active() && is_cpp_record_key_token(current_token().type)) {
                if (member_leading_virtual) {
                    error_custloc("record declarations cannot be declared 'virtual'",
                                  current_token().loc);
                }

                bool consumed_nested_record_decl = false;
                RevertingTentativeParsingAction tentative(*this);
                try {
                    auto nested = parse_cpp_record_specifier();
                    if (gentle_check(TokenType::SEMICOLON)) {
                        tentative.commit();
                        check_and_consume(TokenType::SEMICOLON);
                        append_record_member(std::move(nested));
                        diag_engine->sync_point_reached();
                        last_recovery_idx = std::numeric_limits<size_t>::max();
                        consumed_nested_record_decl = true;
                    }
                } catch (const ParseError& e) {
                    if (e.message.find("C++ parser unsupported syntax:") == 0) {
                        throw;
                    }
                }

                if (consumed_nested_record_decl) {
                    continue;
                }
            }

            auto parsed_members = parse_struct_declaration(member_leading_virtual);
            for (auto& member : parsed_members) {
                append_record_member(std::move(member));
            }
            diag_engine->sync_point_reached();
            last_recovery_idx = std::numeric_limits<size_t>::max();
        } catch (ParseError& e) {
            if (is_in_tentative_context()) {
                throw;
            }
            size_t recover_start_idx = get_token_idx();
            skip_to_field_sync_point();
            if (get_token_idx() == recover_start_idx &&
                recover_start_idx == last_recovery_idx &&
                !gentle_check(TokenType::Eof)) {
                advance();
            }
            last_recovery_idx = get_token_idx();
            diag_engine->sync_point_reached();
            append_record_member(
                collect_->collect_error_declaration(e.message, e.location));
        }
    }

    check_and_consume(TokenType::RIGHT_BRACE);

    auto record = make_ast<CppRecordDecl>(
        *ast_ctx,
        record_kind,
        std::move(name),
        std::move(bases),
        std::move(members),
        true,
        key_tok.loc);
    record->provisional_semantic_owner = semantic_owner;
    ast_ctx->append_attrs(record->node_id, std::move(head_attrs));
    return record;
}
