#include "parser.h"

#include "../abi/target_info.h"
#include "../cir/layout.h"
#include "../numeric_utils.h"
#include "../token_spelling.h"

#include <algorithm>
#include <limits>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

bool is_plain_auto_type(const collect::Session& session,
                        cir::TypeId type,
                        cir::AutoTypeFlavor flavor) {
    const cir::File& file = session.file();
    cir::TypeId resolved = file.valid(type) ? file.resolved_type(type) : cir::TypeId{};
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Auto) {
        return false;
    }
    const auto* payload =
        std::get_if<cir::AutoTypePayload>(&file.type_payload(resolved));
    return payload && payload->flavor == flavor;
}

std::optional<uint32_t> direct_template_value_parameter(
    collect::Session& session,
    const collect::ExprResult& expression) {
    uint32_t entity_parameter =
        session.template_value_param_index(expression.entity);
    if (entity_parameter != cir::TemplateValueExprNoParameter) {
        return entity_parameter;
    }
    cir::TemplateValueExpression recipe =
        session.template_value_operand_expression(expression);
    if (!recipe.valid()) {
        return std::nullopt;
    }
    uint32_t node_index = recipe.root;
    while (node_index < recipe.nodes.size() &&
           recipe.nodes[node_index].kind ==
               cir::TemplateValueExprKind::Cast) {
        node_index = recipe.nodes[node_index].lhs;
    }
    if (node_index >= recipe.nodes.size()) {
        return std::nullopt;
    }
    const cir::TemplateValueExprNode& node = recipe.nodes[node_index];
    if (node.kind != cir::TemplateValueExprKind::Parameter ||
        node.parameter_index == cir::TemplateValueExprNoParameter) {
        return std::nullopt;
    }
    return node.parameter_index;
}

collect::DeclFlags declaration_flags_from(bool is_constexpr,
                                          bool is_consteval,
                                          bool is_constinit,
                                          bool is_inline,
                                          bool is_thread_local,
                                          bool is_extern,
                                          bool is_static,
                                          bool is_auto_storage,
                                          bool is_register,
                                          bool is_mutable,
                                          bool is_friend,
                                          bool is_block_byref) {
    collect::DeclFlags flags;
    flags.is_constexpr = is_constexpr;
    flags.is_consteval = is_consteval;
    flags.is_constinit = is_constinit;
    flags.is_inline = is_inline;
    flags.is_thread_local = is_thread_local;
    flags.is_extern = is_extern;
    flags.is_static = is_static;
    flags.is_auto_storage = is_auto_storage;
    flags.is_register = is_register;
    flags.is_mutable = is_mutable;
    flags.is_friend = is_friend;
    flags.is_block_byref = is_block_byref;
    return flags;
}

} // namespace

cir::TypeId Parser::deduce_auto_copy_list_type(
    const collect::ExprResult& initializer,
    SrcLoc loc) {
    if (!initializer.init_list) {
        diagnose(DiagnosticLevel::Error,
                 "initializer-list deduction requires a braced initializer",
                 loc);
        return {};
    }
    const auto& elements = initializer.init_list->elements;
    if (elements.empty() ||
        !elements.front().designators.empty() ||
        elements.front().value.init_list ||
        !elements.front().value.type.valid()) {
        diagnose(DiagnosticLevel::Error,
                 "cannot deduce 'auto' from an empty or untyped initializer list",
                 loc);
        return {};
    }

    const cir::File& file = collect_session_.file();
    cir::TypeId element_type =
        file.resolved_type(elements.front().value.type);
    bool common_element_type = std::all_of(
        elements.begin(),
        elements.end(),
        [&](const collect::InitElementInput& element) {
            return element.designators.empty() &&
                !element.value.init_list && element.value.type.valid() &&
                file.resolved_type(element.value.type) == element_type;
        });
    if (!common_element_type) {
        diagnose(DiagnosticLevel::Error,
                 "cannot deduce a common element type for 'auto' initializer list",
                 loc);
        return {};
    }

    const collect::Session::TemplateInfo* list_template =
        collect_session_.peek_qualified_template_info(
            /*global_qualifier=*/true,
            {std::string_view("std")},
            "initializer_list");
    if (!list_template || !list_template->is_class_template) {
        diagnose(DiagnosticLevel::Error,
                 "cannot deduce 'auto' from an initializer list because "
                 "std::initializer_list is not declared",
                 loc);
        return {};
    }
    collect::Session::TemplateArgument argument;
    argument.kind = cir::TemplateArgumentKind::Type;
    argument.type = collect_session_.type_ref(element_type);
    cir::EntityId specialization = instantiate_template_with_args(
        *list_template, {argument}, loc);
    if (!specialization.valid() ||
        !collect_session_.file().valid(specialization)) {
        return {};
    }
    return collect_session_.file().entity(specialization).type;
}

Parser::ParsedDecl Parser::parse_external_declaration() {
    if (at_end()) {
        return {};
    }
    // GCC's __extension__ may prefix any declaration
    while (check(TokenType::EXTENSION_KW)) {
        consume();
    }
    if (lang_opts_.is_cxx_mode()) {
        if (check(TokenType::MODULE_KEYWORD) ||
            check(TokenType::IMPORT_KEYWORD) ||
            check(TokenType::EXPORT_KEYWORD)) {
            return parse_cxx_module_construct();
        }
        if (check(TokenType::USING)) {
            return parse_cxx_using_declaration();
        }
        if (check(TokenType::NAMESPACE)) {
            return parse_cxx_namespace_declaration();
        }
        if (check(TokenType::TEMPLATE) &&
            peek(1).type != TokenType::LESS_THAN) {
            return parse_cxx_explicit_instantiation_definition();
        }
        if (check(TokenType::TEMPLATE)) {
            return parse_cxx_template_declaration();
        }
        if (check(TokenType::EXTERN) &&
            peek(1).type == TokenType::TEMPLATE) {
            return parse_cxx_explicit_instantiation_declaration();
        }
        if (std::optional<ParsedDecl> conversion =
                try_parse_cxx_out_of_line_conversion_function_declaration()) {
            return std::move(*conversion);
        }
        if (std::optional<ParsedDecl> guide =
                try_parse_cxx_deduction_guide_declaration()) {
            return std::move(*guide);
        }
        if (check(TokenType::EXTERN) &&
            peek(1).type == TokenType::STRING_LITERAL) {
            return parse_cxx_linkage_specification();
        }
        if (check(TokenType::INLINE) &&
            peek(1).type == TokenType::NAMESPACE) {
            consume();
            return parse_cxx_namespace_declaration(/*is_inline=*/true);
        }
    }
    if (lang_opts_.is_objc() && check(TokenType::AT)) {
        return parse_objc_at_declaration();
    }
    if (lang_opts_.is_objc() &&
        (check(TokenType::EXTERN) || check(TokenType::ATTRIBUTE_KW))) {

        RevertingTentativeParsingAction probe(*this);
        while (match(TokenType::EXTERN) || check(TokenType::ATTRIBUTE_KW)) {
            if (check(TokenType::ATTRIBUTE_KW)) {
                (void)parse_gnu_attribute_list();
            }
        }
        if (check(TokenType::AT)) {
            probe.commit();
            return parse_objc_at_declaration();
        }
    }
    if (check(TokenType::STATIC_ASSERT)) {
        return parse_static_assert_declaration();
    }
    if (check(TokenType::ASM_KW)) {

        size_t begin = current_raw_index();
        SrcLoc loc = current().loc;
        consume();
        std::string asm_text;
        if (!match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected '(' after asm", current_loc());
        } else {
            ParsedAsmString parsed_string = parse_asm_string_literal("file-scope asm");
            asm_text = std::move(parsed_string.text);
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after file-scope asm",
                         current_loc());
            }
        }
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after file-scope asm",
                     current_loc());
        }
        collect_session_.collect_file_scope_asm(std::move(asm_text), loc);
        return {make_node(NodeKind::AsmStmt,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload("file-scope asm")),
                {}};
    }
    if (check(TokenType::SEMICOLON)) {

        size_t begin = current_raw_index();
        consume();
        return {make_node(NodeKind::UnknownDecl, begin, last_consumed_raw_end(), {}), {}};
    }
    if (!is_type_start(current().type) && !is_attribute_start()) {

        if ((lang_opts_.is_c_mode() ||
             current().value == "__block") &&
            current().type == TokenType::IDENTIFIER) {
            return parse_declaration(true);
        }
        size_t begin = current_raw_index();
        size_t end = skip_balanced_until_semicolon_or_brace();
        diagnose(DiagnosticLevel::Error, "expected a declaration", loc_for_index(begin));
        return {make_node(NodeKind::UnknownDecl, begin, end, {}, {}, NodeFlagHasError), {}};
    }
    return parse_declaration(true);
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_cxx_out_of_line_conversion_function_declaration() {
    if (!lang_opts_.is_cxx_mode()) {
        return std::nullopt;
    }

    auto skip_balanced_prefix = [&](size_t offset,
                                    TokenType left,
                                    TokenType right) {
        if (peek(offset).type != left) {
            return size_t{0};
        }
        int depth = 0;
        for (size_t index = offset; index < offset + 4096; ++index) {
            TokenType type = peek(index).type;
            if (type == TokenType::Eof || type == TokenType::SEMICOLON) {
                return size_t{0};
            }
            if (type == left) {
                ++depth;
            } else if (type == right && --depth == 0) {
                return index + 1;
            }
        }
        return size_t{0};
    };
    size_t prefix_tokens = 0;
    while (true) {
        TokenType type = peek(prefix_tokens).type;
        if (type == TokenType::INLINE ||
            type == TokenType::CONSTEXPR_KW ||
            type == TokenType::CONSTEVAL_KW) {
            ++prefix_tokens;
            continue;
        }
        if (type == TokenType::LEFT_BRACKET &&
            peek(prefix_tokens + 1).type == TokenType::LEFT_BRACKET) {
            size_t after = skip_balanced_prefix(
                prefix_tokens, TokenType::LEFT_BRACKET,
                TokenType::RIGHT_BRACKET);
            if (after == 0) {
                return std::nullopt;
            }
            prefix_tokens = after;
            continue;
        }
        if (type == TokenType::ATTRIBUTE_KW) {
            size_t after_keyword = prefix_tokens + 1;
            size_t after = skip_balanced_prefix(
                after_keyword, TokenType::LEFT_PAREN,
                TokenType::RIGHT_PAREN);
            if (after == 0) {
                return std::nullopt;
            }
            prefix_tokens = after;
            continue;
        }
        break;
    }
    if (!starts_qualified_conversion_function_id(prefix_tokens)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    collect::DeclFlags flags;
    ParsedAttributes leading_attrs;
    while (true) {
        if (match(TokenType::INLINE)) {
            flags.is_inline = true;
        } else if (match(TokenType::CONSTEXPR_KW)) {
            flags.is_constexpr = true;
        } else if (match(TokenType::CONSTEVAL_KW)) {
            flags.is_consteval = true;
        } else if (check(TokenType::ATTRIBUTE_KW) ||
                   (check(TokenType::LEFT_BRACKET) &&
                    peek(1).type == TokenType::LEFT_BRACKET)) {
            ParsedAttributes parsed =
                try_parse_standard_or_gnu_attributes();
            leading_attrs.attrs.append(std::move(parsed.attrs));
            leading_attrs.syntax.insert(leading_attrs.syntax.end(),
                                        parsed.syntax.begin(),
                                        parsed.syntax.end());
        } else {
            break;
        }
    }
    std::optional<ParsedConversionFunctionDeclarator> parsed =
        parse_conversion_function_declarator(/*require_qualified=*/true);
    if (!parsed) {
        return std::nullopt;
    }

    ParsedDeclarator declarator = std::move(parsed->declarator);
    declarator.has_unsupported_semantics =
        declarator.has_unsupported_semantics || parsed->has_error;
    std::vector<NodeId> children;
    children.insert(children.end(),
                    leading_attrs.syntax.begin(),
                    leading_attrs.syntax.end());
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }
    flags.attrs = std::move(leading_attrs.attrs);
    flags.attrs.append(declarator.attrs);
    FunctionDeclaratorResult function = handle_function_declarator(
        std::move(declarator), children, flags);
    if (!function.parsed_definition && !match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after conversion function declaration",
                 current_loc());
        skip_until_statement_boundary();
        function.decl.has_error = true;
    }
    return ParsedDecl{
        make_node(function.decl.has_error ? NodeKind::UnknownDecl
                                          : NodeKind::FunctionDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("conversion function"),
                  function.decl.has_error ? NodeFlagHasError
                                          : NodeFlagNone),
        std::move(function.decl)};
}

Parser::ParsedDecl Parser::parse_static_assert_declaration() {

    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '(' after '_Static_assert'",
                 current_loc());
    }
    uint64_t taint_before = collect_session_.pattern_taint();
    collect::Session::FullExpressionWatermark full_expression =
        collect_session_.begin_full_expression();
    ParsedExpr condition = parse_conditional_expression();
    bool value_dependent =
        collect_session_.pattern_taint() != taint_before ||
        collect_session_.expr_is_value_dependent(condition.sem);
    std::vector<NodeId> children{condition.syntax};
    std::string message;
    bool has_message = false;
    if (match(TokenType::COMMA)) {
        if (check(TokenType::STRING_LITERAL)) {
            size_t message_begin = current_raw_index();
            has_message = true;
            while (check(TokenType::STRING_LITERAL)) {
                message += current().value;
                consume();
            }
            children.push_back(make_node(NodeKind::StringLiteral,
                                         message_begin,
                                         last_consumed_raw_end(),
                                         {},
                                         text_payload(message)));
        } else {
            diagnose(DiagnosticLevel::Error,
                     "expected string literal for static assertion message",
                     current_loc());
        }
    }
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after static assertion",
                 current_loc());
    }
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after static assertion",
                 current_loc());
    }
    collect_session_.collect_static_assert(std::move(condition.sem),
                                           value_dependent,
                                           std::move(message),
                                           has_message,
                                           full_expression,
                                           loc);
    return {make_node(NodeKind::StaticAssertDecl,
                      begin,
                      last_consumed_raw_end(),
                      children,
                      text_payload("static_assert")),
            {}};
}

collect::DeclResult Parser::handle_typedef_declarator(const ParsedDeclarator& declarator) {
    collect::DeclFlags flags;
    flags.attrs = declarator.attrs;
    flags.type_qualifiers = declarator.type_ref.qualifiers;
    if (collect_session_.contains_auto_type(declarator.type)) {
        diagnose(DiagnosticLevel::Error,
                 "placeholder type deduction is not allowed in typedef declarations",
                 declarator.loc);
        collect::DeclResult decl;
        decl.type = declarator.type;
        decl.has_error = true;
        return decl;
    }
    return collect_session_.declare_typedef(declarator.name,
                                            declarator.type,
                                            declarator.loc,
                                            flags);
}

collect::ParamInput Parser::param_input_from_parsed_param(
    ParsedParam& param,
    bool move_runtime_fragments) {
    collect::ParamInput input;
    input.name = param.name;
    input.type = param.type_ref;
    input.loc = param.loc;
    input.attrs = param.attrs;
    input.is_parameter_pack = param.is_parameter_pack;
    input.prototype_entity = param.prototype_entity;
    input.type_originates_from_template_parameter =
        param.type_originates_from_template_parameter;
    if (move_runtime_fragments) {
        input.vla_bounds = std::move(param.vla_bounds);
    }
    if (param.has_default_argument) {
        collect::ParamInput::DefaultArgument default_argument;
        default_argument.token_begin = param.default_argument_begin;
        default_argument.token_end = param.default_argument_end;
        default_argument.loc = param.default_argument_loc;
        default_argument.declaration_context =
            param.default_argument_declaration_context.valid()
                ? param.default_argument_declaration_context
                : collect_session_.current_decl_context();
        default_argument.lookup_generation =
            param.default_argument_declaration_context.valid()
                ? param.default_argument_lookup_generation
                : collect_session_.lookup_generation();
        default_argument.requires_complete_class_replay =
            param.default_argument_requires_complete_class_replay;
        input.default_argument = default_argument;
    }
    input.source_parameter_pack_name = param.source_parameter_pack_name;
    input.is_parameter_pack_expansion_sentinel =
        param.is_parameter_pack_expansion_sentinel;
    return input;
}

std::vector<collect::ParamInput> Parser::param_inputs_from_parsed_params(
    std::vector<ParsedParam>& params,
    bool move_runtime_fragments) {
    std::vector<collect::ParamInput> inputs;
    inputs.reserve(params.size());
    for (ParsedParam& param : params) {
        inputs.push_back(param_input_from_parsed_param(
            param,
            move_runtime_fragments));
    }
    return inputs;
}

bool Parser::validate_literal_operator_declaration(
    const ParsedDeclarator& declarator,
    const collect::Session::TemplateInfo* template_info,
    bool is_friend) {
    if (declarator.operator_function.kind !=
        cir::OperatorFunctionKind::Literal) {
        return true;
    }

    bool valid = true;
    cir::DeclContextId context = collect_session_.current_decl_context();
    bool namespace_scope = false;
    for (; context.valid() && collect_session_.file().valid(context);
         context = collect_session_.file().decl_context(context).parent) {
        cir::DeclContextKind kind =
            collect_session_.file().decl_context(context).kind;
        if (kind == cir::DeclContextKind::TranslationUnit ||
            kind == cir::DeclContextKind::Namespace) {
            namespace_scope = true;
            break;
        }
        if (kind == cir::DeclContextKind::Record) {
            if (is_friend) {
                continue;
            }
            break;
        }
        if (kind == cir::DeclContextKind::Function ||
            kind == cir::DeclContextKind::Block) {
            break;
        }
    }
    if (!namespace_scope) {
        diagnose(DiagnosticLevel::Error,
                 "literal operator must be declared at namespace scope",
                 declarator.loc);
        valid = false;
    }
    if (collect_session_.in_extern_c_linkage()) {
        diagnose(DiagnosticLevel::Error,
                 "literal operator cannot have C language linkage",
                 declarator.loc);
        valid = false;
    }

    for (const ParsedParam& parameter : declarator.params) {
        if (parameter.has_default_argument) {
            diagnose(DiagnosticLevel::Error,
                     "literal operator parameters cannot have default arguments",
                     parameter.default_argument_loc.isInvalid()
                         ? parameter.loc
                         : parameter.default_argument_loc);
            valid = false;
        }
    }

    if (template_info) {
        if (!declarator.params.empty() || declarator.is_variadic) {
            diagnose(
                DiagnosticLevel::Error,
                "literal operator template must have an empty parameter-declaration-clause",
                declarator.loc);
            valid = false;
        }

        bool valid_template_head = false;
        if (template_info->parameters.size() == 1) {
            const collect::Session::TemplateParameter& parameter =
                template_info->parameters.front();
            if (parameter.kind ==
                collect::Session::TemplateParameterKind::NonType) {
                const cir::File& file = collect_session_.file();
                cir::TypeRef parameter_type =
                    collect_session_.type_ref(parameter.non_type_type);
                cir::TypeRef char_type = collect_session_.type_ref(
                    file.builtin_type(cir::BuiltinTypeKind::Char));
                bool numeric_template = parameter.is_parameter_pack &&
                    collect_session_.same_type_identity(parameter_type,
                                                        char_type);
                cir::TypeId resolved =
                    file.resolved_type(parameter.non_type_type);
                bool string_template = !parameter.is_parameter_pack &&
                    file.valid(resolved) &&
                    (file.type(resolved).kind == cir::TypeKind::Record ||
                     collect_session_.class_template_placeholder_info(
                         parameter.non_type_type) != nullptr);
                valid_template_head =
                    numeric_template || string_template;
            }
        }
        if (!valid_template_head) {
            diagnose(
                DiagnosticLevel::Error,
                "literal operator template requires one 'char' constant parameter pack or one class-type constant parameter",
                declarator.loc);
            valid = false;
        }
        return valid;
    }

    if (declarator.is_variadic ||
        std::any_of(
            declarator.params.begin(),
            declarator.params.end(),
            [](const ParsedParam& parameter) {
                return parameter.is_parameter_pack ||
                    parameter.is_parameter_pack_expansion_sentinel;
            })) {
        diagnose(DiagnosticLevel::Error,
                 "invalid literal operator parameter-declaration-clause",
                 declarator.loc);
        return false;
    }

    const cir::File& file = collect_session_.file();
    auto builtin_ref = [&](cir::BuiltinTypeKind kind) {
        return collect_session_.type_ref(file.builtin_type(kind));
    };
    auto without_top_level_cv = [](cir::TypeRef type) {
        type.qualifiers = static_cast<uint8_t>(
            type.qualifiers &
            ~(cir::QualConst | cir::QualVolatile));
        return type;
    };
    auto matches_builtin = [&](cir::TypeRef type,
                               cir::BuiltinTypeKind kind) {
        return collect_session_.same_type_identity(
            without_top_level_cv(type),
            builtin_ref(kind));
    };
    auto matches_const_character_pointer =
        [&](cir::TypeRef type, cir::BuiltinTypeKind character_kind) {
            cir::TypeRef character = builtin_ref(character_kind);
            character.qualifiers = cir::QualConst;
            cir::TypeRef pointer = collect_session_.type_ref(
                collect_session_.pointer_type(character));
            return collect_session_.same_type_identity(
                without_top_level_cv(type), pointer);
        };
    auto matches_size_type = [&](cir::TypeRef type) {
        if (matches_builtin(type, cir::BuiltinTypeKind::USize)) {
            return true;
        }
        const TargetInfo& target = file.target_info();
        cir::BuiltinTypeKind kind = cir::BuiltinTypeKind::ULongLong;
        if (target.pointer_width <= 32) {
            kind = cir::BuiltinTypeKind::UInt;
        } else if (target.pointer_width <= target.long_width) {
            kind = cir::BuiltinTypeKind::ULong;
        }
        return matches_builtin(type, kind);
    };

    bool valid_parameters = false;
    if (declarator.params.size() == 1) {
        cir::TypeRef parameter = declarator.params[0].type_ref;
        valid_parameters =
            matches_const_character_pointer(
                parameter, cir::BuiltinTypeKind::Char) ||
            matches_builtin(parameter, cir::BuiltinTypeKind::ULongLong) ||
            matches_builtin(parameter, cir::BuiltinTypeKind::LongDouble) ||
            matches_builtin(parameter, cir::BuiltinTypeKind::Char) ||
            matches_builtin(parameter, cir::BuiltinTypeKind::WChar) ||
            matches_builtin(parameter, cir::BuiltinTypeKind::Char8) ||
            matches_builtin(parameter, cir::BuiltinTypeKind::Char16) ||
            matches_builtin(parameter, cir::BuiltinTypeKind::Char32);
    } else if (declarator.params.size() == 2) {
        cir::TypeRef string = declarator.params[0].type_ref;
        cir::TypeRef size = declarator.params[1].type_ref;
        valid_parameters = matches_size_type(size) &&
            (matches_const_character_pointer(
                 string, cir::BuiltinTypeKind::Char) ||
             matches_const_character_pointer(
                 string, cir::BuiltinTypeKind::WChar) ||
             matches_const_character_pointer(
                 string, cir::BuiltinTypeKind::Char8) ||
             matches_const_character_pointer(
                 string, cir::BuiltinTypeKind::Char16) ||
             matches_const_character_pointer(
                 string, cir::BuiltinTypeKind::Char32));
    }
    if (!valid_parameters) {
        diagnose(DiagnosticLevel::Error,
                 "invalid literal operator parameter-declaration-clause",
                 declarator.loc);
        valid = false;
    }
    return valid;
}

bool Parser::validate_symbolic_operator_membership(
    const ParsedDeclarator& declarator,
    const collect::DeclFlags& flags) {
    bool names_record_member = declarator.qualified_context.valid() &&
        collect_session_.file().valid(declarator.qualified_context) &&
        collect_session_.file()
                .decl_context(declarator.qualified_context)
                .kind == cir::DeclContextKind::Record;
    if (names_record_member || declarator.operator_function.kind !=
            cir::OperatorFunctionKind::Symbolic) {
        return false;
    }

    using Spelling = cir::OperatorFunctionSpelling;
    Spelling spelling = declarator.operator_function.spelling;
    bool declared_in_record_context = false;
    for (cir::DeclContextId context =
             collect_session_.current_decl_context();
         context.valid() && collect_session_.file().valid(context);
         context = collect_session_.file().decl_context(context).parent) {
        cir::DeclContextKind kind =
            collect_session_.file().decl_context(context).kind;
        if (kind == cir::DeclContextKind::Record) {
            declared_in_record_context = true;
            break;
        }
        if (kind == cir::DeclContextKind::TranslationUnit ||
            kind == cir::DeclContextKind::Namespace ||
            kind == cir::DeclContextKind::Function ||
            kind == cir::DeclContextKind::Block) {
            break;
        }
    }
    bool nonstatic_record_member =
        declared_in_record_context && !flags.is_static;
    bool cxx26_static_call_operator =
        lang_opts_.is_cxx26_or_later() && flags.is_static &&
        declared_in_record_context && spelling == Spelling::Call;
    bool requires_operator_membership =
        spelling == Spelling::Assign || spelling == Spelling::Arrow ||
        spelling == Spelling::Call || spelling == Spelling::Subscript;
    if (!requires_operator_membership || nonstatic_record_member ||
        cxx26_static_call_operator) {
        return false;
    }

    diagnose(DiagnosticLevel::Error,
             "this overloaded operator must be a non-static member function",
             declarator.loc);
    return true;
}

Parser::FunctionDeclaratorResult Parser::handle_function_declarator(
    ParsedDeclarator declarator,
    std::vector<NodeId>& children,
    collect::DeclFlags flags) {
    if (declarator.has_unsupported_semantics) {
        if (check(TokenType::LEFT_BRACE)) {
            skip_balanced_until_semicolon_or_brace();
            collect::DeclResult decl;
            decl.type = declarator.type;
            decl.has_error = true;
            return {std::move(decl), true};
        }
        collect::DeclResult decl;
        decl.type = declarator.type;
        decl.has_error = true;
        return {std::move(decl), false};
    }
    bool deduce_return = false;
    if (declarator.is_function) {
        deduce_return = collect_session_.function_has_placeholder_return(
            declarator.type);
        const cir::File& file = collect_session_.file();
        cir::TypeId resolved = file.resolved_type(declarator.type);
        const auto* function = file.valid(resolved)
            ? std::get_if<cir::FunctionTypePayload>(
                  &file.type_payload(resolved))
            : nullptr;
        if (function && std::any_of(
                            function->parameters.begin(),
                            function->parameters.end(),
                            [&](const cir::TypeRef& parameter) {
                                return collect_session_.contains_auto_type(
                                    parameter.type);
                            })) {
            diagnose(DiagnosticLevel::Error,
                     "function parameter placeholder did not form an abbreviated function template",
                     declarator.loc);
            collect::DeclResult decl;
            decl.type = declarator.type;
            decl.has_error = true;
            return {std::move(decl), false};
        }
    }

    if (declarator.is_kr_style && !lang_opts_.is_cxx_mode()) {
        while (!at_end() && !check(TokenType::LEFT_BRACE) && is_type_start(current().type)) {
            size_t param_decl_begin = current_raw_index();
            DeclarationParser param_decl_parser(*this);
            cir::TypeRef base_type = param_decl_parser.parse_declaration(false, true);
            while (!at_end()) {
                param_decl_parser.reset_declarator_parsing_state();
                ParsedDeclarator param_decl =
                    param_decl_parser.parse_declarator(base_type, false);
                if (!param_decl.has_name) {
                    diagnose(DiagnosticLevel::Error,
                             "expected K&R parameter declaration name",
                             loc_for_index(param_decl_begin));
                    break;
                }
                auto found = std::find_if(declarator.params.begin(),
                                          declarator.params.end(),
                                          [&](const ParsedParam& param) {
                                              return param.name == param_decl.name;
                                          });
                if (found == declarator.params.end()) {
                    diagnose(DiagnosticLevel::Error,
                             "K&R parameter declaration does not name a parameter",
                             param_decl.loc);
                } else {
                    found->type = param_decl.type;
                    found->type_ref = param_decl.type_ref;
                    found->loc = param_decl.loc;
                }
                if (!match(TokenType::COMMA)) {
                    break;
                }
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after K&R parameter declaration",
                         current_loc());
                skip_until_statement_boundary();
                break;
            }
        }

        const cir::File& file = collect_session_.file();
        const auto* function_payload =
            std::get_if<cir::FunctionTypePayload>(
                &file.type_payload(file.resolved_type(declarator.type)));
        if (function_payload) {
            std::vector<cir::TypeRef> param_types;
            std::vector<uint8_t> parameter_pack_flags;
            bool has_parameter_pack = false;
            param_types.reserve(declarator.params.size());
            parameter_pack_flags.reserve(declarator.params.size());
            for (const ParsedParam& param : declarator.params) {
                if (param.is_parameter_pack_expansion_sentinel) {
                    continue;
                }
                param_types.push_back(param.type_ref);
                uint8_t pack_flag = param.is_parameter_pack ? 1 : 0;
                parameter_pack_flags.push_back(pack_flag);
                has_parameter_pack = has_parameter_pack || pack_flag != 0;
            }
            if (!has_parameter_pack) {
                parameter_pack_flags.clear();
            }
            cir::TypeId rebuilt =
                collect_session_.function_type(function_payload->return_type,
                                               param_types,
                                               declarator.is_variadic,
                                               false,
                                               function_payload->member_is_const,
                                               function_payload->exception_spec,
                                               parameter_pack_flags,
                                               function_payload->member_ref_qualifier,
                                               function_payload->member_is_volatile);
            declarator.type = rebuilt;
            declarator.type_ref = collect_session_.type_ref(rebuilt);
        }
    }

    std::vector<ParsedParam> body_params;
    if (declarator.qualified_context.valid()) {
        body_params = declarator.params;
    }
    std::vector<collect::ParamInput> collect_params;
    collect_params.reserve(declarator.params.size());
    for (ParsedParam& param : declarator.params) {
        if (param.syntax != InvalidNodeId) {
            children.push_back(param.syntax);
        }
        collect_params.push_back(
            param_input_from_parsed_param(param,
                                          /*move_runtime_fragments=*/true));
    }

    if (declarator.operator_function.kind ==
            cir::OperatorFunctionKind::Literal &&
        !validating_literal_operator_template_definition_) {
        const collect::Session::TemplateInfo* specialization =
            declarator.explicit_function_template_specialization_info;
        validate_literal_operator_declaration(
            declarator,
            specialization &&
                    specialization->operator_function.kind ==
                        cir::OperatorFunctionKind::Literal
                ? specialization
                : nullptr,
            flags.is_friend);
    }
    (void)validate_symbolic_operator_membership(declarator, flags);

    const cir::File& file = collect_session_.file();
    const auto* function_payload =
        std::get_if<cir::FunctionTypePayload>(&file.type_payload(file.resolved_type(declarator.type)));
    cir::TypeRef result_type = function_payload
        ? function_payload->return_type
        : collect_session_.type_ref(collect_session_.file().unknown_type());

    if (declarator.qualified_context.valid()) {
        return handle_out_of_line_function(declarator,
                                           std::move(body_params),
                                           std::move(collect_params),
                                           result_type,
                                           children,
                                           flags);
    }

    if (check(TokenType::TRY_KW)) {

        diagnose(DiagnosticLevel::Error,
                 "function try blocks are supported only for constructors",
                 current_loc());
        skip_function_try_block_tokens();
        FunctionDeclaratorResult result;
        result.decl.type = declarator.type;
        result.decl.has_error = true;
        result.parsed_definition = true;
        return result;
    }

    if (check(TokenType::LEFT_BRACE)) {
        auto fn = collect_session_.begin_function_type(declarator.name,
                                                       declarator.type,
                                                       result_type,
                                                       collect_params,
                                                       declarator.loc,
                                                       flags);
        if (fn.decl.entity.valid()) {
            collect_session_.file().entity_mut(fn.decl.entity)
                .operator_function = declarator.operator_function;
        }
        if (declarator.explicit_function_template_specialization_info &&
            fn.decl.entity.valid()) {
            collect_session_.remember_template_specialization(
                fn.decl.entity,
                *declarator.explicit_function_template_specialization_info,
                declarator
                    .explicit_function_template_specialization_arguments);
        }
        if (deduce_return) {
            collect_session_.begin_function_return_deduction(
                fn.decl.entity, declarator.type, declarator.loc);
        }
        ParsedStmt body = parse_compound_statement();
        children.push_back(body.syntax);
        if (deduce_return) {
            if (collect_session_.collecting_pattern()) {

                collect_session_.patch_pattern_function_result_type(
                    fn.decl.entity, declarator.type, declarator.loc);
            } else {
                collect_session_.resolve_deduced_return_type(fn.decl.entity,
                                                             declarator.type,
                                                             declarator.loc);
                if (declarator.has_placeholder_type_constraint &&
                    !validate_placeholder_return_type_constraint(
                        fn.decl.entity,
                        declarator.placeholder_type_constraint_begin,
                        declarator.placeholder_type_constraint_end,
                        declarator.placeholder_type_constraint_loc)) {
                    body.sem.has_error = true;
                }
            }
        }
        collect_session_.finish_function(std::move(body.sem), last_consumed_loc());
        return {std::move(fn.decl), true};
    }

    collect::DeclResult decl =
        collect_session_.declare_function_type(declarator.name,
                                               declarator.type,
                                               result_type,
                                               collect_params,
                                               declarator.loc,
                                               flags);
    if (decl.entity.valid()) {
        collect_session_.file().entity_mut(decl.entity).operator_function =
            declarator.operator_function;
    }
    if (declarator.explicit_function_template_specialization_info &&
        decl.entity.valid()) {
        collect_session_.remember_template_specialization(
            decl.entity,
            *declarator.explicit_function_template_specialization_info,
            declarator.explicit_function_template_specialization_arguments);
    }
    return {std::move(decl), false};
}

Parser::FunctionDeclaratorResult
Parser::handle_abbreviated_function_template(
    ParsedDeclarator declarator,
    collect::Session::TemplateInfo info,
    std::vector<NodeId>& children,
    collect::DeclFlags flags,
    size_t definition_begin,
    bool top_level) {
    (void)children;
    if (!lang_opts_.is_cxx20_or_later()) {
        diagnose(DiagnosticLevel::Error,
                 "abbreviated function templates require C++20",
                 declarator.loc);
        collect::DeclResult error;
        error.type = declarator.type;
        error.has_error = true;
        return {std::move(error), false};
    }
    if (!top_level) {
        diagnose(DiagnosticLevel::Error,
                 "abbreviated function templates cannot be declared at block scope",
                 declarator.loc);
        collect::DeclResult error;
        error.type = declarator.type;
        error.has_error = true;
        if (check(TokenType::LEFT_BRACE)) {
            skip_balanced_until_semicolon_or_brace();
            return {std::move(error), true};
        }
        return {std::move(error), false};
    }
    if (!declarator.has_name || !declarator.is_function ||
        !collect_session_.file().valid(declarator.type)) {
        collect::DeclResult error;
        error.type = declarator.type;
        error.has_error = true;
        return {std::move(error), false};
    }

    info.name = declarator.name;
    info.operator_function = declarator.operator_function;
    info.pattern_type =
        collect_session_.file().resolved_type(declarator.type);
    info.definition_begin = definition_begin;
    info.lexical_context = collect_session_.current_decl_context();
    info.has_internal_linkage = flags.is_static;
    info.declaration_attrs = flags.attrs;
    info.is_deleted = flags.is_deleted;
    record_trailing_function_requires_clause(info, declarator);

    const cir::File& file = collect_session_.file();
    bool record_qualified = declarator.qualified_context.valid() &&
        file.valid(declarator.qualified_context) &&
        file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record;
    if (record_qualified) {
        const cir::Binding* binding = file.lookup_callable_binding(
            declarator.qualified_context,
            declarator.name,
            /*include_parents=*/false);
        cir::EntityId member_template{};
        bool ambiguous = false;
        if (binding) {
            for (cir::EntityId candidate : binding->entities) {
                const collect::Session::TemplateInfo* candidate_info =
                    collect_session_.template_info(candidate);
                if (!candidate_info ||
                    !collect_session_
                         .function_template_declarations_correspond(
                             *candidate_info, info)) {
                    continue;
                }
                if (member_template.valid()) {
                    ambiguous = true;
                    break;
                }
                member_template = candidate;
            }
        }

        bool has_definition = check(TokenType::LEFT_BRACE);
        size_t body_begin = current_raw_index();
        size_t body_end = body_begin;
        if (has_definition) {
            body_end = skip_balanced_until_semicolon_or_brace();
        }
        collect::DeclResult result;
        result.type = declarator.type;
        if (ambiguous || !member_template.valid()) {
            diagnose(
                DiagnosticLevel::Error,
                ambiguous
                    ? "out-of-line abbreviated member function template definition is ambiguous"
                    : "out-of-line abbreviated member function template definition has no matching declaration",
                declarator.loc);
            result.has_error = true;
            return {std::move(result), has_definition};
        }

        info.has_definition = has_definition || info.is_deleted;
        info.definition_begin = body_begin;
        info.definition_end = body_end;
        if (has_definition) {
            size_t method_index = 0;
            cir::EntityId owner =
                file.decl_context(declarator.qualified_context).owner;
            if (const cir::RecordFacts* facts = file.record_facts(owner)) {
                for (size_t index = 0; index < facts->methods.size(); ++index) {
                    if (facts->methods[index].entity == member_template) {
                        method_index = index;
                        break;
                    }
                }
            }
            PendingMemberBody pending;
            pending.method_index = method_index;
            pending.body_begin = body_begin;
            pending.body_end = body_end;
            pending.params = declarator.params;
            if (!collect_session_.collecting_pattern() &&
                !collect_session_.is_instantiating()) {
                validate_member_template_body(
                    info, member_template, pending, declarator.loc);
            }
            uint64_t body_key =
                static_cast<uint64_t>(member_template.index);
            member_template_bodies_[body_key] = std::move(pending);
            collect_session_.track_speculative_rollback(
                [this, body_key] { member_template_bodies_.erase(body_key); });
        }
        if (!collect_session_.define_member_template_entity(
                std::move(info), member_template, declarator.loc)) {
            result.has_error = true;
        }
        result.entity = member_template;
        return {std::move(result), has_definition};
    }

    bool has_body = check(TokenType::LEFT_BRACE);
    info.has_definition = has_body || info.is_deleted;
    if (has_body) {
        info.definition_end = skip_balanced_until_semicolon_or_brace();
        validate_template_definition(info, declarator.loc);
    } else {
        info.definition_end = current_raw_index();
    }

    cir::EntityId entity =
        collect_session_.declare_template(std::move(info), declarator.loc);
    collect_session_.register_function_template_default_arguments(
        entity,
        param_inputs_from_parsed_params(
            declarator.params, /*move_runtime_fragments=*/false),
        declarator.loc);
    collect::DeclResult result;
    result.entity = entity;
    result.type = declarator.type;
    result.has_error = !entity.valid();
    return {std::move(result), has_body};
}

collect::DeclResult Parser::handle_variable_declarator(const ParsedDeclarator& declarator,
                                                       bool top_level,
                                                       std::vector<NodeId>& children,
                                                       collect::DeclFlags flags,
                                                       bool structured_binding_backing) {
    std::optional<collect::ExprResult> initializer;
    cir::TypeId declared_type = declarator.type;
    if (declarator.has_unsupported_semantics) {
        collect::DeclResult decl;
        decl.type = declarator.type;
        decl.has_error = true;
        return decl;
    }

    struct QualifiedScopeExit {
        collect::Session* session = nullptr;
        ~QualifiedScopeExit() {
            if (session) {
                session->leave_scope();
            }
        }
    } qualified_scope;
    if (declarator.qualified_context.valid()) {
        const cir::File& file = collect_session_.file();
        cir::DeclContextKind context_kind =
            file.decl_context(declarator.qualified_context).kind;
        collect::ScopeFlags scope_flags =
            context_kind == cir::DeclContextKind::Record
                ? collect::ScopeFlags::RecordScope
                : collect::ScopeFlags::NamespaceScope |
                      collect::ScopeFlags::FileScope;
        collect_session_.enter_existing_context(declarator.qualified_context,
                                                scope_flags);
        qualified_scope.session = &collect_session_;
        top_level = true;
    }

    cir::EntityId qualified_static_member =
        declarator.qualified_context.valid()
            ? collect_session_.find_record_static_data_member(
                  declarator.qualified_context,
                  declarator.name,
                  declarator.type_ref,
                  flags.is_thread_local
                      ? cir::StorageDuration::Thread
                      : cir::StorageDuration::Static)
            : cir::EntityId{};
    if (qualified_static_member.valid() && flags.is_static) {
        diagnose(DiagnosticLevel::Error,
                 "'static' can only be specified inside the class definition",
                 declarator.loc);
    }
    if (declarator.qualified_context.valid() &&
        collect_session_.file()
                .decl_context(declarator.qualified_context)
                .kind == cir::DeclContextKind::Record &&
        !qualified_static_member.valid()) {

        diagnose(DiagnosticLevel::Error,
                 "out-of-class data member definition does not match a "
                 "static data member declaration",
                 declarator.loc);

        if (match(TokenType::ASSIGN)) {
            ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
            children.push_back(init.syntax);
        } else if (check(TokenType::LEFT_BRACE)) {
            ParsedExpr init = parse_init_list_expression();
            children.push_back(init.syntax);
        } else if (lang_opts_.is_cxx_mode() &&
                   check(TokenType::LEFT_PAREN)) {
            size_t init_begin = current_raw_index();
            consume();
            std::vector<NodeId> init_children;
            if (!check(TokenType::RIGHT_PAREN)) {
                ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
                init_children.push_back(init.syntax);
                while (match(TokenType::COMMA)) {
                    ParsedExpr extra =
                        parse_expression(PrecLevel::ASSIGNMENT);
                    init_children.push_back(extra.syntax);
                }
            }
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after initializer",
                         current_loc());
            }
            children.push_back(make_node(NodeKind::InitListExpr,
                                         init_begin,
                                         last_consumed_raw_end(),
                                         init_children));
        }
        collect::DeclResult invalid;
        invalid.type = declarator.type;
        invalid.has_error = true;
        return invalid;
    }
    if (qualified_static_member.valid() &&
        collect_session_.is_instantiating() &&
        collect_session_.explicit_static_data_member_specialization_declared(
            qualified_static_member)) {
        auto consume_initializer_without_collecting = [&]() {
            size_t diagnostic_watermark = diagnostics_.size();
            collect_session_.begin_speculative_parse();
            if (match(TokenType::ASSIGN)) {
                (void)parse_expression(PrecLevel::ASSIGNMENT);
            } else if (check(TokenType::LEFT_BRACE)) {
                (void)parse_init_list_expression();
            } else if (lang_opts_.is_cxx_mode() &&
                       match(TokenType::LEFT_PAREN)) {
                if (!check(TokenType::RIGHT_PAREN)) {
                    (void)parse_expression(PrecLevel::ASSIGNMENT);
                    while (match(TokenType::COMMA)) {
                        (void)parse_expression(PrecLevel::ASSIGNMENT);
                    }
                }
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after initializer",
                             current_loc());
                }
            }
            collect_session_.rollback_speculative_parse();
            diagnostics_.resize(diagnostic_watermark);
        };
        consume_initializer_without_collecting();
        collect::DeclResult decl;
        decl.entity = qualified_static_member;
        decl.type = declarator.type;
        return decl;
    }

    bool has_init_syntax = check(TokenType::ASSIGN) ||
                           check(TokenType::LEFT_BRACE) ||
                           (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
    collect::ConstructorInitializationKind constructor_init_kind =
        check(TokenType::ASSIGN)
            ? (peek(1).type == TokenType::LEFT_BRACE
                   ? collect::ConstructorInitializationKind::CopyList
                   : collect::ConstructorInitializationKind::Copy)
            : collect::ConstructorInitializationKind::Direct;
    collect::Session::ClosureAbiContextScope closure_abi_context =
        has_init_syntax
            ? collect_session_.enter_variable_initializer_closure_context(
                  declarator.name)
            : collect::Session::ClosureAbiContextScope{};
    if (declarator.deduced_class_template_info) {
        bool has_error = false;
        if (declarator.has_declarator_operators) {
            diagnose(DiagnosticLevel::Error,
                     "deduced class type cannot use declarator operators",
                     declarator.loc);
            has_error = true;
        }
        bool has_direct_initializer =
            lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN);
        bool has_direct_list_initializer = check(TokenType::LEFT_BRACE);
        bool has_copy_initializer = check(TokenType::ASSIGN);
        if (!lang_opts_.is_cxx_mode()) {
            diagnose(DiagnosticLevel::Error,
                     "class template argument deduction requires direct, copy, or default initialization in this context",
                     declarator.loc);
            collect::DeclResult decl;
            decl.type = declared_type;
            decl.has_error = true;
            return decl;
        }

        std::vector<NodeId> init_children;
        std::vector<collect::ExprResult> direct_arguments;
        std::vector<collect::ExprResult> deduction_arguments;
        std::optional<collect::ExprResult> copy_initializer;
        std::optional<collect::ExprResult> list_initializer;
        bool has_copy_list_initializer = false;
        auto append_init_list_deduction_arguments =
            [&](const collect::ExprResult& init) {
            if (!init.init_list) {
                return;
            }
            for (const collect::InitElementInput& element :
                 init.init_list->elements) {
                if (!element.designators.empty()) {
                    continue;
                }
                deduction_arguments.push_back(element.value);
            }
        };
        if (has_direct_initializer) {
            size_t init_begin = current_raw_index();
            consume();
            ParsedExpressionList arguments =
                parse_expression_list(TokenType::RIGHT_PAREN);
            init_children = std::move(arguments.syntax);
            direct_arguments = std::move(arguments.sem);
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after initializer",
                         current_loc());
                has_error = true;
            }
            NodeId init_syntax = make_node(NodeKind::InitListExpr,
                                           init_begin,
                                           last_consumed_raw_end(),
                                           init_children);
            children.push_back(init_syntax);
            deduction_arguments = direct_arguments;
        } else if (has_direct_list_initializer) {
            ParsedExpr init = parse_init_list_expression();
            children.push_back(init.syntax);
            append_init_list_deduction_arguments(init.sem);
            list_initializer = std::move(init.sem);
        } else if (has_copy_initializer) {
            consume();
            ParsedExpr init = check(TokenType::LEFT_BRACE)
                ? parse_init_list_expression()
                : parse_expression(PrecLevel::ASSIGNMENT);
            children.push_back(init.syntax);
            if (init.sem.category == collect::ValueCategory::InitList) {
                has_copy_list_initializer = true;
                append_init_list_deduction_arguments(init.sem);
                list_initializer = std::move(init.sem);
            } else {
                deduction_arguments.push_back(init.sem);
                copy_initializer = std::move(init.sem);
            }
        }

        CtadInitializationKind initialization_kind =
            CtadInitializationKind::Default;
        if (has_direct_initializer || has_direct_list_initializer) {
            initialization_kind = CtadInitializationKind::Direct;
        } else if (has_copy_list_initializer) {
            initialization_kind = CtadInitializationKind::CopyList;
        } else if (has_copy_initializer) {
            initialization_kind = CtadInitializationKind::Copy;
        }
        bool selected_aggregate_candidate = false;
        cir::TypeId deduced_type = deduce_class_template_initialization_type(
            *declarator.deduced_class_template_info,
            deduction_arguments,
            declarator.deduced_class_template_loc.isInvalid()
                ? declarator.loc
                : declarator.deduced_class_template_loc,
            initialization_kind,
            list_initializer ? &*list_initializer : nullptr,
            &selected_aggregate_candidate);
        if (!deduced_type.valid()) {
            collect::DeclResult decl;
            decl.type = declared_type;
            decl.has_error = true;
            return decl;
        }
        declared_type = deduced_type;

        if (collect_session_.collecting_pattern() &&
            collect_session_.is_dependent_type(declared_type)) {
            collect_session_.bump_pattern_taint();
            collect::DeclResult deferred = top_level
                ? collect_session_.declare_global_variable(
                      declarator.name,
                      declared_type,
                      std::nullopt,
                      declarator.loc,
                      flags,
                      has_direct_initializer ||
                          has_direct_list_initializer ||
                          has_copy_initializer)
                : collect_session_.declare_local_variable(
                      declarator.name,
                      declared_type,
                      std::nullopt,
                      declarator.loc,
                      flags,
                      has_direct_initializer ||
                          has_direct_list_initializer ||
                          has_copy_initializer);
            deferred.has_error = deferred.has_error || has_error;
            return deferred;
        }

        collect::DeclResult started = top_level
            ? collect_session_.declare_global_variable(declarator.name,
                                                       declared_type,
                                                       std::nullopt,
                                                       declarator.loc,
                                                       flags,
                                                       has_direct_initializer ||
                                                           has_direct_list_initializer ||
                                                           has_copy_initializer)
            : collect_session_.declare_local_variable(declarator.name,
                                                      declared_type,
                                                      std::nullopt,
                                                      declarator.loc,
                                                      flags,
                                                      has_direct_initializer ||
                                                          has_direct_list_initializer ||
                                                          has_copy_initializer);
        started.has_error = started.has_error || has_error;
        if (has_direct_initializer &&
            collect_session_.record_has_user_constructor(declared_type)) {
            return collect_session_.construct_variable(std::move(started),
                                                       std::move(direct_arguments),
                                                       declarator.loc);
        }
        const cir::File& file = collect_session_.file();
        cir::TypeId resolved_declared_type =
            file.resolved_type(declared_type);
        auto direct_initializer_is_same_type_copy = [&]() {
            return direct_arguments.size() == 1 &&
                   direct_arguments.front().type.valid() &&
                   file.resolved_type(direct_arguments.front().type) ==
                       resolved_declared_type;
        };
        bool direct_type_is_record =
            file.valid(resolved_declared_type) &&
            file.type(resolved_declared_type).kind == cir::TypeKind::Record;
        bool use_aggregate_direct_initializer =
            (has_direct_initializer || has_direct_list_initializer) &&
            !collect_session_.record_has_user_constructor(declared_type) &&
            direct_type_is_record &&
            (has_direct_list_initializer ||
             selected_aggregate_candidate ||
             !direct_initializer_is_same_type_copy());

        std::optional<collect::ExprResult> initializer;
        if (list_initializer.has_value()) {
            initializer = std::move(list_initializer);
        } else if (use_aggregate_direct_initializer) {
            std::vector<collect::InitElementInput> elements;
            elements.reserve(direct_arguments.size());
            for (collect::ExprResult& argument : direct_arguments) {
                collect::InitElementInput element;
                element.value = std::move(argument);
                element.loc = declarator.loc;
                elements.push_back(std::move(element));
            }
            initializer =
                collect_session_.collect_init_list_expr(std::move(elements),
                                                        declarator.loc);
        } else if (has_copy_initializer) {
            initializer = std::move(copy_initializer);
        } else if (direct_arguments.size() == 1) {
            initializer = std::move(direct_arguments.front());
        } else if (direct_arguments.size() > 1) {
            diagnose(DiagnosticLevel::Error,
                     "direct initializers with multiple arguments require a class with a matching constructor",
                     declarator.loc);
            started.has_error = true;
        }
        return collect_session_.finish_variable_declaration(std::move(started),
                                                            declared_type,
                                                            std::move(initializer),
                                                            declarator.loc,
                                                            flags,
                                                            declarator.name,
                                                            constructor_init_kind);
    }
    bool two_phase = !collect_session_.contains_auto_type(declared_type);
    collect::DeclResult started;
    if (two_phase) {
        if (qualified_static_member.valid()) {
            started.entity = qualified_static_member;

            started.type = collect_session_.file()
                               .entity(qualified_static_member)
                               .type;
            if (!collect_session_
                     .validate_record_static_data_member_definition(
                         qualified_static_member,
                         has_init_syntax,
                         flags,
                         declarator.loc)) {
                started.has_error = true;
            }
            collect_session_.file()
                .entity_mut(qualified_static_member)
                .qualifiers = flags.type_qualifiers;
        } else {
            started = top_level
                ? collect_session_.declare_global_variable(declarator.name,
                                                           declared_type,
                                                           std::nullopt,
                                                           declarator.loc,
                                                           flags,
                                                           has_init_syntax)
                : collect_session_.declare_local_variable(declarator.name,
                                                          declared_type,
                                                          std::nullopt,
                                                          declarator.loc,
                                                          flags,
                                                          has_init_syntax);
        }
    }

    if (match(TokenType::ASSIGN)) {
        ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
        initializer = init.sem;
        children.push_back(init.syntax);
    } else if (check(TokenType::LEFT_BRACE)) {
        ParsedExpr init = parse_init_list_expression();
        initializer = init.sem;
        children.push_back(init.syntax);
    } else if (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN)) {
        size_t init_begin = current_raw_index();
        consume();
        ParsedExpressionList arguments =
            parse_expression_list(TokenType::RIGHT_PAREN);
        std::vector<NodeId> init_children = std::move(arguments.syntax);
        std::vector<collect::ExprResult> direct_arguments =
            std::move(arguments.sem);
        bool has_dependent_pack_expansion =
            arguments.has_dependent_pack_expansion;
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after initializer", current_loc());
        }
        NodeId init_syntax = make_node(NodeKind::InitListExpr,
                                       init_begin,
                                       last_consumed_raw_end(),
                                       init_children);
        children.push_back(init_syntax);

        if (collect_session_.collecting_pattern() &&
            has_dependent_pack_expansion) {
            collect_session_.mark_pattern_unusable();
            return started;
        }

        if (collect_session_.collecting_pattern() &&
            collect_session_.is_dependent_type(declared_type) &&
            direct_arguments.size() > 1) {
            collect_session_.mark_pattern_unusable();
            return started;
        }

        const cir::File& direct_file = collect_session_.file();
        cir::TypeId direct_record_type =
            direct_file.resolved_type(declared_type);
        bool direct_same_type_copy =
            direct_arguments.size() == 1 &&
            direct_arguments.front().type.valid() &&
            direct_file.valid(direct_record_type) &&
            direct_file.type(direct_record_type).kind ==
                cir::TypeKind::Record &&
            direct_file.resolved_type(direct_arguments.front().type) ==
                direct_record_type;
        if (two_phase &&
            (collect_session_.record_has_user_constructor(declared_type) ||
             direct_same_type_copy)) {
            return collect_session_.construct_variable(std::move(started),
                                                       std::move(direct_arguments),
                                                       declarator.loc);
        }
        if (direct_arguments.size() == 1) {
            initializer = std::move(direct_arguments.front());
        } else if (direct_arguments.size() > 1) {
            diagnose(DiagnosticLevel::Error,
                     "direct initializers with multiple arguments require a class with a matching constructor",
                     loc_for_index(init_begin));
        }
    }

    if (collect_session_.contains_auto_type(declared_type)) {
        bool has_gnu_auto =
            collect_session_.contains_auto_type(declared_type,
                                                cir::AutoTypeFlavor::Gnu);
        bool has_decltype_auto =
            collect_session_.contains_auto_type(declared_type,
                                                cir::AutoTypeFlavor::DecltypeAuto);
        bool plain_decltype_auto =
            is_plain_auto_type(collect_session_,
                               declared_type,
                               cir::AutoTypeFlavor::DecltypeAuto);

        if (has_decltype_auto) {
            if (!plain_decltype_auto ||
                has_gnu_auto ||
                collect_session_.contains_auto_type(declared_type,
                                                    cir::AutoTypeFlavor::Cxx) ||
                collect_session_.contains_auto_type(
                    declared_type,
                    cir::AutoTypeFlavor::TemplateNonType) ||
                collect_session_.contains_auto_type(
                    declared_type,
                    cir::AutoTypeFlavor::DecltypeAutoTemplateNonType)) {
                diagnose(DiagnosticLevel::Error,
                         "'decltype(auto)' must appear as the sole type specifier",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            if (!initializer.has_value()) {
                diagnose(DiagnosticLevel::Error,
                         "'decltype(auto)' requires an initializer",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            if (initializer->category == collect::ValueCategory::InitList) {
                diagnose(DiagnosticLevel::Error,
                         "cannot use 'decltype(auto)' with initializer list",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            cir::TypeRef deduced =
                collect_session_.resolve_decltype_expr_type(
                    *initializer,
                    initializer->unparenthesized_id_or_member,
                    declarator.loc);
            if (!deduced.type.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "cannot deduce type for 'decltype(auto)'",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            declared_type = deduced.type;
            flags.type_qualifiers = static_cast<uint8_t>(
                flags.type_qualifiers | deduced.qualifiers);
        } else if (!has_gnu_auto) {

            cir::TypeId auto_pattern = declared_type;
            if (!initializer.has_value()) {
                diagnose(DiagnosticLevel::Error,
                         "declaration with 'auto' type requires an initializer",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            bool copy_list_auto_replaced = false;
            if (initializer->category == collect::ValueCategory::InitList) {
                if (!initializer->init_list) {
                    diagnose(DiagnosticLevel::Error,
                             "initializer-list deduction requires a braced initializer",
                             declarator.loc);
                    collect::DeclResult decl;
                    decl.type = declared_type;
                    decl.has_error = true;
                    return decl;
                }
                const auto& elements = initializer->init_list->elements;
                if (constructor_init_kind ==
                    collect::ConstructorInitializationKind::Direct) {
                    if (!is_plain_auto_type(collect_session_, declared_type,
                                            cir::AutoTypeFlavor::Cxx)) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "direct-list-initialization currently requires "
                            "plain 'auto'",
                            declarator.loc);
                        collect::DeclResult decl;
                        decl.type = declared_type;
                        decl.has_error = true;
                        return decl;
                    }
                    if (elements.size() != 1 ||
                        !elements.front().designators.empty() ||
                        elements.front().value.init_list ||
                        !elements.front().value.type.valid()) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "direct-list-initialization of 'auto' requires "
                            "exactly one typed initializer-clause",
                            declarator.loc);
                        collect::DeclResult decl;
                        decl.type = declared_type;
                        decl.has_error = true;
                        return decl;
                    }
                    initializer->type = elements.front().value.type;
                } else {
                    initializer->type = deduce_auto_copy_list_type(
                        *initializer, declarator.loc);
                    if (!initializer->type.valid()) {
                        collect::DeclResult decl;
                        decl.type = declared_type;
                        decl.has_error = true;
                        return decl;
                    }
                    declared_type = collect_session_.replace_auto_type(
                        declared_type,
                        collect_session_.type_ref(initializer->type),
                        declarator.loc);
                    copy_list_auto_replaced = true;
                }
            }
            if (initializer->has_error) {

                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            const cir::File& file = collect_session_.file();
            bool overload_initializer =
                initializer->category ==
                    collect::ValueCategory::OverloadDesignator ||
                ((initializer->category ==
                      collect::ValueCategory::FunctionDesignator ||
                  initializer->category ==
                      collect::ValueCategory::MemberPointerDesignator) &&
                 (!initializer->candidates.empty() ||
                  initializer->overload_designator));
            if (overload_initializer) {
                declared_type = collect_session_.deduce_auto_type(
                    declared_type, *initializer, declarator.loc);
                if (!declared_type.valid() ||
                    !file.valid(file.resolved_type(declared_type))) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "cannot deduce a common target type for overloaded "
                        "function",
                        declarator.loc);
                    collect::DeclResult decl;
                    decl.type = declared_type;
                    decl.has_error = true;
                    return decl;
                }
                bool function_reference_target =
                    collect_session_.is_reference_type(declared_type) &&
                    (!initializer->overload_designator ||
                     !initializer->overload_designator->address_of_written);
                if (function_reference_target) {

                } else if (initializer->category ==
                    collect::ValueCategory::OverloadDesignator) {
                    *initializer =
                        collect_session_.convert_overload_designator_to_target(
                            std::move(*initializer),
                            declared_type,
                            declarator.loc);
                } else if (initializer->category ==
                           collect::ValueCategory::MemberPointerDesignator) {
                    *initializer = collect_session_
                        .convert_member_pointer_designator_to_target(
                            std::move(*initializer),
                            declared_type,
                            declarator.loc);
                } else {
                    *initializer = collect_session_
                        .convert_function_designator_to_target(
                            std::move(*initializer),
                            declared_type,
                            declarator.loc);
                }
                if (initializer->has_error) {
                    collect::DeclResult decl;
                    decl.type = declared_type;
                    decl.has_error = true;
                    return decl;
                }
            } else if (!copy_list_auto_replaced) {
                if (!initializer->type.valid()) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "cannot deduce type for 'auto': initializer has no type",
                        declarator.loc);
                    collect::DeclResult decl;
                    decl.type = declared_type;
                    decl.has_error = true;
                    return decl;
                }
                cir::TypeRef deduced =
                    collect_session_.type_ref(initializer->type);
                if (is_plain_auto_type(collect_session_,
                                       declared_type,
                                       cir::AutoTypeFlavor::Cxx)) {
                    cir::TypeId initializer_type =
                        file.resolved_type(initializer->type);
                    if (file.valid(initializer_type) &&
                        file.type(initializer_type).kind ==
                            cir::TypeKind::Array) {
                        if (!structured_binding_backing) {
                            deduced = collect_session_.type_ref(
                                collect_session_.pointer_type(
                                    file.array_element_ref(initializer_type)));
                        }
                    } else if (file.valid(initializer_type) &&
                               file.type(initializer_type).kind ==
                                   cir::TypeKind::Function) {
                        deduced = collect_session_.type_ref(
                            collect_session_.pointer_type(
                                collect_session_.type_ref(initializer_type)));
                    }
                    declared_type =
                        collect_session_.replace_auto_type(declared_type,
                                                           deduced,
                                                           declarator.loc);
                } else {
                    declared_type = collect_session_.deduce_auto_type(
                        declared_type, *initializer, declarator.loc);
                }
            }
            if (!declared_type.valid() &&
                collect_session_.collecting_pattern() &&
                (initializer->category ==
                     collect::ValueCategory::Dependent ||
                 initializer->value_dependent ||
                 (initializer->type.valid() &&
                  collect_session_.is_dependent_type(
                      initializer->type)))) {

                collect_session_.mark_pattern_unusable();
                cir::TypeId dependent = collect_session_.dependent_type(
                    ".auto.deduction");
                declared_type = collect_session_.replace_auto_type(
                    auto_pattern,
                    collect_session_.type_ref(dependent),
                    declarator.loc);
            }
            if (!declared_type.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "cannot deduce type for 'auto' from initializer",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = auto_pattern;
                decl.has_error = true;
                return decl;
            }
            if (declarator.has_placeholder_type_constraint &&
                !validate_placeholder_type_constraint(
                    declarator.placeholder_type_constraint_begin,
                    declarator.placeholder_type_constraint_end,
                    declarator.placeholder_type_constraint_loc,
                    collect_session_.type_ref(declared_type),
                    "deduced object")) {
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }

            started = top_level
                ? collect_session_.declare_global_variable(declarator.name,
                                                           declared_type,
                                                           std::nullopt,
                                                           declarator.loc,
                                                           flags,
                                                           true)
                : collect_session_.declare_local_variable(declarator.name,
                                                          declared_type,
                                                          std::nullopt,
                                                          declarator.loc,
                                                          flags,
                                                          true);
            if (structured_binding_backing && started.entity.valid() &&
                collect_session_.file().valid(started.entity)) {

                cir::Entity& backing =
                    collect_session_.file().entity_mut(started.entity);
                backing.object_origin =
                    cir::EntityObjectOrigin::StructuredBindingBacking;
                backing.semantic_context =
                    collect_session_.current_decl_context();
                backing.lexical_context =
                    collect_session_.current_decl_context();
                backing.owning_function =
                    collect_session_.current_function_entity();
            }
            two_phase = true;
        } else {
            if (top_level) {
                diagnose(DiagnosticLevel::Error,
                         "'__auto_type' is not allowed at file scope",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            if (!initializer.has_value()) {
                diagnose(DiagnosticLevel::Error,
                         "'__auto_type' requires an initializer",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            if (initializer->category == collect::ValueCategory::InitList) {
                diagnose(DiagnosticLevel::Error,
                         "cannot use '__auto_type' with initializer list",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            if (!initializer->type.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "cannot deduce type for '__auto_type': initializer has no type",
                         declarator.loc);
                collect::DeclResult decl;
                decl.type = declared_type;
                decl.has_error = true;
                return decl;
            }
            declared_type =
                collect_session_.replace_auto_type(declared_type,
                                                   collect_session_.type_ref(initializer->type),
                                                   declarator.loc);
        }
    }

    if (initializer.has_value()) {
        declared_type =
            collect_session_.complete_initializer_type(declared_type,
                                                       *initializer,
                                                       declarator.loc);
    }

    if (two_phase) {
        return collect_session_.finish_variable_declaration(std::move(started),
                                                            declared_type,
                                                            std::move(initializer),
                                                            declarator.loc,
                                                            flags,
                                                            declarator.name,
                                                            constructor_init_kind);
    }

    if (top_level) {
        return collect_session_.declare_global_variable(declarator.name,
                                                        declared_type,
                                                        std::move(initializer),
                                                        declarator.loc,
                                                        flags);
    }
    return collect_session_.declare_local_variable(declarator.name,
                                                   declared_type,
                                                   std::move(initializer),
                                                   declarator.loc,
                                                   flags);
}

collect::StructuredBindingTupleInput Parser::resolve_structured_binding_tuple(
    const collect::DeclResult& backing,
    size_t binding_count,
    size_t pack_position,
    SrcLoc loc) {
    collect::StructuredBindingTupleInput tuple;
    if (!backing.entity.valid() || !backing.type.valid()) {
        return tuple;
    }

    const cir::File& file = collect_session_.file();
    cir::TypeRef decomposed = collect_session_.type_ref(backing.type);
    cir::TypeId resolved_backing = file.resolved_type(backing.type);
    bool backing_is_lvalue_reference = false;
    if (file.valid(resolved_backing) &&
        (file.type(resolved_backing).kind == cir::TypeKind::LValueReference ||
         file.type(resolved_backing).kind == cir::TypeKind::RValueReference)) {
        backing_is_lvalue_reference =
            file.type(resolved_backing).kind == cir::TypeKind::LValueReference;
        decomposed = file.reference_referred_ref(resolved_backing);
    } else {
        decomposed.qualifiers = static_cast<uint8_t>(
            decomposed.qualifiers | file.entity(backing.entity).qualifiers);
    }
    if (collect_session_.is_dependent_type(decomposed.type)) {
        return tuple;
    }
    cir::TypeId resolved_decomposed = file.resolved_type(decomposed.type);
    if (file.valid(resolved_decomposed) &&
        file.type(resolved_decomposed).kind == cir::TypeKind::Array) {
        return tuple;
    }

    const collect::Session::TemplateInfo* tuple_size_template =
        collect_session_.peek_qualified_template_info(
            /*global_qualifier=*/true,
            {std::string_view("std")},
            "tuple_size");
    if (!tuple_size_template || !tuple_size_template->is_class_template) {
        return tuple;
    }

    collect::Session::TemplateArgument type_argument;
    type_argument.kind = cir::TemplateArgumentKind::Type;
    type_argument.type = decomposed;

    size_t diagnostic_watermark = diagnostics_.size();
    collect_session_.begin_speculative_parse();
    cir::EntityId tuple_size = instantiate_template_with_args(
        *tuple_size_template, {type_argument}, loc);
    collect::Session::MemberEntityLookup size_lookup;
    if (tuple_size.valid() && file.valid(tuple_size)) {
        size_lookup = collect_session_.lookup_member_entities(
            file.entity(tuple_size).type, "value");
    }
    if (!size_lookup.found_name) {
        collect_session_.rollback_speculative_parse();
        diagnostics_.resize(diagnostic_watermark);
        return tuple;
    }
    collect_session_.commit_speculative_parse();
    tuple.selected = true;
    if (size_lookup.ambiguous || size_lookup.entities.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "std::tuple_size specialization has an ambiguous member 'value'",
                 loc);
        tuple.has_error = true;
        return tuple;
    }
    cir::EntityId size_entity = size_lookup.entities.back();

    collect::ExprResult size_expression =
        collect_session_.make_entity_reference(size_entity, "value", loc, true);

    materialize_deferred_static_data_member_expr(size_expression);
    int64_t element_count = 0;
    if (!collect_session_.evaluate_integer_constant(
            size_expression,
            element_count,
            loc,
            "std::tuple_size specialization does not provide an integral constant 'value'")) {
        tuple.has_error = true;
        return tuple;
    }
    if (element_count < 0) {
        diagnose(DiagnosticLevel::Error,
                 "std::tuple_size specialization has a negative size",
                 loc);
        tuple.has_error = true;
        return tuple;
    }
    bool has_pack = pack_position != std::numeric_limits<size_t>::max();
    size_t fixed_count = binding_count - (has_pack ? 1 : 0);
    bool count_matches = has_pack
        ? static_cast<uint64_t>(element_count) >= fixed_count
        : static_cast<uint64_t>(element_count) == binding_count;
    if (!count_matches) {
        diagnose(DiagnosticLevel::Error,
                 "structured binding declares " +
                     std::to_string(binding_count) +
                     (has_pack ? " entries including a pack, but the tuple protocol decomposes into "
                               : " names, but the tuple protocol decomposes into ") +
                     std::to_string(element_count) + " elements",
                 loc);
        tuple.has_error = true;
    }

    const collect::Session::TemplateInfo* tuple_element_template =
        collect_session_.peek_qualified_template_info(
            /*global_qualifier=*/true,
            {std::string_view("std")},
            "tuple_element");
    if (!tuple_element_template || !tuple_element_template->is_class_template) {
        diagnose(DiagnosticLevel::Error,
                 "tuple-like structured binding requires std::tuple_element",
                 loc);
        tuple.has_error = true;
        return tuple;
    }

    size_t available = has_pack && count_matches
        ? static_cast<size_t>(element_count)
        : std::min<size_t>(binding_count,
                           static_cast<size_t>(element_count));
    tuple.elements.reserve(available);
    for (size_t i = 0; i < available; ++i) {
        collect::Session::TemplateArgument index_argument;
        index_argument.kind = cir::TemplateArgumentKind::Value;
        index_argument.value_type = collect_session_.type_ref(
            collect_session_.file().builtin_type(cir::BuiltinTypeKind::ULong));
        index_argument.value_kind = cir::TemplateValueKind::Integer;
        index_argument.integer_value =
            cir::IntegerValue::from_unsigned(i, 64);
        index_argument.value_spelling = std::to_string(i);

        cir::EntityId tuple_element = instantiate_template_with_args(
            *tuple_element_template,
            {index_argument, type_argument},
            loc);
        cir::DeclContextId element_context =
            tuple_element.valid() && file.valid(tuple_element)
                ? file.entity(tuple_element).semantic_context
                : cir::DeclContextId{};
        cir::TypeRef element_type =
            collect_session_.lookup_qualified_type_name_ref_checked(
                element_context, "type", loc);
        if (!element_type.valid()) {
            tuple.has_error = true;
            break;
        }

        collect::ExprResult base = collect_session_.make_entity_reference(
            backing.entity,
            file.entity(backing.entity).name.valid()
                ? file.name(file.entity(backing.entity).name)
                : std::string_view("<structured-binding>"),
            loc);
        if (!backing_is_lvalue_reference) {
            base.category = collect::ValueCategory::XValue;
        }

        std::vector<cir::EntityId> member_specializations;
        const collect::Session::TemplateInfo* first_member_info =
            collect_session_.member_template_info_for_access(
                base, "get", /*is_arrow=*/false);
        bool use_member_get = first_member_info &&
            !first_member_info->parameters.empty() &&
            first_member_info->parameters.front().kind ==
                collect::Session::TemplateParameterKind::NonType;
        std::vector<const collect::Session::TemplateInfo*> member_infos;
        if (use_member_get) {
            cir::DeclContextId member_context =
                file.entity(first_member_info->entity).semantic_context;
            member_infos = collect_session_.function_template_infos_for_name(
                member_context, "get", /*include_parents=*/false);
            if (member_infos.empty()) {
                member_infos.push_back(first_member_info);
            }
        }
        for (const collect::Session::TemplateInfo* info : member_infos) {
            if (!info || info->parameters.empty() ||
                info->parameters.front().kind !=
                    collect::Session::TemplateParameterKind::NonType) {
                continue;
            }
            std::vector<collect::Session::TemplateArgument> deduced;
            std::vector<collect::Session::TemplateArgument> explicit_arguments{
                index_argument};
            if (!collect_session_.deduce_template_arguments(
                    *info, {}, deduced, &explicit_arguments)) {
                continue;
            }
            cir::EntityId specialization = instantiate_template_with_args(
                *info, std::move(deduced), loc);
            if (specialization.valid()) {
                member_specializations.push_back(specialization);
            }
        }

        collect::ExprResult get_call;
        if (use_member_get) {
            if (member_specializations.empty()) {
                diagnose(DiagnosticLevel::Error,
                         "no viable member get<" + std::to_string(i) +
                             "> for tuple-like structured binding",
                         loc);
                tuple.has_error = true;
                break;
            }
            collect::ExprResult callee =
                collect_session_.collect_resolved_member_function_access_expr(
                    std::move(base),
                    member_specializations.front(),
                    "get",
                    /*is_arrow=*/false,
                    loc);
            callee.candidates = member_specializations;
            get_call = collect_session_.collect_call_expr(
                std::move(callee), {}, loc);
        } else {
            std::vector<collect::ExprResult> adl_arguments{base};
            std::vector<cir::EntityId> adl_candidates;
            collect_session_.add_adl_candidates(
                "get", adl_arguments, adl_candidates);
            std::vector<cir::EntityId> specializations;
            for (cir::EntityId candidate : adl_candidates) {
                const collect::Session::TemplateInfo* info =
                    collect_session_.template_info(candidate);
                if (!info) {
                    continue;
                }
                std::vector<collect::Session::TemplateArgument> deduced;
                std::vector<collect::Session::TemplateArgument>
                    explicit_arguments{index_argument};
                if (!collect_session_.deduce_template_arguments(
                        *info, adl_arguments, deduced, &explicit_arguments)) {
                    continue;
                }
                cir::EntityId specialization = instantiate_template_with_args(
                    *info, std::move(deduced), loc);
                if (specialization.valid()) {
                    specializations.push_back(specialization);
                }
            }
            if (specializations.empty()) {
                diagnose(DiagnosticLevel::Error,
                         "no viable argument-dependent get<" +
                             std::to_string(i) +
                             "> for tuple-like structured binding",
                         loc);
                tuple.has_error = true;
                break;
            }
            collect::ExprResult callee =
                collect_session_.make_entity_reference(
                    specializations.front(), "get", loc);
            callee.candidates = specializations;
            callee.suppress_argument_dependent_lookup = true;
            get_call = collect_session_.collect_call_expr(
                std::move(callee), std::move(adl_arguments), loc);
        }

        collect::StructuredBindingTupleElementInput element;
        element.element_type = element_type;
        element.initializer = std::move(get_call);
        element.initializer.has_error =
            element.initializer.has_error || !element.initializer.type.valid();
        tuple.has_error = tuple.has_error || element.initializer.has_error;
        tuple.elements.push_back(std::move(element));
    }
    return tuple;
}

Parser::ParsedDecl Parser::parse_declaration(bool top_level,
                                             bool condition_declaration) {
    size_t begin = current_raw_index();
    struct AccessCaptureGuard {
        collect::Session& session;
        collect::Session::AccessCaptureToken token;
        bool retained = true;
        ~AccessCaptureGuard() {
            if (retained) {
                session.discard_access_capture(token);
            }
        }
        void suspend() { session.suspend_access_capture(token); }
        bool finish(cir::EntityId entity) {
            retained = false;
            return session.finish_access_capture(token, entity);
        }
        void discard() {
            if (retained) {
                session.discard_access_capture(token);
                retained = false;
            }
        }
    } prefix_access{collect_session_,
                    collect_session_.begin_access_capture()};
    TypeParseContext declaration_type_context = top_level
        ? TypeParseContext::type_only(
              TypeParseContext::Origin::NamespaceDeclSpecifier)
        : TypeParseContext{};
    DeclarationParser decl_parser(*this, declaration_type_context);
    cir::TypeRef base_type = decl_parser.parse_declaration(false, true);
    prefix_access.suspend();
    cir::TypeId declared_type = base_type.type;
    bool is_typedef = decl_parser.storage_class == StorageClass::Typedef;
    collect::DeclFlags flags = declaration_flags_from(decl_parser.is_constexpr,
                                                      decl_parser.is_consteval,
                                                      decl_parser.is_constinit,
                                                      decl_parser.is_inline,
                                                      decl_parser.is_thread_local,
                                                      decl_parser.storage_class == StorageClass::Extern,
                                                      decl_parser.storage_class == StorageClass::Static,
                                                      decl_parser.storage_class == StorageClass::Auto,
                                                      decl_parser.storage_class == StorageClass::Register,
                                                      decl_parser.is_mutable,
                                                      decl_parser.is_friend,
                                                      decl_parser.is_block_byref);
    flags.attrs = decl_parser.leading_attrs;
    NodeId type = decl_parser.type_syntax;

    if (condition_declaration) {
        bool invalid_specifier =
            is_typedef || decl_parser.storage_class != StorageClass::None ||
            decl_parser.is_consteval || decl_parser.is_constinit ||
            decl_parser.is_inline || decl_parser.is_thread_local ||
            decl_parser.is_mutable || decl_parser.is_friend ||
            decl_parser.is_block_byref;
        if (invalid_specifier) {
            diagnose(DiagnosticLevel::Error,
                     "invalid declaration specifier in condition",
                     loc_for_index(begin));
        }
    }

    bool structured_binding_syntax =
        lang_opts_.is_cxx_mode() &&
        (check(TokenType::LEFT_BRACKET) ||
         ((check(TokenType::BITWISE_AND) || check(TokenType::LOGICAL_AND)) &&
          peek(1).type == TokenType::LEFT_BRACKET));
    if (structured_binding_syntax) {
        bool has_error = false;
        SrcLoc binding_loc = current_loc();
        if (!lang_opts_.is_cxx17_or_later()) {
            diagnose(DiagnosticLevel::Error,
                     "structured bindings require C++17",
                     binding_loc);
            has_error = true;
        }
        if (!is_plain_auto_type(collect_session_,
                                base_type.type,
                                cir::AutoTypeFlavor::Cxx)) {
            diagnose(DiagnosticLevel::Error,
                     "structured binding declaration requires 'auto'",
                     binding_loc);
            has_error = true;
        }
        bool invalid_specifier =
            is_typedef || decl_parser.is_consteval || decl_parser.is_constinit ||
            decl_parser.is_inline || decl_parser.storage_class == StorageClass::Extern ||
            decl_parser.storage_class == StorageClass::Auto ||
            decl_parser.storage_class == StorageClass::Register ||
            decl_parser.is_mutable || decl_parser.is_friend ||
            decl_parser.is_block_byref;
        if (invalid_specifier) {
            diagnose(DiagnosticLevel::Error,
                     "invalid declaration specifier on structured binding",
                     binding_loc);
            has_error = true;
        }
        if ((decl_parser.storage_class == StorageClass::Static ||
             decl_parser.is_thread_local) &&
            !lang_opts_.is_cxx20_or_later()) {
            diagnose(DiagnosticLevel::Error,
                     "static and thread_local structured bindings require C++20",
                     binding_loc);
            has_error = true;
        }
        if (decl_parser.is_constexpr && !lang_opts_.is_cxx26_or_later()) {
            diagnose(DiagnosticLevel::Error,
                     "constexpr structured bindings require C++26",
                     binding_loc);
            has_error = true;
        }
        if (condition_declaration && !lang_opts_.is_cxx26_or_later()) {
            diagnose(DiagnosticLevel::Error,
                     "structured bindings in conditions require C++26",
                     binding_loc);
            has_error = true;
        }

        cir::TypeRef backing_pattern = base_type;
        if (check(TokenType::BITWISE_AND) || check(TokenType::LOGICAL_AND)) {
            bool rvalue = check(TokenType::LOGICAL_AND);
            consume();
            backing_pattern = collect_session_.type_ref(
                collect_session_.reference_type(
                    base_type,
                    rvalue ? cir::ReferenceKind::RValue
                           : cir::ReferenceKind::LValue));
        }
        if (!match(TokenType::LEFT_BRACKET)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '[' in structured binding declaration",
                     current_loc());
            has_error = true;
        }

        std::vector<collect::StructuredBindingNameInput> binding_names;
        std::vector<NodeId> binding_name_syntax;
        bool saw_pack = false;
        if (check(TokenType::RIGHT_BRACKET)) {
            diagnose(DiagnosticLevel::Error,
                     "structured binding declaration requires at least one name",
                     current_loc());
            has_error = true;
        }
        while (!at_end() && !check(TokenType::RIGHT_BRACKET)) {
            size_t name_begin = current_raw_index();
            bool is_pack = match(TokenType::ELLIPSIS);
            if (is_pack) {
                if (!lang_opts_.is_cxx26_or_later()) {
                    diagnose(DiagnosticLevel::Error,
                             "structured binding packs require C++26",
                             last_consumed_loc());
                    has_error = true;
                }
                if (saw_pack) {
                    diagnose(DiagnosticLevel::Error,
                             "structured binding declaration may contain only one pack",
                             last_consumed_loc());
                    has_error = true;
                }
                saw_pack = true;
            }
            if (!check(TokenType::IDENTIFIER)) {
                diagnose(DiagnosticLevel::Error,
                         "expected identifier in structured binding declaration",
                         current_loc());
                has_error = true;
                while (!at_end() && !check(TokenType::COMMA) &&
                       !check(TokenType::RIGHT_BRACKET)) {
                    consume();
                }
            } else {
                const Token& name_token = consume();
                collect::StructuredBindingNameInput input;
                input.name = name_token.value;
                input.loc = name_token.loc;
                input.is_pack = is_pack;
                ParsedAttributes attrs = try_parse_attributes();
                if (!attrs.attrs.empty() && !lang_opts_.is_cxx26_or_later()) {
                    diagnose(DiagnosticLevel::Error,
                             "attributes on structured binding names require C++26",
                             name_token.loc);
                    has_error = true;
                }
                input.attrs = std::move(attrs.attrs);
                binding_name_syntax.push_back(
                    make_node(NodeKind::StructuredBindingName,
                              name_begin,
                              last_consumed_raw_end(),
                              std::move(attrs.syntax),
                              text_payload(input.name)));
                binding_names.push_back(std::move(input));
            }
            if (!match(TokenType::COMMA)) {
                break;
            }
            if (check(TokenType::RIGHT_BRACKET)) {
                diagnose(DiagnosticLevel::Error,
                         "expected identifier after ',' in structured binding declaration",
                         current_loc());
                has_error = true;
            }
        }
        if (!match(TokenType::RIGHT_BRACKET)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ']' after structured binding names",
                     current_loc());
            has_error = true;
        }

        bool has_initializer = check(TokenType::ASSIGN) ||
                               check(TokenType::LEFT_BRACE) ||
                               check(TokenType::LEFT_PAREN);
        if (!has_initializer) {
            diagnose(DiagnosticLevel::Error,
                     "structured binding declaration requires an initializer",
                     binding_loc);
            has_error = true;
        }

        collect::StructuredBindingStart structured =
            collect_session_.begin_structured_binding(
                std::move(binding_names), binding_loc);
        ParsedDeclarator backing;
        backing.name = structured.backing_name;
        backing.type = backing_pattern.type;
        backing.type_ref = backing_pattern;
        backing.loc = binding_loc;
        backing.has_name = true;

        std::vector<NodeId> children{type};
        children.insert(children.end(),
                        binding_name_syntax.begin(),
                        binding_name_syntax.end());
        collect::Session::LifetimeBoundary boundary =
            collect_session_.begin_lifetime_boundary();
        AccessCaptureGuard declarator_access{
            collect_session_,
            collect_session_.begin_access_capture(prefix_access.token)};
        flags.suppress_name_binding = true;
        flags.type_qualifiers = backing_pattern.qualifiers;
        collect::DeclResult result =
            handle_variable_declarator(backing,
                                       top_level,
                                       children,
                                       flags,
                                       true);
        size_t pack_position = std::numeric_limits<size_t>::max();
        for (size_t i = 0; i < structured.names.size(); ++i) {
            if (structured.names[i].is_pack) {
                pack_position = i;
                break;
            }
        }
        collect::StructuredBindingTupleInput tuple =
            resolve_structured_binding_tuple(
                result,
                structured.names.size(),
                pack_position,
                binding_loc);
        result = collect_session_.finish_structured_binding(
            std::move(structured),
            std::move(result),
            binding_loc,
            condition_declaration,
            std::move(tuple));
        result.has_error = result.has_error || has_error ||
                           !declarator_access.finish(result.entity);
        result.fragment = collect_session_.chain(
            std::move(result.fragment),
            collect_session_.finish_lifetime_boundary(boundary, binding_loc),
            binding_loc);

        if (!condition_declaration && !match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after structured binding declaration",
                     current_loc());
            skip_until_statement_boundary();
            result.has_error = true;
        }
        prefix_access.discard();
        return {make_node(NodeKind::StructuredBindingDecl,
                          begin,
                          last_consumed_raw_end(),
                          children,
                          {},
                          result.has_error ? NodeFlagHasError : NodeFlagNone),
                std::move(result)};
    }

    if (!condition_declaration && check(TokenType::SEMICOLON) &&
        declared_type.valid() &&
        collect_session_.file().valid(declared_type) &&
        (collect_session_.file().type(collect_session_.file().resolved_type(declared_type)).kind ==
             cir::TypeKind::Record ||
         collect_session_.file().type(collect_session_.file().resolved_type(declared_type)).kind ==
             cir::TypeKind::Enum)) {
        cir::TypeId resolved =
            collect_session_.file().resolved_type(declared_type);
        cir::EntityId record_entity =
            collect_session_.file().record_entity(resolved);
        const cir::RecordFacts* record_facts =
            record_entity.valid()
                ? collect_session_.file().record_facts(record_entity)
                : nullptr;
        bool anonymous_union =
            lang_opts_.is_cxx_mode() && !is_typedef && record_facts &&
            record_facts->kind == cir::RecordKind::Union &&
            collect_session_.file().entity(record_entity).is_unnamed_record;
        consume();
        collect::DeclResult decl_result;
        decl_result.type = declared_type;
        if (anonymous_union) {
            decl_result = collect_session_.declare_anonymous_union_variable(
                declared_type, top_level, flags, loc_for_index(begin));
            prefix_access.discard();
        } else {
            decl_result.has_error =
                !prefix_access.finish(record_entity) || decl_result.has_error;
        }
        return {make_node(NodeKind::RecordDecl, begin, last_consumed_raw_end(), {type}), decl_result};
    }

    std::vector<NodeId> children{type};
    std::vector<collect::DeclResult> declaration_results;
    bool saw_function_declaration = false;
    std::optional<cir::TypeId> deduced_class_replacement_type;
    AttributeList pending_declarator_attrs;

    while (!at_end()) {

        collect::Session::LifetimeBoundary declarator_boundary =
            collect_session_.begin_lifetime_boundary();
        AccessCaptureGuard declarator_access{
            collect_session_,
            collect_session_.begin_access_capture(prefix_access.token)};
        decl_parser.reset_declarator_parsing_state();
        ParsedDeclarator declarator = decl_parser.parse_declarator(base_type, false);
        declarator.deduced_class_template_info =
            decl_parser.deduced_class_template_info;
        declarator.deduced_class_template_loc =
            decl_parser.deduced_class_template_loc;
        declarator.attrs.append(std::move(pending_declarator_attrs));
        pending_declarator_attrs = {};
        if (!declarator.has_name) {
            collect_session_.discard_lifetime_boundary(declarator_boundary);
            size_t end = skip_balanced_until_semicolon_or_brace();
            diagnose(DiagnosticLevel::Error, "expected declaration name", loc_for_index(begin));
            return {make_node(NodeKind::UnknownDecl, begin, end, children, {}, NodeFlagHasError), {}};
        }

        if (declarator.syntax != InvalidNodeId) {
            children.push_back(declarator.syntax);
        }

        bool condition_has_initializer =
            check(TokenType::ASSIGN) || check(TokenType::LEFT_BRACE);
        if (condition_declaration) {
            cir::TypeId resolved = collect_session_.file().resolved_type(
                declarator.type);
            bool is_array =
                collect_session_.file().valid(resolved) &&
                collect_session_.file().type(resolved).kind ==
                    cir::TypeKind::Array;
            if (declarator.is_function || is_array) {
                diagnose(DiagnosticLevel::Error,
                         "condition declaration must declare an object",
                         declarator.loc);
            }
            if (!condition_has_initializer) {
                diagnose(DiagnosticLevel::Error,
                         "condition declaration requires an initializer",
                         declarator.loc);
            }
            if (check(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "condition declaration requires a brace-or-equal initializer",
                         declarator.loc);
            }
        }

        std::string asm_label;
        if (check(TokenType::ASM_KW)) {
            children.push_back(parse_asm_label_syntax(&asm_label));
        }
        ParsedAttributes trailing_attrs = try_parse_attributes();
        declarator.attrs.append(std::move(trailing_attrs.attrs));
        children.insert(children.end(),
                        trailing_attrs.syntax.begin(),
                        trailing_attrs.syntax.end());

        AttributeList merged_attrs = flags.attrs;
        merged_attrs.append(declarator.attrs);
        declarator.attrs = std::move(merged_attrs);
        collect::DeclFlags declarator_flags = flags;
        declarator_flags.attrs = declarator.attrs;
        declarator_flags.asm_label = std::move(asm_label);
        declarator_flags.vla_bounds = std::move(declarator.vla_bounds);
        declarator_flags.type_qualifiers = declarator.type_ref.qualifiers;
        if (!declarator.is_function) {
            declarator.type_ref =
                collect_session_.apply_type_attributes(declarator.type_ref,
                                                       declarator.attrs,
                                                       declarator.loc);
            declarator.type = declarator.type_ref.type;
        }

        if (!is_typedef &&
            declarator.is_function &&
            lang_opts_.is_cxx_mode() &&
            match(TokenType::ASSIGN)) {
            SrcLoc suffix_loc = last_consumed_loc();
            if (match(TokenType::DELETE)) {
                declarator_flags.is_deleted = true;
            } else if (match(TokenType::DEFAULT)) {
                const cir::File& file = collect_session_.file();
                bool record_qualified =
                    declarator.qualified_context.valid() &&
                    file.valid(declarator.qualified_context) &&
                    file.decl_context(declarator.qualified_context).kind ==
                        cir::DeclContextKind::Record;
                if (record_qualified) {
                    declarator_flags.is_defaulted = true;
                } else {
                    diagnose(
                        DiagnosticLevel::Error,
                        "explicitly defaulted non-member functions are not "
                        "supported",
                        suffix_loc);
                    declarator.has_unsupported_semantics = true;
                }
            } else if (check(TokenType::INTEGER_CONST) && current().value == "0") {
                consume();
                diagnose(DiagnosticLevel::Error,
                         "pure-specifiers are only valid on virtual member functions",
                         suffix_loc);
                declarator.has_unsupported_semantics = true;
            } else {
                ParsedExpr suffix = parse_expression(PrecLevel::ASSIGNMENT);
                children.push_back(suffix.syntax);
                diagnose(DiagnosticLevel::Error,
                         "unsupported C++ function declaration suffix",
                         suffix_loc);
                declarator.has_unsupported_semantics = true;
            }
        }

        if (is_typedef) {
            collect_session_.discard_lifetime_boundary(declarator_boundary);
            collect::DeclResult result = handle_typedef_declarator(declarator);
            result.has_error =
                !declarator_access.finish(result.entity) || result.has_error;
            declaration_results.push_back(std::move(result));
        } else if (declarator.is_function) {
            collect_session_.discard_lifetime_boundary(declarator_boundary);
            saw_function_declaration = true;
            FunctionDeclaratorResult result;
            if (declarator.abbreviated_template_info.has_value()) {
                collect::Session::TemplateInfo abbreviated =
                    std::move(*declarator.abbreviated_template_info);
                declarator.abbreviated_template_info.reset();
                result = handle_abbreviated_function_template(
                    std::move(declarator),
                    std::move(abbreviated),
                    children,
                    declarator_flags,
                    begin,
                    top_level);
            } else {
                result = handle_function_declarator(
                    std::move(declarator), children, declarator_flags);
            }
            result.decl.has_error =
                !declarator_access.finish(result.decl.entity) ||
                result.decl.has_error;
            if ((declarator_flags.is_deleted ||
                 declarator_flags.is_defaulted) &&
                check(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "'= delete' and '= default' are function definitions "
                         "and must occur "
                         "in a standalone declaration",
                         declarator.loc);
                result.decl.has_error = true;
            }
            if (result.parsed_definition) {
                prefix_access.discard();
                return {make_node(NodeKind::FunctionDecl, begin, last_consumed_raw_end(), children),
                        std::move(result.decl)};
            }
            declaration_results.push_back(std::move(result.decl));
        } else {
            collect::DeclResult result =
                handle_variable_declarator(declarator,
                                           top_level,
                                           children,
                                           declarator_flags);
            result.has_error =
                !declarator_access.finish(result.entity) || result.has_error;
            result.fragment = collect_session_.chain(
                std::move(result.fragment),
                collect_session_.finish_lifetime_boundary(
                    declarator_boundary, declarator.loc),
                declarator.loc);
            if (declarator.deduced_class_template_info && result.type.valid()) {
                cir::TypeId resolved =
                    collect_session_.file().resolved_type(result.type);
                if (!deduced_class_replacement_type.has_value()) {
                    deduced_class_replacement_type = resolved;
                } else if (resolved !=
                           collect_session_.file().resolved_type(
                               *deduced_class_replacement_type)) {
                    diagnose(DiagnosticLevel::Error,
                             "deduced class type differs between declarators",
                             declarator.loc);
                    result.has_error = true;
                }
            }
            declaration_results.push_back(std::move(result));
        }

        if (condition_declaration) {
            if (check(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "condition declaration must contain one declarator",
                         current_loc());
                while (!at_end() && !check(TokenType::RIGHT_PAREN)) {
                    consume();
                }
            }
            break;
        }
        if (!match(TokenType::COMMA)) {
            break;
        }
        if (collect_session_.contains_auto_type(base_type.type, cir::AutoTypeFlavor::Gnu)) {
            diagnose(DiagnosticLevel::Error,
                     "'__auto_type' may only be used with a single declarator",
                     declarator.loc);
        }

        if (check(TokenType::ATTRIBUTE_KW)) {
            ParsedAttributes next_attrs = try_parse_attributes();
            pending_declarator_attrs = std::move(next_attrs.attrs);
            children.insert(children.end(),
                            next_attrs.syntax.begin(),
                            next_attrs.syntax.end());
        }
    }

    if (!condition_declaration && !match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after declaration", current_loc());
        if (top_level) {
            skip_balanced_until_semicolon_or_brace();
        } else {
            skip_until_statement_boundary();
        }
    }
    NodeKind kind = saw_function_declaration && declaration_results.size() == 1
        ? NodeKind::FunctionDecl
        : NodeKind::VarDecl;
    NodeId syntax = make_node(kind, begin, last_consumed_raw_end(), children);
    collect::DeclResult decl_result =
        collect_session_.collect_decl_sequence(std::move(declaration_results),
                                               loc_for_index(begin));
    prefix_access.discard();
    return {syntax, decl_result};
}

NodeId Parser::parse_type_name(cir::TypeId* type_out,
                               bool* is_typedef_out,
                               StorageClass* storage_class_out,
                               cir::TypeRef* type_ref_out,
                               cir::Fragment* vla_bounds_out,
                               bool* type_originates_from_template_parameter_out,
                               TypeParseContext context) {
    size_t begin = current_raw_index();
    DeclarationParser decl_parser(*this, context);
    cir::TypeRef type = decl_parser.parse_declaration(true, true);
    if (vla_bounds_out) {
        *vla_bounds_out = std::move(decl_parser.vla_bounds_fragment);
    }
    if (is_typedef_out) {
        *is_typedef_out = decl_parser.storage_class == StorageClass::Typedef;
    }
    if (storage_class_out) {
        *storage_class_out = decl_parser.storage_class;
    }
    if (type_out) {
        *type_out = type.type;
    }
    if (type_ref_out) {
        *type_ref_out = type;
    }
    if (type_originates_from_template_parameter_out) {
        *type_originates_from_template_parameter_out =
            decl_parser.type_originates_from_template_parameter;
    }
    std::vector<NodeId> children;
    if (decl_parser.type_syntax != InvalidNodeId) {
        children.push_back(decl_parser.type_syntax);
    }
    if (decl_parser.declarator_syntax != InvalidNodeId) {
        children.push_back(decl_parser.declarator_syntax);
    }
    return make_node(NodeKind::TypeName,
                     begin,
                     last_consumed_raw_end(),
                     children,
                     text_payload(collect_session_.file().format_type(type)));
}

NodeId Parser::parse_name_node(NodeKind kind) {
    size_t begin = current_raw_index();
    std::string text = std::string(current().value);
    consume();
    return make_node(kind, begin, last_consumed_raw_end(), {}, text_payload(std::move(text)));
}

bool Parser::is_attribute_start() const {
    if (check(TokenType::ATTRIBUTE_KW) || check(TokenType::ALIGNAS)) {
        return true;
    }
    if (check(TokenType::LEFT_BRACKET) &&
        peek(1).type == TokenType::LEFT_BRACKET) {

        return !(lang_opts_.is_objc() && !lang_opts_.is_cxx_mode());
    }
    return false;
}

ParsedAttribute Parser::parse_alignas_attribute() {
    Token align_tok = current();
    consume();
    ParsedAttribute attr;
    attr.name = "aligned";
    attr.kind = AttributeKind::Aligned;
    attr.syntax = AttributeSyntax::Alignas;
    attr.loc = align_tok.loc;

    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '(' after alignment specifier",
                 align_tok.loc);
        return attr;
    }
    auto parse_alignment = [&]() -> std::optional<int64_t> {
        const bool starts_qualified_name =
            lang_opts_.is_cxx_mode() && starts_cxx_qualified_name();
        bool qualified_type_id =
            starts_qualified_name && peek_cxx_qualified_type().has_value();
        if (starts_qualified_name && !qualified_type_id) {

            RevertingTentativeParsingAction trial(
                *this, TentativeMode::CollectBacked);
            size_t diagnostics_before = diagnostics_.size();
            size_t errors_before =
                collect_session_.file().errors().size();
            cir::TypeId probed_type{};
            parse_type_name(&probed_type);
            qualified_type_id =
                probed_type.valid() &&
                (check(TokenType::RIGHT_PAREN) ||
                 check(TokenType::ELLIPSIS)) &&
                diagnostics_.size() == diagnostics_before &&
                collect_session_.file().errors().size() == errors_before;
        }
        const bool starts_type_id =
            starts_qualified_name
                ? qualified_type_id
                : is_type_start(current().type);
        if (starts_type_id &&
            current().type != TokenType::ALIGNAS &&
            current().type != TokenType::ATTRIBUTE_KW) {
            std::optional<std::string> direct_pack_name;
            if (current().isIdentifierLike()) {
                direct_pack_name = std::string(current().value);
            }
            cir::TypeId type{};
            parse_type_name(&type);
            if (direct_pack_name.has_value() &&
                collect_session_.type_contains_type_parameter_pack(type)) {
                collect_session_.capture_type_parameter_pack_name(
                    *direct_pack_name);
            }
            if (!type.valid() || collect_session_.is_dependent_type(type)) {
                return std::nullopt;
            }
            std::optional<size_t> alignment =
                cir::align_of_type(collect_session_.file(), type);
            return alignment.has_value()
                ? std::optional<int64_t>(static_cast<int64_t>(*alignment))
                : std::nullopt;
        }
        ParsedExpr expr = parse_conditional_expression();
        if (collect_session_.expr_is_value_dependent(expr.sem)) {
            return std::nullopt;
        }
        int64_t value = 0;
        if (!collect_session_.evaluate_integer_constant(
                expr.sem,
                value,
                align_tok.loc,
                "alignment attribute is not an integer constant expression")) {
            return std::nullopt;
        }
        return value;
    };

    std::optional<int64_t> strictest;
    if (expression_list_element_has_pack_ellipsis(TokenType::RIGHT_PAREN,
                                                  TokenType::RIGHT_PAREN)) {
        std::optional<PackExpansionPattern> pattern =
            try_parse_pack_expansion_pattern(
                [&] { (void)parse_alignment(); });
        if (pattern.has_value() && pattern->has_pack_names()) {
            bool dependent = false;
            std::optional<size_t> count =
                resolve_pack_expansion_element_count(*pattern, &dependent);
            if (dependent) {
                parse_pack_expansion_pattern_deferred(
                    [&] { (void)parse_alignment(); });
                cursor_ = pattern->after_ellipsis_cursor;
                last_consumed_raw_end_ =
                    pattern->after_ellipsis_last_consumed_raw_end;
            } else {
                replay_pack_expansion_elements(
                    *pattern,
                    count.value_or(0),
                    [&](size_t) {
                        std::optional<int64_t> alignment = parse_alignment();
                        if (alignment.has_value() &&
                            (!strictest.has_value() ||
                             *alignment > *strictest)) {
                            strictest = *alignment;
                        }
                    });
            }
        } else if (pattern.has_value()) {
            diagnose(
                DiagnosticLevel::Error,
                "pack expansion pattern does not contain an unexpanded pack",
                pattern->ellipsis_loc);
            cursor_ = pattern->after_ellipsis_cursor;
            last_consumed_raw_end_ =
                pattern->after_ellipsis_last_consumed_raw_end;
        }
    } else {
        strictest = parse_alignment();
    }
    if (strictest.has_value()) {
        attr.args.push_back(
            AttributeArg::integer(*strictest, align_tok.loc));
    }
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after alignment specifier",
                 current_loc());
        while (!at_end() &&
               !check(TokenType::RIGHT_PAREN) &&
               !check(TokenType::SEMICOLON) &&
               !check(TokenType::LEFT_BRACE)) {
            consume();
        }
        match(TokenType::RIGHT_PAREN);
    }
    return attr;
}

Parser::ParsedAttributes Parser::try_parse_attributes() {
    ParsedAttributes parsed;
    while (!at_end()) {
        if (check(TokenType::ATTRIBUTE_KW)) {
            ParsedAttributes gnu = parse_gnu_attribute_list();
            parsed.attrs.append(std::move(gnu.attrs));
            parsed.syntax.insert(parsed.syntax.end(), gnu.syntax.begin(), gnu.syntax.end());
            continue;
        }
        if (check(TokenType::ALIGNAS)) {
            size_t begin = current_raw_index();
            ParsedAttribute attr = parse_alignas_attribute();
            parsed.attrs.attrs.push_back(std::move(attr));
            parsed.syntax.push_back(make_node(NodeKind::AmbiguousSyntax,
                                              begin,
                                              last_consumed_raw_end(),
                                              {},
                                              text_payload("alignas")));
            continue;
        }
        if (check(TokenType::LEFT_BRACKET) &&
            peek(1).type == TokenType::LEFT_BRACKET) {
            ParsedAttributes standard = parse_cxx_standard_attribute_list();
            parsed.attrs.append(std::move(standard.attrs));
            parsed.syntax.insert(parsed.syntax.end(),
                                 standard.syntax.begin(),
                                 standard.syntax.end());
            continue;
        }
        break;
    }
    return parsed;
}

Parser::ParsedAttributes Parser::try_parse_standard_or_gnu_attributes() {
    ParsedAttributes parsed;
    while (!at_end()) {
        if (check(TokenType::ATTRIBUTE_KW)) {
            ParsedAttributes gnu = parse_gnu_attribute_list();
            parsed.attrs.append(std::move(gnu.attrs));
            parsed.syntax.insert(parsed.syntax.end(), gnu.syntax.begin(), gnu.syntax.end());
            continue;
        }
        if (check(TokenType::LEFT_BRACKET) &&
            peek(1).type == TokenType::LEFT_BRACKET) {
            ParsedAttributes standard = parse_cxx_standard_attribute_list();
            parsed.attrs.append(std::move(standard.attrs));
            parsed.syntax.insert(parsed.syntax.end(),
                                 standard.syntax.begin(),
                                 standard.syntax.end());
            continue;
        }
        break;
    }
    return parsed;
}

size_t Parser::skip_attribute_specifier_sequence_offset(size_t offset) const {
    auto skip_parenthesized = [&](size_t begin) {
        int depth = 0;
        size_t cursor = begin;
        do {
            TokenType type = peek(cursor).type;
            if (type == TokenType::Eof) {
                return cursor;
            }
            if (type == TokenType::LEFT_PAREN) {
                ++depth;
            } else if (type == TokenType::RIGHT_PAREN) {
                --depth;
            }
            ++cursor;
        } while (depth > 0);
        return cursor;
    };

    while (true) {
        TokenType type = peek(offset).type;
        if ((type == TokenType::ATTRIBUTE_KW ||
             type == TokenType::ALIGNAS) &&
            peek(offset + 1).type == TokenType::LEFT_PAREN) {
            offset = skip_parenthesized(offset + 1);
            continue;
        }
        if (type != TokenType::LEFT_BRACKET ||
            peek(offset + 1).type != TokenType::LEFT_BRACKET) {
            return offset;
        }

        offset += 2;
        int paren_depth = 0;
        int brace_depth = 0;
        int bracket_depth = 0;
        while (true) {
            type = peek(offset).type;
            if (type == TokenType::Eof) {
                return offset;
            }
            if (type == TokenType::RIGHT_BRACKET &&
                peek(offset + 1).type == TokenType::RIGHT_BRACKET &&
                paren_depth == 0 &&
                brace_depth == 0 &&
                bracket_depth == 0) {
                offset += 2;
                break;
            }
            if (type == TokenType::LEFT_PAREN) {
                ++paren_depth;
            } else if (type == TokenType::RIGHT_PAREN &&
                       paren_depth > 0) {
                --paren_depth;
            } else if (type == TokenType::LEFT_BRACE) {
                ++brace_depth;
            } else if (type == TokenType::RIGHT_BRACE &&
                       brace_depth > 0) {
                --brace_depth;
            } else if (type == TokenType::LEFT_BRACKET) {
                ++bracket_depth;
            } else if (type == TokenType::RIGHT_BRACKET &&
                       bracket_depth > 0) {
                --bracket_depth;
            }
            ++offset;
        }
    }
}

Parser::ParsedAttributes Parser::parse_gnu_attribute_list() {
    ParsedAttributes parsed;
    while (check(TokenType::ATTRIBUTE_KW)) {
        size_t begin = current_raw_index();
        consume();
        if (!match(TokenType::LEFT_PAREN) || !match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '((' after __attribute__",
                     last_consumed_loc());
            parsed.syntax.push_back(make_node(NodeKind::AmbiguousSyntax,
                                              begin,
                                              last_consumed_raw_end(),
                                              {},
                                              text_payload("__attribute__"),
                                              NodeFlagHasError));
            continue;
        }
        while (!at_end() && !check(TokenType::RIGHT_PAREN)) {
            if (match(TokenType::COMMA)) {
                continue;
            }
            ParsedAttribute attr = parse_single_gnu_attribute();
            parsed.attrs.attrs.push_back(std::move(attr));
            if (!check(TokenType::RIGHT_PAREN)) {
                match(TokenType::COMMA);
            }
        }
        match(TokenType::RIGHT_PAREN);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after __attribute__ list",
                     current_loc());
        }
        parsed.syntax.push_back(make_node(NodeKind::AmbiguousSyntax,
                                          begin,
                                          last_consumed_raw_end(),
                                          {},
                                          text_payload("__attribute__")));
    }
    return parsed;
}

Parser::ParsedAttributes Parser::parse_cxx_standard_attribute_list() {
    ParsedAttributes parsed;
    size_t begin = current_raw_index();
    consume();
    consume();
    std::string using_namespace;
    if (check(TokenType::USING)) {
        consume();
        if (current().isIdentifierLike()) {
            using_namespace = canonicalize_attribute_name(current().value);
            consume();
        } else {
            diagnose(DiagnosticLevel::Error,
                     "expected namespace name after 'using' in attribute list",
                     current_loc());
        }
        if (!match(TokenType::COLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ':' after attribute namespace",
                     current_loc());
        }
    }

    auto parse_standard_attribute = [&]() {
        ParsedAttribute attr;
        if (!current().isIdentifierLike()) {
            diagnose(DiagnosticLevel::Error,
                     "expected attribute name in attribute list",
                     current_loc());
            if (!at_end()) {
                consume();
            }
            return attr;
        }

        attr.loc = current().loc;
        attr.syntax = AttributeSyntax::Standard;
        std::string first = std::string(current().value);
        consume();
        bool has_scope_resolution = false;
        if (check(TokenType::SCOPE_RESOLUTION)) {
            consume();
            has_scope_resolution = true;
        } else if (check(TokenType::COLON) &&
                   peek(1).type == TokenType::COLON) {
            consume();
            consume();
            has_scope_resolution = true;
        }
        if (has_scope_resolution) {
            attr.ns = canonicalize_attribute_name(first);
            if (current().isIdentifierLike()) {
                attr.name = current().value;
                consume();
            } else {
                diagnose(DiagnosticLevel::Error,
                         "expected attribute name after '::'",
                         current_loc());
            }
        } else {
            attr.ns = using_namespace;
            attr.name = first;
        }

        const AttributeDescriptor* desc =
            AttributeRegistry::instance().find(attr.canonical_name());
        attr.kind = desc ? desc->kind : AttributeKind::Unknown;
        if (match(TokenType::LEFT_PAREN)) {
            bool parse_integer_expression =
                attr.kind == AttributeKind::Aligned ||
                attr.canonical_name() == "vector_size" ||
                attr.canonical_name() == "ext_vector_type";
            while (!at_end() && !check(TokenType::RIGHT_PAREN)) {
                if (match(TokenType::COMMA)) {
                    continue;
                }
                Token arg = current();
                if (arg.isIdentifierLike() &&
                    peek(1).type == TokenType::ASSIGN) {
                    std::string key = std::string(arg.value);
                    consume();
                    consume();
                    if (current().type == TokenType::STRING_LITERAL ||
                        current().isIdentifierLike() ||
                        is_integer_token(current().type) ||
                        is_floating_token(current().type) ||
                        current().type == TokenType::PP_NUMBER) {
                        attr.args.push_back(AttributeArg::key_value(
                            key,
                            std::string(current().value),
                            current().loc));
                        consume();
                    }
                } else if (parse_integer_expression) {
                    ParsedExpr expr = parse_conditional_expression();
                    int64_t value = 0;
                    if (collect_session_.expr_is_value_dependent(expr.sem)) {
                        AttributeArg dependent =
                            AttributeArg::token_text("<dependent>", arg.loc);
                        if (std::optional<uint32_t> parameter =
                                direct_template_value_parameter(
                                    collect_session_, expr.sem)) {
                            dependent.dependent_value_param_index =
                                *parameter;
                        }
                        attr.args.push_back(std::move(dependent));
                    } else {
                        std::string message =
                            attr.kind == AttributeKind::Aligned
                                ? "alignment attribute is not an integer constant expression"
                                : attr.canonical_name() == "vector_size"
                                      ? "vector_size requires an integer constant expression"
                                      : "ext_vector_type requires an integer constant expression";
                        if (collect_session_.evaluate_integer_constant(
                                expr.sem, value, arg.loc, message)) {
                            attr.args.push_back(
                                AttributeArg::integer(value, arg.loc));
                        }
                    }
                } else if (arg.type == TokenType::STRING_LITERAL) {
                    attr.args.push_back(AttributeArg::string(
                        std::string(arg.value), arg.loc));
                    consume();
                } else if (is_integer_token(arg.type)) {
                    int64_t value = 0;
                    if (auto integer = parse_integer_literal_u64(arg.value)) {
                        value = static_cast<int64_t>(*integer);
                    }
                    attr.args.push_back(AttributeArg::integer(value, arg.loc));
                    consume();
                } else if (is_floating_token(arg.type)) {
                    long double value = 0.0;
                    try {
                        value = std::stold(std::string(arg.value));
                    } catch (...) {
                        value = 0.0;
                    }
                    attr.args.push_back(AttributeArg::floating(
                        std::string(arg.value), value, arg.loc));
                    consume();
                } else if (arg.isIdentifierLike()) {
                    attr.args.push_back(AttributeArg::identifier(
                        std::string(arg.value), arg.loc));
                    consume();
                } else {
                    attr.args.push_back(AttributeArg::token_text(
                        std::string(arg.value), arg.loc));
                    consume();
                }
                if (!check(TokenType::RIGHT_PAREN)) {
                    match(TokenType::COMMA);
                }
            }
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after attribute arguments",
                         current_loc());
            }
        }
        if (attr.kind == AttributeKind::Unknown) {
            diagnose_flagged(WarningId::UnknownAttributes,
                             "unknown attribute '" + attr.name + "'",
                             attr.loc);
        }
        return attr;
    };

    while (!at_end()) {
        if (check(TokenType::RIGHT_BRACKET) &&
            peek(1).type == TokenType::RIGHT_BRACKET) {
            consume();
            consume();
            break;
        }
        if (match(TokenType::COMMA)) {
            continue;
        }
        if (expression_list_element_has_pack_ellipsis(
                TokenType::COMMA, TokenType::RIGHT_BRACKET)) {
            std::optional<PackExpansionPattern> pattern =
                try_parse_pack_expansion_pattern(
                    [&] { (void)parse_standard_attribute(); });
            if (pattern.has_value()) {
                if (!pattern->has_pack_names()) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "pack expansion pattern does not contain an unexpanded pack",
                        pattern->ellipsis_loc);
                    cursor_ = pattern->after_ellipsis_cursor;
                    last_consumed_raw_end_ =
                        pattern->after_ellipsis_last_consumed_raw_end;
                } else {
                    bool dependent = false;
                    std::optional<size_t> count =
                        resolve_pack_expansion_element_count(*pattern,
                                                             &dependent);
                    if (dependent) {
                        ParsedAttribute attr;
                        parse_pack_expansion_pattern_deferred(
                            [&] { attr = parse_standard_attribute(); });
                        parsed.attrs.attrs.push_back(std::move(attr));
                        cursor_ = pattern->after_ellipsis_cursor;
                        last_consumed_raw_end_ =
                            pattern->after_ellipsis_last_consumed_raw_end;
                    } else {
                        replay_pack_expansion_elements(
                            *pattern,
                            count.value_or(0),
                            [&](size_t) {
                                parsed.attrs.attrs.push_back(
                                    parse_standard_attribute());
                            });
                    }
                }
                if (!check(TokenType::RIGHT_BRACKET)) {
                    match(TokenType::COMMA);
                }
                continue;
            }
        }
        parsed.attrs.attrs.push_back(parse_standard_attribute());
        if (!check(TokenType::RIGHT_BRACKET)) {
            match(TokenType::COMMA);
        }
    }
    parsed.syntax.push_back(make_node(NodeKind::AmbiguousSyntax,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload("[[attribute]]")));
    return parsed;
}

ParsedAttribute Parser::parse_single_gnu_attribute() {
    ParsedAttribute attr;
    attr.loc = current().loc;
    attr.syntax = AttributeSyntax::GNU;
    if (!current().isIdentifierLike()) {
        diagnose(DiagnosticLevel::Error,
                 "expected attribute name",
                 current_loc());
        return attr;
    }
    attr.name = current().value;
    consume();

    bool parse_vector_arg =
        attr.canonical_name() == "vector_size" ||
        attr.canonical_name() == "ext_vector_type";
    if (match(TokenType::LEFT_PAREN)) {
        while (!at_end() && !check(TokenType::RIGHT_PAREN)) {
            if (match(TokenType::COMMA)) {
                continue;
            }
            Token arg = current();
            if (arg.isIdentifierLike() && peek(1).type == TokenType::ASSIGN) {
                std::string key = std::string(arg.value);
                consume();
                consume();
                if (current().type == TokenType::STRING_LITERAL ||
                    current().isIdentifierLike() ||
                    is_integer_token(current().type) ||
                    is_floating_token(current().type) ||
                    current().type == TokenType::PP_NUMBER) {
                    attr.args.push_back(
                        AttributeArg::key_value(key, std::string(current().value), current().loc));
                    consume();
                }
            } else if (parse_vector_arg) {
                ParsedExpr expr = parse_conditional_expression();
                int64_t value = 0;
                if (collect_session_.expr_is_value_dependent(expr.sem)) {
                    AttributeArg dependent =
                        AttributeArg::token_text("<dependent>", arg.loc);
                    if (std::optional<uint32_t> parameter =
                            direct_template_value_parameter(
                                collect_session_, expr.sem)) {
                        dependent.dependent_value_param_index =
                            *parameter;
                    }
                    attr.args.push_back(std::move(dependent));
                } else if (collect_session_.evaluate_integer_constant(
                               expr.sem,
                               value,
                               arg.loc,
                               attr.canonical_name() == "vector_size"
                                   ? "vector_size requires an integer constant expression"
                                   : "ext_vector_type requires an integer constant expression")) {
                    attr.args.push_back(AttributeArg::integer(value, arg.loc));
                }
            } else if (arg.type == TokenType::STRING_LITERAL) {
                attr.args.push_back(AttributeArg::string(std::string(arg.value), arg.loc));
                consume();
            } else if (arg.isIdentifierLike() &&
                       (peek(1).type == TokenType::COMMA ||
                        peek(1).type == TokenType::RIGHT_PAREN)) {

                attr.args.push_back(AttributeArg::identifier(std::string(arg.value), arg.loc));
                consume();
            } else if (is_integer_token(arg.type) &&
                       (peek(1).type == TokenType::COMMA ||
                        peek(1).type == TokenType::RIGHT_PAREN)) {
                int64_t value = 0;
                if (auto parsed = parse_integer_literal_u64(arg.value)) {
                    value = static_cast<int64_t>(*parsed);
                }
                attr.args.push_back(AttributeArg::integer(value, arg.loc));
                consume();
            } else if (is_floating_token(arg.type)) {
                long double value = 0.0;
                try {
                    value = std::stold(std::string(arg.value));
                } catch (...) {
                    value = 0.0;
                }
                attr.args.push_back(AttributeArg::floating(std::string(arg.value), value, arg.loc));
                consume();
            } else if (arg.type == TokenType::SCOPE_RESOLUTION ||
                       arg.type == TokenType::LEFT_PAREN ||
                       arg.isIdentifierLike() ||
                       is_integer_token(arg.type) ||
                       arg.type == TokenType::NEGATE ||
                       arg.type == TokenType::PLUS ||
                       arg.type == TokenType::BITWISE_NOT ||
                       arg.type == TokenType::LOGICAL_NOT) {

                ParsedExpr expr = parse_conditional_expression();
                int64_t value = 0;
                if (collect_session_.expr_is_value_dependent(expr.sem)) {
                    attr.args.push_back(AttributeArg::token_text("<dependent>", arg.loc));
                } else if (collect_session_.evaluate_integer_constant(
                               expr.sem,
                               value,
                               arg.loc,
                               "attribute '" + attr.canonical_name() +
                                   "' requires an integer constant expression")) {
                    attr.args.push_back(AttributeArg::integer(value, arg.loc));
                } else {

                    attr.args.push_back(AttributeArg::token_text("<invalid>", arg.loc));
                }
            } else {
                attr.args.push_back(AttributeArg::token_text(std::string(arg.value), arg.loc));
                consume();
            }
            if (!check(TokenType::RIGHT_PAREN)) {
                match(TokenType::COMMA);
            }
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after attribute arguments",
                     current_loc());
        }
    }
    const AttributeDescriptor* desc =
        AttributeRegistry::instance().find(attr.canonical_name());
    attr.kind = desc ? desc->kind : AttributeKind::Unknown;
    if (attr.kind == AttributeKind::Unknown) {
        diagnose_flagged(WarningId::UnknownAttributes,
                         "unknown attribute '" + attr.name + "'",
                         attr.loc);
    }
    return attr;
}

NodeId Parser::parse_gnu_attribute_syntax() {
    ParsedAttributes attrs = parse_gnu_attribute_list();
    return attrs.syntax.empty() ? InvalidNodeId : attrs.syntax.front();
}

NodeId Parser::parse_asm_label_syntax(std::string* label_out) {
    size_t begin = current_raw_index();
    consume();
    if (check(TokenType::LEFT_PAREN)) {
        int parens = 0;
        do {
            TokenType type = current().type;
            if (label_out && type == TokenType::STRING_LITERAL) {
                *label_out += current().value;
            }
            consume();
            if (type == TokenType::LEFT_PAREN) ++parens;
            if (type == TokenType::RIGHT_PAREN) --parens;
        } while (!at_end() && parens > 0);
    }
    return make_node(NodeKind::AmbiguousSyntax,
                     begin,
                     last_consumed_raw_end(),
                     {},
                     text_payload("asm"));
}

NodeId Parser::parse_cxx_standard_attribute_syntax() {
    size_t begin = current_raw_index();
    consume();
    if (check(TokenType::LEFT_BRACKET)) {
        consume();
    }
    while (!at_end()) {
        if (check(TokenType::RIGHT_BRACKET) &&
            peek(1).type == TokenType::RIGHT_BRACKET) {
            consume();
            consume();
            break;
        }
        consume();
    }
    return make_node(NodeKind::AmbiguousSyntax,
                     begin,
                     last_consumed_raw_end(),
                     {},
                     text_payload("[[attribute]]"));
}

Parser::ParsedParam Parser::parse_parameter(
    bool instantiate_default_argument,
    TypeParseContext context) {
    size_t begin = current_raw_index();
    DeclarationParser decl_parser(*this, context);
    decl_parser.defer_abbreviated_parameter_rewrite = true;
    cir::TypeRef param_base = decl_parser.parse_declaration(false, true);
    decl_parser.allow_parameter_pack_declarator = true;
    ParsedDeclarator declarator = decl_parser.parse_declarator(param_base, true);
    std::vector<NodeId> children{decl_parser.type_syntax};
    std::string param_name = declarator.has_name ? declarator.name : "<anonymous>";
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }
    AttributeList attrs = decl_parser.leading_attrs;
    bool has_default_argument = false;
    size_t default_argument_begin = 0;
    size_t default_argument_end = 0;
    SrcLoc default_argument_loc{};
    if (match(TokenType::ASSIGN)) {
        if (!lang_opts_.is_cxx_mode()) {
            diagnose(DiagnosticLevel::Error,
                     "default arguments are only allowed in C++ declarations",
                     last_consumed_loc());
        }
        default_argument_begin = current_raw_index();
        default_argument_loc = current_loc();
        bool defer_default_argument_collection =
            collect_session_.is_instantiating() &&
            !instantiate_default_argument &&
            !instantiate_member_parameter_defaults_;
        size_t diagnostic_watermark = diagnostics_.size();
        if (defer_default_argument_collection) {
            collect_session_.begin_speculative_parse();
        }
        ParsedExpr default_arg = parse_expression(PrecLevel::ASSIGNMENT);
        if (defer_default_argument_collection) {
            collect_session_.rollback_speculative_parse();
            diagnostics_.resize(diagnostic_watermark);
        }
        default_argument_end = current_raw_index();
        children.push_back(default_arg.syntax);
        has_default_argument = true;
    }
    ParsedAttributes trailing_attrs = try_parse_attributes();
    attrs.append(declarator.attrs);
    attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(), trailing_attrs.syntax.begin(), trailing_attrs.syntax.end());
    if (!declarator.is_function) {
        declarator.type_ref =
            collect_session_.apply_type_attributes(declarator.type_ref,
                                                   attrs,
                                                   declarator.loc);
        declarator.type = declarator.type_ref.type;
    }
    adjust_function_parameter_type(declarator.type_ref);
    declarator.type = declarator.type_ref.type;
    NodeId syntax = make_node(NodeKind::ParamDecl, begin, last_consumed_raw_end(), children);
    bool is_parameter_pack =
        decl_parser.is_parameter_pack || declarator.is_parameter_pack;
    ParsedParam result{syntax,
                       std::move(param_name),
                       declarator.type,
                       declarator.type_ref,
                       declarator.loc,
                       std::move(attrs),
                       has_default_argument,
                       default_argument_begin,
                       default_argument_end,
                       default_argument_loc,
                       {},
                       std::move(declarator.vla_bounds),
                       is_parameter_pack,
                       {},
                       false};
    result.abbreviated_type_constraints =
        std::move(decl_parser.abbreviated_type_constraints);
    result.type_originates_from_template_parameter =
        decl_parser.type_originates_from_template_parameter;
    return result;
}

void Parser::adjust_function_parameter_type(cir::TypeRef& type_ref) {
    const cir::File& file = collect_session_.file();
    cir::TypeId resolved = file.valid(type_ref.type)
        ? file.resolved_type(type_ref.type)
        : cir::TypeId{};
    if (!file.valid(resolved)) {
        return;
    }
    const cir::Type& type = file.type(resolved);
    if (type.kind == cir::TypeKind::Array) {
        const auto* array =
            std::get_if<cir::ArrayTypePayload>(&file.type_payload(resolved));
        if (!array) {
            return;
        }
        cir::TypeId pointer =
            collect_session_.pointer_type(array->element_type);
        type_ref = cir::TypeRef{pointer,
                                type_ref.qualifiers,
                                type_ref.memory_space};
        return;
    }
    if (type.kind == cir::TypeKind::Function) {
        cir::TypeId pointer =
            collect_session_.pointer_type(file.type_ref(type_ref.type));
        type_ref = cir::TypeRef{pointer,
                                type_ref.qualifiers,
                                type_ref.memory_space};
    }
}

std::vector<Parser::ParsedParam> Parser::parse_parameter_list(
    bool instantiate_default_arguments,
    TypeParseContext context,
    bool* is_variadic_out,
    const std::function<void(ParsedParam&, uint32_t)>&
        on_finalized_parameter,
    ParameterListPolicy policy) {
    std::vector<ParsedParam> params;
    if (is_variadic_out) {
        *is_variadic_out = false;
    }
    if (match(TokenType::RIGHT_PAREN)) {
        return params;
    }
    if (check(TokenType::VOID) && peek(1).type == TokenType::RIGHT_PAREN) {
        consume();
        match(TokenType::RIGHT_PAREN);
        return params;
    }
    while (!at_end()) {
        if (check(TokenType::ELLIPSIS)) {
            if (!is_variadic_out) {
                diagnose(DiagnosticLevel::Error,
                         "expected parameter declaration",
                         current_loc());
                skip_until_statement_boundary();
                break;
            }
            consume();
            *is_variadic_out = true;
            if (policy == ParameterListPolicy::RequirementLocal) {
                diagnose(
                    DiagnosticLevel::Error,
                    "requires-expression parameter list shall not terminate with an ellipsis",
                    last_consumed_loc());
            }
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(
                    DiagnosticLevel::Error,
                    policy == ParameterListPolicy::RequirementLocal
                        ? "expected ')' after requires-expression parameter list"
                        : "expected ')' after variadic parameter list",
                    current_loc());
            }
            break;
        }
        bool starts_constrained_placeholder =
            lang_opts_.is_cxx_mode() &&
            starts_type_constraint_placeholder();
        if (!is_type_start(current().type) && !is_attribute_start() &&
            !starts_constrained_placeholder &&
            !(context.is_type_only() && starts_cxx_qualified_name())) {
            diagnose(
                DiagnosticLevel::Error,
                policy == ParameterListPolicy::RequirementLocal
                    ? "expected requires-expression parameter declaration"
                    : "expected parameter declaration",
                current_loc());
            skip_until_statement_boundary();
            break;
        }

        size_t pattern_cursor = cursor_;
        size_t pattern_last_consumed = last_consumed_raw_end_;
        collect::Session::ParameterPackPatternCaptureScope pack_scope;
        bool capture_packs = lang_opts_.is_cxx_mode();
        if (capture_packs) {
            pack_scope = collect_session_.begin_parameter_pack_pattern_capture();
        }
        ParsedParam param =
            parse_parameter(instantiate_default_arguments, context);
        std::vector<collect::Session::ParameterPackIdentity> packs;
        if (capture_packs) {
            packs = collect_session_.finish_parameter_pack_pattern_capture(
                pack_scope);
        }
        bool parsed_parameter_pack = param.is_parameter_pack;
        size_t finalized_begin = params.size();
        if (policy == ParameterListPolicy::RequirementLocal &&
            param.has_default_argument) {
            diagnose(
                DiagnosticLevel::Error,
                "requires-expression local parameter shall not have a default argument",
                param.default_argument_loc.isInvalid()
                    ? param.loc
                    : param.default_argument_loc);
        } else if (parsed_parameter_pack && param.has_default_argument) {
            diagnose(DiagnosticLevel::Error,
                     "function parameter pack cannot have a default argument",
                     param.default_argument_loc);
        }
        if (!packs.empty() && param.is_parameter_pack) {
            append_decorated_parameter_pack(param,
                                            packs,
                                            pattern_cursor,
                                            pattern_last_consumed,
                                            params);
        } else if (!packs.empty()) {
            diagnose(DiagnosticLevel::Error,
                     "unexpanded template parameter pack '" +
                         packs.front().name + "' is not supported yet",
                     param.loc);
            params.push_back(std::move(param));
        } else if (!append_concrete_type_parameter_pack(param, params)) {
            params.push_back(std::move(param));
        }
        if (on_finalized_parameter) {
            for (size_t i = finalized_begin; i < params.size(); ++i) {
                on_finalized_parameter(params[i],
                                       static_cast<uint32_t>(i));
            }
        }
        if (match(TokenType::RIGHT_PAREN)) {
            break;
        }
        if (!match(TokenType::COMMA)) {
            diagnose(
                DiagnosticLevel::Error,
                policy == ParameterListPolicy::RequirementLocal
                    ? "expected ',' or ')' in requires-expression parameter list"
                    : "expected ',' or ')' in parameter list",
                current_loc());
            while (!at_end() && !check(TokenType::RIGHT_PAREN) && !check(TokenType::LEFT_BRACE)) {
                consume();
            }
            match(TokenType::RIGHT_PAREN);
            break;
        }
    }
    return params;
}

void Parser::append_decorated_parameter_pack(
    ParsedParam& pattern_param,
    const std::vector<collect::Session::ParameterPackIdentity>& packs,
    size_t pattern_cursor,
    size_t pattern_last_consumed_raw_end,
    std::vector<ParsedParam>& destination) {

    std::optional<size_t> element_count;
    bool dependent = false;
    for (const collect::Session::ParameterPackIdentity& pack : packs) {
        std::optional<size_t> count =
            collect_session_.parameter_pack_element_count(pack);
        if (!count.has_value()) {
            dependent = true;
            break;
        }
        if (element_count.has_value() &&
            *element_count != *count) {
            diagnose(DiagnosticLevel::Error,
                     "pack expansion contains packs with different lengths",
                     pattern_param.loc);
            *element_count = std::min(*element_count, *count);
        } else if (!element_count.has_value()) {
            element_count = *count;
        }
    }
    if (dependent) {
        destination.push_back(std::move(pattern_param));
        return;
    }

    size_t end_cursor = cursor_;
    size_t end_last_consumed = last_consumed_raw_end_;
    std::string source_name = pattern_param.name != "<anonymous>"
        ? pattern_param.name
        : std::string{};
    size_t count = element_count.value_or(0);
    if (count == 0) {
        ParsedParam sentinel = std::move(pattern_param);
        sentinel.syntax = InvalidNodeId;
        sentinel.is_parameter_pack = false;
        sentinel.source_parameter_pack_name = source_name;
        sentinel.is_parameter_pack_expansion_sentinel = true;
        destination.push_back(std::move(sentinel));
        return;
    }
    for (size_t i = 0; i < count; ++i) {
        cursor_ = pattern_cursor;
        last_consumed_raw_end_ = pattern_last_consumed_raw_end;
        auto replay_scope =
            collect_session_.begin_parameter_pack_element_replay(packs, i);
        ParsedParam expanded = parse_parameter();
        collect_session_.finish_parameter_pack_element_replay(replay_scope);
        if (cursor_ != end_cursor) {
            diagnose(DiagnosticLevel::Error,
                     "could not replay parameter pack expansion pattern",
                     pattern_param.loc);
            cursor_ = end_cursor;
            last_consumed_raw_end_ = end_last_consumed;
        }
        expanded.syntax = i == 0 ? pattern_param.syntax : InvalidNodeId;
        expanded.name = source_name.empty()
            ? "<anonymous>"
            : source_name + "." + std::to_string(i);
        expanded.is_parameter_pack = false;
        expanded.source_parameter_pack_name = source_name;
        expanded.is_parameter_pack_expansion_sentinel = false;
        destination.push_back(std::move(expanded));
    }
    cursor_ = end_cursor;
    last_consumed_raw_end_ = end_last_consumed;
}

bool Parser::append_concrete_type_parameter_pack(
    ParsedParam param,
    std::vector<ParsedParam>& destination) {
    if (!param.is_parameter_pack) {
        return false;
    }
    std::optional<std::vector<collect::Session::TemplateArgument>>
        concrete_type_pack =
            collect_session_.template_type_pack_arguments(param.type);
    if (!concrete_type_pack.has_value()) {
        return false;
    }

    std::string source_name = param.name != "<anonymous>"
        ? param.name
        : std::string{};
    if (concrete_type_pack->empty()) {
        ParsedParam sentinel = param;
        sentinel.syntax = InvalidNodeId;
        sentinel.is_parameter_pack = false;
        sentinel.source_parameter_pack_name = source_name;
        sentinel.is_parameter_pack_expansion_sentinel = true;
        destination.push_back(std::move(sentinel));
    }
    size_t element_index = 0;
    for (const collect::Session::TemplateArgument& element :
         *concrete_type_pack) {
        if (element.kind != cir::TemplateArgumentKind::Type) {
            continue;
        }
        ParsedParam expanded = param;
        expanded.syntax = element_index == 0 ? param.syntax : InvalidNodeId;
        expanded.name = source_name.empty()
            ? "<anonymous>"
            : source_name + "." + std::to_string(element_index);
        expanded.type = element.type.type;
        expanded.type_ref = element.type;
        expanded.is_parameter_pack = false;
        expanded.source_parameter_pack_name = source_name;
        expanded.is_parameter_pack_expansion_sentinel = false;
        destination.push_back(std::move(expanded));
        ++element_index;
    }
    return true;
}

} // namespace aburi::syntax
