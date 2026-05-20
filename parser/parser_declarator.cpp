#include "parser.h"

namespace {
bool is_lone_unnamed_void_parameter_list(
    const std::vector<QualType>& args,
    const std::vector<std::unique_ptr<DeclarationParser>>& parsed_args,
    bool is_variadic) {
    if (is_variadic || args.size() != 1 || parsed_args.size() != 1) {
        return false;
    }
    const auto* param = parsed_args.front().get();
    return param &&
        param->result_type &&
        param->result_type->isVoid() &&
        param->qualifiers == QUAL_NONE &&
        param->name.empty() &&
        !param->is_parameter_pack &&
        !param->default_argument;
}

bool parse_cpp_operator_function_name(DeclarationParser& decl_parser) {
    auto* mgnt = decl_parser.mgnt;
    auto* pars = decl_parser.pars;
    if (!pars->lang_opts.is_cxx_mode() || !mgnt->gentle_check(TokenType::OPERATOR_KW)) {
        return false;
    }

    Token operator_kw_tok = mgnt->current_token();
    mgnt->advance(); // consume 'operator'

    auto set_operator_name = [&](std::string op_name) {
        if (decl_parser.name.empty()) {
            decl_parser.name = std::move(op_name);
            decl_parser.loc = operator_kw_tok.loc;
        } else {
            decl_parser.error_custloc(
                "Potentially two names in a declarator",
                decl_parser.begin_loc);
        }
    };

    auto parse_conversion_function_name = [&]() -> bool {
        if (decl_parser.first_half) {
            decl_parser.error_custloc(
                "conversion function cannot have a declared return type",
                decl_parser.begin_loc);
        }

        DeclarationParser conversion_type_parser(pars);
        conversion_type_parser.parse_new_type_id_context = true;
        auto parsed_type = conversion_type_parser.parse_declaration(false);
        if (!parsed_type) {
            decl_parser.error_custloc(
                "expected type-id after 'operator' in conversion-function-id",
                operator_kw_tok.loc);
        }
        if (!conversion_type_parser.name.empty()) {
            decl_parser.error_custloc(
                "conversion-function-id requires a type-id, not a declarator-id",
                operator_kw_tok.loc);
        }

        QualType conversion_target(
            parsed_type,
            conversion_type_parser.qualifiers);
        while (true) {
            if (mgnt->gentle_check_and_consume(TokenType::MULTIPLY)) {
                conversion_target = QualType(
                    std::make_shared<PointerType>(conversion_target));
                continue;
            }
            if (mgnt->gentle_check_and_consume(TokenType::BITWISE_AND)) {
                conversion_target = QualType(
                    std::make_shared<ReferenceType>(
                        conversion_target,
                        ReferenceKind::LValue));
                continue;
            }
            if (mgnt->gentle_check_and_consume(TokenType::LOGICAL_AND)) {
                conversion_target = QualType(
                    std::make_shared<ReferenceType>(
                        conversion_target,
                        ReferenceKind::RValue));
                continue;
            }
            break;
        }
        decl_parser.is_conversion_function = true;
        decl_parser.conversion_target_type = conversion_target;
        if (decl_parser.name.empty()) {
            decl_parser.name = "operator " + conversion_target.to_string();
            decl_parser.loc = operator_kw_tok.loc;
        }
        return true;
    };

    if (auto operator_name =
            pars->try_parse_cpp_overloadable_operator_function_id_name_after_operator_keyword()) {
        set_operator_name(std::move(*operator_name));
    } else {
        return parse_conversion_function_name();
    }

    return true;
}
} // namespace

std::shared_ptr<CType> DeclarationParser::parse_declaration(bool run_second_half) {
        DeclarationParser::TypeTally tally;
        begin_loc = mgnt->current_token().loc;
        typedef_resolved_type = nullptr;
        typedef_resolved_qualifiers = QUAL_NONE;
        pending_cxx_auto_type_constraint = nullptr;
        is_block_byref = false;
        is_constexpr = false;
        is_consteval = false;
        is_mutable = false;
        is_inline = false;
        explicit_specifier = CppExplicitSpecifier{};
        bool parsing = true;
        std::shared_ptr<CType> atomic_type_specifier = nullptr; // _Atomic(type-name) resolved type
        // Collect declaration-specifier tokens first; semantic normalization is
        // resolved after this pass once we know the complete specifier set.
        while (parsing) {
            Token t = mgnt->current_token();
            bool blocks_enabled =
                pars && pars->type_ctx && pars->type_ctx->target &&
                darwin_blocks::blocks_enabled_for_langopts(
                    pars->lang_opts,
                    *pars->type_ctx->target);
            if (blocks_enabled &&
                t.type == TokenType::IDENTIFIER &&
                t.value == "__block") {
                if (in_function_parameter) {
                    error_custloc(
                        "__block attribute not allowed, only allowed on local variables",
                        t.loc);
                }
                tally.block_byref_count++;
                is_block_byref = true;
                mgnt->advance();
                continue;
            }
            switch (t.type) {
                // Type Specifiers
                case TokenType::VOID:     tally.void_count++; break;
                case TokenType::CHAR:     tally.char_count++; break;
                case TokenType::SHORT:    tally.short_count++; break;
                case TokenType::INT:      tally.int_count++; break;
                case TokenType::LONG:     tally.long_count++; break;
                case TokenType::FLOAT:    tally.float_count++; break;
                case TokenType::DOUBLE:   tally.double_count++; break;
                case TokenType::SIGNED:   tally.signed_count++; break;
                case TokenType::UNSIGNED: tally.unsigned_count++; break;
                case TokenType::BOOL:     tally.bool_count++; break;
                case TokenType::WCHAR_T:  tally.wchar_count++; break;
                case TokenType::CHAR16_T: tally.char16_count++; break;
                case TokenType::CHAR32_T: tally.char32_count++; break;
                case TokenType::INT128:   tally.int128_count++; break;
                case TokenType::UINT128_T: tally.int128_count++; tally.unsigned_count++; break;
                case TokenType::AUTO_TYPE: tally.auto_type_count++; break;
                case TokenType::COMPLEX:  tally.complex_count++; break;
                case TokenType::FLOAT16:  tally.float16_count++; break;
                case TokenType::STRUCT:
                case TokenType::UNION:
                case TokenType::CLASS: {
                    bool is_class_keyword = t.type == TokenType::CLASS;
                    if (!pars->is_cxx_mode_active()) {
                        if (is_class_keyword) {
                            parsing = false;
                            continue;
                        }
                        struct_obj = pars->parse_struct_specifier();
                        // parsing = false; We can have storage classes after the fact
                        continue;
                    }

                    if (!is_class_keyword) {
                        // Keep legacy anonymous struct/union declarators in the
                        // C-style parser path for now; named records use C++ parsing.
                        if (mgnt->peek_token().type == TokenType::IDENTIFIER) {
                            cpp_record_obj = pars->parse_cpp_record_specifier();
                        } else {
                            // Probe using C++ record parsing so named records get
                            // full semantic construction, but fall back cleanly to
                            // C-style handling for anonymous struct/union declarators.
                            Parser::RevertingTentativeParsingAction tentative(*pars);
                            auto tentative_record = pars->parse_cpp_record_specifier();
                            auto* tentative_cpp_record =
                                dyn_cast<CppRecordDecl>(tentative_record.get());
                            if (!tentative_cpp_record) {
                                error_custloc(
                                    "internal parser error: expected CppRecordDecl for struct/union specifier",
                                    t.loc);
                            }
                            if (!tentative_cpp_record->name.empty()) {
                                tentative.commit();
                                cpp_record_obj = std::move(tentative_record);
                            }
                        }
                        if (!cpp_record_obj) {
                            struct_obj = pars->parse_struct_specifier();
                            continue;
                        }
                    } else {
                        cpp_record_obj = pars->parse_cpp_record_specifier();
                    }

                    auto* cpp_record_decl = dyn_cast<CppRecordDecl>(cpp_record_obj.get());
                    if (!cpp_record_decl) {
                        error_custloc("internal parser error: expected CppRecordDecl for record specifier",
                                      t.loc);
                    }
                    if (!pars->is_in_template_pattern_context()) {
                        struct_obj = pars->build_cpp_record_semantic_decl(
                            *cpp_record_decl,
                            std::nullopt,
                            true);
                        if (!struct_obj) {
                            if (cpp_record_decl->name.empty()) {
                                error_custloc(
                                    "C++ parser unsupported syntax: anonymous class declarator",
                                    cpp_record_decl->location);
                            }
                            error_custloc(
                                "internal parser error: failed to build semantic declaration for class '"
                                    + cpp_record_decl->name + "'",
                                cpp_record_decl->location);
                        }
                    }
                    continue;
                }
                case TokenType::TYPENAME: {
                    if (!pars->is_cxx_mode_active()) {
                        parsing = false;
                        continue;
                    }
                    if (auto parsed_named_type =
                            pars->try_parse_cpp_named_type_specifier()) {
                        typedef_resolved_type =
                            parsed_named_type->type.get_shared();
                        typedef_resolved_qualifiers =
                            parsed_named_type->type.get_qualifiers();
                        if (parsed_named_type->typedef_symbol) {
                            for (const auto& attr :
                                 parsed_named_type->typedef_symbol->sym_attrs.attrs) {
                                leading_attrs.push_back(attr);
                            }
                        }
                        continue;
                    }
                    error_custloc("expected qualified type name after 'typename'",
                                  t.loc);
                }
                case TokenType::ENUM:
                    enum_obj = pars->parse_enum_specifier();
                    continue;
                    // Type Qualifiers
                case TokenType::CONST:    qualifiers |= QUAL_CONST; break;
                case TokenType::VOLATILE: qualifiers |= QUAL_VOLATILE; break;
                case TokenType::RESTRICT: qualifiers |= QUAL_RESTRICT; break;
                case TokenType::ATOMIC:
                    // _Atomic can be either a qualifier (_Atomic int x) or
                    // a type specifier (_Atomic(type-name) x).
                    if (mgnt->peek_token().type == TokenType::LEFT_PAREN) {
                        // _Atomic(type-name) form: parse the inner type and
                        // use it as the resolved base type with _Atomic applied.
                        mgnt->advance(); // consume _Atomic
                        mgnt->advance(); // consume (
                        auto inner_decl = DeclarationParser(pars);
                        auto inner_type = inner_decl.parse_declaration();
                        mgnt->check_and_consume(TokenType::RIGHT_PAREN);
                        atomic_type_specifier = inner_type;
                        qualifiers |= QUAL_ATOMIC;
                        continue; // don't advance again
                    }
                    qualifiers |= QUAL_ATOMIC;
                    break;
                case TokenType::INLINE:   tally.inline_count++; break;
                case TokenType::CONSTEVAL_KW:
                    if (!pars->is_cxx_mode_active()) {
                        parsing = false;
                        continue;
                    }
                    if (!pars->lang_opts.is_cxx20_or_later()) {
                        error_custloc("'consteval' is only available in C++20",
                                      t.loc);
                    }
                    tally.consteval_count++;
                    break;
                case TokenType::FRIEND_KW:
                    if (!pars->is_cxx_mode_active()) {
                        parsing = false;
                        continue;
                    }
                    if (is_friend) {
                        error_custloc("duplicate 'friend' specifier", t.loc);
                    }
                    is_friend = true;
                    break;
                case TokenType::EXPLICIT_KW:
                    if (!pars->is_cxx_mode_active()) {
                        parsing = false;
                        continue;
                    }
                    if (explicit_specifier.is_present) {
                        error_custloc(
                            "duplicate 'explicit' specifier",
                            t.loc);
                    }
                    explicit_specifier =
                        pars->parse_cpp_optional_explicit_specifier();
                    continue;
                    // Storage Class Specifiers
                case TokenType::STATIC:   tally.static_count++; break;
                case TokenType::EXTERN:   tally.extern_count++; break;
                case TokenType::MUTABLE_KW:
                    if (!pars->is_cxx_mode_active()) {
                        parsing = false;
                        continue;
                    }
                    tally.mutable_count++;
                    break;
                case TokenType::AUTO:
                    if (pars->is_cxx_mode_active()) {
                        tally.cxx_auto_count++;
                    } else {
                        tally.auto_count++;
                    }
                    break;
                case TokenType::REGISTER: tally.register_count++; break;
                case TokenType::TYPEDEF:  tally.typedef_count++; break;
                case TokenType::NORETURN_KW: {
                    // _Noreturn is a function specifier, reuse existing noreturn attribute
                    ParsedAttribute noreturn_attr;
                    noreturn_attr.name = "noreturn";
                    noreturn_attr.loc = t.loc;
                    noreturn_attr.resolved_kind = AttributeKind::NORETURN;
                    leading_attrs.push_back(std::move(noreturn_attr));
                    break;
                }
                case TokenType::ALIGNAS: {
                    // _Alignas(type-name) or _Alignas(constant-expression)
                    mgnt->advance(); // consume _Alignas
                    mgnt->check_and_consume(TokenType::LEFT_PAREN);
                    AttributeArg alignment_arg;
                    bool have_alignment_arg = false;
                    if (pars->isTokenDeclarationSpec(mgnt->current_token())) {
                        // _Alignas(type-name) uses the type's alignment requirement.
                        int64_t alignment = 0;
                        auto align_dp = DeclarationParser(this->pars);
                        auto align_type = align_dp.parse_declaration();
                        if (align_type == nullptr) {
                            error("Error parsing type in _Alignas");
                        }
                        auto align_cursor = desugar_type(align_type);
                        if (!align_cursor) {
                            align_cursor = align_type;
                        }
                        while (true) {
                            if (auto arr = dyn_cast_shared<ArrayType>(align_cursor)) {
                                align_cursor = arr->element_type.get_shared();
                                continue;
                            }
                            if (auto complex = dyn_cast_shared<ComplexType>(align_cursor)) {
                                align_cursor = complex->element_type;
                                continue;
                            }
                            if (auto en = dyn_cast_shared<EnumType>(align_cursor)) {
                                align_cursor = en->semantic_underlying_type();
                                continue;
                            }
                            break;
                        }
                        if (auto obj = dyn_cast_shared<ObjectType>(align_cursor)) {
                            alignment = static_cast<int64_t>(obj->getAlignment());
                        } else if (auto vec = dyn_cast_shared<VectorType>(align_cursor)) {
                            alignment = vec->getWidthBytes();
                        } else if (align_cursor) {
                            alignment = align_cursor->getWidthBytes();
                        }
                        alignment_arg = AttributeArg::make_int(alignment, t.loc);
                        have_alignment_arg = true;
                    } else {
                        // _Alignas(constant-expression)
                        auto align_expr = pars->parse_conditional_expression();
                        auto val = try_evaluate_with_consteval_compat(
                            align_expr.get(), ConstEvalMode::c_ice());
                        if (val.has_value()) {
                            alignment_arg = AttributeArg::make_int(*val, t.loc);
                            have_alignment_arg = true;
                        } else if (pars->is_cxx_mode_active() &&
                                   pars->expr_depends_on_active_template_parameter(
                                       align_expr.get())) {
                            alignment_arg = AttributeArg::make_expr(
                                std::shared_ptr<Expr>(align_expr.release()),
                                t.loc);
                            have_alignment_arg = true;
                        } else {
                            error("_Alignas requires a constant expression");
                        }
                    }
                    mgnt->check_and_consume(TokenType::RIGHT_PAREN);
                    if (!have_alignment_arg) {
                        error("_Alignas requires a constant expression");
                    }
                    if (alignment_arg.kind == AttributeArg::Kind::INTEGER) {
                        int64_t alignment = alignment_arg.int_value;
                        if (alignment < 0) {
                            error("_Alignas requires a non-negative alignment");
                        }
                        if (alignment == 0) {
                            // C11/C23: _Alignas(0) has no effect.
                            continue;
                        }
                        if ((alignment & (alignment - 1)) != 0) {
                            error("_Alignas requires a power-of-two alignment");
                        }
                    }
                    // Create an ALIGNED attribute
                    ParsedAttribute aligned_attr;
                    aligned_attr.name = "aligned";
                    aligned_attr.loc = t.loc;
                    aligned_attr.resolved_kind = AttributeKind::ALIGNED;
                    aligned_attr.args.push_back(std::move(alignment_arg));
                    leading_attrs.push_back(std::move(aligned_attr));
                    continue; // don't advance, we already consumed
                }
                case TokenType::THREAD_LOCAL: tally.thread_local_count++; break;
                case TokenType::EXTENSION_KW:
                    // __extension__ is a no-op prefix in declaration context
                    break;
                case TokenType::TYPEOF_KW: {
                    // typeof(expr) or typeof(type-name)
                    mgnt->advance(); // consume typeof
                    mgnt->check_and_consume(TokenType::LEFT_PAREN);
                    if (pars->isTokenDeclarationSpec(mgnt->current_token())) {
                        // typeof(type-name)
                        auto typeof_dp = DeclarationParser(this->pars);
                        auto typeof_type = typeof_dp.parse_declaration();
                        if (typeof_type == nullptr) {
                            error("Error parsing type in typeof");
                        }
                        typedef_resolved_type = typeof_type;
                    } else {
                        // typeof(expr) - defer resolution to sema
                        auto typeof_expr = pars->parse_expression();
                        if (!typeof_expr) {
                            error("Error parsing expression in typeof");
                        }
                        typedef_resolved_type = std::make_shared<TypeofExprType>(
                            std::shared_ptr<Expr>(typeof_expr.release()));
                    }
                    mgnt->check_and_consume(TokenType::RIGHT_PAREN);
                    continue; // don't advance, we already consumed
                }
                case TokenType::DECLTYPE_KW: {
                    if (pars->is_cxx_mode_active() &&
                        mgnt->peek_token(1).type == TokenType::LEFT_PAREN &&
                        mgnt->peek_token(2).type == TokenType::AUTO &&
                        mgnt->peek_token(3).type == TokenType::RIGHT_PAREN) {
                        mgnt->advance(); // decltype
                        mgnt->check_and_consume(TokenType::LEFT_PAREN);
                        mgnt->check_and_consume(TokenType::AUTO);
                        mgnt->check_and_consume(TokenType::RIGHT_PAREN);
                        tally.decltype_auto_count++;
                        continue;
                    }
                    QualType decltype_type =
                        pars->parse_cpp_decltype_type_specifier();
                    typedef_resolved_type = decltype_type.get_shared();
                    typedef_resolved_qualifiers = decltype_type.get_qualifiers();
                    continue; // don't advance, we already consumed
                }
                case TokenType::ATTRIBUTE_KW: {
                    auto parsed_attrs = pars->try_parse_attributes();
                    leading_attrs.insert(leading_attrs.end(),
                        std::make_move_iterator(parsed_attrs.begin()),
                        std::make_move_iterator(parsed_attrs.end()));
                    continue; // don't advance, try_parse_attributes already consumed
                }
                case TokenType::LEFT_BRACKET: {
                    // C23 [[...]] attribute syntax
                    if (pars->peek_token().type == TokenType::LEFT_BRACKET) {
                        auto parsed_attrs = pars->try_parse_attributes();
                        leading_attrs.insert(leading_attrs.end(),
                            std::make_move_iterator(parsed_attrs.begin()),
                            std::make_move_iterator(parsed_attrs.end()));
                        continue;
                    }
                    parsing = false;
                    continue;
                }
                    // If it's not a specifier, we are done with this part of the declaration
                default:
                    if ((t.type == TokenType::CONSTEXPR_KW) ||
                        (t.type == TokenType::IDENTIFIER &&
                         t.value == "constexpr" &&
                         pars->is_c23_constexpr_enabled())) {
                        tally.constexpr_count++;
                        mgnt->advance();
                        continue;
                    }
                    if (pars->is_cxx_mode_active() &&
                        pars->lang_opts.is_cxx20_or_later() &&
                        !pending_cxx_auto_type_constraint &&
                        (t.type == TokenType::IDENTIFIER ||
                         t.type == TokenType::SCOPE_RESOLUTION ||
                         (t.type == TokenType::COLON &&
                          mgnt->peek_token().type == TokenType::COLON))) {
                        Parser::RevertingTentativeParsingAction tentative(*pars);
                        std::optional<CppTypeConstraint> type_constraint;
                        try {
                            type_constraint =
                                pars->parse_cpp_type_constraint(
                                    /*diagnose_on_failure=*/false);
                        } catch (const ParseError&) {
                            type_constraint = std::nullopt;
                        } catch (const FatalErrorLimitReached&) {
                            throw;
                        }
                        bool followed_by_placeholder =
                            type_constraint &&
                            (mgnt->current_token().type == TokenType::AUTO ||
                             (mgnt->current_token().type ==
                                  TokenType::DECLTYPE_KW &&
                              mgnt->peek_token(1).type ==
                                  TokenType::LEFT_PAREN &&
                              mgnt->peek_token(2).type == TokenType::AUTO &&
                              mgnt->peek_token(3).type ==
                                  TokenType::RIGHT_PAREN));
                        if (followed_by_placeholder) {
                            tentative.commit();
                            pending_cxx_auto_type_constraint =
                                std::make_shared<CppTypeConstraint>(
                                    std::move(*type_constraint));
                            continue;
                        }
                    }
                    if (is_gnu_attribute_token(t)) {
                        auto parsed_attrs = pars->try_parse_attributes();
                        leading_attrs.insert(leading_attrs.end(),
                            std::make_move_iterator(parsed_attrs.begin()),
                            std::make_move_iterator(parsed_attrs.end()));
                        continue;
                    }
                    if (t.type == TokenType::IDENTIFIER && !typedef_resolved_type) {
                        if (pars->is_cxx_mode_active() &&
                            is_builtin_type_pack_element_name(t.value)) {
                            mgnt->advance();
                            auto arguments = pars->parse_cpp_template_argument_list();
                            if (arguments.empty() ||
                                arguments.front().kind !=
                                    TemplateArgumentKind::Value) {
                                error_custloc(
                                    "__type_pack_element requires an index argument",
                                    t.loc);
                            }
                            for (size_t idx = 1; idx < arguments.size(); ++idx) {
                                if (arguments[idx].kind !=
                                    TemplateArgumentKind::Type) {
                                    error_custloc(
                                        "__type_pack_element arguments after the index must be types",
                                        t.loc);
                                }
                            }
                            typedef_resolved_type =
                                std::make_shared<BuiltinTypePackElementType>(
                                    std::move(arguments));
                            continue;
                        }
                        BuiltinTypeTransformKind builtin_transform_kind;
                        if (lookup_builtin_type_transform_kind(
                                t.value,
                                builtin_transform_kind)) {
                            mgnt->advance();
                            mgnt->check_and_consume(TokenType::LEFT_PAREN);
                            auto transform_dp = DeclarationParser(this->pars);
                            auto operand_type = transform_dp.parse_declaration();
                            if (operand_type == nullptr) {
                                error("Error parsing type in builtin type transform");
                            }
                            typedef_resolved_type =
                                std::make_shared<BuiltinTypeTransformType>(
                                    builtin_transform_kind,
                                    QualType(
                                        operand_type,
                                        transform_dp.qualifiers));
                            mgnt->check_and_consume(TokenType::RIGHT_PAREN);
                            continue;
                        }
                    }
                    // Check if this token sequence names a type-name, but only if we
                    // haven't already seen any type specifiers (to avoid consuming
                    // declarator names e.g. in "typedef int MyInt;" where MyInt is the
                    // declarator, not a type).
                    if ((t.type == TokenType::IDENTIFIER ||
                         (pars->is_cxx_mode_active() &&
                          (t.type == TokenType::SCOPE_RESOLUTION ||
                           (t.type == TokenType::COLON &&
                            mgnt->peek_token().type == TokenType::COLON)))) &&
                        !typedef_resolved_type) {
                        bool has_type_specifier = (tally.void_count || tally.char_count ||
                            tally.short_count || tally.int_count || tally.long_count ||
                            tally.float_count || tally.double_count || tally.bool_count ||
                            tally.wchar_count || tally.char16_count ||
                            tally.char32_count ||
                            tally.signed_count || tally.unsigned_count ||
                            tally.int128_count || tally.auto_type_count ||
                            tally.cxx_auto_count ||
                            tally.decltype_auto_count ||
                            tally.complex_count);
                        if (!has_type_specifier && !struct_obj && !enum_obj) {
                            if (pars->is_cxx_mode_active()) {
                                if (auto parsed_named_type =
                                        pars->try_parse_cpp_named_type_specifier()) {
                                    typedef_resolved_type =
                                        parsed_named_type->type.get_shared();
                                    typedef_resolved_qualifiers =
                                        parsed_named_type->type.get_qualifiers();
                                    if (parsed_named_type->typedef_symbol) {
                                        for (const auto& attr :
                                             parsed_named_type->typedef_symbol->sym_attrs.attrs) {
                                            leading_attrs.push_back(attr);
                                        }
                                    }
                                    continue;
                                }
                            } else if (t.type == TokenType::IDENTIFIER) {
                                auto named_type = pars->collect_->collect_lookup_type_name(
                                    t.value, true, false);
                                if (named_type) {
                                    typedef_resolved_type = named_type.get_shared();
                                    typedef_resolved_qualifiers = named_type.get_qualifiers();
                                    if (auto typedef_sym =
                                            pars->collect_->collect_lookup_typedef_symbol(t.value)) {
                                        for (const auto& attr : typedef_sym->sym_attrs.attrs) {
                                            leading_attrs.push_back(attr);
                                        }
                                    }
                                    mgnt->advance();
                                    continue;
                                }
                            }
                        }
                    }
                    parsing = false;
                    continue;
            }
            mgnt->advance();
        }

        str_class = resolveStorageClass(tally);
        is_consteval = tally.consteval_count > 0;
        is_inline = tally.inline_count > 0 || is_consteval;
        is_thread_local = tally.thread_local_count > 0;
        is_constexpr = tally.constexpr_count > 0 || is_consteval;
        is_mutable = tally.mutable_count > 0;
        base_qualifiers = qualifiers; // save base qualifiers for multi-declarator lists

        // If we have a struct type, use it
        if (struct_obj) {
            // todo: verify we don't have any instances of basic tyes (int, char, etc..)
            // tally.{int,short,...}Count should be equal to 0
            auto* struct_obj_dcast = cast<ObjectDecl>(struct_obj.get());
            auto resolved = apply_declspec_type_attributes(struct_obj_dcast->get_tag_type());
            first_half = resolved;
            if (run_second_half) {
                return parse_declarator(resolved);
            } else {
                return first_half;
            }
        }

        if (enum_obj) {
            auto* enum_obj_dcast = cast<EnumDecl>(enum_obj.get());
            auto resolved = apply_declspec_type_attributes(enum_obj_dcast->get_tag_type());
            first_half = resolved;
            if (run_second_half) {
                return parse_declarator(resolved);
            } else {
                return first_half;
            }
        }

        // If a typedef-name was used as the type specifier
        if (typedef_resolved_type) {
            // Preserve qualifiers that are part of the typedef name itself
            // (e.g. typedef volatile union U V; V *p -> pointer to volatile U).
            base_qualifiers =
                static_cast<uint8_t>(base_qualifiers | typedef_resolved_qualifiers);
            qualifiers = base_qualifiers;
            auto resolved = apply_declspec_type_attributes(typedef_resolved_type);
            first_half = resolved;
            if (run_second_half) {
                return parse_declarator(resolved);
            } else {
                return first_half;
            }
        }

        // _Atomic(type-name) specifier: use the inner type as the base
        if (atomic_type_specifier) {
            auto resolved = apply_declspec_type_attributes(atomic_type_specifier);
            first_half = resolved;
            if (run_second_half) {
                return parse_declarator(resolved);
            } else {
                return first_half;
            }
        }

        // Handle __auto_type: produce AutoType placeholder
        if (tally.auto_type_count > 0) {
            validateTally(tally);
            auto auto_placeholder = std::make_shared<AutoType>(AutoTypeFlavor::Gnu);
            auto resolved = apply_declspec_type_attributes(auto_placeholder);
            first_half = resolved;
            if (run_second_half) {
                return parse_declarator(resolved);
            } else {
                return first_half;
            }
        }

        // Handle C++ auto placeholder type deduction
        if (tally.cxx_auto_count > 0) {
            validateTally(tally);
            auto auto_placeholder = std::make_shared<AutoType>(
                AutoTypeFlavor::Cxx,
                pending_cxx_auto_type_constraint);
            pending_cxx_auto_type_constraint = nullptr;
            auto resolved = apply_declspec_type_attributes(auto_placeholder);
            first_half = resolved;
            if (run_second_half) {
                return parse_declarator(resolved);
            } else {
                return first_half;
            }
        }

        // Handle C++ decltype(auto) placeholder type deduction
        if (tally.decltype_auto_count > 0) {
            validateTally(tally);
            if (qualifiers != QUAL_NONE) {
                error_custloc(
                    "'decltype(auto)' cannot be combined with cv-qualifiers",
                    begin_loc);
            }
            auto auto_placeholder =
                std::make_shared<AutoType>(
                    AutoTypeFlavor::DecltypeAuto,
                    pending_cxx_auto_type_constraint);
            pending_cxx_auto_type_constraint = nullptr;
            auto resolved = apply_declspec_type_attributes(auto_placeholder);
            first_half = resolved;
            if (run_second_half) {
                return parse_declarator(resolved);
            } else {
                return first_half;
            }
        }

        // In gnu89/permissive mode, clamp duplicate type specifiers
        // (e.g. #define int unsigned causes "unsigned unsigned")
        if (pars->lang_opts.implicit_int) {
            if (tally.int_count > 1) tally.int_count = 1;
            if (tally.signed_count > 1) tally.signed_count = 1;
            if (tally.unsigned_count > 1) tally.unsigned_count = 1;
        }
        // GNU extension: bare "_Complex" defaults to "double _Complex".
        if (tally.complex_count &&
            tally.float_count == 0 && tally.double_count == 0 &&
            tally.char_count == 0 && tally.short_count == 0 &&
            tally.int_count == 0 && tally.long_count == 0 &&
            tally.signed_count == 0 && tally.unsigned_count == 0 &&
            tally.void_count == 0 && tally.bool_count == 0 &&
            tally.int128_count == 0 && tally.float16_count == 0) {
            tally.double_count = 1;
        }
        validateTally(tally); // Ensure no "unsigned float" etc.
        auto ret = resolveBuiltinType(tally, *pars->type_ctx.get());
        if (ret == nullptr) {
            bool can_parse_typeless_conversion_function =
                allow_typeless_conversion_function &&
                pars->is_cxx_mode_active() &&
                mgnt->current_token().type == TokenType::OPERATOR_KW;
            // K&R / C89 implicit int: no type specifiers means int
            if (pars->lang_opts.implicit_int) {
                ret = pars->type_ctx->get_builtin(BuiltinTypes::Int);
            } else if (can_parse_typeless_conversion_function) {
                first_half = nullptr;
                if (run_second_half) {
                    return parse_declarator(nullptr);
                }
                return nullptr;
            } else {
                error_custloc("Couldn't find corresponding internal type", begin_loc);
            }
        }
        ret = apply_declspec_type_attributes(ret);
        first_half = ret;
        if (run_second_half) {
            return parse_declarator(ret);
        } else {
            return first_half;
        }
    }
    // get ready to parse a new declarator

void DeclarationParser::reset_declarator_parsing_state() {
        name = "";
        loc = SrcLoc();
        qualifiers = base_qualifiers; // restore base qualifiers for next declarator
        func_args.clear();
        captured_func_args = false;
        trailing_function_cv_qualifiers = QUAL_NONE;
        trailing_function_ref_qualifier = 0;
        is_conversion_function = false;
        conversion_target_type = nullptr;
        kr_param_names.clear();
        preparsed_sym = nullptr;
        default_argument.reset();
        trailing_requires_clause.reset();
        is_parameter_pack = false;
        is_kr_style = false;
        asm_label = std::nullopt;
        // Don't clear leading_attrs here - they persist across declarators in the same declaration
    }

std::optional<QualType> DeclarationParser::parse_cpp_trailing_return_type() {
    if (!pars->is_cxx_mode_active() ||
        !mgnt->gentle_check_and_consume(TokenType::ARROW)) {
        return std::nullopt;
    }

    DeclarationParser return_parser(pars);
    return_parser.parse_new_type_id_context = true;
    QualType return_type(return_parser.parse_declaration());
    if (!return_type) {
        error("trailing return type must be a type-id");
    }
    if (!return_parser.name.empty()) {
        return_parser.error_custloc(
            "trailing return type must be a type-id",
            return_parser.loc.isInvalid() ? return_parser.begin_loc
                                          : return_parser.loc);
    }
    if (return_parser.str_class != StorageClass::NONE ||
        return_parser.is_inline ||
        return_parser.is_constexpr ||
        return_parser.is_consteval ||
        return_parser.is_friend ||
        return_parser.explicit_specifier.is_present) {
        return_parser.error_custloc(
            "trailing return type cannot contain declaration specifiers",
            return_parser.begin_loc);
    }
    if (return_parser.is_parameter_pack) {
        return_parser.error_custloc(
            "trailing return type cannot be a parameter pack",
            return_parser.begin_loc);
    }
    return return_type;
}

    // Handles pointers *, block pointers ^, and type qualifiers (const, volatile, restrict, _Atomic)

std::shared_ptr<CType> DeclarationParser::parse_declarator(std::shared_ptr<CType> base) {
        std::shared_ptr<CType> new_type = base;
        uint8_t current_quals = base_qualifiers; // qualifiers from declaration specifiers apply to base type

        auto parse_post_pointer_qualifiers = [&]() {
            while (true) {
                if (mgnt->gentle_check_and_consume(TokenType::CONST)) current_quals |= QUAL_CONST;
                else if (mgnt->gentle_check_and_consume(TokenType::VOLATILE)) current_quals |= QUAL_VOLATILE;
                else if (mgnt->gentle_check_and_consume(TokenType::RESTRICT)) current_quals |= QUAL_RESTRICT;
                else if (mgnt->gentle_check_and_consume(TokenType::ATOMIC)) current_quals |= QUAL_ATOMIC;
                else if (mgnt->gentle_check_and_consume(TokenType::NULLABILITY_QUALIFIER)) { /* skip */ }
                else if (is_gnu_attribute_token(mgnt->current_token())) {
                    auto ptr_attrs = pars->try_parse_attributes();
                    leading_attrs.insert(leading_attrs.end(),
                        std::make_move_iterator(ptr_attrs.begin()),
                        std::make_move_iterator(ptr_attrs.end()));
                } else {
                    break;
                }
            }
        };

        while (is_gnu_attribute_token(mgnt->current_token())) {
            auto parsed_attrs = pars->try_parse_attributes();
            leading_attrs.insert(leading_attrs.end(),
                std::make_move_iterator(parsed_attrs.begin()),
                std::make_move_iterator(parsed_attrs.end()));
        }

        while (true) {
            if (pars->is_cxx_mode_active() && mgnt->gentle_check(TokenType::IDENTIFIER)) {
                size_t offset = 0;
                std::vector<std::string> scope_components;
                bool saw_scope = false;

                scope_components.push_back(mgnt->peek_token(offset).value);
                ++offset;

                auto consume_scope_resolution = [&](size_t& scope_offset) -> bool {
                    Token sep = mgnt->peek_token(scope_offset);
                    if (sep.type == TokenType::SCOPE_RESOLUTION) {
                        ++scope_offset;
                        return true;
                    }
                    if (sep.type == TokenType::COLON &&
                        mgnt->peek_token(scope_offset + 1).type == TokenType::COLON) {
                        scope_offset += 2;
                        return true;
                    }
                    return false;
                };

                while (consume_scope_resolution(offset)) {
                    saw_scope = true;
                    Token next = mgnt->peek_token(offset);
                    if (next.type == TokenType::MULTIPLY) {
                        break;
                    }
                    if (next.type != TokenType::IDENTIFIER) {
                        saw_scope = false;
                        break;
                    }
                    scope_components.push_back(next.value);
                    ++offset;
                }

                if (saw_scope && mgnt->peek_token(offset).type == TokenType::MULTIPLY) {
                    for (size_t consumed = 0; consumed < offset; ++consumed) {
                        mgnt->advance();
                    }
                    mgnt->advance(); // consume '*'

                    std::string owner_name = scope_components.back();
                    QualType owner_type = pars->collect_->collect_lookup_type_name(
                        owner_name,
                        true,
                        true);
                    bool owner_is_dependent =
                        owner_type &&
                        type_depends_on_template_parameters(owner_type);
                    if (!owner_type ||
                        (!owner_is_dependent &&
                         canonical_type_kind(owner_type) != TypeKind::Object)) {
                        error("pointer-to-member declarator requires class/struct/union type");
                    }

                    new_type = std::make_shared<MemberPointerType>(
                        owner_type,
                        QualType(new_type, current_quals));
                    current_quals = QUAL_NONE;
                    parse_post_pointer_qualifiers();
                    continue;
                }
            }

            if (mgnt->gentle_check_and_consume(TokenType::MULTIPLY)) {
                // Create pointer to current type with its qualifiers
                new_type = std::make_shared<PointerType>(QualType(new_type, current_quals));
                // Parse qualifiers after * (these qualify the pointer, or propagate to next level)
                current_quals = QUAL_NONE;
                parse_post_pointer_qualifiers();
            } else if (mgnt->gentle_check_and_consume(TokenType::BITWISE_XOR)) {
                // Apple Block pointer: ^ in declarator context
                new_type = std::make_shared<BlockPointerType>(QualType(new_type, current_quals));
                current_quals = QUAL_NONE;
                parse_post_pointer_qualifiers();
            } else if (pars->is_cxx_mode_active() &&
                       (mgnt->gentle_check(TokenType::BITWISE_AND) ||
                        mgnt->gentle_check(TokenType::LOGICAL_AND))) {
                bool is_rvalue_reference = mgnt->gentle_check_and_consume(TokenType::LOGICAL_AND);
                if (!is_rvalue_reference) {
                    mgnt->check_and_consume(TokenType::BITWISE_AND);
                }
                QualType referred_type(new_type, current_quals);
                if (canonical_type_kind(referred_type) == TypeKind::Reference) {
                    error("cannot declare reference to reference");
                }
                new_type = std::make_shared<ReferenceType>(
                    referred_type,
                    is_rvalue_reference ? ReferenceKind::RValue : ReferenceKind::LValue);
                current_quals = QUAL_NONE;
            } else {
                break;
            }
        }
        // Update qualifiers to reflect the outermost qualifiers (for the variable itself)
        qualifiers = current_quals;
        return parse_direct_declarator(new_type);
    }
    // int (*const [])(unsigned int, ...) turns to

std::shared_ptr<CType> DeclarationParser::parse_direct_declarator(std::shared_ptr<CType> base) {
        loc = mgnt->current_token().loc; // in case theres no identifer
        std::shared_ptr<CType> old_type = base;
        std::shared_ptr<CType> new_type = nullptr;
        std::shared_ptr<CType> over_arch = nullptr;
        auto try_parse_qualified_cpp_declarator_name =
            [&]() -> bool {
                if (!pars->is_cxx_mode_active()) {
                    return false;
                }

                size_t saved_idx = mgnt->get_token_idx();
                auto saved_split_state = mgnt->get_split_token_state();
                auto restore = [&]() {
                    mgnt->set_token_idx(saved_idx);
                    mgnt->set_split_token_state(saved_split_state);
                };

                bool has_global_qualifier = false;
                if (mgnt->gentle_check(TokenType::SCOPE_RESOLUTION) ||
                    (mgnt->gentle_check(TokenType::COLON) &&
                     mgnt->peek_token().type == TokenType::COLON)) {
                    has_global_qualifier = true;
                    pars->consume_cpp_scope_resolution();
                }

                bool saw_scope_resolution = false;
                if ((has_global_qualifier || mgnt->gentle_check(TokenType::IDENTIFIER)) &&
                    mgnt->gentle_check(TokenType::OPERATOR_KW)) {
                    return parse_cpp_operator_function_name(*this);
                }

                while (true) {
                    if (!mgnt->gentle_check(TokenType::IDENTIFIER)) {
                        restore();
                        return false;
                    }

                    Token ident_tok = mgnt->current_token();
                    std::string component_name = ident_tok.value;
                    std::vector<TemplateArgument> component_template_arguments;
                    bool component_has_template_argument_list = false;

                    mgnt->advance();
                    if (mgnt->gentle_check(TokenType::LESS_THAN)) {
                        component_has_template_argument_list = true;
                        component_template_arguments =
                            pars->parse_cpp_template_argument_list();
                    }

                    if (!(mgnt->gentle_check(TokenType::SCOPE_RESOLUTION) ||
                          (mgnt->gentle_check(TokenType::COLON) &&
                           mgnt->peek_token().type == TokenType::COLON))) {
                        if (!has_global_qualifier && !saw_scope_resolution) {
                            restore();
                            return false;
                        }

                        if (name.empty()) {
                            name = component_name;
                            loc = ident_tok.loc;
                        } else {
                            error_custloc(
                                "Potentially two names in a declarator",
                                this->begin_loc);
                        }
                        if ((pars->is_parsing_cpp_explicit_specialization() ||
                             pars->is_in_template_pattern_context()) &&
                            component_has_template_argument_list &&
                            !has_explicit_specialization_argument_list) {
                            explicit_specialization_arguments =
                                std::move(component_template_arguments);
                            has_explicit_specialization_argument_list = true;
                        }
                        return true;
                    }

                    saw_scope_resolution = true;
                    pars->consume_cpp_scope_resolution();
                    if (mgnt->gentle_check(TokenType::OPERATOR_KW)) {
                        return parse_cpp_operator_function_name(*this);
                    }
                }
            };
        if (parse_new_type_id_context &&
            pars->is_cxx_mode_active() &&
            mgnt->gentle_check(TokenType::LEFT_PAREN)) {
            result_type = base;
            return base;
        }
        if (mgnt->gentle_check_and_consume(TokenType::LEFT_PAREN)) {
            // GNU extension: parenthesized declarator can start with attributes.
            auto paren_attrs = pars->try_parse_attributes();
            if (!paren_attrs.empty() && pars->isTokenDeclarationSpec(mgnt->current_token())) {
                Parser::TentativeParsingAction tentative(*pars);
                auto saved_name = name;
                auto saved_loc = loc;
                auto saved_quals = qualifiers;
                try {
                    DeclarationParser nested_decl(this->pars);
                    nested_decl.in_function_parameter = in_function_parameter;
                    nested_decl.arrays_are_pointers = arrays_are_pointers;
                    nested_decl.is_parameter_pack = is_parameter_pack;
                    auto nested_type = nested_decl.parse_declaration();
                    if (nested_type && mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                        leading_attrs.insert(leading_attrs.end(),
                            std::make_move_iterator(paren_attrs.begin()),
                            std::make_move_iterator(paren_attrs.end()));
                        leading_attrs.insert(leading_attrs.end(),
                            std::make_move_iterator(nested_decl.leading_attrs.begin()),
                            std::make_move_iterator(nested_decl.leading_attrs.end()));
                        if (name.empty()) {
                            name = nested_decl.name;
                            loc = nested_decl.loc;
                        }
                        qualifiers = nested_decl.qualifiers;
                        is_parameter_pack = nested_decl.is_parameter_pack;
                        result_type = nested_type;
                        tentative.commit();
                        return nested_type;
                    }
                } catch (ParseError&) {
                }
                name = saved_name;
                loc = saved_loc;
                qualifiers = saved_quals;
            }
            // per 6.7.8/6.7.7 (c23 spec) we need something inside here, otherwise its a function declarator
            // we need placeholder as we don't know the "chld" of the unner type yet
            auto curr_token = mgnt->get_token_idx();
            // Declarator grammar is inside-out (`int (*p)[4]`): parse inner
            // declarator around a placeholder, then substitute the real base.
            auto placeholder_type = std::make_shared<PlaceholderType>();
            // Save and clear base_qualifiers: the inner declarator in parentheses
            // must not inherit qualifiers from the declaration specifiers.
            // e.g., in `const int *(p)[2]`, the const applies to the pointed-to
            // type, not to the pointer variable itself.
            auto saved_base_quals = base_qualifiers;
            base_qualifiers = QUAL_NONE;
            over_arch = parse_declarator(placeholder_type);
            base_qualifiers = saved_base_quals;
            if (mgnt->get_token_idx() == curr_token) {
                // Abstract function declarator support: int (int), int ((int)), etc.
                // If there is no inner declarator but a parameter-type-list starts here,
                // treat this parenthesized form as an abstract function type around a placeholder.
                bool parsed_abstract_function = false;
                auto saved_pos = mgnt->get_token_idx();
                if (pars->isTokenDeclarationSpec(mgnt->current_token())) {
                    std::vector<QualType> args;
                    std::vector<std::unique_ptr<DeclarationParser>> local_args;
                    bool found_ellipsis = false;
                    bool parse_ok = true;
                    bool saw_default_argument = false;
                    pars->collect_->collect_enter_scope(ScopeFlags::PrototypeScope);
                    struct ParamScopeGuard {
                        Parser* parser;
                        ~ParamScopeGuard() {
                            parser->collect_->collect_leave_scope();
                        }
                    } param_scope_guard{pars};
                    while (true) {
                        if (mgnt->gentle_check_and_consume(TokenType::ELLIPSIS)) {
                            found_ellipsis = true;
                            break;
                        }
                        auto dp = std::make_unique<DeclarationParser>(this->pars);
                        dp->in_function_parameter = true;
                        auto ctype = dp->parse_declaration();
                        if (ctype == nullptr) {
                            parse_ok = false;
                            break;
                        }
                        if (!dp->name.empty()) {
                            auto temp_sym = std::make_shared<Symbol>(
                                dp->name,
                                SymbolKind::VARIABLE,
                                QualType(ctype, dp->qualifiers),
                                dp->str_class,
                                VariableLinkage::NONE);
                            pars->collect_->collect_bind_symbol_in_current_scope(
                                dp->name, temp_sym);
                            dp->preparsed_sym = temp_sym;
                        }
                        args.push_back(ctype);
                        local_args.push_back(std::move(dp));
                        auto* parsed_param = local_args.back().get();
                        bool has_default_argument = false;
                        if (mgnt->gentle_check(TokenType::ASSIGN)) {
                            if (!pars->is_cxx_mode_active()) {
                                error("default arguments are only allowed in C++ declarations");
                            }
                            mgnt->advance(); // '='
                            parsed_param->default_argument =
                                pars->parse_assignment_expression();
                            if (!parsed_param->default_argument) {
                                error("invalid default argument expression");
                            }
                            has_default_argument = true;
                        }
                        if (has_default_argument) {
                            saw_default_argument = true;
                        } else if (saw_default_argument) {
                            error("parameter without a default argument follows parameter with a default argument");
                        }
                        while (is_gnu_attribute_token(mgnt->current_token())) {
                            pars->try_parse_attributes();
                        }
                        if (mgnt->gentle_check_and_consume(TokenType::COMMA)) {
                            continue;
                        }
                        break;
                    }
                    if (parse_ok && mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                        std::vector<uint8_t> parameter_pack_flags;
                        parameter_pack_flags.reserve(local_args.size());
                        for (const auto& local_arg : local_args) {
                            parameter_pack_flags.push_back(
                                local_arg && local_arg->is_parameter_pack ? 1 : 0);
                        }
                        if (!captured_func_args) {
                            func_args = std::move(local_args);
                            captured_func_args = true;
                        }
                        auto func_type = std::make_shared<FunctionType>();
                        func_type->parameters = std::move(args);
                        func_type->parameter_pack_flags =
                            std::move(parameter_pack_flags);
                        func_type->normalize_parameter_pack_flags();
                        func_type->is_variadic = found_ellipsis;
                        func_type->has_prototype = true;
                        func_type->ret_type = QualType(placeholder_type);
                        over_arch = func_type;
                        parsed_abstract_function = true;
                    }
                }
                if (!parsed_abstract_function) {
                    bool parsed_constructor_like_empty_param_list = false;
                    if (pars->is_cxx_mode_active() &&
                        name.empty() &&
                        old_type &&
                        canonical_type_kind(old_type) == TypeKind::Object &&
                        mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                        // In C++ class member declarator parsing, constructor
                        // declarations spelled through declaration-specifiers
                        // can arrive here as an abstract empty parameter list.
                        auto func_type = std::make_shared<FunctionType>();
                        func_type->parameters = {};
                        func_type->is_variadic = false;
                        func_type->has_prototype = true;
                        func_type->ret_type = QualType(placeholder_type);
                        over_arch = func_type;
                        parsed_constructor_like_empty_param_list = true;
                    }
                    if (!parsed_constructor_like_empty_param_list) {
                        // If parse_declarator didn't consume a single token,
                        // there was nothing declarator-like inside these parentheses.
                        over_arch = nullptr;
                        mgnt->set_token_idx(saved_pos);
                    }
                }
            } else {
                mgnt->check_and_consume(TokenType::RIGHT_PAREN);
            }
        } else if (try_parse_qualified_cpp_declarator_name()) {
            // Parsed qualified declarator name.
        } else if (parse_cpp_operator_function_name(*this)) {
            // Parsed operator-function declarator name.
        } else if (in_function_parameter &&
                   pars->is_cxx_mode_active() &&
                   pars->is_in_template_pattern_context() &&
                   mgnt->gentle_check_and_consume(TokenType::ELLIPSIS)) {
            is_parameter_pack = true;
            if (mgnt->gentle_check(TokenType::IDENTIFIER)) {
                if (name.empty()) {
                    name = mgnt->current_token().value;
                    loc = mgnt->current_token().loc;
                } else {
                    error_custloc("Potentially two names in a declarator", this->begin_loc);
                }
                mgnt->advance();
            }
        } else if (mgnt->gentle_check(TokenType::IDENTIFIER)) {
            if (name.empty()) {
                name = mgnt->current_token().value;
                loc = mgnt->current_token().loc;
            } else {
                error_custloc("Potentially two names in a declarator", this->begin_loc);
            }
            mgnt->advance();
            if (pars->is_cxx_mode_active() &&
                (pars->is_parsing_cpp_explicit_specialization() ||
                 pars->is_in_template_pattern_context()) &&
                !has_explicit_specialization_argument_list &&
                mgnt->gentle_check(TokenType::LESS_THAN)) {
                explicit_specialization_arguments =
                    pars->parse_cpp_template_argument_list();
                has_explicit_specialization_argument_list = true;
            }
        }
        // void (*signal(int, void (*)(int)))(int)
        // we might ahve Pointer(Placeholder)
        bool consumed_outer_param_array_suffix = false;
        bool has_trailing_return_type = false;
        while (true) {
            if (mgnt->gentle_check_and_consume(TokenType::LEFT_BRACKET)) {
                // inner becomes overarching
                std::optional<size_t> size = std::nullopt;
                std::shared_ptr<Expr> size_expr_shared = nullptr;
                bool saw_static_bound = false;
                uint8_t array_param_quals = QUAL_NONE;
                auto consume_array_param_qualifier = [&]() -> bool {
                    if (mgnt->gentle_check_and_consume(TokenType::CONST)) {
                        array_param_quals |= QUAL_CONST;
                        return true;
                    }
                    if (mgnt->gentle_check_and_consume(TokenType::VOLATILE)) {
                        array_param_quals |= QUAL_VOLATILE;
                        return true;
                    }
                    if (mgnt->gentle_check_and_consume(TokenType::RESTRICT)) {
                        array_param_quals |= QUAL_RESTRICT;
                        return true;
                    }
                    if (mgnt->gentle_check_and_consume(TokenType::ATOMIC)) {
                        array_param_quals |= QUAL_ATOMIC;
                        return true;
                    }
                    return false;
                };
                if (in_function_parameter) {
                    // C11 6.7.6.3 allows qualifiers/static inside parameter array brackets.
                    while (true) {
                        bool consumed = false;
                        consumed = consume_array_param_qualifier();
                        if (mgnt->gentle_check_and_consume(TokenType::STATIC)) {
                            saw_static_bound = true;
                            consumed = true;
                        }
                        if (!consumed) break;
                    }
                }
                if (!mgnt->gentle_check(TokenType::RIGHT_BRACKET)) {
                    if (in_function_parameter && mgnt->gentle_check_and_consume(TokenType::MULTIPLY)) {
                        // Parameter VLA with unspecified bound: int a[*]
                        auto int_type = pars->type_ctx->get_builtin(BuiltinTypes::Int);
                        size_expr_shared = std::make_shared<IntegerLiteral>(
                            "1", QualType(int_type), mgnt->current_token().loc);
                    } else {
                        // Parse constant expression for array size
                        auto size_expr = pars->parse_conditional_expression();
                        auto bound = pars->collect_->collect_array_bound_expression(std::move(size_expr));
                        size = bound.constant_size;
                        size_expr_shared = std::move(bound.variable_size_expr);
                    }
                }
                mgnt->check_and_consume(TokenType::RIGHT_BRACKET);
                if (in_function_parameter && saw_static_bound &&
                    !size.has_value() && size_expr_shared == nullptr) {
                    error("array parameter with 'static' requires a bound");
                }
                // For the outermost array in a function parameter:
                // - Declaration-specifier qualifiers (in 'qualifiers') go on the element type
                //   so that `const int a[]` decays to `const int *`
                // - Bracket qualifiers (array_param_quals) stay on the outer level
                //   so that `int a[const]` decays to `int *const`
                uint8_t elem_extra_quals = QUAL_NONE;
                if (in_function_parameter && !consumed_outer_param_array_suffix) {
                    elem_extra_quals = qualifiers; // declaration-specifier qualifiers -> element type
                    qualifiers = array_param_quals; // only bracket qualifiers stay outer
                    consumed_outer_param_array_suffix = true;
                }
                // the pointer bec
                std::shared_ptr<CType> insert;
                auto placeholder_type = std::make_shared<PlaceholderType>();
                if (arrays_are_pointers) {
                    insert = std::make_shared<PointerType>(QualType(placeholder_type));
                } else {
                    if (size_expr_shared) {
                        insert = std::make_shared<ArrayType>(QualType(placeholder_type, elem_extra_quals), size_expr_shared);
                    } else {
                        insert = std::make_shared<ArrayType>(QualType(placeholder_type, elem_extra_quals), size);
                    }
                }
                if (new_type == nullptr) {
                    new_type = insert;
                } else {
                    new_type = replace_placeholder(new_type, insert);
                }
                if (over_arch != nullptr) {
                    new_type = replace_placeholder(over_arch, new_type);
                    over_arch = nullptr;
                }
            } else if (mgnt->gentle_check(TokenType::LEFT_PAREN)) {
                if (parse_new_type_id_context && pars->is_cxx_mode_active()) {
                    if (new_type == nullptr) {
                        if (over_arch == nullptr) {
                            new_type = old_type;
                        } else {
                            new_type = replace_placeholder(over_arch, old_type);
                            over_arch = nullptr;
                        }
                    } else {
                        if (old_type || !is_conversion_function) {
                            new_type = replace_placeholder(new_type, old_type);
                        }
                    }
                    break;
                }
                size_t lparen_token_idx = mgnt->get_token_idx();
                mgnt->advance(); // consume '('

                auto finish_as_direct_initializer_suffix = [&]() {
                    mgnt->set_token_idx(lparen_token_idx);
                    if (new_type == nullptr) {
                        if (over_arch == nullptr) {
                            new_type = old_type;
                        } else {
                            new_type = replace_placeholder(over_arch, old_type);
                            over_arch = nullptr;
                        }
                    } else {
                        if (old_type || !is_conversion_function) {
                            new_type = replace_placeholder(new_type, old_type);
                        }
                    }
                };

                auto cxx_parameter_clause_parses = [&]() -> bool {
                    Parser::RevertingTentativeParsingAction tentative(*pars);
                    try {
                        pars->collect_->collect_enter_scope(
                            ScopeFlags::PrototypeScope);
                        struct ProbeParamScopeGuard {
                            Parser* parser;
                            ~ProbeParamScopeGuard() {
                                parser->collect_->collect_leave_scope();
                            }
                        } param_scope_guard{pars};

                        if (mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                            return true;
                        }

                        bool saw_default_argument = false;
                        while (true) {
                            if (mgnt->gentle_check_and_consume(TokenType::ELLIPSIS)) {
                                return mgnt->gentle_check_and_consume(
                                    TokenType::RIGHT_PAREN);
                            }

                            auto dp = std::make_unique<DeclarationParser>(
                                this->pars);
                            dp->in_function_parameter = true;
                            auto ctype = dp->parse_declaration();
                            if (ctype == nullptr) {
                                return false;
                            }

                            bool has_default_argument = false;
                            if (mgnt->gentle_check(TokenType::ASSIGN)) {
                                mgnt->advance(); // '='
                                auto default_argument =
                                    pars->parse_assignment_expression();
                                if (!default_argument) {
                                    return false;
                                }
                                has_default_argument = true;
                            }

                            if (has_default_argument) {
                                saw_default_argument = true;
                            } else if (saw_default_argument) {
                                return false;
                            }

                            while (is_gnu_attribute_token(mgnt->current_token())) {
                                pars->try_parse_attributes();
                            }
                            if (mgnt->gentle_check_and_consume(TokenType::COMMA)) {
                                continue;
                            }
                            if (mgnt->gentle_check_and_consume(
                                    TokenType::RIGHT_PAREN)) {
                                return true;
                            }
                            return false;
                        }
                    } catch (const ParseError&) {
                        return false;
                    } catch (const FatalErrorLimitReached&) {
                        throw;
                    }
                };

                auto cxx_direct_initializer_clause_parses = [&]() -> bool {
                    Parser::RevertingTentativeParsingAction tentative(*pars);
                    try {
                        if (mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                            return true;
                        }

                        while (true) {
                            auto expr =
                                pars
                                    ->parse_assignment_expression_with_optional_pack_expansion();
                            if (!expr) {
                                return false;
                            }
                            if (mgnt->gentle_check_and_consume(TokenType::COMMA)) {
                                if (mgnt->gentle_check(TokenType::RIGHT_PAREN)) {
                                    return false;
                                }
                                continue;
                            }
                            return mgnt->gentle_check_and_consume(
                                TokenType::RIGHT_PAREN);
                        }
                    } catch (const ParseError&) {
                        return false;
                    } catch (const FatalErrorLimitReached&) {
                        throw;
                    }
                };

                // C++ declaration disambiguation:
                // if this suffix cannot parse as a parameter-declaration-clause,
                // but can parse as an initializer expression list, leave it for
                // object direct-initialization.
                if (pars->is_cxx_mode_active() &&
                    !in_function_parameter &&
                    !name.empty()) {
                    bool looks_like_parameter_clause =
                        mgnt->gentle_check(TokenType::RIGHT_PAREN) ||
                        mgnt->gentle_check(TokenType::ELLIPSIS) ||
                        pars->isTokenDeclarationSpec(mgnt->current_token());
                    if (!looks_like_parameter_clause ||
                        (!cxx_parameter_clause_parses() &&
                         cxx_direct_initializer_clause_parses())) {
                        finish_as_direct_initializer_suffix();
                        break;
                    }
                }

                std::vector<QualType> args;
                std::vector<std::unique_ptr<DeclarationParser>> local_args;
                bool found_ellipsis = false;
                bool has_prototype = true;
                pars->collect_->collect_enter_scope(ScopeFlags::PrototypeScope);
                struct ParamScopeGuard {
                    Parser* parser;
                    ~ParamScopeGuard() { parser->collect_->collect_leave_scope(); }
                } param_scope_guard{pars};
                if (mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                    // In C, empty () is K&R unspecified parameters.
                    // In C++, empty () is a real prototype with zero parameters.
                    has_prototype = pars->is_cxx_mode_active();
                } else {
                    // Try K&R identifier-list detection: f(a, b, c)
                    bool did_kr = false;
                    if (!pars->is_cxx_mode_active() &&
                        mgnt->gentle_check(TokenType::IDENTIFIER) &&
                        !pars->isTokenDeclarationSpec(mgnt->current_token())) {
                        auto saved_pos = mgnt->get_token_idx();
                        std::vector<std::string> tentative_names;
                        bool is_kr_ident_list = true;
                        tentative_names.push_back(mgnt->current_token().value);
                        mgnt->advance();
                        while (mgnt->gentle_check_and_consume(TokenType::COMMA)) {
                            if (!mgnt->gentle_check(TokenType::IDENTIFIER) ||
                                pars->isTokenDeclarationSpec(mgnt->current_token())) {
                                is_kr_ident_list = false;
                                break;
                            }
                            tentative_names.push_back(mgnt->current_token().value);
                            mgnt->advance();
                        }
                        if (is_kr_ident_list && mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                            kr_param_names = std::move(tentative_names);
                            is_kr_style = true;
                            has_prototype = false;
                            did_kr = true;
                        } else {
                            mgnt->set_token_idx(saved_pos);
                        }
                    }
                    if (!did_kr) {
                        bool saw_default_argument = false;
                        while (true) {
                            if (mgnt->gentle_check_and_consume(TokenType::ELLIPSIS)) {
                                found_ellipsis = true;
                                mgnt->check_and_consume(TokenType::RIGHT_PAREN);
                                break;
                            }
                            auto dp = std::make_unique<DeclarationParser>(this->pars);
                            dp->in_function_parameter = true;
                            // dp->arrays_are_pointers = true; we convert in sema
                            auto ctype = dp->parse_declaration();
                            if (ctype == nullptr) {
                                error("Error parsing function declaration");
                            }
                            if (!dp->name.empty()) {
                                // Make prior parameter names visible while parsing subsequent
                                // parameter bounds (e.g. int f(int n, int a[n])).
                                auto temp_sym = std::make_shared<Symbol>(
                                    dp->name, SymbolKind::VARIABLE,
                                    QualType(ctype, dp->qualifiers), dp->str_class,
                                    VariableLinkage::NONE);
                                pars->collect_->collect_bind_symbol_in_current_scope(dp->name, temp_sym);
                                dp->preparsed_sym = temp_sym;
                            }
                            args.push_back(ctype);
                            local_args.push_back(std::move(dp));
                            auto* parsed_param = local_args.back().get();
                            bool has_default_argument = false;
                            if (mgnt->gentle_check(TokenType::ASSIGN)) {
                                if (!pars->is_cxx_mode_active()) {
                                    error("default arguments are only allowed in C++ declarations");
                                }
                                mgnt->advance(); // '='
                                parsed_param->default_argument =
                                    pars->parse_assignment_expression();
                                if (!parsed_param->default_argument) {
                                    error("invalid default argument expression");
                                }
                                has_default_argument = true;
                            }
                            if (has_default_argument) {
                                saw_default_argument = true;
                            } else if (saw_default_argument) {
                                error("parameter without a default argument follows parameter with a default argument");
                            }
                            // Skip trailing attributes on parameters (e.g. __attribute__((__noescape__)))
                            while (is_gnu_attribute_token(mgnt->current_token())) {
                                pars->try_parse_attributes();
                            }
                            if (mgnt->gentle_check_and_consume(TokenType::COMMA)) {
                                continue;
                            } else if (mgnt->gentle_check_and_consume(TokenType::RIGHT_PAREN)) {
                            break;
                            } else {
                                error("Invalid token while parsing function declaration");
                            }
                        }
                    }
                }
                if (is_lone_unnamed_void_parameter_list(
                        args,
                        local_args,
                        found_ellipsis)) {
                    args.clear();
                    local_args.clear();
                }
                std::vector<uint8_t> parameter_pack_flags;
                if (!captured_func_args) {
                    parameter_pack_flags.reserve(local_args.size());
                    for (const auto& local_arg : local_args) {
                        parameter_pack_flags.push_back(
                            local_arg && local_arg->is_parameter_pack ? 1 : 0);
                    }
                    func_args = std::move(local_args);
                    captured_func_args = true;
                } else {
                    parameter_pack_flags.reserve(func_args.size());
                    for (const auto& func_arg : func_args) {
                        parameter_pack_flags.push_back(
                            func_arg && func_arg->is_parameter_pack ? 1 : 0);
                    }
                }
                auto func_type = std::make_shared<FunctionType>();
                func_type->parameters = args;
                func_type->parameter_pack_flags =
                    std::move(parameter_pack_flags);
                func_type->normalize_parameter_pack_flags();
                func_type->is_variadic = found_ellipsis;
                func_type->has_prototype = has_prototype;
                if (new_type == nullptr) {
                    if (is_conversion_function && conversion_target_type) {
                        new_type = conversion_target_type.get_shared();
                        qualifiers = conversion_target_type.get_qualifiers();
                    } else {
                        new_type = std::make_shared<PlaceholderType>(); // If not nullptr we assume new_type has a placeholder
                    }
                }
                func_type->ret_type = new_type;
                if (pars->is_cxx_mode_active()) {
                    while (true) {
                        if (mgnt->gentle_check_and_consume(TokenType::CONST)) {
                            trailing_function_cv_qualifiers |= QUAL_CONST;
                            continue;
                        }
                        if (mgnt->gentle_check_and_consume(TokenType::VOLATILE)) {
                            trailing_function_cv_qualifiers |= QUAL_VOLATILE;
                            continue;
                        }
                        break;
                    }
                    if (mgnt->gentle_check_and_consume(TokenType::LOGICAL_AND)) {
                        trailing_function_ref_qualifier = 2;
                    } else if (mgnt->gentle_check_and_consume(TokenType::BITWISE_AND)) {
                        trailing_function_ref_qualifier = 1;
                    }
                    if (trailing_function_ref_qualifier == 1) {
                        func_type->member_ref_qualifier =
                            FunctionRefQualifierKind::LValue;
                    } else if (trailing_function_ref_qualifier == 2) {
                        func_type->member_ref_qualifier =
                            FunctionRefQualifierKind::RValue;
                    }
                }
                Collect::CppThisContext noexcept_cpp_this_context;
                QualType noexcept_record_lookup_type;
                bool has_noexcept_cpp_this_context =
                    pars->build_cpp_member_declarator_expression_context(
                        *this,
                        *func_type,
                        noexcept_cpp_this_context,
                        noexcept_record_lookup_type);
                pars->parse_cpp_optional_noexcept_spec(
                    *func_type,
                    has_noexcept_cpp_this_context
                        ? &noexcept_cpp_this_context
                        : nullptr,
                    noexcept_record_lookup_type);
                if (auto trailing_return_type = parse_cpp_trailing_return_type()) {
                    auto* leading_auto =
                        old_type ? dyn_cast<AutoType>(old_type.get()) : nullptr;
                    if (!leading_auto ||
                        leading_auto->flavor != AutoTypeFlavor::Cxx ||
                        base_qualifiers != QUAL_NONE) {
                        error("function with trailing return type must specify return type 'auto'");
                    }
                    func_type->ret_type = *trailing_return_type;
                    has_trailing_return_type = true;
                }
                if (pars->lang_opts.is_cxx20_or_later() &&
                    mgnt->gentle_check(TokenType::REQUIRES_KW)) {
                    mgnt->advance(); // consume 'requires'
                    trailing_requires_clause =
                        pars->parse_cpp_constraint_expression();
                    if (!trailing_requires_clause) {
                        error("invalid trailing requires-clause");
                    }
                }
                // C11 6.7.6.3: A function declarator shall not return a function type
                if (func_type->ret_type &&
                    canonical_type_kind(func_type->ret_type) == TypeKind::Function) {
                    error("function cannot return a function type (use a function pointer instead)");
                }
                new_type = func_type;
                if (over_arch != nullptr) {
                    new_type = replace_placeholder(over_arch, new_type);
                    over_arch = nullptr;
                }
            } else {
                if (new_type == nullptr) { // there was no array or function
                    if (over_arch == nullptr) {
                        new_type = old_type;
                    } else {
                        new_type = replace_placeholder(over_arch, old_type);
                        over_arch = nullptr;
                    }
                  //  new_type = old_type; // cointinuing
                } else {
                    // this will insert basic type at the end
                    if (!has_trailing_return_type &&
                        (old_type || !is_conversion_function)) {
                        new_type = replace_placeholder(new_type, old_type);
                    }
                }
                break;
            }
        }
        result_type = new_type; // this will be overwritetn by the final one  at the end
        return new_type;
}


std::shared_ptr<CType> DeclarationParser::replace_placeholder(std::shared_ptr<CType> wrap, std::shared_ptr<CType> insert) {
        if (auto place = dyn_cast_shared<PlaceholderType>(wrap)) {
            return insert;
        } else if (auto aplace = dyn_cast_shared<ArrayType>(wrap)) {
            auto elem_quals = aplace->element_type.get_qualifiers();
            auto new_type = replace_placeholder(aplace->element_type.get_shared(), insert);
            aplace->element_type = QualType(new_type, elem_quals);
            return aplace;
        } else if (auto pplace = dyn_cast_shared<PointerType>(wrap)) {
            auto new_type = replace_placeholder(pplace->pointed_type.get_shared(), insert);
            pplace->pointed_type = new_type;
            return pplace;
        } else if (auto rplace = dyn_cast_shared<ReferenceType>(wrap)) {
            auto quals = rplace->referred_type.get_qualifiers();
            auto new_type = replace_placeholder(rplace->referred_type.get_shared(), insert);
            rplace->referred_type = QualType(new_type, quals);
            return rplace;
        } else if (auto bplace = dyn_cast_shared<BlockPointerType>(wrap)) {
            auto new_type = replace_placeholder(bplace->pointed_type.get_shared(), insert);
            bplace->pointed_type = new_type;
            return bplace;
        } else if (auto mplace = dyn_cast_shared<MemberPointerType>(wrap)) {
            auto quals = mplace->member_type.get_qualifiers();
            auto new_type = replace_placeholder(mplace->member_type.get_shared(), insert);
            mplace->member_type = QualType(new_type, quals);
            return mplace;
        } else if (auto fplace = dyn_cast_shared<FunctionType>(wrap)) {
            auto new_type = replace_placeholder(fplace->ret_type.get_shared(), insert);
            fplace->ret_type = new_type;
            return fplace;
        } else {
            throw std::runtime_error("Compiler internal error: unhandled node in replace_placeholder");
        }

    }
