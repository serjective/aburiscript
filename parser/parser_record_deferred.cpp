#include "parser.h"

// Deferred inline member parsing for record bodies.
// This logic is parser-stateful and intentionally isolated from the
// record-semantic build phases so class layout and body reparsing can evolve
// independently.

Parser::CppCtorBaseInitializerTarget
Parser::resolve_cpp_ctor_base_initializer_target(
    const RecordSemanticState& semantic_state,
    QualType owner_type,
    const CppCtorInitializer& initializer) {
    CppCtorBaseInitializerTarget result;
    const std::string initializer_name =
        !initializer.target_spelling.empty()
            ? initializer.target_spelling
            : initializer.member_name;
    SrcLoc loc = initializer.location;
    if (initializer_name.empty()) {
        return result;
    }

    auto make_target =
        [](const std::string& base_name,
           QualType base_type,
           bool is_virtual) -> CppCtorBaseInitializerTarget {
        CppCtorBaseInitializerTarget target;
        target.type = base_type;
        target.base_name = base_name;
        target.is_virtual = is_virtual;
        return target;
    };

    auto target_spelling_matches = [&](const std::string& base_name) {
        return base_name == initializer_name ||
               (!initializer.member_name.empty() &&
                base_name == initializer.member_name);
    };

    for (const auto& base : semantic_state.bases) {
        if (target_spelling_matches(base.name)) {
            return make_target(base.name, base.type, base.is_virtual);
        }
    }
    for (const auto& virtual_base : semantic_state.virtual_bases) {
        if (target_spelling_matches(virtual_base.name)) {
            return make_target(virtual_base.name, virtual_base.type, true);
        }
    }

    if (!collect_) {
        return result;
    }

    auto normalize_type = [&](QualType type) -> QualType {
        if (!type) {
            return QualType();
        }
        if (auto realized = collect_->collect_try_realize_deferred_semantic_type(type)) {
            return realized;
        }
        return type;
    };

    auto resolve_dependent_aliases =
        [&](auto&& self, QualType type) -> QualType {
        type = normalize_type(type);
        if (!type) {
            return QualType();
        }

        QualType desugared = desugar_typedefs(type);
        if (!desugared) {
            return type;
        }

        if (auto dependent_name =
                desugared.as_shared<DependentNameType>()) {
            QualType qualifier_type = self(self, dependent_name->qualifier_type);
            if (!qualifier_type) {
                return type;
            }

            const ClassTemplateDecl* class_template = nullptr;
            std::vector<TemplateArgument> template_arguments;
            QualType qualifier_desugared = desugar_typedefs(qualifier_type);
            if (auto qualifier_specialization =
                    qualifier_desugared.as_shared<TemplateSpecializationType>()) {
                class_template = dyn_cast<ClassTemplateDecl>(
                    const_cast<Decl*>(
                        qualifier_specialization->primary_template));
                template_arguments = qualifier_specialization->arguments;
            } else if (auto qualifier_object =
                           desugar_type(qualifier_type, ast_ctx.get())
                               .as_shared<ObjectType>()) {
                class_template = qualifier_object->get_primary_class_template();
                template_arguments =
                    qualifier_object->get_template_specialization_arguments();
            }
            if (!class_template) {
                return type;
            }

            const ObjectDecl* pattern_decl =
                class_template->pattern_semantic_decl();
            const RecordSemanticState* pattern_state =
                pattern_decl ? record_semantics_cache_lookup(pattern_decl)
                             : nullptr;
            if (!pattern_state) {
                return type;
            }

            for (auto it = pattern_state->nested_types.rbegin();
                 it != pattern_state->nested_types.rend();
                 ++it) {
                if (it->name != dependent_name->member_name) {
                    continue;
                }
                QualType substituted = collect_->collect_substitute_template_type(
                    it->type,
                    class_template->parameters,
                    template_arguments,
                    loc);
                if (!substituted) {
                    return type;
                }
                substituted = self(self, substituted);
                if (!substituted) {
                    return type;
                }
                return substituted.with_qualifiers(
                    static_cast<uint8_t>(
                        substituted.get_qualifiers() |
                        desugared.get_qualifiers()));
            }
            return type;
        }

        if (auto transform =
                desugared.as_shared<BuiltinTypeTransformType>()) {
            QualType operand_type = self(self, transform->operand_type);
            if (!operand_type) {
                return type;
            }
            switch (transform->transform_kind) {
                case BuiltinTypeTransformKind::RemoveConst:
                case BuiltinTypeTransformKind::RemoveVolatile:
                case BuiltinTypeTransformKind::RemoveCV:
                case BuiltinTypeTransformKind::RemoveCVRef:
                case BuiltinTypeTransformKind::RemoveReference: {
                    QualType transformed = apply_builtin_type_transform(
                        transform->transform_kind,
                        operand_type,
                        ast_ctx.get());
                    return transformed ? transformed : operand_type;
                }
                default:
                    return type;
            }
        }

        if (auto specialization =
                desugared.as_shared<TemplateSpecializationType>()) {
            if (const auto* alias_template =
                    dyn_cast<AliasTemplateDecl>(
                        const_cast<Decl*>(specialization->primary_template))) {
                QualType instantiated =
                    collect_->collect_try_instantiate_alias_template_specialization(
                        alias_template,
                        specialization->arguments,
                        loc);
                instantiated = normalize_type(instantiated);
                if (instantiated &&
                    !instantiated.equals_qualified(type)) {
                    QualType resolved = self(self, instantiated);
                    if (resolved) {
                        return resolved;
                    }
                    return instantiated;
                }
            }

            std::vector<TemplateArgument> rewritten_arguments =
                specialization->arguments;
            bool changed = false;
            for (auto& argument : rewritten_arguments) {
                if (argument.kind != TemplateArgumentKind::Type) {
                    continue;
                }
                QualType rewritten_type = self(self, argument.type);
                if (rewritten_type &&
                    !rewritten_type.equals_qualified(argument.type)) {
                    argument.type = rewritten_type;
                    changed = true;
                }
            }
            if (!changed) {
                return type;
            }
            return QualType(
                std::make_shared<TemplateSpecializationType>(
                    specialization->template_name,
                    specialization->primary_template,
                    std::move(rewritten_arguments),
                    specialization->is_dependent,
                    specialization->is_class_template_placeholder),
                desugared.get_qualifiers());
        }

        return type;
    };

    QualType named_type = initializer.target_type;
    if (!named_type) {
        named_type =
            collect_->collect_lookup_record_nested_type(owner_type, initializer_name);
    }
    if (!named_type) {
        named_type = collect_->collect_lookup_type_name(
            initializer_name,
            true,
            true);
    }
    if (!named_type && initializer.member_name != initializer_name) {
        named_type =
            collect_->collect_lookup_record_nested_type(owner_type,
                                                        initializer.member_name);
        if (!named_type) {
            named_type = collect_->collect_lookup_type_name(
                initializer.member_name,
                true,
                true);
        }
    }
    if (!named_type) {
        return result;
    }
    named_type = normalize_type(named_type);

    auto same_initializer_type = [&](QualType lhs, QualType rhs) {
        lhs = resolve_dependent_aliases(resolve_dependent_aliases, lhs);
        rhs = resolve_dependent_aliases(resolve_dependent_aliases, rhs);
        if (!lhs || !rhs) {
            return false;
        }
        if (lhs.equals_unqualified(rhs)) {
            return true;
        }
        QualType lhs_canonical = desugar_type(lhs, ast_ctx.get());
        QualType rhs_canonical = desugar_type(rhs, ast_ctx.get());
        if (lhs_canonical && rhs_canonical &&
            lhs_canonical.equals_unqualified(rhs_canonical)) {
            return true;
        }
        return types_equivalent_after_template_argument_canonicalization(
            lhs,
            rhs,
            ast_ctx.get(),
            true);
    };

    auto dependent_class_template_identity = [&](QualType type)
        -> const Decl* {
        type = resolve_dependent_aliases(resolve_dependent_aliases, type);
        if (!type || !type_depends_on_template_parameters(type, ast_ctx.get())) {
            return nullptr;
        }

        QualType spelled = desugar_typedefs(type);
        if (auto specialization =
                spelled.as_shared<TemplateSpecializationType>()) {
            return specialization->primary_template;
        }

        QualType canonical = desugar_type(type, ast_ctx.get());
        if (auto object_type = canonical.as_shared<ObjectType>()) {
            if (object_type->is_class_template_specialization()) {
                return object_type->get_primary_class_template();
            }
        }
        return nullptr;
    };

    auto same_dependent_class_template =
        [&](QualType initializer_type, QualType base_type) {
        const Decl* initializer_template =
            dependent_class_template_identity(initializer_type);
        const Decl* base_template =
            dependent_class_template_identity(base_type);
        return initializer_template &&
               base_template &&
               template_decls_share_lookup_identity(
                   initializer_template,
                   base_template);
    };

    std::vector<CppCtorBaseInitializerTarget> matches;
    std::vector<CppCtorBaseInitializerTarget> dependent_matches;
    for (const auto& base : semantic_state.bases) {
        if (same_initializer_type(named_type, base.type)) {
            matches.push_back(make_target(base.name, base.type, base.is_virtual));
        } else if (same_dependent_class_template(named_type, base.type)) {
            dependent_matches.push_back(
                make_target(base.name, base.type, base.is_virtual));
        }
    }
    for (const auto& virtual_base : semantic_state.virtual_bases) {
        if (same_initializer_type(named_type, virtual_base.type)) {
            matches.push_back(make_target(virtual_base.name, virtual_base.type, true));
        } else if (same_dependent_class_template(named_type, virtual_base.type)) {
            dependent_matches.push_back(
                make_target(virtual_base.name, virtual_base.type, true));
        }
    }

    if (matches.size() == 1) {
        return matches.front();
    }
    if (matches.size() > 1) {
        result.found_non_base_type = true;
        diag_engine->report_error(
            "constructor initializer '" + initializer_name +
                "' is ambiguous between base classes",
            loc);
        return result;
    }
    if (dependent_matches.size() == 1) {
        return dependent_matches.front();
    }
    if (dependent_matches.size() > 1) {
        result.found_non_base_type = true;
        diag_engine->report_error(
            "constructor initializer '" + initializer_name +
                "' is ambiguous between dependent base classes",
            loc);
        return result;
    }

    bool has_field_with_name = false;
    for (const auto& field : semantic_state.fields) {
        if (field.name == initializer_name ||
            (!initializer.member_name.empty() &&
             field.name == initializer.member_name)) {
            has_field_with_name = true;
            break;
        }
    }
    if (!has_field_with_name) {
        result.found_non_base_type = true;
        diag_engine->report_error(
            "constructor initializer '" + initializer_name +
                "' names a type that is not a direct or virtual base",
            loc);
    }
    return result;
}

void Parser::build_cpp_record_parse_deferred_bodies(
    const CppRecordDeferredParseContext& ctx) {
    struct DeferredInlineParserState {
        size_t token_idx = 0;
        std::shared_ptr<CType> active_func_type;
        LanguageLinkage active_decl_linkage = LanguageLinkage::None;
        std::unordered_set<std::string> active_seen_stmt_labels;
        std::unordered_set<std::string> active_stmt_labels;
        std::vector<std::unordered_map<std::string, std::string>> active_local_label_scopes;
        uint64_t active_local_label_unique_id = 0;
    };
    auto capture_deferred_inline_parser_state = [&]() -> DeferredInlineParserState {
        DeferredInlineParserState state;
        state.token_idx = get_token_idx();
        state.active_func_type = func_type;
        state.active_decl_linkage = current_language_linkage_;
        state.active_seen_stmt_labels = seen_stmt_labels;
        state.active_stmt_labels = stmt_labels;
        state.active_local_label_scopes = local_label_scopes_;
        state.active_local_label_unique_id = local_label_unique_id_;
        return state;
    };
    auto restore_deferred_inline_parser_state =
        [&](DeferredInlineParserState&& state) {
        current_language_linkage_ = state.active_decl_linkage;
        func_type = std::move(state.active_func_type);
        set_token_idx(state.token_idx);
        seen_stmt_labels = std::move(state.active_seen_stmt_labels);
        stmt_labels = std::move(state.active_stmt_labels);
        local_label_scopes_ = std::move(state.active_local_label_scopes);
        local_label_unique_id_ = state.active_local_label_unique_id;
    };
    auto parse_deferred_constructor_member_initializers =
        [&](CppConstructorDecl* ctor) {
        if (!ctor) {
            return;
        }
        size_t saved_idx = get_token_idx();
        bool saw_base_initializer = false;
        bool saw_delegating_initializer = false;
        std::unordered_set<std::string> seen_resolved_initializers;
        auto initializer_display_name =
            [](const CppCtorInitializer& initializer) -> std::string {
            if (!initializer.target_spelling.empty()) {
                return initializer.target_spelling;
            }
            return initializer.member_name;
        };
        auto note_resolved_initializer =
            [&](const std::string& key,
                const CppCtorInitializer& initializer) {
            if (initializer.is_pack_expansion) {
                return;
            }
            if (!seen_resolved_initializers.insert(key).second) {
                diag_engine->report_error(
                    "constructor mem-initializer-list has duplicate initializer '" +
                        initializer_display_name(initializer) + "'",
                    initializer.location);
            }
        };
        for (auto& mem_init : ctor->ctor_initializers) {
            mem_init.member_expr.reset();
            mem_init.init_expr.reset();
            mem_init.is_base_initializer = false;
            mem_init.resolved_target_type = nullptr;

            if (mem_init.is_delegating_initializer) {
                saw_delegating_initializer = true;
                note_resolved_initializer("delegating", mem_init);
                if (ctor->ctor_initializers.size() != 1) {
                    diag_engine->report_error(
                        "delegating constructor initializer must appear alone",
                        mem_init.location);
                }
                if (!ctx.record_type) {
                    diag_engine->report_error(
                        "delegating constructor target type is unavailable",
                        mem_init.location);
                    continue;
                }
                mem_init.resolved_target_type = QualType(ctx.record_type);
                if (mem_init.deferred_init_end_token_idx <=
                    mem_init.deferred_init_begin_token_idx) {
                    continue;
                }

                set_token_idx(mem_init.deferred_init_begin_token_idx);
                std::unique_ptr<Expr> parsed_init;
                if (gentle_check(TokenType::LEFT_PAREN)) {
                    advance();
                    std::vector<std::unique_ptr<Expr>> args;
                    if (!gentle_check(TokenType::RIGHT_PAREN)) {
                        do {
                            args.push_back(
                                parse_assignment_expression_with_optional_pack_expansion());
                        } while (gentle_check_and_consume(TokenType::COMMA));
                    }
                    check_and_consume(TokenType::RIGHT_PAREN);
                    mem_init.init_expr =
                        collect_->collect_member_initializer_expression(
                            std::move(args),
                            QualType(ctx.record_type),
                            false,
                            mem_init.location,
                            true);
                } else if (gentle_check(TokenType::LEFT_BRACE)) {
                    parsed_init = parse_init_list();
                } else {
                    error("expected '(' or '{' in constructor member initializer");
                }

                set_token_idx(mem_init.deferred_init_end_token_idx);
                if (!mem_init.init_expr && parsed_init) {
                    mem_init.init_expr =
                        collect_->collect_member_initializer_expression(
                            std::move(parsed_init),
                            QualType(ctx.record_type),
                            mem_init.location);
                }
                continue;
            }

            auto base_init_target =
                resolve_cpp_ctor_base_initializer_target(
                    ctx.semantic_state,
                    QualType(ctx.record_type),
                    mem_init);
            if (base_init_target) {
                saw_base_initializer = true;
                mem_init.is_base_initializer = true;
                mem_init.member_name = base_init_target.base_name;
                mem_init.resolved_target_type = base_init_target.type;
                note_resolved_initializer(
                    "base:" + base_init_target.type.to_string(),
                    mem_init);
            } else if (base_init_target.found_non_base_type) {
                continue;
            }

            MemberExpr* member_expr = nullptr;
            if (!base_init_target) {
                auto this_expr = collect_->collect_cpp_this_expression(mem_init.location);
                mem_init.member_expr = collect_->collect_member_expression(
                    std::move(this_expr),
                    mem_init.member_name,
                    true,
                    mem_init.location);
                member_expr = dyn_cast<MemberExpr>(mem_init.member_expr.get());
                if (!member_expr || !member_expr->member_type) {
                    continue;
                }
                note_resolved_initializer(
                    "member:" + mem_init.member_name,
                    mem_init);
            }
            if (mem_init.deferred_init_end_token_idx <=
                mem_init.deferred_init_begin_token_idx) {
                continue;
            }

            set_token_idx(mem_init.deferred_init_begin_token_idx);
            std::unique_ptr<Expr> parsed_init;
            if (gentle_check(TokenType::LEFT_PAREN)) {
                advance();
                std::vector<std::unique_ptr<Expr>> args;
                if (!gentle_check(TokenType::RIGHT_PAREN)) {
                    do {
                        args.push_back(
                            parse_assignment_expression_with_optional_pack_expansion());
                    } while (gentle_check_and_consume(TokenType::COMMA));
                }
                check_and_consume(TokenType::RIGHT_PAREN);

                if (base_init_target) {
                    mem_init.init_expr =
                        collect_->collect_member_initializer_expression(
                            std::move(args),
                            base_init_target.type,
                            false,
                            mem_init.location,
                            true);
                } else if (type_depends_on_template_parameters(
                               member_expr->member_type,
                               ast_ctx.get()) ||
                           canonical_type_kind(member_expr->member_type) ==
                               TypeKind::Object ||
                           args.empty()) {
                    mem_init.init_expr =
                        collect_->collect_member_initializer_expression(
                            std::move(args),
                            member_expr->member_type,
                            false,
                            mem_init.location);
                } else if (args.size() > 1) {
                    diag_engine->report_error(
                        "constructor member initializer for non-class member '" +
                            mem_init.member_name +
                            "' requires a single expression",
                        mem_init.location);
                } else {
                    parsed_init = std::move(args.front());
                }
            } else if (gentle_check(TokenType::LEFT_BRACE)) {
                parsed_init = parse_init_list();
            } else {
                error("expected '(' or '{' in constructor member initializer");
            }

            set_token_idx(mem_init.deferred_init_end_token_idx);
            if (mem_init.init_expr) {
                continue;
            }
            if (!parsed_init) {
                continue;
            }
            if (base_init_target) {
                mem_init.init_expr =
                    collect_->collect_member_initializer_expression(
                        std::move(parsed_init),
                        base_init_target.type,
                        mem_init.location);
            } else if (canonical_type_kind(member_expr->member_type) ==
                TypeKind::Reference) {
                mem_init.init_expr = std::move(parsed_init);
            } else {
                mem_init.init_expr = collect_->collect_member_initializer_expression(
                    std::move(parsed_init),
                    member_expr->member_type,
                    mem_init.location);
            }
        }

        if (!saw_delegating_initializer &&
            !saw_base_initializer &&
            ctx.semantic_state.bases.size() == 1) {
            const auto& direct_base = ctx.semantic_state.bases.front();
            if (direct_base.type &&
                canonical_type_kind(direct_base.type) == TypeKind::Object) {
                CppCtorInitializer implicit_base_init;
                implicit_base_init.member_name = direct_base.name;
                implicit_base_init.target_spelling = direct_base.name;
                implicit_base_init.target_type = direct_base.type;
                implicit_base_init.resolved_target_type = direct_base.type;
                implicit_base_init.is_implicit = true;
                implicit_base_init.is_base_initializer = true;
                implicit_base_init.location = ctor->location;
                std::vector<std::unique_ptr<Expr>> args;
                implicit_base_init.init_expr =
                    collect_->collect_member_initializer_expression(
                        std::move(args),
                        direct_base.type,
                        false,
                        ctor->location,
                        true);
                ctor->ctor_initializers.insert(
                    ctor->ctor_initializers.begin(),
                    std::move(implicit_base_init));
            }
        }
        set_token_idx(saved_idx);
    };
    auto parse_deferred_inline_member_body =
        [&](auto* member_decl,
            bool is_static_member_function,
            bool allow_ctor_mem_initializer_after_try,
            auto&& pre_body_hook) {
        if (!member_decl || !member_decl->has_deferred_inline_body() ||
            member_decl->body) {
            return;
        }

        DeferredInlineParserState saved_state =
            capture_deferred_inline_parser_state();
        seen_stmt_labels.clear();
        stmt_labels.clear();
        local_label_scopes_.clear();
        local_label_unique_id_ = 0;

        auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
        auto function_scope = entered_scope.scope;

        QualType previous_record_lookup_type =
            collect_->collect_current_cpp_record_lookup_type();
        QualType active_record_lookup_type =
            ctx.semantic_owner && ctx.semantic_owner->get_record_type()
                ? QualType(ctx.semantic_owner->get_record_type())
                : QualType(ctx.record_type);
        if (active_record_lookup_type) {
            collect_->collect_set_current_cpp_record_lookup_type(
                active_record_lookup_type);
        }

        Collect::CppThisContext cpp_this_context;
        cpp_this_context.is_member_function = true;
        cpp_this_context.is_static_member_function = is_static_member_function;
        auto fn_type = dyn_cast_shared<FunctionType>(member_decl->type);
        if (!cpp_this_context.is_static_member_function &&
            fn_type &&
            !fn_type->parameters.empty()) {
            cpp_this_context.this_type = fn_type->parameters.front();
        }
        if (!cpp_this_context.this_type &&
            (ctx.current_instantiation_type || active_record_lookup_type)) {
            QualType implicit_this_owner_type =
                (!cpp_this_context.is_static_member_function &&
                 ctx.current_instantiation_type)
                    ? ctx.current_instantiation_type
                    : active_record_lookup_type;
            cpp_this_context.this_type = QualType(
                std::make_shared<PointerType>(implicit_this_owner_type));
        } else if (!cpp_this_context.is_static_member_function &&
                   cpp_this_context.this_type &&
                   ctx.current_instantiation_type) {
            uint8_t pointee_quals = QUAL_NONE;
            if (auto this_ptr =
                    cpp_this_context.this_type.as_shared<PointerType>()) {
                pointee_quals = this_ptr->pointed_type.get_qualifiers();
            }
            QualType qualified_owner(
                ctx.current_instantiation_type.get_shared(),
                static_cast<uint8_t>(
                    ctx.current_instantiation_type.get_qualifiers() |
                    pointee_quals));
            cpp_this_context.this_type = QualType(
                std::make_shared<PointerType>(qualified_owner));
        }
        cpp_this_context.access_context_type =
            ctx.current_instantiation_type
                ? ctx.current_instantiation_type
                : active_record_lookup_type;

        func_type = member_decl->type;
        current_language_linkage_ = LanguageLinkage::None;
        collect_->collect_start_function_definition(
            member_decl->name,
            QualType(member_decl->type),
            cpp_this_context,
            is_in_template_pattern_context());
        Collect::ImmediateFunctionContextScope immediate_function_context_guard(
            collect_.get(), member_decl->is_consteval != 0);

        for (auto& param_decl_base : member_decl->parameters) {
            auto* param_decl = dyn_cast<ParamDecl>(param_decl_base.get());
            if (!param_decl || !param_decl->has_name() ||
                param_decl->get_name() == "this") {
                continue;
            }
            param_decl->sym = collect_->collect_declare_variable_symbol(
                param_decl->get_name(),
                param_decl->type,
                param_decl->storage_class,
                false,
                false,
                param_decl->location);
        }

        cxx_record_parse_stack_.push_back(
            CppRecordParseFrame{
                ctx.record.record_kind,
                ctx.record.name,
                ctx.semantic_owner,
                ctx.primary_class_template,
                ctx.current_instantiation_type});
        struct RecordParseScopeGuard {
            std::vector<CppRecordParseFrame>* stack = nullptr;
            ~RecordParseScopeGuard() {
                if (stack && !stack->empty()) {
                    stack->pop_back();
                }
            }
        } record_parse_scope_guard{&cxx_record_parse_stack_};

        try {
            pre_body_hook(member_decl);
            set_token_idx(member_decl->deferred_inline_body_begin_token_idx);
            if (gentle_check(TokenType::TRY_KW)) {
                auto try_stmt = parse_cpp_try_statement(
                    function_scope,
                    allow_ctor_mem_initializer_after_try);
                SrcLoc body_loc = try_stmt ? try_stmt->location : SrcLoc();
                std::vector<std::unique_ptr<Stmt>> stmts;
                stmts.push_back(std::move(try_stmt));
                member_decl->body = collect_->collect_compound_statement(
                    std::move(stmts), function_scope, body_loc);
            } else {
                member_decl->body = parse_compound_stmt(function_scope);
            }
            member_decl->scope = function_scope;
            member_decl->stmt_labels.insert(
                stmt_labels.begin(), stmt_labels.end());
            set_token_idx(member_decl->deferred_inline_body_end_token_idx);
            member_decl->clear_deferred_inline_body_token_range();
            collect_->collect_leave_scope();
            collect_->collect_finish_function_definition(function_scope);
            collect_->collect_set_current_cpp_record_lookup_type(
                previous_record_lookup_type);
        } catch (...) {
            collect_->collect_abort_function_definition();
            collect_->collect_leave_scope();
            collect_->collect_set_current_cpp_record_lookup_type(
                previous_record_lookup_type);
            restore_deferred_inline_parser_state(std::move(saved_state));
            throw;
        }

        restore_deferred_inline_parser_state(std::move(saved_state));
    };
    auto parse_deferred_inline_method_body = [&](CppMethodDecl* method_decl) {
        parse_deferred_inline_member_body(
            method_decl,
            method_decl &&
                method_decl->storage_class == StorageClass::STATIC,
            false,
            [](CppMethodDecl*) {});
    };
    auto parse_deferred_inline_constructor_body =
        [&](CppConstructorDecl* ctor_decl) {
        parse_deferred_inline_member_body(
            ctor_decl,
            false,
            true,
            [&](CppConstructorDecl* ctor) {
                parse_deferred_constructor_member_initializers(ctor);
            });
    };
    auto parse_deferred_inline_destructor_body =
        [&](CppDestructorDecl* dtor_decl) {
        parse_deferred_inline_member_body(
            dtor_decl,
            false,
            false,
            [](CppDestructorDecl*) {});
    };
    auto parse_deferred_inline_friend_body =
        [&](FriendDecl* friend_decl) {
        auto* function_decl =
            friend_decl ? friend_decl->function_pattern_decl() : nullptr;
        if (!friend_decl || !function_decl ||
            !friend_decl->has_deferred_inline_body() ||
            function_decl->body) {
            return;
        }

        DeferredInlineParserState saved_state =
            capture_deferred_inline_parser_state();
        seen_stmt_labels.clear();
        stmt_labels.clear();
        local_label_scopes_.clear();
        local_label_unique_id_ = 0;

        auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
        auto function_scope = entered_scope.scope;

        QualType previous_record_lookup_type =
            collect_->collect_current_cpp_record_lookup_type();
        collect_->collect_set_current_cpp_record_lookup_type(QualType(nullptr));

        Collect::CppThisContext cpp_this_context;
        cpp_this_context.friend_access_type =
            friend_decl->granting_record_type
                ? friend_decl->granting_record_type
                : (ctx.record_type ? QualType(ctx.record_type) : QualType(nullptr));

        func_type = function_decl->type;
        current_language_linkage_ = LanguageLinkage::None;
        collect_->collect_start_function_definition(
            function_decl->name,
            QualType(function_decl->type),
            cpp_this_context,
            is_in_template_pattern_context());
        Collect::ImmediateFunctionContextScope immediate_function_context_guard(
            collect_.get(), function_decl->is_consteval != 0);

        for (auto& param_decl_base : function_decl->parameters) {
            auto* param_decl = dyn_cast<ParamDecl>(param_decl_base.get());
            if (!param_decl || !param_decl->has_name()) {
                continue;
            }
            param_decl->sym = collect_->collect_declare_variable_symbol(
                param_decl->get_name(),
                param_decl->type,
                param_decl->storage_class,
                false,
                false,
                param_decl->location);
        }

        try {
            set_token_idx(friend_decl->deferred_inline_body_begin_token_idx);
            if (gentle_check(TokenType::TRY_KW)) {
                auto try_stmt = parse_cpp_try_statement(
                    function_scope,
                    false);
                SrcLoc body_loc = try_stmt ? try_stmt->location : SrcLoc();
                std::vector<std::unique_ptr<Stmt>> stmts;
                stmts.push_back(std::move(try_stmt));
                function_decl->body = collect_->collect_compound_statement(
                    std::move(stmts), function_scope, body_loc);
            } else {
                function_decl->body = parse_compound_stmt(function_scope);
            }
            function_decl->scope = function_scope;
            function_decl->stmt_labels.insert(
                stmt_labels.begin(), stmt_labels.end());
            set_token_idx(friend_decl->deferred_inline_body_end_token_idx);
            friend_decl->clear_deferred_inline_body_token_range();
            collect_->collect_leave_scope();
            collect_->collect_finish_function_definition(function_scope);
            collect_->collect_set_current_cpp_record_lookup_type(
                previous_record_lookup_type);
        } catch (...) {
            collect_->collect_abort_function_definition();
            collect_->collect_leave_scope();
            collect_->collect_set_current_cpp_record_lookup_type(
                previous_record_lookup_type);
            restore_deferred_inline_parser_state(std::move(saved_state));
            throw;
        }

        restore_deferred_inline_parser_state(std::move(saved_state));
    };
    auto parse_deferred_inline_method_template_body =
        [&](FunctionTemplateDecl* method_template) {
        auto* templated_function =
            method_template ? method_template->function_decl() : nullptr;
        auto* templated_method =
            dyn_cast<CppMethodDecl>(templated_function);
        auto* templated_ctor =
            dyn_cast<CppConstructorDecl>(templated_function);
        if (!templated_method && !templated_ctor) {
            return;
        }

        collect_->collect_enter_scope(ScopeFlags::TemplateParameterScope);
        struct TemplateScopeGuard {
            Collect* collect = nullptr;
            ~TemplateScopeGuard() {
                if (collect) {
                    collect->collect_leave_scope();
                }
            }
        } template_scope_guard{collect_.get()};

        active_template_parameter_stack_.push_back({});
        struct ActiveTemplateParameterGuard {
            std::vector<std::vector<const TemplateParameterDecl*>>* stack = nullptr;
            ~ActiveTemplateParameterGuard() {
                if (stack && !stack->empty()) {
                    stack->pop_back();
                }
            }
        } active_template_parameter_guard{&active_template_parameter_stack_};
        ++template_pattern_depth_;
        struct TemplatePatternGuard {
            uint32_t* depth = nullptr;
            ~TemplatePatternGuard() {
                if (depth) {
                    --(*depth);
                }
            }
        } template_pattern_guard{&template_pattern_depth_};

        auto& active_parameters = active_template_parameter_stack_.back();
        active_parameters.reserve(method_template->parameters.size());
        for (const auto& parameter : method_template->parameters) {
            const auto* template_parameter = parameter.get();
            if (!template_parameter) {
                continue;
            }
            active_parameters.push_back(template_parameter);
            if (auto* type_parameter =
                    dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
                if (!type_parameter->name.empty()) {
                    collect_->collect_declare_type_name_symbol(
                        type_parameter->name,
                        QualType(type_parameter->type),
                        type_parameter->location);
                }
                continue;
            }
            if (auto* non_type_parameter =
                    dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
                if (!non_type_parameter->name.empty() &&
                    non_type_parameter->sym) {
                    collect_->collect_bind_symbol_in_current_scope(
                        non_type_parameter->name,
                        non_type_parameter->sym);
                }
            }
        }

        if (templated_ctor) {
            parse_deferred_inline_constructor_body(templated_ctor);
            return;
        }

        parse_deferred_inline_method_body(templated_method);
    };
    auto parse_deferred_inline_friend_template_body =
        [&](FriendDecl* friend_decl) {
        auto* friend_template =
            friend_decl ? friend_decl->function_template_decl() : nullptr;
        if (!friend_template || !friend_template->function_decl()) {
            return;
        }

        collect_->collect_enter_scope(ScopeFlags::TemplateParameterScope);
        struct TemplateScopeGuard {
            Collect* collect = nullptr;
            ~TemplateScopeGuard() {
                if (collect) {
                    collect->collect_leave_scope();
                }
            }
        } template_scope_guard{collect_.get()};

        active_template_parameter_stack_.push_back({});
        struct ActiveTemplateParameterGuard {
            std::vector<std::vector<const TemplateParameterDecl*>>* stack = nullptr;
            ~ActiveTemplateParameterGuard() {
                if (stack && !stack->empty()) {
                    stack->pop_back();
                }
            }
        } active_template_parameter_guard{&active_template_parameter_stack_};
        ++template_pattern_depth_;
        struct TemplatePatternGuard {
            uint32_t* depth = nullptr;
            ~TemplatePatternGuard() {
                if (depth) {
                    --(*depth);
                }
            }
        } template_pattern_guard{&template_pattern_depth_};

        auto& active_parameters = active_template_parameter_stack_.back();
        active_parameters.reserve(friend_template->parameters.size());
        for (const auto& parameter : friend_template->parameters) {
            const auto* template_parameter = parameter.get();
            if (!template_parameter) {
                continue;
            }
            active_parameters.push_back(template_parameter);
            if (auto* type_parameter =
                    dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
                if (!type_parameter->name.empty()) {
                    collect_->collect_declare_type_name_symbol(
                        type_parameter->name,
                        QualType(type_parameter->type),
                        type_parameter->location);
                }
                continue;
            }
            if (auto* non_type_parameter =
                    dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
                if (!non_type_parameter->name.empty() &&
                    non_type_parameter->sym) {
                    collect_->collect_bind_symbol_in_current_scope(
                        non_type_parameter->name,
                        non_type_parameter->sym);
                }
            }
        }

        parse_deferred_inline_friend_body(friend_decl);
    };

    for (const auto& member : ctx.record.members) {
        auto* method_decl = dyn_cast<CppMethodDecl>(member.get());
        if (!method_decl) {
            auto* method_template = dyn_cast<FunctionTemplateDecl>(member.get());
            if (!method_template) {
                continue;
            }
            parse_deferred_inline_method_template_body(method_template);
            continue;
        }
        parse_deferred_inline_method_body(method_decl);
    }
    for (const auto& member : ctx.record.members) {
        auto* ctor_decl = dyn_cast<CppConstructorDecl>(member.get());
        if (!ctor_decl) {
            continue;
        }
        parse_deferred_inline_constructor_body(ctor_decl);
    }
    for (const auto& member : ctx.record.members) {
        auto* dtor_decl = dyn_cast<CppDestructorDecl>(member.get());
        if (!dtor_decl) {
            continue;
        }
        parse_deferred_inline_destructor_body(dtor_decl);
    }
    for (const auto& member : ctx.record.members) {
        auto* friend_decl = dyn_cast<FriendDecl>(member.get());
        if (!friend_decl) {
            continue;
        }
        if (friend_decl->function_template_decl()) {
            parse_deferred_inline_friend_template_body(friend_decl);
            continue;
        }
        parse_deferred_inline_friend_body(friend_decl);
    }
}
