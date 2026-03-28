#include "parser.h"

// Deferred inline member parsing for record bodies.
// This logic is parser-stateful and intentionally isolated from the
// record-semantic build phases so class layout and body reparsing can evolve
// independently.

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
        struct BaseInitializerTarget {
            QualType type;
            bool is_virtual = false;
        };
        auto base_initializer_target_for_name =
            [&](const std::string& init_name)
            -> std::optional<BaseInitializerTarget> {
            for (const auto& base : ctx.semantic_state.bases) {
                if (base.name == init_name) {
                    BaseInitializerTarget target;
                    target.type = base.type;
                    target.is_virtual = base.is_virtual;
                    return target;
                }
            }
            for (const auto& virtual_base : ctx.semantic_state.virtual_bases) {
                if (virtual_base.name == init_name) {
                    BaseInitializerTarget target;
                    target.type = virtual_base.type;
                    target.is_virtual = true;
                    return target;
                }
            }
            return std::nullopt;
        };
        bool saw_base_initializer = false;
        bool saw_delegating_initializer = false;
        for (auto& mem_init : ctor->ctor_initializers) {
            mem_init.member_expr.reset();
            mem_init.init_expr.reset();
            mem_init.is_base_initializer = false;

            if (mem_init.is_delegating_initializer) {
                saw_delegating_initializer = true;
                if (!ctx.record_type) {
                    diag_engine->report_error(
                        "delegating constructor target type is unavailable",
                        mem_init.location);
                    continue;
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
                base_initializer_target_for_name(mem_init.member_name);
            if (base_init_target.has_value()) {
                saw_base_initializer = true;
                mem_init.is_base_initializer = true;
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
                            base_init_target->type,
                            false,
                            mem_init.location,
                            true);
                } else if (canonical_type_kind(member_expr->member_type) ==
                    TypeKind::Object) {
                    mem_init.init_expr =
                        collect_->collect_member_initializer_expression(
                            std::move(args),
                            member_expr->member_type,
                            false,
                            mem_init.location);
                } else if (args.empty()) {
                    diag_engine->report_error(
                        "constructor member initializer for '" +
                            mem_init.member_name +
                            "' requires an initializer expression",
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
                        base_init_target->type,
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

        Collect::CppThisContext cpp_this_context;
        cpp_this_context.is_member_function = true;
        cpp_this_context.is_static_member_function = is_static_member_function;
        auto fn_type = dyn_cast_shared<FunctionType>(member_decl->type);
        if (!cpp_this_context.is_static_member_function &&
            fn_type &&
            !fn_type->parameters.empty()) {
            cpp_this_context.this_type = fn_type->parameters.front();
        }
        if (!cpp_this_context.this_type && ctx.record_type) {
            cpp_this_context.this_type = QualType(
                std::make_shared<PointerType>(QualType(ctx.record_type)));
        }

        func_type = member_decl->type;
        current_language_linkage_ = LanguageLinkage::None;
        collect_->collect_start_function_definition(
            member_decl->name,
            QualType(member_decl->type),
            cpp_this_context);

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
                param_decl->location);
        }

        cxx_record_parse_stack_.push_back(
            CppRecordParseFrame{ctx.record.record_kind, ctx.record.name});
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
        } catch (...) {
            collect_->collect_abort_function_definition();
            collect_->collect_leave_scope();
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
    auto parse_deferred_inline_method_template_body =
        [&](FunctionTemplateDecl* method_template) {
        auto* templated_method =
            method_template
                ? dyn_cast<CppMethodDecl>(method_template->function_decl())
                : nullptr;
        if (!templated_method) {
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

        parse_deferred_inline_method_body(templated_method);
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
}
