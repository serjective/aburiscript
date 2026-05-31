#include "parser.h"
#include "../helpers/auto_type_utils.h"
#include "../helpers/qualified_name_utils.h"
#include "../perf_stats.h"

#include <limits>

std::vector<const Expr*> Parser::collect_decl_default_arguments(
    const FuncDecl* decl) const {
    std::vector<const Expr*> defaults;
    if (!decl) {
        return defaults;
    }
    defaults.resize(decl->parameters.size(), nullptr);
    for (size_t index = 0; index < decl->parameters.size(); ++index) {
        auto* param_decl = dyn_cast<ParamDecl>(decl->parameters[index].get());
        if (!param_decl) {
            continue;
        }
        defaults[index] = get_param_decl_default_argument(param_decl);
    }
    return defaults;
}

void Parser::register_function_default_arguments(
    const std::shared_ptr<Symbol>& sym,
    const FuncDecl* decl,
    SrcLoc fallback_loc) {
    if (!is_cxx_mode_active() || !sym || !decl || sym->kind != SymbolKind::FUNCTION) {
        return;
    }

    std::vector<const Expr*> incoming_defaults = collect_decl_default_arguments(decl);
    bool has_incoming_defaults = false;
    for (const Expr* expr : incoming_defaults) {
        if (expr) {
            has_incoming_defaults = true;
            break;
        }
    }
    if (!has_incoming_defaults &&
        !get_symbol_cpp_default_arguments(sym.get())) {
        return;
    }

    size_t conflict_index = std::numeric_limits<size_t>::max();
    if (merge_symbol_cpp_default_arguments(sym.get(),
                                           incoming_defaults,
                                           &conflict_index)) {
        return;
    }

    SrcLoc conflict_loc = fallback_loc;
    if (conflict_index < decl->parameters.size()) {
        auto* param_decl = dyn_cast<ParamDecl>(decl->parameters[conflict_index].get());
        if (param_decl) {
            if (const Expr* expr = get_param_decl_default_argument(param_decl)) {
                conflict_loc = expr->location;
            } else if (!param_decl->location.isInvalid()) {
                conflict_loc = param_decl->location;
            }
        }
    }
    error_custloc("redefinition of default argument", conflict_loc);
}

bool Parser::function_type_has_ordinary_cxx_auto_parameters(
    const std::shared_ptr<CType>& type) const {
    auto function_type = dyn_cast_shared<FunctionType>(type);
    if (!function_type) {
        return false;
    }
    for (const auto& param_type : function_type->parameters) {
        if (auto_type_utils::has_ordinary_cxx_auto_type(param_type.get_shared())) {
            return true;
        }
    }
    return false;
}

void Parser::validate_function_parameter_auto_placeholders(
    const std::shared_ptr<FunctionType>& function_type,
    SrcLoc loc) {
    if (!function_type) {
        return;
    }

    bool has_ordinary_cxx_auto_param = false;
    bool has_decltype_auto_param = false;
    bool has_gnu_auto_param = false;
    for (const auto& param_type : function_type->parameters) {
        has_ordinary_cxx_auto_param |=
            auto_type_utils::has_ordinary_cxx_auto_type(param_type.get_shared());
        has_decltype_auto_param |=
            auto_type_utils::has_decltype_auto_type(param_type.get_shared());
        has_gnu_auto_param |=
            auto_type_utils::has_gnu_auto_type(param_type.get_shared());
    }

    if (has_decltype_auto_param) {
        error_custloc(
            "'decltype(auto)' is not allowed in function parameter declarations",
            loc);
    }
    if (has_gnu_auto_param) {
        error_custloc(
            "'__auto_type' is not allowed in function parameter declarations",
            loc);
    }
    if (has_ordinary_cxx_auto_param && !lang_opts.is_cxx20_or_later()) {
        error_custloc(
            "'auto' in function parameter declarations requires C++20",
            loc);
    }
}

void Parser::lower_cxx_auto_function_parameter_placeholders(
    std::vector<std::unique_ptr<Decl>>& parameters,
    const std::shared_ptr<FunctionType>& function_type,
    TemplateParameterList& template_parameters,
    uint32_t parameter_depth,
    SrcLoc loc) {
    if (!ast_ctx) {
        error_custloc(
            "internal error: missing AST context for abbreviated function template",
            loc);
    }

    bool changed = false;
    for (auto& parameter : parameters) {
        auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
        if (!param_decl || !param_decl->type ||
            !auto_type_utils::has_ordinary_cxx_auto_type(
                param_decl->type.get_shared())) {
            continue;
        }

        const bool is_parameter_pack = param_decl->is_parameter_pack;
        auto rewritten_type =
            auto_type_utils::replace_cxx_auto_placeholders_with_callback(
                param_decl->type.get_shared(),
                [&](size_t, const AutoType& auto_type) -> QualType {
                    const uint32_t parameter_index =
                        static_cast<uint32_t>(template_parameters.size());
                    std::string invented_name =
                        "__aburi_auto_param_" +
                        std::to_string(parameter_depth) + "_" +
                        std::to_string(parameter_index);
                    auto parameter_type =
                        std::make_shared<TemplateTypeParmType>(
                            invented_name,
                            parameter_depth,
                            parameter_index,
                            is_parameter_pack);
                    auto parameter_decl = make_ast<TemplateTypeParmDecl>(
                        *ast_ctx,
                        invented_name,
                        parameter_depth,
                        parameter_index,
                        parameter_type,
                        is_parameter_pack,
                        param_decl->location);
                    parameter_type->parameter_decl = parameter_decl.get();
                    if (auto_type.type_constraint) {
                        std::vector<TemplateArgument> concept_arguments;
                        concept_arguments.push_back(
                            TemplateArgument(QualType(parameter_type)));
                        concept_arguments.insert(
                            concept_arguments.end(),
                            auto_type.type_constraint->template_arguments.begin(),
                            auto_type.type_constraint->template_arguments.end());
                        parameter_decl->type_constraint =
                            collect_->collect_concept_specialization_expression(
                                auto_type.type_constraint->concept_decl,
                                auto_type.type_constraint->concept_name,
                                std::move(concept_arguments),
                                auto_type.type_constraint->location);
                    }
                    template_parameters.push_back(std::move(parameter_decl));
                    return QualType(parameter_type);
                });

        param_decl->type = QualType(
            rewritten_type,
            param_decl->type.get_qualifiers());
        if (param_decl->sym) {
            param_decl->sym->type = param_decl->type;
        }
        changed = true;
    }

    if (!changed || !function_type) {
        return;
    }

    function_type->clear_parameters();
    function_type->parameters.reserve(parameters.size());
    function_type->parameter_pack_flags.reserve(parameters.size());
    for (const auto& parameter : parameters) {
        auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
        if (!param_decl) {
            error_custloc(
                "internal error: function parameter did not produce ParamDecl",
                loc);
        }
        function_type->push_parameter(
            param_decl->type,
            param_decl->is_parameter_pack);
    }
}

TemplateParameterList*
Parser::active_abbreviated_function_template_parameters() {
    if (!active_abbreviated_function_template_context_) {
        return nullptr;
    }
    return active_abbreviated_function_template_context_->parameters;
}

uint32_t
Parser::active_abbreviated_function_template_parameter_depth() const {
    if (!active_abbreviated_function_template_context_) {
        return template_parameter_depth_;
    }
    return active_abbreviated_function_template_context_->parameter_depth;
}

std::unique_ptr<Decl> Parser::wrap_abbreviated_function_template_if_needed(
    std::unique_ptr<Decl> function_decl,
    TemplateParameterList template_parameters,
    SrcLoc loc,
    bool publish_namespace_template) {
    if (template_parameters.empty()) {
        return function_decl;
    }
    auto* function = dyn_cast<FuncDecl>(function_decl.get());
    if (!function) {
        error_custloc(
            "internal error: abbreviated function template target is not a function",
            loc);
    }
    if (isa<CppDestructorDecl>(function)) {
        error_custloc("destructor cannot be a template", function->location);
    }
    if (function->name.empty()) {
        fail_cpp_unsupported("unnamed function template", function->location);
    }

    std::string template_name = function->name;
    auto template_decl = make_ast<FunctionTemplateDecl>(
        *ast_ctx,
        std::move(template_parameters),
        std::move(function_decl),
        loc);
    finalize_primary_template_decl(
        template_decl.get(),
        template_name,
        LookupNamespace::Ordinary);
    if (publish_namespace_template) {
        collect_->collect_add_function_template_decl(
            template_name,
            template_decl.get());
    }
    return template_decl;
}

bool Parser::current_token_is_from_system_header() {
    if (!tok_mgnt.sm) {
        return false;
    }
    SrcLoc loc = current_token().loc;
    if (loc.isInvalid()) {
        return false;
    }
    const auto& entry = tok_mgnt.sm->getEntryForLocation(loc);
    if (entry.is_expansion) {
        if (entry.macro_src.caller.isInvalid()) {
            return false;
        }
        const auto& caller_entry = tok_mgnt.sm->getEntryForLocation(
            entry.macro_src.caller);
        return !caller_entry.is_expansion &&
               caller_entry.file_src &&
               caller_entry.file_src->is_system_header;
    }
    return entry.file_src && entry.file_src->is_system_header;
}

bool Parser::should_skip_system_header_function_body_semantics() {
    return lang_opts.syntax_only &&
           current_token_is_from_system_header();
}

void Parser::skip_function_body_tokens() {
    auto skip_balanced = [&](TokenType open_tok, TokenType close_tok) {
        if (!gentle_check(open_tok)) {
            error("expected function body");
        }
        size_t depth = 0;
        do {
            if (gentle_check(TokenType::Eof)) {
                error("unexpected end of file while skipping function body");
            }
            if (gentle_check(open_tok)) {
                ++depth;
            } else if (gentle_check(close_tok)) {
                if (depth == 0) {
                    error("unbalanced function body");
                }
                --depth;
            }
            advance();
        } while (depth > 0);
    };

    if (gentle_check(TokenType::LEFT_BRACE)) {
        skip_balanced(TokenType::LEFT_BRACE, TokenType::RIGHT_BRACE);
        return;
    }

    if (!gentle_check(TokenType::TRY_KW)) {
        error("expected function body");
    }
    advance();
    skip_balanced(TokenType::LEFT_BRACE, TokenType::RIGHT_BRACE);
    while (gentle_check(TokenType::CATCH_KW)) {
        advance();
        skip_balanced(TokenType::LEFT_PAREN, TokenType::RIGHT_PAREN);
        skip_balanced(TokenType::LEFT_BRACE, TokenType::RIGHT_BRACE);
    }
}

std::unique_ptr<Decl> Parser::parse_function(DeclarationParser * decl_parser,
                                             SrcLoc loc,
                                             std::shared_ptr<Symbol> predecl_sym,
                                             TemplateParameterList*
                                                 abbreviated_template_parameters_out) {

    /*
     * high level overmap is to check words for basic types/quantifiers,
     * then check custom type, then deduce we have identifer
     * */
    if (func_type == nullptr) {
        seen_stmt_labels.clear();
        stmt_labels.clear();
        local_label_scopes_.clear();
        local_label_unique_id_ = 0;
    }

    bool in_class_member_context =
        is_cxx_mode_active() &&
        !decl_parser->is_friend &&
        !cxx_record_parse_stack_.empty() &&
        !cxx_record_parse_stack_.back().name.empty();
    bool is_static_member =
        in_class_member_context &&
        decl_parser->str_class == StorageClass::STATIC;
    if (decl_parser->is_conversion_function &&
        (!in_class_member_context || is_static_member)) {
        error_custloc(
            "conversion function must be a non-static member function",
            loc);
    }
    QualType predecl_original_type =
        predecl_sym ? predecl_sym->type : QualType();
    validate_cpp_operator_function_declaration(
        decl_parser->name,
        in_class_member_context,
        is_static_member,
        loc);
    bool is_operator_new_delete =
        decl_parser->name == "operatornew" ||
        decl_parser->name == "operatornew[]" ||
        decl_parser->name == "operatordelete" ||
        decl_parser->name == "operatordelete[]";
    if (decl_parser->is_consteval && is_operator_new_delete) {
        error_custloc(
            "allocation/deallocation function cannot be consteval",
            loc);
    }

    auto fin_funcdecl = collect_->collect_function_declaration(
        decl_parser->name,
        decl_parser->result_type,
        decl_parser->str_class,
        decl_parser->is_inline,
        decl_parser->asm_label,
        loc,
        current_decl_language_linkage());
    fin_funcdecl->is_constexpr = decl_parser->is_constexpr;
    fin_funcdecl->is_consteval = decl_parser->is_consteval;
    if (fin_funcdecl->is_consteval) {
        fin_funcdecl->is_constexpr = true;
        fin_funcdecl->is_inline = true;
        if (predecl_sym && predecl_sym->kind == SymbolKind::FUNCTION) {
            predecl_sym->is_consteval = true;
            predecl_sym->is_constexpr = true;
            predecl_sym->is_inline = true;
        }
    }
    fin_funcdecl->trailing_requires_clause =
        std::move(decl_parser->trailing_requires_clause);
    auto synthesize_parameter_decls_from_function_type =
        [&](FuncDecl* decl) {
            if (!decl || !decl->parameters.empty()) {
                return;
            }
            auto fn_type =
                desugar_type(QualType(decl->type)).as_shared<FunctionType>();
            if (!fn_type || !fn_type->has_prototype) {
                return;
            }
            for (size_t index = 0; index < fn_type->parameters.size(); ++index) {
                const auto& param_type = fn_type->parameters[index];
                auto param_decl = collect_->collect_parameter_declaration(
                    param_type,
                    "",
                    nullptr,
                    StorageClass::NONE,
                    loc);
                if (auto* typed_param = dyn_cast<ParamDecl>(param_decl.get())) {
                    typed_param->is_parameter_pack =
                        fn_type->parameter_is_pack(index);
                }
                decl->parameters.push_back(std::move(param_decl));
            }
        };
    auto adopt_prior_prototype_for_c_declaration =
        [&](FuncDecl* decl) {
            if (!decl || is_cxx_mode_active() || !predecl_sym ||
                predecl_sym->kind != SymbolKind::FUNCTION) {
                return;
            }
            auto current_fn =
                desugar_type(QualType(decl->type)).as_shared<FunctionType>();
            auto prior_fn =
                desugar_type(predecl_sym->type).as_shared<FunctionType>();
            if (!current_fn || !prior_fn ||
                current_fn->has_prototype ||
                !prior_fn->has_prototype ||
                prior_fn->is_variadic) {
                return;
            }
            if (!predecl_sym->type.equals_unqualified(QualType(decl->type))) {
                return;
            }
            decl->type = predecl_sym->type.get_shared();
        };
    if (predecl_sym &&
        predecl_sym->kind == SymbolKind::FUNCTION &&
        decl_parser->is_inline) {
        fin_funcdecl->has_prior_non_inline_declaration =
            predecl_sym->had_non_inline_declaration != 0;
    }
    if (auto fin_fn_type = dyn_cast_shared<FunctionType>(fin_funcdecl->type)) {
        size_t user_param_count = fin_fn_type->parameters.size();
        validate_function_parameter_auto_placeholders(fin_fn_type, loc);
        if (auto_type_utils::has_gnu_auto_type(fin_fn_type->ret_type.get_shared())) {
            error("'__auto_type' is not allowed in function return types");
        }
        if (auto_type_utils::has_decltype_auto_type(
                fin_fn_type->ret_type.get_shared()) &&
            !auto_type_utils::is_decltype_auto_placeholder(
                fin_fn_type->ret_type.get_shared())) {
            error("'decltype(auto)' can only be used as a function return placeholder");
        }
        if (decl_parser->is_conversion_function && user_param_count != 0) {
            error_custloc(
                "conversion function cannot have parameters",
                loc);
        }
    }
    if (is_cxx_mode_active()) {
        auto current_scope = collect_->collect_current_scope();
        auto qualifier_prefix =
            qualified_name_utils::namespace_prefix_from_effective_decl_scope(
                current_scope);
        if (qualifier_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                fin_funcdecl.get(), std::move(*qualifier_prefix));
        }
    }
    fin_funcdecl->explicit_specialization_arguments =
        decl_parser->explicit_specialization_arguments;
    fin_funcdecl->has_explicit_specialization_argument_list =
        decl_parser->has_explicit_specialization_argument_list;
    if (predecl_sym && predecl_sym->kind == SymbolKind::FUNCTION &&
        predecl_sym->friend_access_type) {
        fin_funcdecl->friend_access_type = predecl_sym->friend_access_type;
    }
    if (!fin_funcdecl->friend_access_type &&
        is_in_template_pattern_context()) {
        fin_funcdecl->friend_access_type =
            lookup_friend_access_type_for_current_function_template_redeclaration(
                fin_funcdecl.get());
    }

    auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
    auto new_scope = entered_scope.scope;
    if (decl_parser->is_kr_style) {
        // K&R old-style function definition: parse declaration-list between ) and {
        parse_kr_declaration_list(
            decl_parser,
            fin_funcdecl.get(),
            predecl_original_type);
    } else {
        bool seenVoid = false;
        for (auto &i: decl_parser->func_args) {
            retain_type_specifier_decl_if_needed(*i);
            if (i->is_consteval) {
                error("'consteval' is not valid for function parameter declarations");
            }
            if (i->is_constexpr) {
                error("'constexpr' is not valid for function parameter declarations");
            }
            if (i->explicit_specifier.is_present) {
                error("'explicit' is not valid for function parameter declarations");
            }
            if (i->result_type->isVoid()) {
                seenVoid = true;
                if (!i->name.empty()) {
                    error("Argument cannot have 'void' type");
                }
            }
            auto param_type = QualType(i->result_type, i->qualifiers);
            std::shared_ptr<Symbol> param_sym = nullptr;
            if (!i->name.empty()) {
                if (i->preparsed_sym) {
                    auto existing_in_scope = collect_->collect_lookup_variable_symbol(i->name, false);
                    if (existing_in_scope && existing_in_scope != i->preparsed_sym) {
                        error("redefinition of '" + i->name + "'");
                    }
                    param_sym = i->preparsed_sym;
                    param_sym->type = param_type;
                    if (param_sym->uid.empty()) {
                        collect_->collect_add_global_symbol(param_sym);
                    }
                    collect_->collect_bind_symbol_in_current_scope(i->name, param_sym);
                } else {
                    param_sym = collect_->collect_declare_variable_symbol(
                        i->name, param_type, i->str_class, false, false, i->begin_loc);
                }
            }
            auto new_param_decl_base = collect_->collect_parameter_declaration(param_type,
                i->name, param_sym, i->str_class, i->begin_loc);
            if (auto* param_decl = dyn_cast<ParamDecl>(new_param_decl_base.get())) {
                param_decl->is_constexpr = i->is_constexpr;
                param_decl->is_parameter_pack = i->is_parameter_pack;
                set_param_decl_default_argument(
                    param_decl,
                    std::move(i->default_argument));
            }
            fin_funcdecl->parameters.push_back(std::move(new_param_decl_base));

        }
        if (seenVoid) {
            auto *func_ty = dyn_cast<FunctionType>(decl_parser->result_type.get());
            if (func_ty && func_ty->is_variadic) {
                error("'void' parameter cannot be combined with '...'");
            }
            if (fin_funcdecl->parameters.size() != 1) {
                error("mixed up 'void' with other function arguments in declaration");
            }
        }
    }
    if (auto fin_fn_type = dyn_cast_shared<FunctionType>(fin_funcdecl->type);
        fin_fn_type &&
        function_type_has_ordinary_cxx_auto_parameters(fin_fn_type)) {
        TemplateParameterList local_abbreviated_template_parameters;
        TemplateParameterList* target_template_parameters =
            active_abbreviated_function_template_parameters();
        if (!target_template_parameters) {
            target_template_parameters = &local_abbreviated_template_parameters;
        }
        lower_cxx_auto_function_parameter_placeholders(
            fin_funcdecl->parameters,
            fin_fn_type,
            *target_template_parameters,
            active_abbreviated_function_template_parameter_depth(),
            loc);
        if (abbreviated_template_parameters_out) {
            *abbreviated_template_parameters_out =
                std::move(local_abbreviated_template_parameters);
        }
    }
    register_function_default_arguments(predecl_sym, fin_funcdecl.get(), loc);
    // Parse attributes after function declarator, before body
    auto func_trailing_attrs = try_parse_attributes();
    ast_ctx->append_attrs(fin_funcdecl->node_id, std::move(func_trailing_attrs));

    if (gentle_check(TokenType::ASSIGN)) {
        SrcLoc suffix_loc = current_token().loc;
        advance(); // '='
        if (gentle_check(TokenType::DELETE)) {
            fin_funcdecl->is_deleted = true;
            advance(); // 'delete'
        } else if (gentle_check(TokenType::DEFAULT)) {
            fin_funcdecl->is_defaulted = true;
            advance(); // 'default'
        } else {
            fail_cpp_unsupported("function declaration suffix", suffix_loc);
        }
    }

    // check to see if already in scope, and if so check to see if types are compatible
    std::unique_ptr<Stmt> compound_stmt = nullptr;

    if (gentle_check(TokenType::SEMICOLON) || gentle_check(TokenType::COMMA)) {
        // it's a prototype declaration — don't consume ';' or ','
        // so the caller's multi-declarator loop can handle them uniformly
        adopt_prior_prototype_for_c_declaration(fin_funcdecl.get());
        synthesize_parameter_decls_from_function_type(fin_funcdecl.get());
        collect_->collect_leave_scope();
        fin_funcdecl->body = nullptr;
        return std::move(fin_funcdecl);
    }
    if (predecl_sym && predecl_sym->kind == SymbolKind::FUNCTION &&
        !in_class_member_context) {
        predecl_sym->type = QualType(fin_funcdecl->type);
    }
    auto prev_func_type = func_type;
    auto prev_decl_language_linkage = current_language_linkage_;
    func_type = fin_funcdecl->type;
    Collect::CppThisContext cpp_this_context;
    QualType active_record_lookup_type;
    if (is_cxx_mode_active() &&
        !cxx_record_parse_stack_.empty() &&
        !cxx_record_parse_stack_.back().name.empty()) {
        const auto& record_frame = cxx_record_parse_stack_.back();
        cpp_this_context.is_member_function = true;
        cpp_this_context.is_static_member_function =
            fin_funcdecl->storage_class == StorageClass::STATIC;
        active_record_lookup_type = record_frame.current_instantiation_type;
        if (!active_record_lookup_type && record_frame.semantic_owner &&
            record_frame.semantic_owner->get_record_type()) {
            active_record_lookup_type =
                QualType(record_frame.semantic_owner->get_record_type());
        }
        if (!active_record_lookup_type) {
            auto owner_type_raw = collect_->collect_lookup_tag_type(
                record_frame.name,
                true);
            auto owner_type = dyn_cast_shared<ObjectType>(owner_type_raw);
            if (owner_type) {
                active_record_lookup_type = QualType(owner_type);
            }
        }
        if (!cpp_this_context.is_static_member_function) {
            QualType predecl_this_type;
            if (predecl_original_type) {
                auto predecl_fn_type =
                    desugar_type(predecl_original_type).as_shared<FunctionType>();
                if (predecl_fn_type && !predecl_fn_type->parameters.empty()) {
                    predecl_this_type = predecl_fn_type->parameters.front();
                }
            }
            if (record_frame.current_instantiation_type) {
                uint8_t pointee_quals = QUAL_NONE;
                if (auto this_ptr =
                        predecl_this_type.as_shared<PointerType>()) {
                    pointee_quals = this_ptr->pointed_type.get_qualifiers();
                }
                QualType qualified_owner =
                    record_frame.current_instantiation_type.with_qualifiers(
                        pointee_quals);
                cpp_this_context.this_type = QualType(
                    std::make_shared<PointerType>(qualified_owner));
            } else if (predecl_this_type) {
                cpp_this_context.this_type = predecl_this_type;
            } else if (active_record_lookup_type) {
                cpp_this_context.this_type = QualType(
                    std::make_shared<PointerType>(active_record_lookup_type));
            }
        }
        cpp_this_context.access_context_type = active_record_lookup_type;
    }
    if (!cpp_this_context.friend_access_type &&
        fin_funcdecl->friend_access_type) {
        cpp_this_context.friend_access_type =
            fin_funcdecl->friend_access_type;
    }
    QualType previous_record_lookup_type =
        collect_->collect_current_cpp_record_lookup_type();
    struct FunctionRecordLookupGuard {
        Collect* collect = nullptr;
        QualType previous_type = nullptr;
        ~FunctionRecordLookupGuard() {
            if (collect) {
                collect->collect_set_current_cpp_record_lookup_type(previous_type);
            }
        }
    } function_record_lookup_guard{
        active_record_lookup_type ? collect_.get() : nullptr,
        previous_record_lookup_type};
    if (active_record_lookup_type) {
        collect_->collect_set_current_cpp_record_lookup_type(
            active_record_lookup_type);
    }
    collect_->collect_start_function_definition(
        fin_funcdecl->name,
        QualType(fin_funcdecl->type),
        cpp_this_context,
        is_in_template_pattern_context());
    current_language_linkage_ = LanguageLinkage::None;
    Collect::ImmediateFunctionContextScope immediate_function_context_guard(
        collect_.get(), fin_funcdecl->is_consteval != 0);
    try {
        if (should_skip_system_header_function_body_semantics() &&
            gentle_check(TokenType::LEFT_BRACE)) {
            SrcLoc body_loc = current_token().loc;
            if (auto* profiler = active_perf_profiler()) {
                profiler->add_counter(
                    PerfCounter::ParserSkippedSystemFunctionBodies);
            }
            skip_function_body_tokens();
            collect_->collect_mark_current_function_body_semantics_skipped();
            std::vector<std::unique_ptr<Stmt>> stmts;
            compound_stmt = collect_->collect_compound_statement(
                std::move(stmts), new_scope, body_loc);
        } else if (gentle_check(TokenType::LEFT_BRACE)) {
            compound_stmt = parse_compound_stmt(new_scope);
            // its a statement
        } else if (is_cxx_mode_active() && gentle_check(TokenType::TRY_KW)) {
            auto try_stmt = parse_cpp_try_statement(new_scope);
            SrcLoc body_loc = try_stmt ? try_stmt->location : SrcLoc();
            std::vector<std::unique_ptr<Stmt>> stmts;
            stmts.push_back(std::move(try_stmt));
            compound_stmt = collect_->collect_compound_statement(
                std::move(stmts), new_scope, body_loc);
        } else if (decl_parser->is_kr_style && isTokenDeclarationSpec(current_token())) {
            // K&R identifier-list used in prototype context (e.g. int f(a, b);)
            // This shouldn't happen since we already parsed the declaration-list,
            // but handle gracefully
            collect_->collect_abort_function_definition();
            collect_->collect_leave_scope();
            func_type = prev_func_type;
            current_language_linkage_ = prev_decl_language_linkage;
            error("unexpected declaration after K&R function declarator");
            return {};
        } else {
            Token tok = current_token();
            collect_->collect_abort_function_definition();
            collect_->collect_leave_scope();
            func_type = prev_func_type;
            current_language_linkage_ = prev_decl_language_linkage;
            error("While parsing a function, we encountered a \""
                          + tok.value + R"(" while we were expecting "(" )" );

            return {};
        }
    } catch (...) {
        current_language_linkage_ = prev_decl_language_linkage;
        throw;
    }
    current_language_linkage_ = prev_decl_language_linkage;

    fin_funcdecl->body = std::move(compound_stmt);
    fin_funcdecl->scope = new_scope;
    fin_funcdecl->stmt_labels.insert(stmt_labels.begin(), stmt_labels.end());
    collect_->collect_leave_scope();
    collect_->collect_finish_function_definition(new_scope);
    func_type = prev_func_type;

    return std::move(fin_funcdecl);
}

void Parser::parse_kr_declaration_list(DeclarationParser *decl_parser,
                                       FuncDecl *func_decl,
                                       QualType visible_prototype_type) {
    // Parse declaration-list between ) and { for K&R old-style definitions.
    // e.g.:  int add(a, b) int a; int b; { ... }
    //        int add(a, b) int a, b; { ... }
    auto &kr_names = decl_parser->kr_param_names;

    // Map: param name -> resolved type + storage class + qualifiers
    struct KRParamInfo {
        std::shared_ptr<CType> type;
        StorageClass str_class = StorageClass::NONE;
        uint8_t qualifiers = QUAL_NONE;
        SrcLoc loc;
    };
    std::unordered_map<std::string, KRParamInfo> declared_params;

    // Parse each declaration line: "int a;" or "int a, b;" or "int *p;"
    while (isTokenDeclarationSpec(current_token())) {
        auto dp = DeclarationParser(this);
        dp.parse_declaration(false); // parse specifiers only (no declarator)
        auto base_type = dp.first_half;
        auto base_str_class = dp.str_class;

        // Validate: only register storage class allowed in K&R declaration-list
        if (base_str_class != StorageClass::NONE && base_str_class != StorageClass::REGISTER) {
            error("only 'register' storage class is allowed in K&R parameter declaration");
        }

        // Parse comma-separated declarators
        bool first = true;
        while (true) {
            if (first) {
                first = false;
            } else {
                dp.reset_declarator_parsing_state();
            }
            auto resolved_type = dp.parse_declarator(base_type);

            if (dp.name.empty()) {
                error("expected parameter name in K&R declaration-list");
            }

            // Check that the declared name is in the identifier-list
            bool found_in_list = false;
            for (const auto &kr_name : kr_names) {
                if (kr_name == dp.name) {
                    found_in_list = true;
                    break;
                }
            }
            if (!found_in_list) {
                error("'" + dp.name + "' is not in the K&R parameter identifier-list");
            }

            // Check for duplicate declarations
            if (declared_params.count(dp.name)) {
                error("duplicate declaration of parameter '" + dp.name + "' in K&R declaration-list");
            }

            declared_params[dp.name] = {resolved_type, base_str_class, dp.qualifiers, dp.loc};

            if (gentle_check_and_consume(TokenType::COMMA)) {
                continue;
            } else {
                break;
            }
        }
        check_and_consume(TokenType::SEMICOLON);
    }

    // Build ParamDecl nodes in identifier-list order
    auto *func_ty = dyn_cast<FunctionType>(decl_parser->result_type.get());
    std::vector<QualType> visible_proto_params;
    bool use_visible_prototype = false;
    auto capture_visible_prototype =
        [&](QualType candidate_type) -> bool {
            auto visible_fn =
                desugar_type(candidate_type).as_shared<FunctionType>();
            if (!visible_fn || !visible_fn->has_prototype ||
                visible_fn->is_variadic ||
                visible_fn->parameters.size() != kr_names.size()) {
                return false;
            }
            visible_proto_params = visible_fn->parameters;
            return true;
        };
    use_visible_prototype =
        capture_visible_prototype(visible_prototype_type);
    if (!use_visible_prototype) {
        auto visible_sym =
            collect_->collect_lookup_variable_symbol(decl_parser->name, true);
        if (visible_sym && visible_sym->kind == SymbolKind::FUNCTION) {
            use_visible_prototype =
                capture_visible_prototype(visible_sym->type);
        }
    }
    std::vector<QualType> param_types;
    auto apply_kr_default_promotions = [&](QualType qt) -> QualType {
        auto builtin = qt.as_shared<BuiltinType>();
        if (!builtin) {
            return qt;
        }
        switch (builtin->builtin_kind) {
            case BuiltinTypes::Float:
                return QualType(type_ctx->get_builtin(BuiltinTypes::Double), qt.get_qualifiers());
            default:
                return qt;
        }
    };

    for (size_t param_idx = 0; param_idx < kr_names.size(); ++param_idx) {
        const auto &pname = kr_names[param_idx];
        auto it = declared_params.find(pname);
        std::shared_ptr<CType> param_type;
        StorageClass param_sc = StorageClass::NONE;
        uint8_t param_quals = QUAL_NONE;
        SrcLoc param_loc;

        if (it != declared_params.end()) {
            param_type = it->second.type;
            param_sc = it->second.str_class;
            param_quals = it->second.qualifiers;
            param_loc = it->second.loc;
        } else {
            // Undeclared K&R parameter defaults to int
            param_type = type_ctx->get_builtin(BuiltinTypes::Int);
        }

        auto declared_param_type = QualType(param_type, param_quals);
        if (use_visible_prototype) {
            declared_param_type = visible_proto_params[param_idx];
        } else {
            declared_param_type = apply_kr_default_promotions(declared_param_type);
        }
        std::shared_ptr<Symbol> param_sym = collect_->collect_declare_variable_symbol(
            pname, declared_param_type, param_sc, false, false, param_loc);
        auto new_param_decl_base = collect_->collect_parameter_declaration(declared_param_type, pname, param_sym, param_sc, param_loc);
        func_decl->parameters.push_back(std::move(new_param_decl_base));
        param_types.push_back(declared_param_type);
    }

    // Keep classic K&R behavior for standalone old-style definitions, but if a
    // visible prototype already exists, honor that signature for this
    // definition's callable type to avoid caller/callee ABI mismatches.
    if (func_ty) {
        func_ty->parameters = std::move(param_types);
        func_ty->parameter_pack_flags.clear();
        func_ty->normalize_parameter_pack_flags();
        func_ty->has_prototype = use_visible_prototype;
    }
}

std::unique_ptr<Decl> Parser::parse_translation_unit() {
    Token begin_tok = current_token();
    collect_->collect_start_translation_unit();

    // Register __builtin_va_list as a built-in typedef using target-specific type
    auto va_list_type = type_ctx->target->get_va_list_type(*type_ctx);
    collect_->collect_declare_typedef_symbol("__builtin_va_list", QualType(va_list_type), begin_tok.loc);

    std::vector<std::unique_ptr<Decl>> declarations;
    size_t last_recovery_idx = std::numeric_limits<size_t>::max();
    while (!gentle_check(TokenType::Eof)) {
        try {
            if (gentle_check(TokenType::ASM_KW)) {
                SrcLoc asm_loc = current_token().loc;
                advance(); // consume asm/__asm__/__asm
                // File-scope asm: no qualifiers permitted
                check_and_consume(TokenType::LEFT_PAREN);
                std::string asm_str = parse_asm_string_literal();
                check_and_consume(TokenType::RIGHT_PAREN);
                check_and_consume(TokenType::SEMICOLON);
                declarations.push_back(collect_->collect_file_scope_asm_declaration(
                    std::move(asm_str), asm_loc));
                diag_engine->sync_point_reached();
                last_recovery_idx = std::numeric_limits<size_t>::max();
                continue;
            }
            auto declars = parse_declaration();
            if (declars.empty()) {
                error("While parsing translation unit, we "
                    "encountered a non-declaration, or we had an error parsing declaration");
                continue; // unreachable — error() throws, but keeps the loop safe
            }
            diag_engine->sync_point_reached();
            last_recovery_idx = std::numeric_limits<size_t>::max();
            declarations.insert(declarations.end(), std::make_move_iterator(declars.begin()),
                std::make_move_iterator(declars.end()));
        } catch (ParseError& e) {
            if (is_in_tentative_context()) {
                throw;
            }
            reset_top_level_state();
            size_t recover_start_idx = get_token_idx();
            skip_to_next_top_level_decl();
            if (get_token_idx() == recover_start_idx &&
                recover_start_idx == last_recovery_idx &&
                !gentle_check(TokenType::Eof)) {
                advance();
            }
            last_recovery_idx = get_token_idx();
            diag_engine->sync_point_reached();
            declarations.push_back(collect_->collect_error_declaration(e.message, e.location));
        }
    }
    return collect_->collect_finish_translation_unit(std::move(declarations), begin_tok.loc);
}
// todo: is this better suited to belong in collect?
