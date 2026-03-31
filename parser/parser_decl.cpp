#include "parser.h"
#include "../helpers/auto_type_utils.h"
#include "../helpers/qualified_name_utils.h"

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

std::unique_ptr<Decl> Parser::parse_function(DeclarationParser * decl_parser,
                                             SrcLoc loc,
                                             std::shared_ptr<Symbol> predecl_sym) {

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
        !cxx_record_parse_stack_.empty() &&
        cxx_record_parse_stack_.back().kind != CppRecordKind::Union;
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

    auto fin_funcdecl = collect_->collect_function_declaration(
        decl_parser->name,
        decl_parser->result_type,
        decl_parser->str_class,
        decl_parser->is_inline,
        decl_parser->asm_label,
        loc,
        current_decl_language_linkage());
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
            for (const auto& param_type : fn_type->parameters) {
                auto param_decl = collect_->collect_parameter_declaration(
                    param_type,
                    "",
                    nullptr,
                    StorageClass::NONE,
                    loc);
                decl->parameters.push_back(std::move(param_decl));
            }
        };
    if (predecl_sym &&
        predecl_sym->kind == SymbolKind::FUNCTION &&
        decl_parser->is_inline) {
        fin_funcdecl->has_prior_non_inline_declaration =
            predecl_sym->had_non_inline_declaration != 0;
    }
    if (auto fin_fn_type = dyn_cast_shared<FunctionType>(fin_funcdecl->type)) {
        bool has_cxx_auto_param = false;
        bool has_gnu_auto_param = false;
        size_t user_param_count = fin_fn_type->parameters.size();
        for (const auto& param_type : fin_fn_type->parameters) {
            has_cxx_auto_param |=
                auto_type_utils::has_cxx_auto_type(param_type.get_shared());
            has_gnu_auto_param |=
                auto_type_utils::has_gnu_auto_type(param_type.get_shared());
        }
        if (has_cxx_auto_param) {
            fail_cpp_unsupported("auto in function parameter declarations", loc);
        }
        if (has_gnu_auto_param) {
            error("'__auto_type' is not allowed in function parameter declarations");
        }
        if (auto_type_utils::has_gnu_auto_type(fin_fn_type->ret_type.get_shared())) {
            error("'__auto_type' is not allowed in function return types");
        }
        if (decl_parser->is_conversion_function && user_param_count != 0) {
            error_custloc(
                "conversion function cannot have parameters",
                loc);
        }
    }
    if (predecl_sym && predecl_sym->kind == SymbolKind::FUNCTION) {
        // Keep predecl symbols structurally tied to the current function type
        // so recursive calls observe deduced return-type updates.
        if (!in_class_member_context) {
            predecl_sym->type = QualType(fin_funcdecl->type);
        }
    }
    if (is_cxx_mode_active()) {
        auto current_scope = collect_->collect_current_scope();
        auto qualifier_prefix =
            qualified_name_utils::namespace_prefix_from_scope(current_scope);
        if (qualifier_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                fin_funcdecl.get(), std::move(*qualifier_prefix));
        }
    }
    fin_funcdecl->explicit_specialization_arguments =
        decl_parser->explicit_specialization_arguments;
    fin_funcdecl->has_explicit_specialization_argument_list =
        decl_parser->has_explicit_specialization_argument_list;

    auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
    auto new_scope = entered_scope.scope;
    if (decl_parser->is_kr_style) {
        // K&R old-style function definition: parse declaration-list between ) and {
        parse_kr_declaration_list(decl_parser, fin_funcdecl.get());
    } else {
        bool seenVoid = false;
        for (auto &i: decl_parser->func_args) {
            retain_type_specifier_decl_if_needed(*i);
            if (i->is_constexpr) {
                error("'constexpr' is not valid for function parameter declarations");
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
                        i->name, param_type, i->str_class, false, i->begin_loc);
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
    register_function_default_arguments(predecl_sym, fin_funcdecl.get(), loc);
    // Parse attributes after function declarator, before body
    auto func_trailing_attrs = try_parse_attributes();
    ast_ctx->append_attrs(fin_funcdecl->node_id, std::move(func_trailing_attrs));

    // check to see if already in scope, and if so check to see if types are compatible
    std::unique_ptr<Stmt> compound_stmt = nullptr;

    if (gentle_check(TokenType::SEMICOLON) || gentle_check(TokenType::COMMA)) {
        // it's a prototype declaration — don't consume ';' or ','
        // so the caller's multi-declarator loop can handle them uniformly
        synthesize_parameter_decls_from_function_type(fin_funcdecl.get());
        collect_->collect_leave_scope();
        fin_funcdecl->body = nullptr;
        return std::move(fin_funcdecl);
    }
    auto prev_func_type = func_type;
    auto prev_decl_language_linkage = current_language_linkage_;
    func_type = fin_funcdecl->type;
    Collect::CppThisContext cpp_this_context;
    if (is_cxx_mode_active() &&
        !cxx_record_parse_stack_.empty() &&
        cxx_record_parse_stack_.back().kind != CppRecordKind::Union &&
        !cxx_record_parse_stack_.back().name.empty()) {
        cpp_this_context.is_member_function = true;
        cpp_this_context.is_static_member_function =
            fin_funcdecl->storage_class == StorageClass::STATIC;
        if (!cpp_this_context.is_static_member_function) {
            if (predecl_original_type) {
                auto predecl_fn_type =
                    desugar_type(predecl_original_type).as_shared<FunctionType>();
                if (predecl_fn_type && !predecl_fn_type->parameters.empty()) {
                    cpp_this_context.this_type = predecl_fn_type->parameters.front();
                }
            }
            if (!cpp_this_context.this_type) {
                auto owner_type_raw = collect_->collect_lookup_tag_type(
                    cxx_record_parse_stack_.back().name, true);
                auto owner_type = dyn_cast_shared<ObjectType>(owner_type_raw);
                if (owner_type) {
                    cpp_this_context.this_type =
                        QualType(std::make_shared<PointerType>(QualType(owner_type)));
                }
            }
        }
    }
    collect_->collect_start_function_definition(
        fin_funcdecl->name, QualType(fin_funcdecl->type), cpp_this_context);
    current_language_linkage_ = LanguageLinkage::None;
    try {
        if (gentle_check(TokenType::LEFT_BRACE)) {
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

void Parser::parse_kr_declaration_list(DeclarationParser *decl_parser, FuncDecl *func_decl) {
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
    if (auto visible_sym = collect_->collect_lookup_variable_symbol(decl_parser->name, true)) {
        if (visible_sym->kind == SymbolKind::FUNCTION) {
            auto visible_fn = visible_sym->type.as_shared<FunctionType>();
            if (visible_fn && visible_fn->has_prototype && !visible_fn->is_variadic &&
                visible_fn->parameters.size() == kr_names.size()) {
                visible_proto_params = visible_fn->parameters;
                use_visible_prototype = true;
            }
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
            pname, declared_param_type, param_sc, false, param_loc);
        auto new_param_decl_base = collect_->collect_parameter_declaration(declared_param_type, pname, param_sym, param_sc, param_loc);
        func_decl->parameters.push_back(std::move(new_param_decl_base));
        param_types.push_back(declared_param_type);
    }

    // Keep classic K&R behavior for standalone old-style definitions, but if a
    // visible prototype already exists, honor that signature for this
    // definition's callable type to avoid caller/callee ABI mismatches.
    if (func_ty) {
        func_ty->parameters = std::move(param_types);
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
