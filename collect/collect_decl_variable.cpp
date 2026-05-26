#include "collect.h"
#include "collect_decl_internal.h"

#include "../ast/special_members.h"

using namespace collect_decl_internal;

namespace {

bool should_defer_template_dependent_initializer_semantics(
    const Collect& collect,
    QualType target_type,
    const Expr* init) {
    if (!init) {
        return false;
    }
    return collect.expression_depends_on_template_parameters(init) ||
           type_depends_on_template_parameters(target_type);
}

bool any_initializer_argument_depends_on_template_parameters(
    const Collect& collect,
    const std::vector<std::unique_ptr<Expr>>& init_args) {
    for (const auto& arg : init_args) {
        if (arg && collect.expression_depends_on_template_parameters(arg.get())) {
            return true;
        }
    }
    return false;
}

const Expr* extract_first_value_init_list(const Expr* init) {
    if (!init) {
        return nullptr;
    }
    auto* init_list = dyn_cast<InitListExpr>(init);
    if (!init_list) {
        return init;
    }
    if (init_list->elements.size() != 1) {
        return nullptr;
    }
    const auto& element = init_list->elements.front();
    if (!element.designators.empty()) {
        return nullptr;
    }
    return element.value.get();
}

bool should_use_implicit_special_member_constructor_overload(
    QualType target_type,
    const RecordSemanticState* record_state,
    const Expr* init,
    const ASTContext* ast_ctx) {
    if (!target_type || !record_state || !init) {
        return false;
    }
    if (!record_state->definition_data.has_copy_constructor &&
        !record_state->definition_data.has_move_constructor) {
        return false;
    }

    const Expr* source_expr =
        extract_first_value_init_list(init);
    if (!source_expr) {
        return false;
    }
    QualType source_type = const_cast<Expr*>(source_expr)->get_type();
    if (!source_type) {
        return false;
    }

    QualType canonical_target =
        collect_internal::remove_reference_and_desugar(target_type, ast_ctx);
    QualType canonical_source =
        collect_internal::remove_reference_and_desugar(source_type, ast_ctx);
    return canonical_target &&
           canonical_source &&
           canonical_target->kind == TypeKind::Object &&
           canonical_source->kind == TypeKind::Object &&
           (canonical_source.equals_unqualified(canonical_target) ||
            types_equivalent_after_template_argument_canonicalization(
                source_type,
                target_type,
                ast_ctx,
                /*ignore_top_level_qualifiers=*/true));
}

bool is_same_type_object_prvalue_initializer(
    const Collect& collect,
    QualType target_type,
    const Expr* init,
    const ASTContext* ast_ctx) {
    if (!target_type || !init) {
        return false;
    }
    if (const auto* init_list = dyn_cast<InitListExpr>(init);
        init_list && init_list->elements.empty()) {
        return false;
    }
    QualType source_type = const_cast<Expr*>(init)->get_type();
    if (!source_type) {
        return false;
    }

    QualType canonical_target =
        collect_internal::remove_reference_and_desugar(target_type, ast_ctx);
    QualType canonical_source =
        collect_internal::remove_reference_and_desugar(source_type, ast_ctx);
    if (!canonical_target ||
        !canonical_source ||
        canonical_target->kind != TypeKind::Object ||
        canonical_source->kind != TypeKind::Object) {
        return false;
    }

    bool same_object_type =
        canonical_source.equals_unqualified(canonical_target) ||
        types_equivalent_after_template_argument_canonicalization(
            source_type,
            target_type,
            ast_ctx,
            /*ignore_top_level_qualifiers=*/true);
    if (!same_object_type) {
        return false;
    }

    return collect.classify_value_category(const_cast<Expr*>(init)) ==
           Collect::ValueCategory::PRValue;
}

bool empty_class_initialization_needs_default_constructor_overload(
    const RecordSemanticState* record_state,
    const Expr* init,
    bool aggregate_initialization_candidate) {
    const auto* init_list = dyn_cast<InitListExpr>(init);
    if (!record_state || !init_list || !init_list->elements.empty()) {
        return false;
    }

    for (const auto& ctor : record_state->constructors) {
        if (!ctor.decl) {
            continue;
        }
        if (!cpp_constructor_is_viable_default_candidate(
                ctor,
                /*allow_protected_access=*/false)) {
            continue;
        }
        if (!aggregate_initialization_candidate) {
            return true;
        }
        return ctor.symbol &&
               (ctor.decl->has_deferred_defaulted_body ||
                !ctor.decl->ctor_initializers.empty());
    }

    return false;
}

} // namespace
/*
 * Does this variable have "bearing" or is it a simple visibility statment (like for extern)
 */
bool Collect::is_definition_bearing_variable_declaration(
    StorageClass storage_class,
    const VariableDeclFlags& flags,
    const Expr* init) const {
    if (flags.is_cpp_static_data_member) {
        if (flags.is_file_scope) {
            if (init) {
                return true;
            }
            return storage_class != StorageClass::EXTERN;
        }
        return flags.is_inline || init != nullptr;
    }

    if (init) {
        return true;
    }

    if (storage_class == StorageClass::EXTERN) {
        return false;
    }

    if (flags.is_file_scope) {
        return true;
    }

    return storage_class != StorageClass::EXTERN;
}

bool Collect::is_inline_equivalent_variable_definition(
    StorageClass storage_class,
    const VariableDeclFlags& flags,
    const Expr* init) const {
    if (!is_definition_bearing_variable_declaration(storage_class, flags, init)) {
        return false;
    }
    if (flags.is_inline) {
        return true;
    }
    return flags.is_cpp_static_data_member && flags.is_constexpr && init != nullptr;
}

Collect::ArrayBoundResult Collect::collect_array_bound_expression(std::unique_ptr<Expr> expr) const {

    ArrayBoundResult result{};
    if (!expr) {
        return result;
    }

    expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
    if (!expr) {
        return result;
    }

    auto bound_eval_mode = lang_opts_.is_cxx_mode()
        ? ConstEvalMode::cpp_core_constant_expression()
        : ConstEvalMode::c_ice();
    auto eval_result = try_evaluate_with_consteval_compat(
        expr.get(), bound_eval_mode);
    if (eval_result.has_value() && *eval_result >= 0) {
        result.constant_size = static_cast<size_t>(*eval_result);
        return result;
    }
    auto float_cast_eval = try_evaluate_float_cast_array_bound(expr.get());
    if (float_cast_eval.has_value() && *float_cast_eval >= 0) {
        result.constant_size = static_cast<size_t>(*float_cast_eval);
        return result;
    }

    result.variable_size_expr = std::shared_ptr<Expr>(expr.release());
    return result;
}


std::unique_ptr<Decl> Collect::collect_static_assert_declaration(
    std::unique_ptr<Expr> condition,
    std::string message,
    bool has_message,
    SrcLoc loc,
    bool defer_in_template_definition) const {

    if (!condition) {
        report_error("static assertion requires a constant expression", loc);
        return collect_make<NopDecl>(loc);
    }
    const bool defer_cpp_template_definition_assert =
        lang_opts_.is_cxx_mode() && defer_in_template_definition;
    if (current_constexpr_if_branch_state() !=
        CppConstexprIfBranchState::Active) {
        return collect_make<StaticAssertDecl>(
            std::move(condition), std::move(message), has_message, loc);
    }
    if (expression_is_value_dependent_for_constant_evaluation(
            condition.get(),
            defer_in_template_definition)) {
        return collect_make<StaticAssertDecl>(
            std::move(condition), std::move(message), has_message, loc);
    }
    condition = collect_apply_standard_conversions(std::move(condition), ExprUseContext::RValue);
    auto mode = lang_opts_.is_cxx_mode()
        ? ConstEvalMode::cpp_core_constant_expression()
        : ConstEvalMode::c_ice();
    auto val = try_evaluate_constant_expression_demand(
        condition.get(),
        mode,
        loc);
    if (!val.has_value()) {
        report_error(lang_opts_.is_cxx_mode()
                         ? "static assertion expression is not a constant expression"
                         : "static assertion expression is not an integer constant expression",
                     loc);
        return collect_make<NopDecl>(loc);
    }
    if (*val == 0) {
        if (defer_cpp_template_definition_assert) {
            return collect_make<StaticAssertDecl>(
                std::move(condition), std::move(message), has_message, loc);
        }
        std::string text = "static assertion failed";
        if (has_message && !message.empty()) {
            text += ": " + message;
        }
        report_error(text, loc);
    }
    if (defer_cpp_template_definition_assert) {
        return collect_make<StaticAssertDecl>(
            std::move(condition), std::move(message), has_message, loc);
    }
    // Static assertions are compile-time only and should not reach codegen.
    return collect_make<NopDecl>(loc);
}


std::unique_ptr<Decl> Collect::collect_variable_declaration(QualType declared_type, const std::string& name,
    std::unique_ptr<Expr> init, std::shared_ptr<Symbol> sym, StorageClass storage_class,
    const VariableDeclFlags& flags, SrcLoc loc, LanguageLinkage language_linkage) {

    bool is_constexpr = flags.is_constexpr;
    bool is_inline = flags.is_inline;
    bool is_file_scope = flags.is_file_scope;
    bool is_cpp_static_data_member = flags.is_cpp_static_data_member;
    bool allow_constexpr_redeclaration_without_initializer =
        flags.allow_constexpr_redeclaration_without_initializer;
    bool is_thread_local = flags.is_thread_local;
    bool is_block_byref = flags.is_block_byref;
    bool is_copy_initialization =
        variable_initialization_is_copy(flags.initialization_kind);
    bool allow_abstract_object_type_instantiation = flags.allow_abstract_object_type_instantiation;
    bool caller_tracks_symbol_definition = flags.caller_tracks_symbol_definition;

    if (declared_type &&
        !is_class_template_placeholder_type(declared_type) &&
        contains_deferred_semantic_type(declared_type.get_shared())) {
        declared_type = resolve_typeof_types(declared_type, loc);
    }
    if (is_constexpr && declared_type) {
        declared_type = declared_type.with_const();
    }
    QualType written_declared_type = declared_type;
    if (is_constexpr && storage_class == StorageClass::EXTERN) {
        report_error("'constexpr' cannot be combined with 'extern'", loc);
    }
    if (is_constexpr && storage_class == StorageClass::AUTO) {
        report_error("'constexpr' cannot be combined with 'auto'", loc);
    }

    if (auto placeholder = get_class_template_placeholder_type(declared_type)) {
        auto* primary_class_template =
            dyn_cast<ClassTemplateDecl>(
                const_cast<Decl*>(placeholder->primary_template));
        if (const auto* canonical_template =
                get_template_decl_canonical_decl(primary_class_template)) {
            primary_class_template =
                dyn_cast<ClassTemplateDecl>(
                    const_cast<TemplateDecl*>(canonical_template));
        }
        if (!primary_class_template) {
            report_error(
                "class template argument deduction requires a class template",
                loc);
        } else if (!init) {
            report_error(
                "declaration of variable '" + name +
                    "' with deduced class template type '" +
                    declared_type.to_string() + "' requires an initializer",
                loc);
        } else {
            std::vector<Expr*> ctad_args;
            bool has_designated_initializer = false;
            if (auto* init_list = dyn_cast<InitListExpr>(init.get())) {
                ctad_args.reserve(init_list->elements.size());
                for (const auto& element : init_list->elements) {
                    if (!element.designators.empty()) {
                        has_designated_initializer = true;
                        break;
                    }
                    ctad_args.push_back(element.value.get());
                }
            } else {
                ctad_args.push_back(init.get());
            }

            if (has_designated_initializer) {
                report_error(
                    "class template argument deduction does not support designated initializers",
                    loc);
            } else {
                bool deduction_is_dependent =
                    type_depends_on_template_parameters(
                        declared_type,
                        ast_ctx_.get());
                for (Expr* arg : ctad_args) {
                    if (arg &&
                        (expression_depends_on_template_parameters(arg) ||
                         type_depends_on_template_parameters(
                             arg->get_type(),
                             ast_ctx_.get()))) {
                        deduction_is_dependent = true;
                        break;
                    }
                }
                if (deduction_is_dependent) {
                    if (auto* init_list = dyn_cast<InitListExpr>(init.get())) {
                        init_list->type = declared_type;
                    }
                } else {
                    QualType deduced_type;
                    bool is_list_initialization = false;
                    if (auto* init_list = dyn_cast<InitListExpr>(init.get())) {
                        is_list_initialization = !init_list->is_paren_init;
                    }
                    if (resolve_class_template_argument_deduction(
                            primary_class_template,
                            ctad_args,
                            is_list_initialization,
                            is_copy_initialization,
                            loc,
                            deduced_type) &&
                        deduced_type) {
                        declared_type = deduced_type;
                        if (sym) {
                            sym->type = declared_type;
                        }
                    }
                }
            }
        }
    }

    resolve_auto_variable_type(declared_type, init, sym, name, loc);
    // First reconcile: merge array bounds from a prior forward declaration
    // (e.g., "extern int a[];" followed by "int a[3];") before the initializer
    // is processed.  A second reconcile after initializer analysis (below)
    // propagates bounds deduced from the init-list back to the symbol.
    reconcile_array_declared_type_with_symbol(declared_type, sym);
    validate_variable_declared_type(
        declared_type,
        name,
        init,
        storage_class,
        is_inline,
        is_file_scope,
        is_cpp_static_data_member,
        loc);

    // --- Classify the variable declaration ---
    // These derived flags determine which code paths (constructor selection,
    // destructor binding, initializer processing) apply to this variable.
    VariableInitializationSelection selection;
    auto record_type =
        declared_type
            ? desugar_type(declared_type, ast_ctx_.get()).as_shared<ObjectType>()
            : nullptr;
    const TagDecl* tag_decl = record_type ? record_type->get_decl() : nullptr;
    const ObjectDecl* record_decl =
        (tag_decl && tag_decl->is_record_decl())
            ? static_cast<const ObjectDecl*>(tag_decl)
            : nullptr;
    const RecordSemanticState* record_state =
        record_decl ? record_semantics_cache_lookup(record_decl) : nullptr;

    bool constexpr_default_initialization_allowed =
        is_constexpr &&
        !init &&
        lang_opts_.is_cxx_mode() &&
        cpp_type_is_const_default_constructible(
            declared_type,
            ast_ctx_.get());
    if (is_constexpr && !init &&
        !allow_constexpr_redeclaration_without_initializer &&
        !constexpr_default_initialization_allowed) {
        report_error("constexpr variable requires an initializer", loc);
    }

    struct VarDeclAnalysis {
        bool is_automatic_storage = false;
        bool is_definition_bearing = false;
        bool is_plain_extern_declaration = false;
        bool is_abstract_object_type = false;
        bool may_use_constructor_initialization = false;
        bool should_use_constructor_overload = false;
        bool supports_non_automatic_destructor_cleanup = false;
    } analysis;

    analysis.is_automatic_storage =
        !is_file_scope &&
        storage_class != StorageClass::STATIC &&
        storage_class != StorageClass::EXTERN &&
        !is_thread_local;
    analysis.is_definition_bearing =
        is_definition_bearing_variable_declaration(
            storage_class,
            flags,
            init.get());
    analysis.is_plain_extern_declaration =
        storage_class == StorageClass::EXTERN && !init;
    analysis.is_abstract_object_type =
        lang_opts_.is_cxx_mode() &&
        record_type &&
        canonical_type_kind(declared_type, ast_ctx_.get()) == TypeKind::Object &&
        record_state &&
        record_state->is_abstract;

    if (analysis.is_abstract_object_type &&
        !allow_abstract_object_type_instantiation &&
        !analysis.is_plain_extern_declaration) {
        report_error(
            "cannot instantiate abstract class type '" +
                declared_type.to_string() + "'",
            loc);
    }

    analysis.may_use_constructor_initialization =
        lang_opts_.is_cxx_mode() &&
        record_type &&
        canonical_type_kind(declared_type, ast_ctx_.get()) == TypeKind::Object &&
        analysis.is_definition_bearing &&
        (!analysis.is_abstract_object_type || allow_abstract_object_type_instantiation);
    bool has_constructor_template = false;
    if (record_state) {
        for (const auto& method_template : record_state->method_templates) {
            auto* function_template = method_template.decl;
            if (function_template &&
                isa<CppConstructorDecl>(function_template->function_decl())) {
                has_constructor_template = true;
                break;
            }
        }
    }
    bool defer_initializer_semantics =
        should_defer_template_dependent_initializer_semantics(
            *this,
            declared_type,
            init.get());
    bool same_type_prvalue_initializer =
        is_same_type_object_prvalue_initializer(
            *this,
            declared_type,
            init.get(),
            ast_ctx_.get());
    bool aggregate_initialization_candidate =
        record_type && is_aggregate_type(declared_type.get_shared());
    analysis.should_use_constructor_overload =
        record_state &&
        !defer_initializer_semantics &&
        !same_type_prvalue_initializer &&
        (!record_state->constructors.empty() || has_constructor_template) &&
        (has_constructor_template ||
         record_state->definition_data.has_user_declared_constructor ||
         empty_class_initialization_needs_default_constructor_overload(
             record_state,
             init.get(),
             aggregate_initialization_candidate) ||
         should_use_implicit_special_member_constructor_overload(
             declared_type,
             record_state,
             init.get(),
             ast_ctx_.get()));

    if (is_block_byref) {
        if (!analysis.is_automatic_storage) {
            report_error(
                "'__block' is only supported on automatic local variables",
                loc);
        }
        auto declared_kind = canonical_type_kind(declared_type, ast_ctx_.get());
        if (declared_kind == TypeKind::Array) {
            report_error(
                "C parser unsupported syntax: '__block' array variables",
                loc);
        }
        if (declared_kind == TypeKind::Reference) {
            report_error(
                "C++ parser unsupported syntax: '__block' reference variables",
                loc);
        }
    }

    // --- Constructor selection (C++ only) ---
    if (analysis.may_use_constructor_initialization) {
        if (!init) {
            if (record_state && !record_state->constructors.empty()) {
                std::vector<std::unique_ptr<Expr>> ctor_args;
                selection.used_constructor_initialization = true;
                if (!select_constructor_for_variable_initialization(
                        record_type,
                        std::move(ctor_args),
                        false,
                        false,
                        declared_type,
                        loc,
                        selection)) {
                    init = collect_make<ErrorExpr>("no matching constructor", loc);
                }
            }
        } else if (analysis.should_use_constructor_overload) {
            std::vector<std::unique_ptr<Expr>> ctor_args;
            bool ctor_is_list_init = false;
            selection.used_constructor_initialization = true;
            if (auto* init_list = dyn_cast<InitListExpr>(init.get())) {
                ctor_is_list_init = !init_list->is_paren_init;
                auto owned_list = std::unique_ptr<InitListExpr>(
                    static_cast<InitListExpr*>(init.release()));
                for (auto& elem : owned_list->elements) {
                    if (!elem.designators.empty()) {
                        report_error(
                            "designated initializers are not supported in constructor initialization",
                            elem.loc);
                    }
                    if (!elem.value) {
                        report_error(
                            "missing initializer expression in constructor argument list",
                            elem.loc);
                        continue;
                    }
                    ctor_args.push_back(std::move(elem.value));
                }
            } else {
                ctor_args.push_back(std::move(init));
            }

            if (select_constructor_for_variable_initialization(
                    record_type,
                    std::move(ctor_args),
                    ctor_is_list_init,
                    is_copy_initialization,
                    declared_type,
                    loc,
                    selection)) {
                if (selection.nonconstructor_init_expr) {
                    selection.used_constructor_initialization = false;
                    init = std::move(selection.nonconstructor_init_expr);
                } else {
                    selection.used_constructor_initialization = true;
                    init.reset();
                }
            } else {
                init = collect_make<ErrorExpr>("no matching constructor", loc);
            }
        }
    }

    analysis.supports_non_automatic_destructor_cleanup =
        analysis.is_definition_bearing &&
        !is_thread_local &&
        (is_file_scope || storage_class == StorageClass::STATIC);

    // --- Destructor diagnostics and binding (C++ only) ---
    if (lang_opts_.is_cxx_mode() &&
        record_type &&
        canonical_type_kind(declared_type, ast_ctx_.get()) == TypeKind::Object &&
        !analysis.is_automatic_storage &&
        !analysis.supports_non_automatic_destructor_cleanup &&
        !analysis.is_plain_extern_declaration &&
        record_state &&
        record_state->definition_data.has_user_declared_destructor) {
        if (is_thread_local) {
            report_error(
                "thread-local storage duration for variable '" + name +
                    "' of type '" + declared_type.to_string() +
                    "' with user-declared destructor is not supported yet",
                loc);
        } else {
            report_error(
                "non-automatic storage duration for variable '" + name +
                    "' of type '" + declared_type.to_string() +
                    "' with user-declared destructor is not supported yet",
                loc);
        }
    }

    if (lang_opts_.is_cxx_mode() &&
        record_type &&
        canonical_type_kind(declared_type, ast_ctx_.get()) == TypeKind::Object &&
        (analysis.is_automatic_storage ||
         (analysis.supports_non_automatic_destructor_cleanup &&
          !analysis.is_plain_extern_declaration)) &&
        record_state &&
        !record_state->destructors.empty()) {
        selection.destructor_symbol = select_destructor_for_variable(
            name,
            declared_type,
            record_type,
            loc);
    }

    // --- Initializer processing ---
    if (init && !selection.used_constructor_initialization) {
        declared_type = clone_top_level_incomplete_array(declared_type);
        if (!defer_initializer_semantics) {
            init = process_initializer_for_type(std::move(init), declared_type, loc);
        }
        if (!defer_initializer_semantics &&
            declared_type &&
            canonical_type_kind(declared_type, ast_ctx_.get()) ==
                TypeKind::Array) {
            auto arr_type =
                desugar_type(declared_type, ast_ctx_.get()).as_shared<ArrayType>();
            if (arr_type && arr_type->size_kind == ArraySizeKind::Incomplete) {
                if (auto* init_node = dyn_cast<InitListExpr>(init.get())) {
                    arr_type->size_kind = ArraySizeKind::Constant;
                    if (!init_node->mappings.empty()) {
                        arr_type->size = init_node->mappings.rbegin()->first + 1;
                    } else {
                        arr_type->size = 0;
                    }
                } else if (auto* str_lit = dyn_cast<StringLiteral>(init.get())) {
                    auto str_lit_type = str_lit->ctype.as_shared<ArrayType>();
                    if (str_lit_type) {
                        arr_type->size_kind = ArraySizeKind::Constant;
                        arr_type->size = str_lit_type->size;
                    }
                }
            }
        }
    }

    auto validate_constexpr_initializer = [&](Expr* initializer) {
        if (!is_constexpr || !initializer || defer_initializer_semantics) {
            return;
        }
        std::string constexpr_failure;
        SrcLoc constexpr_failure_loc = loc;
        ConstEvalMode constexpr_mode = lang_opts_.is_cxx_mode()
            ? ConstEvalMode::cpp_core_constant_expression()
            : ConstEvalMode::c23_constexpr_initializer();
        if (!validate_constexpr_initializer_expr(
                *this,
                initializer,
                constexpr_mode,
                constexpr_failure,
                constexpr_failure_loc)) {
            report_error(
                "constexpr initializer is not a constant expression: " + constexpr_failure,
                constexpr_failure_loc);
        }
    };
    validate_constexpr_initializer(init.get());

    // --- Finalize symbol and build declaration node ---
    if (sym) {
        // Second reconcile: propagate array bounds deduced from the initializer
        // (e.g., "int a[] = {1,2,3};" yields size 3) back to the symbol type.
        reconcile_array_declared_type_with_symbol(declared_type, sym);
        sym->type = desugar_type(declared_type, ast_ctx_.get());
        sym->is_constexpr = is_constexpr;
        sym->is_block_byref = is_block_byref;
    }

    auto decl = collect_make<VariableDecl>(declared_type,
        name,
        std::move(init),
        std::move(sym),
        storage_class,
        is_inline,
        loc);
    decl->original_type = written_declared_type;
    if (selection.used_constructor_initialization && selection.constructor_symbol) {
        if (!collect_ensure_defaulted_special_member_body(
                selection.constructor_symbol,
                loc)) {
            report_error(
                "failed to materialize defaulted constructor '" +
                    selection.constructor_symbol->name + "'",
                loc);
        } else if (selection.constructor_symbol->is_deleted) {
            report_error(
                "call to deleted constructor '" +
                    selection.constructor_symbol->name + "'",
                loc);
        }
        decl->init = collect_make<CppConstructExpr>(
            selection.constructor_symbol,
            std::move(selection.constructor_args),
            declared_type,
            selection.constructor_is_list_init,
            loc);
    }
    if (selection.used_constructor_initialization) {
        validate_constexpr_initializer(decl->init.get());
    }
    if (selection.destructor_symbol && ast_ctx_) {
        ast_ctx_->set_cpp_variable_destructor_symbol(
            decl->node_id,
            selection.destructor_symbol);
    }
    decl->is_constexpr = is_constexpr;
    decl->is_thread_local = is_thread_local;
    decl->is_block_byref = is_block_byref;
    decl->initialization_kind = flags.initialization_kind;
    decl->set_language_linkage(language_linkage);
    if (decl->sym && !caller_tracks_symbol_definition) {
        bool has_owner_record =
            static_cast<bool>(get_symbol_owner_record_type(decl->sym.get()));
        bool is_definition_bearing =
            is_definition_bearing_variable_declaration(
                storage_class,
                flags,
                decl->init.get());
        if (is_definition_bearing &&
            lang_opts_.is_cxx_mode() &&
            is_file_scope &&
            !has_owner_record &&
            decl->sym->variable_definition &&
            decl->sym->variable_definition != decl.get()) {
            report_error("redefinition of '" + name + "'", loc);
        }
        if (is_definition_bearing) {
            if (!has_owner_record) {
                decl->sym->is_defined = true;
            }
            decl->sym->variable_definition = decl.get();
        }
    }
    return decl;
}

std::unique_ptr<Expr> Collect::collect_member_initializer_expression(
    std::unique_ptr<Expr> init,
    QualType member_type,
    SrcLoc loc) {
    if (isa<InitListExpr>(init.get()) &&
        should_defer_template_dependent_initializer_semantics(
            *this, member_type, init.get())) {
        return init;
    }
    return process_initializer_for_type(std::move(init), member_type, loc);
}

std::unique_ptr<Expr> Collect::collect_class_object_initializer_expression(
    std::vector<std::unique_ptr<Expr>> init_args,
    QualType object_type,
    bool is_list_init,
    bool is_copy_initialization,
    SrcLoc loc,
    bool allow_abstract_object_type_instantiation,
    const Expr* original_init_for_classification) {
    if (!object_type) {
        report_error("class object initializer has invalid target type", loc);
        return collect_make<ErrorExpr>("invalid class object initializer", loc);
    }

    auto make_deferred_init_list =
        [&](std::vector<std::unique_ptr<Expr>> args) {
            auto init_list = collect_make<InitListExpr>(loc);
            init_list->is_paren_init = !is_list_init;
            init_list->elements.reserve(args.size());
            for (auto& arg : args) {
                InitElement elem;
                elem.value = std::move(arg);
                elem.loc = loc;
                init_list->elements.push_back(std::move(elem));
            }
            return init_list;
        };

    bool object_type_is_dependent =
        type_depends_on_template_parameters(object_type, ast_ctx_.get());
    bool has_dependent_argument =
        any_initializer_argument_depends_on_template_parameters(
            *this, init_args);

    if (object_type_is_dependent || has_dependent_argument) {
        return make_deferred_init_list(std::move(init_args));
    }

    auto object_kind = canonical_type_kind(object_type, ast_ctx_.get());
    if (object_kind != TypeKind::Object) {
        report_error("class object initializer requires an object type", loc);
        return collect_make<ErrorExpr>("invalid class object initializer", loc);
    }

    if (!is_list_init &&
        init_args.size() == 1 &&
        original_init_for_classification &&
        is_same_type_object_prvalue_initializer(
            *this,
            object_type,
            original_init_for_classification,
            ast_ctx_.get())) {
        return process_initializer_for_type(
            std::move(init_args.front()),
            object_type,
            loc);
    }

    auto init_list = make_deferred_init_list(std::move(init_args));
    auto record_type =
        desugar_type(object_type, ast_ctx_.get()).as_shared<ObjectType>();
    const TagDecl* tag_decl = record_type ? record_type->get_decl() : nullptr;
    const ObjectDecl* record_decl =
        (tag_decl && tag_decl->is_record_decl())
            ? static_cast<const ObjectDecl*>(tag_decl)
            : nullptr;
    const RecordSemanticState* record_state =
        record_decl ? record_semantics_cache_lookup(record_decl) : nullptr;

    if (record_type &&
        record_state &&
        record_state->is_abstract &&
        !allow_abstract_object_type_instantiation) {
        report_error(
            "cannot instantiate abstract class type '" +
                object_type.to_string() + "'",
            loc);
        return collect_make<ErrorExpr>(
            "cannot instantiate abstract class type", loc);
    }

    bool has_constructor_template = false;
    if (record_state) {
        for (const auto& method_template : record_state->method_templates) {
            auto* function_template = method_template.decl;
            if (function_template &&
                isa<CppConstructorDecl>(function_template->function_decl())) {
                has_constructor_template = true;
                break;
            }
        }
    }

    bool defer_initializer_semantics =
        should_defer_template_dependent_initializer_semantics(
            *this,
            object_type,
            init_list.get());
    bool same_type_prvalue_initializer =
        is_same_type_object_prvalue_initializer(
            *this,
            object_type,
            init_list.get(),
            ast_ctx_.get());
    bool aggregate_initialization_candidate =
        record_type && is_aggregate_type(object_type.get_shared());
    bool should_use_constructor_overload =
        record_state &&
        !defer_initializer_semantics &&
        !same_type_prvalue_initializer &&
        (!record_state->constructors.empty() || has_constructor_template) &&
        (has_constructor_template ||
         record_state->definition_data.has_user_declared_constructor ||
         empty_class_initialization_needs_default_constructor_overload(
             record_state,
             init_list.get(),
             aggregate_initialization_candidate) ||
         should_use_implicit_special_member_constructor_overload(
             object_type,
             record_state,
             init_list.get(),
             ast_ctx_.get()));

    if (defer_initializer_semantics) {
        return init_list;
    }

    if (should_use_constructor_overload) {
        auto owned_list = std::unique_ptr<InitListExpr>(
            static_cast<InitListExpr*>(init_list.release()));
        std::vector<std::unique_ptr<Expr>> ctor_args;
        ctor_args.reserve(owned_list->elements.size());
        for (auto& elem : owned_list->elements) {
            if (!elem.designators.empty()) {
                report_error(
                    "designated initializers are not supported in constructor initialization",
                    elem.loc);
            }
            if (!elem.value) {
                report_error(
                    "missing initializer expression in constructor argument list",
                    elem.loc);
                continue;
            }
            ctor_args.push_back(std::move(elem.value));
        }

        VariableInitializationSelection selection;
        if (!select_constructor_for_variable_initialization(
                record_type,
                std::move(ctor_args),
                is_list_init,
                is_copy_initialization,
                object_type,
                loc,
                selection)) {
            return collect_make<ErrorExpr>("no matching constructor", loc);
        }
        if (selection.nonconstructor_init_expr) {
            return std::move(selection.nonconstructor_init_expr);
        }
        if (!selection.constructor_symbol) {
            return nullptr;
        }
        if (!collect_ensure_defaulted_special_member_body(
                selection.constructor_symbol,
                loc)) {
            report_error(
                "failed to materialize defaulted constructor '" +
                    selection.constructor_symbol->name + "'",
                loc);
            return collect_make<ErrorExpr>(
                "failed to materialize defaulted constructor", loc);
        }
        if (selection.constructor_symbol->is_deleted) {
            report_error(
                "call to deleted constructor '" +
                    selection.constructor_symbol->name + "'",
                loc);
            return collect_make<ErrorExpr>("deleted constructor call", loc);
        }
        return collect_make<CppConstructExpr>(
            selection.constructor_symbol,
            std::move(selection.constructor_args),
            object_type,
            selection.constructor_is_list_init,
            loc);
    }

    return process_initializer_for_type(std::move(init_list), object_type, loc);
}

std::unique_ptr<Expr> Collect::collect_member_initializer_expression(
    std::vector<std::unique_ptr<Expr>> init_args,
    QualType member_type,
    bool is_list_init,
    SrcLoc loc,
    bool allow_abstract_object_type_instantiation,
    bool is_copy_initialization) {
    if (!member_type) {
        report_error("constructor member initializer has invalid member type", loc);
        return collect_make<ErrorExpr>("invalid member type", loc);
    }

    bool member_type_is_dependent =
        type_depends_on_template_parameters(member_type, ast_ctx_.get());

    auto make_deferred_init_list =
        [&](std::vector<std::unique_ptr<Expr>> args) {
            auto init_list = collect_make<InitListExpr>(loc);
            init_list->is_paren_init = !is_list_init;
            init_list->elements.reserve(args.size());
            for (auto& arg : args) {
                InitElement elem;
                elem.value = std::move(arg);
                elem.loc = loc;
                init_list->elements.push_back(std::move(elem));
            }
            return init_list;
        };

    if (member_type_is_dependent) {
        return make_deferred_init_list(std::move(init_args));
    }

    auto member_kind = canonical_type_kind(member_type, ast_ctx_.get());
    if (member_kind != TypeKind::Object) {
        if (init_args.empty()) {
            if (member_kind == TypeKind::Reference) {
                report_error(
                    "reference type cannot be value-initialized",
                    loc);
                return collect_make<ErrorExpr>(
                    "invalid reference value-initialization",
                    loc);
            }
            if (member_kind == TypeKind::Function) {
                report_error(
                    "function type cannot be value-initialized",
                    loc);
                return collect_make<ErrorExpr>(
                    "invalid function value-initialization",
                    loc);
            }
            return collect_cpp_value_init_expression(member_type, loc);
        }
        if (init_args.size() != 1) {
            report_error(
                "constructor member initializer for non-class member requires a single expression",
                loc);
            return collect_make<ErrorExpr>("invalid member initializer", loc);
        }
        return collect_member_initializer_expression(std::move(init_args.front()),
                                                     member_type,
                                                     loc);
    }

    return collect_class_object_initializer_expression(
        std::move(init_args),
        member_type,
        is_list_init,
        is_copy_initialization,
        loc,
        allow_abstract_object_type_instantiation);
}

std::unique_ptr<Expr> Collect::collect_variable_initializer_expression(
    std::unique_ptr<Expr> init,
    QualType variable_type,
    VariableInitializationKind initialization_kind,
    SrcLoc loc,
    bool allow_abstract_object_type_instantiation) {
    if (!init) {
        return nullptr;
    }

    auto effective_kind = initialization_kind;
    if (effective_kind == VariableInitializationKind::None) {
        if (auto* init_list = dyn_cast<InitListExpr>(init.get())) {
            effective_kind = init_list->is_paren_init
                ? VariableInitializationKind::Direct
                : VariableInitializationKind::DirectList;
        }
    }

    bool is_cxx_object =
        lang_opts_.is_cxx_mode() &&
        variable_type &&
        canonical_type_kind(variable_type, ast_ctx_.get()) == TypeKind::Object;
    if (!is_cxx_object) {
        return process_initializer_for_type(std::move(init), variable_type, loc);
    }

    if (auto* init_list = dyn_cast<InitListExpr>(init.get())) {
        bool has_designators = false;
        for (const auto& elem : init_list->elements) {
            if (!elem.designators.empty()) {
                has_designators = true;
                break;
            }
        }
        if (has_designators) {
            return process_initializer_for_type(
                std::move(init),
                variable_type,
                loc);
        }
        bool is_list_init =
            effective_kind == VariableInitializationKind::None
                ? !init_list->is_paren_init
                : variable_initialization_is_list(effective_kind);
        bool is_copy_initialization =
            variable_initialization_is_copy(effective_kind);
        const Expr* original_init = init.get();
        auto owned_list = std::unique_ptr<InitListExpr>(
            static_cast<InitListExpr*>(init.release()));
        std::vector<std::unique_ptr<Expr>> init_args;
        init_args.reserve(owned_list->elements.size());
        for (auto& elem : owned_list->elements) {
            if (!elem.value) {
                report_error(
                    "missing initializer expression in variable initializer",
                    elem.loc);
                continue;
            }
            init_args.push_back(std::move(elem.value));
        }
        return collect_class_object_initializer_expression(
            std::move(init_args),
            variable_type,
            is_list_init,
            is_copy_initialization,
            loc,
            allow_abstract_object_type_instantiation,
            original_init);
    }

    const Expr* original_init = init.get();
    std::vector<std::unique_ptr<Expr>> init_args;
    init_args.push_back(std::move(init));
    return collect_class_object_initializer_expression(
        std::move(init_args),
        variable_type,
        /*is_list_init=*/false,
        variable_initialization_is_copy(effective_kind),
        loc,
        allow_abstract_object_type_instantiation,
        original_init);
}


std::unique_ptr<Decl> Collect::collect_parameter_declaration(QualType type, const std::string& name, std::shared_ptr<Symbol> sym, StorageClass storage_class, SrcLoc loc) {

    QualType original_type = type;
    if (type) {
        if (contains_deferred_semantic_type(type.get_shared())) {
            type = resolve_typeof_types(type, loc);
            original_type = type;
        }
        type = decay_parameter_type(type);
    }
    if (storage_class != StorageClass::NONE && storage_class != StorageClass::REGISTER) {
        report_error("invalid storage class for function parameter", loc);
    }
    if (type && type->isVoid() && !name.empty()) {
        report_error("parameter '" + name + "' has incomplete type 'void'", loc);
    }
    if (type && type.is_restrict() &&
        canonical_type_kind(type, ast_ctx_.get()) != TypeKind::Pointer &&
        canonical_type_kind(type, ast_ctx_.get()) != TypeKind::Array) {
        report_error("'restrict' qualifier can only be applied to pointer types", loc);
    }
    if (sym) {
        sym->type = desugar_type(type, ast_ctx_.get());
    }
    auto decl = collect_make<ParamDecl>(type, name, std::move(sym), storage_class, loc);
    decl->original_type = original_type.get_shared();
    return decl;
}
