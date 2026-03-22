#include "collect.h"
#include "collect_internal.h"
#include "../helpers/auto_type_utils.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"

using namespace collect_internal;

namespace {
void append_unique_function_candidate(
    std::vector<std::shared_ptr<Symbol>>& candidates,
    const std::shared_ptr<Symbol>& candidate) {
    if (!candidate || candidate->kind != SymbolKind::FUNCTION) {
        return;
    }
    for (const auto& existing : candidates) {
        if (existing == candidate) {
            return;
        }
    }
    candidates.push_back(candidate);
}

void append_unique_function_template_candidate(
    std::vector<const FunctionTemplateDecl*>& candidates,
    const Decl* decl) {
    auto* function_template = dyn_cast<FunctionTemplateDecl>(decl);
    if (!function_template) {
        return;
    }
    for (const auto* existing : candidates) {
        if (existing == function_template) {
            return;
        }
    }
    candidates.push_back(function_template);
}

std::vector<const FunctionTemplateDecl*> lookup_unqualified_function_templates(
    std::string_view callee_name,
    const std::shared_ptr<Scope>& current_scope) {
    std::vector<const FunctionTemplateDecl*> template_candidates;
    if (!current_scope) {
        return template_candidates;
    }

    const DeclBinding* template_binding =
        LookupEngine::lookup_unqualified_template_binding(
            std::string(callee_name),
            current_scope,
            true,
            LookupNamespace::Ordinary);
    if (!template_binding) {
        return template_candidates;
    }

    append_unique_function_template_candidate(
        template_candidates,
        template_binding->template_decl);
    for (const auto* decl : template_binding->template_overload_candidates) {
        append_unique_function_template_candidate(template_candidates, decl);
    }
    return template_candidates;
}

std::vector<std::shared_ptr<Symbol>> lookup_qualified_function_candidates(
    std::string_view callee_name,
    const CppQualifiedExprInfo& qualified_info,
    const DeclContext* current_decl_context) {
    std::vector<std::shared_ptr<Symbol>> function_candidates;
    if (!current_decl_context) {
        return function_candidates;
    }

    LookupEngine::QualifiedNameSpec name_spec;
    name_spec.has_global_qualifier = qualified_info.has_global_qualifier;
    name_spec.qualifiers = qualified_info.qualifiers;
    name_spec.terminal_name = std::string(callee_name);
    auto qualified_lookup = LookupEngine::lookup_qualified_name(
        name_spec,
        current_decl_context,
        LookupNamespace::Ordinary);
    const DeclBinding* binding =
        qualified_lookup.status == LookupEngine::QualifiedLookupStatus::Found
            ? qualified_lookup.binding
            : nullptr;
    if (!binding) {
        return function_candidates;
    }

    append_unique_function_candidate(function_candidates, binding->symbol);
    for (const auto& candidate : binding->overload_candidates) {
        append_unique_function_candidate(function_candidates, candidate);
    }
    return function_candidates;
}

std::string format_explicit_template_callee_name(
    const CppQualifiedExprInfo* qualified_info,
    std::string_view terminal_name) {
    std::string name;
    if (qualified_info && qualified_info->has_global_qualifier) {
        name += "::";
    }
    if (qualified_info) {
        for (const auto& qualifier : qualified_info->qualifiers) {
            name += qualifier;
            name += "::";
        }
    }
    name += terminal_name;
    return name;
}

std::vector<const FunctionTemplateDecl*> lookup_qualified_function_templates(
    std::string_view callee_name,
    const CppQualifiedExprInfo& qualified_info,
    const DeclContext* current_decl_context) {
    std::vector<const FunctionTemplateDecl*> template_candidates;
    if (!current_decl_context) {
        return template_candidates;
    }

    LookupEngine::QualifiedNameSpec name_spec;
    name_spec.has_global_qualifier = qualified_info.has_global_qualifier;
    name_spec.qualifiers = qualified_info.qualifiers;
    name_spec.terminal_name = std::string(callee_name);
    auto qualified_lookup = LookupEngine::lookup_qualified_name(
        name_spec,
        current_decl_context,
        LookupNamespace::Ordinary);
    const DeclBinding* template_binding =
        qualified_lookup.status == LookupEngine::QualifiedLookupStatus::Found
            ? qualified_lookup.binding
            : nullptr;
    if (!template_binding) {
        return template_candidates;
    }

    append_unique_function_template_candidate(
        template_candidates,
        template_binding->template_decl);
    for (const auto* decl : template_binding->template_overload_candidates) {
        append_unique_function_template_candidate(template_candidates, decl);
    }
    return template_candidates;
}

} // namespace

std::unique_ptr<Expr>
Collect::complete_selected_function_template_specialization_symbol(
    std::shared_ptr<Symbol>& selected_symbol,
    SrcLoc loc,
    std::string_view failure_message) const {
    if (!selected_symbol) {
        return nullptr;
    }
    const auto* specialization_info =
        get_symbol_function_template_specialization(selected_symbol.get());
    if (!specialization_info || !specialization_info->primary_template) {
        return nullptr;
    }

    std::shared_ptr<Symbol> completed_symbol = nullptr;
    auto* completed_decl = instantiate_function_template_specialization(
        specialization_info->primary_template,
        specialization_info->arguments,
        loc,
        &completed_symbol,
        /*instantiate_definition=*/true);
    if (!completed_decl || !completed_symbol) {
        return collect_make<ErrorExpr>(std::string(failure_message), loc);
    }
    selected_symbol = std::move(completed_symbol);
    return nullptr;
}

std::unique_ptr<Expr> Collect::resolve_overloaded_function_call(
    FuncCall* call,
    VarRef* callee_ref,
    SrcLoc loc) const {

    if (!call || !callee_ref || !lang_opts_.is_cxx_mode() || !current_scope_) {
        return nullptr;
    }

    const auto* qualified_info = callee_ref->get_cpp_qualified_info();
    if (qualified_info && qualified_info->is_type_qualified) {
        auto qualified_owner_analysis =
            analyze_cpp_qualified_expr_owner(qualified_info, ast_ctx_.get());
        auto qualified_owner_type = qualified_owner_analysis.qualifier_record_type;
        const ObjectDecl* owner_record_decl =
            qualified_owner_analysis.qualifier_record_decl;
        if (!qualified_owner_type || !owner_record_decl) {
            return nullptr;
        }

        const std::string& callee_name = callee_ref->get_name();
        std::string display_name =
            format_explicit_template_callee_name(qualified_info, callee_name);
        const ObjectDecl* access_context_decl = nullptr;
        if (func_state_.current_function_is_cpp_member) {
            access_context_decl =
                current_record_decl_from_this_type(func_state_.current_function_cpp_this_type);
        }

        std::vector<OverloadCallCandidate> overload_candidates;
        bool saw_private_member = false;
        bool saw_protected_member = false;
        for (const auto& method_match :
             find_record_methods(qualified_owner_type.get(), callee_name)) {
            const auto* method = method_match.method;
            if (!method || !method->is_static || !method->symbol) {
                continue;
            }
            if (method->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_match.owner_record_decl,
                        access_context_decl)) {
                    saw_private_member = true;
                    continue;
                }
            }
            if (method->declared_access == RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_match.owner_record_decl,
                    access_context_decl,
                    owner_record_decl,
                    true);
                if (!protected_ok) {
                    saw_protected_member = true;
                    continue;
                }
            }

            OverloadCallCandidate call_candidate;
            call_candidate.symbol = method->symbol;
            call_candidate.implicit_object_arg_kind =
                OverloadImplicitObjectArgKind::None;
            overload_candidates.push_back(std::move(call_candidate));
        }

        bool saw_template_instantiation = false;
        for (const auto& method_template_match :
             find_record_method_templates(qualified_owner_type.get(), callee_name)) {
            const auto* method_template = method_template_match.method_template;
            const auto* function_template =
                method_template ? method_template->decl : nullptr;
            if (!method_template || !function_template || !method_template->is_static) {
                continue;
            }
            if (method_template->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_template_match.owner_record_decl,
                        access_context_decl)) {
                    saw_private_member = true;
                    continue;
                }
            }
            if (method_template->declared_access == RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_template_match.owner_record_decl,
                    access_context_decl,
                    owner_record_decl,
                    true);
                if (!protected_ok) {
                    saw_protected_member = true;
                    continue;
                }
            }

            std::vector<TemplateArgument> deduced_arguments;
            if (!deduce_function_template_call_arguments(
                    function_template,
                    call->args,
                    deduced_arguments)) {
                continue;
            }

            std::shared_ptr<Symbol> specialization_symbol = nullptr;
            auto* specialization_decl =
                instantiate_function_template_specialization(
                    function_template,
                    deduced_arguments,
                    loc,
                    &specialization_symbol,
                    /*instantiate_definition=*/false);
            if (!specialization_decl || !specialization_symbol) {
                continue;
            }
            saw_template_instantiation = true;

            OverloadCallCandidate call_candidate;
            call_candidate.symbol = std::move(specialization_symbol);
            call_candidate.implicit_object_arg_kind =
                OverloadImplicitObjectArgKind::None;
            overload_candidates.push_back(std::move(call_candidate));
        }

        if (overload_candidates.empty()) {
            if (auto inaccessible_error = report_inaccessible_member(
                    callee_name,
                    saw_private_member,
                    saw_protected_member,
                    loc)) {
                return inaccessible_error;
            }
            if (saw_template_instantiation ||
                !find_record_method_templates(
                    qualified_owner_type.get(),
                    callee_name).empty()) {
                report_error(
                    "no matching member function template specialization for '" +
                        display_name + "'",
                    loc);
                return collect_make<ErrorExpr>(
                    "no matching member function template specialization",
                    loc);
            }
            return nullptr;
        }

        std::shared_ptr<Symbol> selected_symbol = nullptr;
        OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
            OverloadImplicitObjectArgKind::None;
        if (auto overload_error = select_overload_candidate(
                display_name,
                overload_candidates,
                call->args,
                nullptr,
                loc,
                selected_symbol,
                selected_implicit_object_arg_kind)) {
            return overload_error;
        }

        (void)selected_implicit_object_arg_kind;
        if (!selected_symbol) {
            return nullptr;
        }
        if (auto completion_error =
                complete_selected_function_template_specialization_symbol(
                    selected_symbol,
                    loc,
                    "failed to instantiate selected member function template specialization")) {
            return completion_error;
        }
        callee_ref->symref = std::move(selected_symbol);
        return nullptr;
    }

    const std::string& callee_name = callee_ref->get_name();
    std::string display_name =
        format_explicit_template_callee_name(qualified_info, callee_name);
    auto current_decl_context = get_current_decl_context();
    auto function_candidates =
        qualified_info
            ? lookup_qualified_function_candidates(
                  callee_name,
                  *qualified_info,
                  current_decl_context.get())
            : LookupEngine::lookup_unqualified_function_candidates(
                  callee_name, current_scope_, true);
    auto template_candidates =
        qualified_info
            ? lookup_qualified_function_templates(
                  callee_name,
                  *qualified_info,
                  current_decl_context.get())
            : lookup_unqualified_function_templates(callee_name, current_scope_);

    QualType named_type = nullptr;
    if (!qualified_info) {
        named_type = collect_lookup_type_name(
            callee_name,
            true,
            true);
    }
    auto named_record_type =
        remove_reference_and_desugar(named_type, ast_ctx_.get())
            .as_shared<ObjectType>();
    const ObjectDecl* named_record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(named_record_type ? named_record_type->get_decl() : nullptr));

    if (named_record_type && named_record_decl && !function_candidates.empty()) {
        std::vector<OverloadCallCandidate> constructor_overload_candidates;
        constructor_overload_candidates.reserve(function_candidates.size());
        for (const auto& candidate : function_candidates) {
            std::shared_ptr<ObjectType> constructor_owner_type = nullptr;
            if (!classify_constructor_symbol_call(
                    candidate, constructor_owner_type, ast_ctx_.get())) {
                continue;
            }
            const ObjectDecl* constructor_owner_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(
                    constructor_owner_type ? constructor_owner_type->get_decl() : nullptr));
            if (!constructor_owner_decl || constructor_owner_decl != named_record_decl) {
                continue;
            }

            OverloadCallCandidate call_candidate;
            call_candidate.symbol = candidate;
            call_candidate.implicit_object_arg_kind = OverloadImplicitObjectArgKind::Regular;
            constructor_overload_candidates.push_back(std::move(call_candidate));
        }

        if (!constructor_overload_candidates.empty()) {
            QualType owner_ptr_type(
                std::make_shared<PointerType>(QualType(named_record_type)));
            auto synthetic_object_symbol = std::make_shared<Symbol>(
                "__aburi_ctor_object",
                SymbolKind::VARIABLE,
                owner_ptr_type,
                StorageClass::NONE,
                VariableLinkage::NONE);
            auto synthetic_object_expr = collect_make<VarRef>(
                synthetic_object_symbol,
                loc);

            std::shared_ptr<Symbol> selected_constructor_symbol = nullptr;
            OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
                OverloadImplicitObjectArgKind::None;
            if (auto constructor_overload_error = resolve_overloaded_call_candidates(
                    callee_name,
                    constructor_overload_candidates,
                    call->args,
                    synthetic_object_expr.get(),
                    loc,
                    selected_constructor_symbol,
                    selected_implicit_object_arg_kind)) {
                return constructor_overload_error;
            }

            (void)selected_implicit_object_arg_kind;
            if (selected_constructor_symbol) {
                callee_ref->symref = std::move(selected_constructor_symbol);
            }
            return nullptr;
        }
    }

    if (function_candidates.size() == 1 &&
        template_candidates.empty() &&
        !callee_ref->symref) {
        callee_ref->symref = function_candidates.front();
    }
    if (function_candidates.size() <= 1 && template_candidates.empty()) {
        return nullptr;
    }

    std::vector<OverloadCallCandidate> overload_candidates;
    overload_candidates.reserve(
        function_candidates.size() + template_candidates.size());
    for (const auto& candidate : function_candidates) {
        OverloadCallCandidate call_candidate;
        call_candidate.symbol = candidate;
        call_candidate.implicit_object_arg_kind = OverloadImplicitObjectArgKind::None;
        overload_candidates.push_back(std::move(call_candidate));
    }
    for (const auto* function_template : template_candidates) {
        std::vector<TemplateArgument> deduced_arguments;
        if (!deduce_function_template_call_arguments(
                function_template, call->args, deduced_arguments)) {
            continue;
        }

        std::shared_ptr<Symbol> specialization_symbol = nullptr;
        auto* specialization_decl =
            instantiate_function_template_specialization(
                function_template,
                deduced_arguments,
                loc,
                &specialization_symbol,
                /*instantiate_definition=*/false);
        if (!specialization_decl || !specialization_symbol) {
            continue;
        }

        OverloadCallCandidate call_candidate;
        call_candidate.symbol = std::move(specialization_symbol);
        call_candidate.implicit_object_arg_kind = OverloadImplicitObjectArgKind::None;
        overload_candidates.push_back(std::move(call_candidate));
    }

    if (overload_candidates.empty()) {
        return nullptr;
    }

    std::shared_ptr<Symbol> selected_symbol = nullptr;
    OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
        OverloadImplicitObjectArgKind::None;
    if (auto overload_error = resolve_overloaded_call_candidates(
            display_name,
            overload_candidates,
            call->args,
            nullptr,
            loc,
            selected_symbol,
            selected_implicit_object_arg_kind)) {
        return overload_error;
    }

    (void)selected_implicit_object_arg_kind;
    if (selected_symbol) {
        if (auto completion_error =
                complete_selected_function_template_specialization_symbol(
                    selected_symbol,
                    loc,
                    "failed to instantiate selected function template specialization")) {
            return completion_error;
        }
        callee_ref->symref = std::move(selected_symbol);
    }
    return nullptr;
}


std::unique_ptr<Expr> Collect::collect_function_call(std::unique_ptr<Expr> callee, std::vector<std::unique_ptr<Expr>> args, SrcLoc loc) const {
    return collect_function_call(
        std::move(callee),
        std::move(args),
        {},
        false,
        loc);
}

std::unique_ptr<Expr> Collect::collect_function_call(
    std::unique_ptr<Expr> callee,
    std::vector<std::unique_ptr<Expr>> args,
    std::vector<TemplateArgument> explicit_template_args,
    SrcLoc loc) const {
    return collect_explicit_template_call_impl(
        std::move(callee),
        std::move(explicit_template_args),
        std::move(args),
        loc);
}

std::unique_ptr<Expr> Collect::collect_function_call(
    std::unique_ptr<Expr> callee,
    std::vector<std::unique_ptr<Expr>> args,
    std::vector<TemplateArgument> explicit_template_args,
    bool has_explicit_template_args,
    SrcLoc loc) const {
    if (has_explicit_template_args) {
        return collect_explicit_template_call_impl(
            std::move(callee),
            std::move(explicit_template_args),
            std::move(args),
            loc);
    }
    if (isa<DependentMemberPointerAccessExpr>(callee.get())) {
        return collect_dependent_call_expression(
            std::move(callee),
            std::move(args),
            loc);
    }
    if (isa<UnresolvedMemberExpr>(callee.get()) ||
        isa<UnresolvedLookupExpr>(callee.get())) {
        return collect_dependent_call_expression(
            std::move(callee),
            std::move(args),
            loc);
    }
    auto* callee_var_ref = dyn_cast<VarRef>(strip_implicit_casts(callee.get()));
    if (callee_var_ref &&
        callee_var_ref->symref &&
        callee_var_ref->symref->kind != SymbolKind::FUNCTION &&
        type_depends_on_template_parameters(
            callee_var_ref->get_type(),
            ast_ctx_.get())) {
        return collect_dependent_call_expression(
            std::move(callee),
            std::move(args),
            loc);
    }
    auto call = collect_make<FuncCall>(std::move(callee), std::move(args), loc);
    if (!call->func) {
        return call;
    }

    // Canonical C++ call pipeline:
    // 1) function-object (`obj(args)`) overload,
    // 2) builtin / free-function overload handling,
    // 3) member-call overload selection,
    // then final type/argument normalization.
    MemberCallSelection member_call_selection;
    if (auto error = try_function_object_call_overload(call, loc)) {
        return error;
    }
    if (auto early_result = try_builtin_or_overloaded_varref_call(call, loc)) {
        return early_result;
    }
    if (auto error = try_member_function_overload_call(
            call, member_call_selection, loc)) {
        return error;
    }

    return finalize_call_expression(std::move(call), member_call_selection, loc);
}

std::unique_ptr<Expr> Collect::collect_explicit_function_template_call(
    std::unique_ptr<Expr> callee,
    std::vector<TemplateArgument> explicit_template_args,
    std::vector<std::unique_ptr<Expr>> args,
    SrcLoc loc) const {
    return collect_explicit_template_call_impl(
        std::move(callee),
        std::move(explicit_template_args),
        std::move(args),
        loc);
}

std::unique_ptr<Expr> Collect::collect_dependent_call_expression(
    std::unique_ptr<Expr> callee,
    std::vector<std::unique_ptr<Expr>> args,
    SrcLoc loc) const {
    QualType dependent_call_type(
        std::make_shared<AutoType>(AutoTypeFlavor::Cxx));
    return collect_make<DependentCallExpr>(
        std::move(callee),
        std::move(args),
        dependent_call_type,
        /*known_function_type=*/QualType(nullptr),
        loc);
}

std::unique_ptr<Expr> Collect::collect_pack_expansion_expression(
    std::unique_ptr<Expr> pattern,
    SrcLoc loc) const {
    return collect_make<PackExpansionExpr>(std::move(pattern), loc);
}

std::unique_ptr<Expr> Collect::collect_fold_expression(
    BinOpTypes op,
    FoldDirection direction,
    std::unique_ptr<Expr> pattern,
    std::unique_ptr<Expr> init,
    SrcLoc loc) const {
    QualType dependent_fold_type(
        std::make_shared<AutoType>(AutoTypeFlavor::Cxx));
    return collect_make<FoldExpr>(
        op,
        direction,
        std::move(pattern),
        std::move(init),
        dependent_fold_type,
        loc);
}

std::unique_ptr<Expr> Collect::build_dependent_explicit_template_call(
    std::unique_ptr<Expr> callee,
    std::vector<TemplateArgument> explicit_template_args,
    std::vector<std::unique_ptr<Expr>> args,
    SrcLoc loc) const {
    if (!callee) {
        return collect_make<ErrorExpr>(
            "missing callee for dependent explicit template call",
            loc);
    }

    QualType dependent_call_type(
        std::make_shared<AutoType>(AutoTypeFlavor::Cxx));

    if (auto* member_callee = dyn_cast<MemberExpr>(callee.get())) {
        auto member_base_analysis = analyze_cpp_member_lookup_base(
            member_callee->base ? member_callee->base->get_type() : QualType(nullptr),
            member_callee->isArrow != 0,
            func_state_.current_function_is_cpp_member
                ? func_state_.current_function_cpp_this_type
                : QualType(nullptr),
            ast_ctx_.get());

        auto owned_member = std::unique_ptr<MemberExpr>(
            static_cast<MemberExpr*>(callee.release()));
        auto unresolved_member = collect_make<UnresolvedMemberExpr>(
            std::move(owned_member->base),
            owned_member->get_member_name(),
            owned_member->member_type,
            std::optional<std::vector<TemplateArgument>>(
                std::move(explicit_template_args)),
            owned_member->isArrow != 0,
            member_base_analysis.is_current_instantiation,
            /*names_dependent_base=*/false,
            /*requires_template_keyword=*/true,
            owned_member->suppress_virtual_dispatch != 0,
            owned_member->location);
        return collect_make<DependentCallExpr>(
            std::move(unresolved_member),
            std::move(args),
            dependent_call_type,
            nullptr,
            loc);
    }

    auto* callee_ref = dyn_cast<VarRef>(callee.get());
    if (!callee_ref) {
        return collect_make<ErrorExpr>(
            "explicit template arguments require a function or member template name",
            loc);
    }

    const auto* qualified_info = callee_ref->get_cpp_qualified_info();
    auto qualifier = build_dependent_lookup_qualifier(qualified_info);

    auto unresolved_lookup = collect_make<UnresolvedLookupExpr>(
        callee_ref->get_name(),
        std::move(qualifier),
        std::optional<std::vector<TemplateArgument>>(
            std::move(explicit_template_args)),
        /*requires_template_keyword=*/true,
        /*is_dependent=*/true,
        dependent_call_type,
        callee_ref->location);
    return collect_make<DependentCallExpr>(
        std::move(unresolved_lookup),
        std::move(args),
        dependent_call_type,
        nullptr,
        loc);
}

std::unique_ptr<Expr> Collect::collect_explicit_template_call_impl(
    std::unique_ptr<Expr> callee,
    std::vector<TemplateArgument> explicit_template_args,
    std::vector<std::unique_ptr<Expr>> args,
    SrcLoc loc) const {
    if (!lang_opts_.is_cxx_mode()) {
        report_error("explicit template arguments require C++ mode", loc);
        return collect_make<ErrorExpr>(
            "explicit template arguments require C++ mode",
            loc);
    }
    if (!callee) {
        return collect_make<ErrorExpr>(
            "explicit template arguments require a function or member template name",
            loc);
    }

    if (auto* unresolved_member = dyn_cast<UnresolvedMemberExpr>(callee.get())) {
        auto owned_member = std::unique_ptr<UnresolvedMemberExpr>(
            static_cast<UnresolvedMemberExpr*>(callee.release()));
        owned_member->explicit_template_arguments =
            std::move(explicit_template_args);
        owned_member->requires_template_keyword = true;
        return collect_dependent_call_expression(
            std::move(owned_member),
            std::move(args),
            loc);
    }
    if (auto* unresolved_lookup = dyn_cast<UnresolvedLookupExpr>(callee.get())) {
        auto owned_lookup = std::unique_ptr<UnresolvedLookupExpr>(
            static_cast<UnresolvedLookupExpr*>(callee.release()));
        owned_lookup->explicit_template_arguments =
            std::move(explicit_template_args);
        owned_lookup->requires_template_keyword = true;
        return collect_dependent_call_expression(
            std::move(owned_lookup),
            std::move(args),
            loc);
    }

    if (auto* member_callee = dyn_cast<MemberExpr>(callee.get())) {
        std::shared_ptr<ObjectType> record_type = nullptr;
        QualType member_base_type = nullptr;
        if (member_callee->base) {
            member_base_type = member_callee->base->get_type();
            auto semantic_base_type = desugar_type(member_base_type);
            if (member_callee->isArrow) {
                auto ptr_type = semantic_base_type.as_shared<PointerType>();
                if (ptr_type) {
                    record_type =
                        desugar_type(ptr_type->pointed_type).as_shared<ObjectType>();
                }
            } else {
                record_type = semantic_base_type.as_shared<ObjectType>();
            }
        }
        if (!record_type) {
            if (analyze_cpp_member_lookup_base(
                    member_base_type,
                    member_callee->isArrow != 0,
                    func_state_.current_function_is_cpp_member
                        ? func_state_.current_function_cpp_this_type
                        : QualType(nullptr),
                    ast_ctx_.get())
                    .is_dependent) {
                return build_dependent_explicit_template_call(
                    std::move(callee),
                    std::move(explicit_template_args),
                    std::move(args),
                    loc);
            }
            report_error(
                "member explicit-template calls are not supported yet",
                loc);
            return collect_make<ErrorExpr>(
                "member explicit-template calls are not supported yet",
                loc);
        }
        auto method_templates =
            find_record_method_templates(
                record_type.get(),
                member_callee->get_member_name());
        if (method_templates.empty()) {
            report_error(
                "no member function template named '" +
                    member_callee->get_member_name() + "'",
                loc);
            return collect_make<ErrorExpr>(
                "missing member function template",
                loc);
        }

        const ObjectDecl* object_record_decl = record_decl_from_record_type(record_type.get());
        const ObjectDecl* access_context_decl = nullptr;
        if (func_state_.current_function_is_cpp_member) {
            access_context_decl =
                current_record_decl_from_this_type(func_state_.current_function_cpp_this_type);
        }

        std::vector<OverloadCallCandidate> overload_candidates;
        overload_candidates.reserve(method_templates.size());
        bool saw_private_method = false;
        bool saw_protected_method = false;
        bool saw_instantiation = false;
        for (const auto& method_template_match : method_templates) {
            const auto* method_template = method_template_match.method_template;
            const auto* function_template =
                method_template ? method_template->decl : nullptr;
            const auto* pattern =
                function_template ? function_template->function_decl() : nullptr;
            if (!method_template || !function_template || !pattern) {
                continue;
            }
            if (method_template->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_template_match.owner_record_decl,
                        access_context_decl)) {
                    saw_private_method = true;
                    continue;
                }
            }
            if (method_template->declared_access == RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_template_match.owner_record_decl,
                    access_context_decl,
                    object_record_decl,
                    method_template->is_static);
                if (!protected_ok) {
                    saw_protected_method = true;
                    continue;
                }
            }

            TemplateArgumentBindings explicit_bindings;
            std::string binding_error;
            if (!bind_explicit_template_arguments_prefix_to_parameters(
                    function_template->parameters,
                    explicit_template_args,
                    explicit_bindings,
                    &binding_error)) {
                report_error(
                    "function template '" + pattern->name +
                        "' template arguments do not match the parameter list" +
                        (binding_error.empty() ? std::string() : ": " + binding_error),
                    loc);
                continue;
            }

            std::unique_ptr<Expr> deduction_object_arg;
            std::vector<Expr*> deduction_args;
            deduction_args.reserve(args.size() + (method_template->is_static ? 0 : 1));
            if (!method_template->is_static) {
                std::string clone_error;
                auto cloned_base = clone_expr_tree(
                    member_callee->base.get(),
                    ast_ctx_.get(),
                    &clone_error);
                if (!cloned_base) {
                    std::string message = clone_error.empty()
                        ? "member template implicit object argument is not clonable"
                        : "member template implicit object argument is not clonable: " +
                            clone_error;
                    report_error(message, loc);
                    return collect_make<ErrorExpr>(
                        "unsupported member template implicit object argument",
                        loc);
                }
                deduction_object_arg = build_overload_implicit_object_arg(
                    OverloadImplicitObjectArgKind::MemberObject,
                    std::move(cloned_base),
                    member_callee->isArrow,
                    loc);
                if (!deduction_object_arg) {
                    report_error(
                        "failed to build member template implicit object argument",
                        loc);
                    return collect_make<ErrorExpr>(
                        "invalid member template implicit object argument",
                        loc);
                }
                if (isa<ErrorExpr>(deduction_object_arg.get())) {
                    return std::move(deduction_object_arg);
                }
                deduction_args.push_back(deduction_object_arg.get());
            }
            for (const auto& arg : args) {
                deduction_args.push_back(arg.get());
            }

            std::vector<TemplateArgument> specialization_arguments;
            if (!deduce_function_template_call_arguments(
                    function_template,
                    deduction_args,
                    specialization_arguments,
                    &explicit_bindings)) {
                continue;
            }

            std::shared_ptr<Symbol> specialization_symbol = nullptr;
            auto* specialization_decl =
                instantiate_function_template_specialization(
                    function_template,
                    specialization_arguments,
                    loc,
                    &specialization_symbol,
                    /*instantiate_definition=*/false);
            if (!specialization_decl || !specialization_symbol) {
                continue;
            }
            saw_instantiation = true;

            OverloadCallCandidate candidate;
            candidate.symbol = std::move(specialization_symbol);
            candidate.implicit_object_arg_kind = method_template->is_static
                ? OverloadImplicitObjectArgKind::None
                : OverloadImplicitObjectArgKind::MemberObject;
            overload_candidates.push_back(std::move(candidate));
        }

        if (overload_candidates.empty()) {
            if (auto inaccessible_error = report_inaccessible_member(
                    member_callee->get_member_name(),
                    saw_private_method,
                    saw_protected_method,
                    loc)) {
                return inaccessible_error;
            }
            if (!saw_instantiation) {
                report_error(
                    "no matching member function template specialization for '" +
                        member_callee->get_member_name() + "'",
                    loc);
            }
            return collect_make<ErrorExpr>(
                "no matching member function template specialization",
                loc);
        }

        std::shared_ptr<Symbol> selected_symbol = nullptr;
        OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
            OverloadImplicitObjectArgKind::None;
        if (auto overload_error = select_overload_candidate(
                member_callee->get_member_name(),
                overload_candidates,
                args,
                member_callee->base.get(),
                loc,
                selected_symbol,
                selected_implicit_object_arg_kind)) {
            return overload_error;
        }
        if (!selected_symbol) {
            report_error(
                "no matching member function template specialization for '" +
                    member_callee->get_member_name() + "'",
                loc);
            return collect_make<ErrorExpr>(
                "no selected member function template specialization",
                loc);
        }

        if (auto completion_error =
                complete_selected_function_template_specialization_symbol(
                    selected_symbol,
                    loc,
                    "failed to instantiate selected member function template specialization")) {
            return completion_error;
        }

        auto member_owner = std::unique_ptr<MemberExpr>(
            static_cast<MemberExpr*>(callee.release()));
        MemberCallSelection member_call_selection;
        member_call_selection.selected = true;
        member_call_selection.is_arrow = member_owner->isArrow;
        member_call_selection.name = member_owner->get_member_name();
        member_call_selection.suppress_virtual_dispatch =
            member_owner->suppress_virtual_dispatch != 0;
        member_call_selection.has_implicit_object_argument =
            selected_implicit_object_arg_kind != OverloadImplicitObjectArgKind::None;
        member_call_selection.symbol = selected_symbol;
        if (record_type) {
            member_call_selection.record_decl =
                canonical_record_decl(dyn_cast<ObjectDecl>(record_type->get_decl()));
        }

        auto implicit_object_arg = build_overload_implicit_object_arg(
            selected_implicit_object_arg_kind,
            std::move(member_owner->base),
            member_owner->isArrow,
            member_owner->location);
        auto selected_call = collect_make<FuncCall>(
            collect_identifier_reference(
                member_owner->get_member_name(),
                std::move(selected_symbol),
                member_owner->location),
            std::move(args),
            loc);
        if (selected_implicit_object_arg_kind !=
                OverloadImplicitObjectArgKind::None &&
            implicit_object_arg) {
            selected_call->args.insert(
                selected_call->args.begin(),
                std::move(implicit_object_arg));
        }
        return finalize_call_expression(
            std::move(selected_call),
            member_call_selection,
            loc);
    }

    auto* callee_ref = dyn_cast<VarRef>(callee.get());
    if (!callee_ref) {
        report_error(
            "explicit template arguments require a function or member template name",
            loc);
        return collect_make<ErrorExpr>(
            "explicit template arguments require function or member template name",
            loc);
    }

    const auto* qualified_info = callee_ref->get_cpp_qualified_info();
    if (qualified_info && qualified_info->is_type_qualified) {
        auto qualified_owner_analysis =
            analyze_cpp_qualified_expr_owner(qualified_info, ast_ctx_.get());
        auto qualified_owner_type = qualified_owner_analysis.qualifier_record_type;
        const ObjectDecl* owner_record_decl =
            qualified_owner_analysis.qualifier_record_decl;
        if (!qualified_owner_type || !owner_record_decl) {
            if (qualified_owner_analysis.is_dependent_context()) {
                return build_dependent_explicit_template_call(
                    std::move(callee),
                    std::move(explicit_template_args),
                    std::move(args),
                    loc);
            }
            report_error(
                "type-qualified explicit-template calls are not supported yet",
                loc);
            return collect_make<ErrorExpr>(
                "type-qualified explicit-template calls are not supported yet",
                loc);
        }

        const std::string& callee_name = callee_ref->get_name();
        std::string display_name =
            format_explicit_template_callee_name(qualified_info, callee_name);
        const ObjectDecl* access_context_decl = nullptr;
        if (func_state_.current_function_is_cpp_member) {
            access_context_decl =
                current_record_decl_from_this_type(func_state_.current_function_cpp_this_type);
        }

        auto method_templates =
            find_record_method_templates(qualified_owner_type.get(), callee_name);
        if (method_templates.empty()) {
            report_error(
                "no member function template named '" + display_name + "'",
                loc);
            return collect_make<ErrorExpr>(
                "missing member function template",
                loc);
        }

        std::vector<OverloadCallCandidate> overload_candidates;
        overload_candidates.reserve(method_templates.size());
        bool saw_private_method = false;
        bool saw_protected_method = false;
        bool saw_instantiation = false;
        bool saw_nonstatic_method = false;
        bool attempted_qualified_object_expr = false;
        std::unique_ptr<Expr> qualified_object_expr;
        std::unique_ptr<Expr> qualified_object_error;
        auto ensure_qualified_object_expr = [&]() -> Expr* {
            if (attempted_qualified_object_expr) {
                return qualified_object_expr.get();
            }
            attempted_qualified_object_expr = true;

            auto this_expr = collect_cpp_this_expression(loc);
            if (!this_expr || isa<ErrorExpr>(this_expr.get())) {
                qualified_object_error = std::move(this_expr);
                return nullptr;
            }

            auto this_ptr_type =
                desugar_type(this_expr->get_type()).as_shared<PointerType>();
            uint8_t owner_quals = this_ptr_type
                ? this_ptr_type->pointed_type.get_qualifiers()
                : QUAL_NONE;
            QualType owner_qt(qualified_owner_type, owner_quals);
            QualType owner_ptr_type(std::make_shared<PointerType>(owner_qt));
            auto owner_this_expr = collect_cpp_named_cast(
                Collect::CppNamedCastKind::Static,
                std::move(this_expr),
                owner_ptr_type,
                loc);
            if (!owner_this_expr || isa<ErrorExpr>(owner_this_expr.get())) {
                qualified_object_error = std::move(owner_this_expr);
                return nullptr;
            }

            qualified_object_expr = std::move(owner_this_expr);
            return qualified_object_expr.get();
        };
        for (const auto& method_template_match : method_templates) {
            const auto* method_template = method_template_match.method_template;
            const auto* function_template =
                method_template ? method_template->decl : nullptr;
            const auto* pattern =
                function_template ? function_template->function_decl() : nullptr;
            if (!method_template || !function_template || !pattern) {
                continue;
            }
            if (method_template->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_template_match.owner_record_decl,
                        access_context_decl)) {
                    saw_private_method = true;
                    continue;
                }
            }
            if (method_template->declared_access == RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_template_match.owner_record_decl,
                    access_context_decl,
                    owner_record_decl,
                    method_template->is_static);
                if (!protected_ok) {
                    saw_protected_method = true;
                    continue;
                }
            }

            TemplateArgumentBindings explicit_bindings;
            std::string binding_error;
            if (!bind_explicit_template_arguments_prefix_to_parameters(
                    function_template->parameters,
                    explicit_template_args,
                    explicit_bindings,
                    &binding_error)) {
                report_error(
                    "function template '" + pattern->name +
                        "' template arguments do not match the parameter list" +
                        (binding_error.empty() ? std::string() : ": " + binding_error),
                    loc);
                continue;
            }

            std::vector<Expr*> deduction_args;
            deduction_args.reserve(args.size() + (method_template->is_static ? 0 : 1));
            if (!method_template->is_static) {
                saw_nonstatic_method = true;
                Expr* qualified_object_arg = ensure_qualified_object_expr();
                if (!qualified_object_arg) {
                    continue;
                }
                deduction_args.push_back(qualified_object_arg);
            }
            for (const auto& arg : args) {
                deduction_args.push_back(arg.get());
            }

            std::vector<TemplateArgument> specialization_arguments;
            if (!deduce_function_template_call_arguments(
                    function_template,
                    deduction_args,
                    specialization_arguments,
                    &explicit_bindings)) {
                continue;
            }

            std::shared_ptr<Symbol> specialization_symbol = nullptr;
            auto* specialization_decl =
                instantiate_function_template_specialization(
                    function_template,
                    specialization_arguments,
                    loc,
                    &specialization_symbol,
                    /*instantiate_definition=*/false);
            if (!specialization_decl || !specialization_symbol) {
                continue;
            }
            saw_instantiation = true;

            OverloadCallCandidate candidate;
            candidate.symbol = std::move(specialization_symbol);
            candidate.implicit_object_arg_kind = method_template->is_static
                ? OverloadImplicitObjectArgKind::None
                : OverloadImplicitObjectArgKind::MemberObject;
            overload_candidates.push_back(std::move(candidate));
        }

        if (overload_candidates.empty()) {
            if (auto inaccessible_error = report_inaccessible_member(
                    callee_name,
                    saw_private_method,
                    saw_protected_method,
                    loc)) {
                return inaccessible_error;
            }
            if (!saw_instantiation && saw_nonstatic_method && qualified_object_error) {
                return std::move(qualified_object_error);
            }
            if (!saw_instantiation) {
                report_error(
                    "no matching member function template specialization for '" +
                        display_name + "'",
                    loc);
            }
            return collect_make<ErrorExpr>(
                "no matching member function template specialization",
                loc);
        }

        std::shared_ptr<Symbol> selected_symbol = nullptr;
        OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
            OverloadImplicitObjectArgKind::None;
        if (auto overload_error = select_overload_candidate(
                display_name,
                overload_candidates,
                args,
                qualified_object_expr.get(),
                loc,
                selected_symbol,
                selected_implicit_object_arg_kind)) {
            return overload_error;
        }

        if (!selected_symbol) {
            report_error(
                "no matching member function template specialization for '" +
                    display_name + "'",
                loc);
            return collect_make<ErrorExpr>(
                "no selected member function template specialization",
                loc);
        }
        if (auto completion_error =
                complete_selected_function_template_specialization_symbol(
                    selected_symbol,
                    loc,
                    "failed to instantiate selected member function template specialization")) {
            return completion_error;
        }

        MemberCallSelection member_call_selection;
        auto selected_call = collect_make<FuncCall>(
            make_hidden_overload_callee(std::move(selected_symbol), loc),
            std::move(args),
            loc);
        if (selected_implicit_object_arg_kind !=
                OverloadImplicitObjectArgKind::None &&
            qualified_object_expr) {
            auto implicit_object_arg = build_overload_implicit_object_arg(
                selected_implicit_object_arg_kind,
                std::move(qualified_object_expr),
                true,
                loc);
            if (!implicit_object_arg) {
                report_error(
                    "failed to build qualified member template implicit object argument",
                    loc);
                return collect_make<ErrorExpr>(
                    "invalid qualified member template implicit object argument",
                    loc);
            }
            if (isa<ErrorExpr>(implicit_object_arg.get())) {
                return implicit_object_arg;
            }
            selected_call->args.insert(
                selected_call->args.begin(),
                std::move(implicit_object_arg));
        }
        return finalize_call_expression(
            std::move(selected_call),
            member_call_selection,
            loc);
    }

    if (!current_scope_) {
        report_error("internal error: missing scope for explicit template call", loc);
        return collect_make<ErrorExpr>(
            "missing scope for explicit template call", loc);
    }

    const std::string& callee_name = callee_ref->get_name();
    std::string display_name =
        format_explicit_template_callee_name(qualified_info, callee_name);
    auto template_candidates =
        qualified_info
            ? lookup_qualified_function_templates(
                  callee_name,
                  *qualified_info,
                  get_current_decl_context().get())
            : lookup_unqualified_function_templates(callee_name, current_scope_);
    if (template_candidates.empty()) {
        report_error(
            "no function template named '" + display_name + "'",
            loc);
        return collect_make<ErrorExpr>("missing function template", loc);
    }

    std::vector<OverloadCallCandidate> overload_candidates;
    overload_candidates.reserve(template_candidates.size());
    bool saw_instantiation = false;
    for (const auto* function_template : template_candidates) {
        TemplateArgumentBindings explicit_bindings;
        std::string binding_error;
        if (!bind_explicit_template_arguments_prefix_to_parameters(
                function_template->parameters,
                explicit_template_args,
                explicit_bindings,
                &binding_error)) {
            const auto* pattern = function_template->function_decl();
            report_error(
                "function template '" +
                    std::string(pattern ? pattern->name : display_name) +
                    "' template arguments do not match the parameter list" +
                    (binding_error.empty() ? std::string() : ": " + binding_error),
                loc);
            continue;
        }

        std::vector<TemplateArgument> specialization_arguments;
        if (!deduce_function_template_call_arguments(
                function_template,
                args,
                specialization_arguments,
                &explicit_bindings)) {
            continue;
        }

        std::shared_ptr<Symbol> specialization_symbol = nullptr;
        auto* specialization_decl =
            instantiate_function_template_specialization(
                function_template,
                specialization_arguments,
                loc,
                &specialization_symbol,
                /*instantiate_definition=*/false);
        if (!specialization_decl || !specialization_symbol) {
            continue;
        }
        saw_instantiation = true;
        OverloadCallCandidate candidate;
        candidate.symbol = std::move(specialization_symbol);
        overload_candidates.push_back(std::move(candidate));
    }

    if (overload_candidates.empty()) {
        if (!saw_instantiation) {
            report_error(
                "no matching function template specialization for '" +
                    display_name + "'",
                loc);
        }
        return collect_make<ErrorExpr>(
            "no matching function template specialization",
            loc);
    }

    std::shared_ptr<Symbol> selected_symbol = nullptr;
    OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
        OverloadImplicitObjectArgKind::None;
    if (auto overload_error = select_overload_candidate(
            display_name,
            overload_candidates,
            args,
            nullptr,
            loc,
            selected_symbol,
            selected_implicit_object_arg_kind)) {
        return overload_error;
    }

    (void)selected_implicit_object_arg_kind;
    if (!selected_symbol) {
        report_error(
            "no matching function template specialization for '" +
                display_name + "'",
            loc);
        return collect_make<ErrorExpr>(
            "no selected function template specialization",
            loc);
    }
    if (auto completion_error =
            complete_selected_function_template_specialization_symbol(
                selected_symbol,
                loc,
                "failed to instantiate selected function template specialization")) {
        return completion_error;
    }

    MemberCallSelection member_call_selection;
    auto selected_call = collect_make<FuncCall>(
        make_hidden_overload_callee(std::move(selected_symbol), loc),
        std::move(args),
        loc);
    return finalize_call_expression(
        std::move(selected_call),
        member_call_selection,
        loc);
}

std::unique_ptr<Expr> Collect::materialize_concrete_qualified_lookup_expression(
    const std::string& name,
    const DependentLookupQualifier& qualifier,
    bool looks_like_call,
    SrcLoc loc,
    QualType implicit_this_type) const {
    auto make_qualified_var_ref =
        [&](std::shared_ptr<Symbol> symbol) -> std::unique_ptr<Expr> {
            auto qualified_ref =
                collect_identifier_reference(name, std::move(symbol), loc);
            if (isa<VarRef>(qualified_ref.get())) {
                qualified_ref = attach_cpp_qualified_info_to_expr(
                    std::move(qualified_ref),
                    build_cpp_qualified_expr_info(qualifier));
            }
            return qualified_ref;
        };

    if (!qualifier.is_type_qualified) {
        return make_qualified_var_ref(nullptr);
    }

    QualType resolved_owner_type =
        finalize_deferred_semantic_type(qualifier.qualifier_type, loc);
    auto resolved_qualified_info = build_cpp_qualified_expr_info(
        qualifier.has_global_qualifier,
        qualifier.qualifiers,
        resolved_owner_type,
        qualifier.is_type_qualified,
        qualifier.is_current_instantiation);
    auto qualified_owner_analysis =
        analyze_cpp_qualified_expr_owner(&resolved_qualified_info, ast_ctx_.get());
    auto qualified_owner_type = qualified_owner_analysis.qualifier_record_type;
    const ObjectDecl* qualified_owner_record_decl =
        qualified_owner_analysis.qualifier_record_decl;
    if (!qualified_owner_type || !qualified_owner_record_decl) {
        report_error(
            "failed to resolve qualified owner type for dependent lookup '" +
                name + "'",
            loc);
        return collect_make<ErrorExpr>(
            "unresolved qualified owner after substitution",
            loc);
    }

    auto member_lookup = lookup_record_member_name(
        qualified_owner_type.get(),
        name);
    size_t static_callable_matches =
        member_lookup.static_method_matches +
        member_lookup.static_method_template_matches;
    size_t total_matches =
        member_lookup.field_matches +
        member_lookup.static_method_matches +
        member_lookup.static_method_template_matches +
        member_lookup.static_data_matches +
        member_lookup.nonstatic_method_matches +
        member_lookup.nonstatic_method_template_matches;

    if (looks_like_call &&
        static_callable_matches > 0 &&
        member_lookup.nonstatic_method_matches == 0 &&
        member_lookup.nonstatic_method_template_matches == 0 &&
        member_lookup.field_matches == 0 &&
        member_lookup.static_data_matches == 0) {
        std::shared_ptr<Symbol> selected_symbol = nullptr;
        if (member_lookup.static_method_matches == 1 &&
            member_lookup.static_method_template_matches == 0 &&
            member_lookup.single_static_method &&
            member_lookup.single_static_method->symbol) {
            selected_symbol = member_lookup.single_static_method->symbol;
        }
        return make_qualified_var_ref(std::move(selected_symbol));
    }

    if (total_matches > 1) {
        report_error("member '" + name + "' is ambiguous", loc);
        return collect_make<ErrorExpr>("ambiguous member reference", loc);
    }

    if (member_lookup.static_data_matches == 1 &&
        member_lookup.single_static_data_member &&
        member_lookup.single_static_data_member->symbol) {
        return make_qualified_var_ref(
            member_lookup.single_static_data_member->symbol);
    }

    if (member_lookup.static_method_matches == 1 &&
        member_lookup.nonstatic_method_matches == 0 &&
        member_lookup.static_method_template_matches == 0 &&
        member_lookup.nonstatic_method_template_matches == 0 &&
        member_lookup.field_matches == 0 &&
        member_lookup.single_static_method &&
        member_lookup.single_static_method->symbol) {
        return make_qualified_var_ref(member_lookup.single_static_method->symbol);
    }

    if (total_matches == 1 &&
        (member_lookup.static_data_matches == 1 ||
         member_lookup.static_method_matches == 1)) {
        report_error(
            "internal error: missing symbol for resolved qualified lookup '" +
                name + "'",
            loc);
        return collect_make<ErrorExpr>(
            "missing qualified lookup symbol",
            loc);
    }

    if (total_matches == 0) {
        report_error(
            "no member named '" + name + "' in '" +
                qualified_owner_type->to_string() + "'",
            loc);
        return collect_make<ErrorExpr>(
            "missing qualified member",
            loc);
    }

    auto this_expr = implicit_this_type
        ? collect_make<CppThisExpr>(implicit_this_type, loc)
        : collect_cpp_this_expression(loc);
    if (isa<ErrorExpr>(this_expr.get())) {
        return this_expr;
    }
    auto this_ptr_type =
        desugar_type(this_expr->get_type()).as_shared<PointerType>();
    uint8_t owner_quals = this_ptr_type
        ? this_ptr_type->pointed_type.get_qualifiers()
        : QUAL_NONE;
    QualType owner_qt(qualified_owner_type, owner_quals);
    QualType owner_ptr_type(std::make_shared<PointerType>(owner_qt));
    auto owner_this_expr =
        collect_cpp_named_cast(
            Collect::CppNamedCastKind::Static,
            std::move(this_expr),
            owner_ptr_type,
            loc);
    return collect_member_expression(
        std::move(owner_this_expr),
        name,
        true,
        loc,
        looks_like_call,
        true);
}

bool Collect::resolve_dependent_expr_after_substitution(
    std::unique_ptr<Expr>& expr,
    QualType implicit_this_type,
    std::string* error_out) const {
    if (auto* block = dyn_cast<BlockExpr>(expr.get())) {
        if (block->semantic_info.invoke_decl) {
            return true;
        }
        if (!collect_finalize_block_expression(*block, error_out)) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to finalize block expression after substitution";
            }
            return false;
        }
        return true;
    }
    if (auto* lambda = dyn_cast<CppLambdaExpr>(expr.get())) {
        if (lambda->semantic_info.call_operator_decl ||
            lambda->semantic_info.call_operator_template) {
            return true;
        }
        if (!collect_finalize_cpp_lambda_expression(*lambda, error_out)) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to finalize lambda expression after substitution";
            }
            return false;
        }
        return true;
    }

    auto strip_stale_dependent_implicit_casts =
        [&](std::unique_ptr<Expr>& candidate) {
            while (auto* cast = dyn_cast<ImplicitCast>(candidate.get())) {
                if (!cast->expr) {
                    return;
                }
                bool cast_type_still_dependent =
                    type_depends_on_template_parameters(
                        cast->ctype,
                        ast_ctx_.get());
                bool source_type_still_dependent =
                    type_depends_on_template_parameters(
                        cast->expr->get_type(),
                        ast_ctx_.get());
                if (!cast_type_still_dependent || source_type_still_dependent) {
                    return;
                }
                switch (cast->kind) {
                    case ImplicitCastTypes::LVALUE_TO_RVALUE:
                    case ImplicitCastTypes::FUNCTION_TO_POINTER:
                    case ImplicitCastTypes::ARRAY_TO_POINTER:
                    case ImplicitCastTypes::LAMBDA_TO_FUNCTION_POINTER:
                    case ImplicitCastTypes::ARITH_CAST:
                    case ImplicitCastTypes::RAW_CAST:
                        break;
                    default:
                        return;
                }
                auto owned_cast = std::unique_ptr<ImplicitCast>(
                    static_cast<ImplicitCast*>(candidate.release()));
                candidate = std::move(owned_cast->expr);
            }
        };

    auto unresolved_member_still_dependent =
        [&](const UnresolvedMemberExpr* unresolved_member) -> bool {
            if (!unresolved_member) {
                return false;
            }
            return analyze_cpp_member_lookup_base(
                       unresolved_member->base
                           ? unresolved_member->base->get_type()
                           : QualType(nullptr),
                       unresolved_member->isArrow != 0,
                       implicit_this_type,
                       ast_ctx_.get())
                .is_dependent;
        };

    auto unresolved_lookup_still_dependent =
        [&](const UnresolvedLookupExpr* unresolved_lookup) -> bool {
            if (!unresolved_lookup) {
                return false;
            }
            return dependent_lookup_qualifier_is_dependent(
                unresolved_lookup->qualifier,
                ast_ctx_.get());
        };

    auto materialize_unresolved_member =
        [&](std::unique_ptr<UnresolvedMemberExpr> owned_member,
            bool allow_overloaded_method_set)
            -> std::unique_ptr<Expr> {
            return collect_member_expression(
                std::move(owned_member->base),
                owned_member->member_name,
                owned_member->isArrow != 0,
                owned_member->location,
                allow_overloaded_method_set,
                owned_member->suppress_virtual_dispatch != 0);
        };

    auto materialize_unresolved_lookup =
        [&](std::unique_ptr<UnresolvedLookupExpr> owned_lookup,
            bool looks_like_call) -> std::unique_ptr<Expr> {
            return materialize_concrete_qualified_lookup_expression(
                owned_lookup->name,
                owned_lookup->qualifier,
                looks_like_call,
                owned_lookup->location,
                implicit_this_type);
        };

    auto find_stale_lambda_object_call_symbol =
        [&](const FuncCall* call) -> std::shared_ptr<Symbol> {
            if (!call || call->args.empty()) {
                return nullptr;
            }

            auto* callee_ref =
                dyn_cast<VarRef>(strip_implicit_casts(call->func.get()));
            if (!callee_ref || !callee_ref->symref) {
                return nullptr;
            }

            bool call_type_has_auto =
                auto_type_utils::auto_type_flavors_in(
                    call->ctype.get_shared()) != 0;
            bool callee_type_has_auto =
                auto_type_utils::auto_type_flavors_in(
                    callee_ref->symref->type.get_shared()) != 0;
            if (!call_type_has_auto && !callee_type_has_auto) {
                return nullptr;
            }
            Expr* object_expr = strip_implicit_casts(call->args.front().get());
            if (auto* unary_object = dyn_cast<UnaryOperation>(object_expr);
                unary_object &&
                unary_object->uop == UnaryOpTypes::ADDRESS_OF &&
                unary_object->exp) {
                object_expr = strip_implicit_casts(unary_object->exp.get());
            }
            auto* object_ref = dyn_cast<VarRef>(object_expr);
            if (!object_ref || !object_ref->symref ||
                !object_ref->symref->variable_definition ||
                !object_ref->symref->variable_definition->init) {
                return nullptr;
            }

            auto* lambda = dyn_cast<CppLambdaExpr>(
                object_ref->symref->variable_definition->init.get());
            if (!lambda || !lambda->semantic_info.call_operator_symbol) {
                return nullptr;
            }

            auto specialized_function_type =
                desugar_type(
                    lambda->semantic_info.call_operator_symbol->type,
                    ast_ctx_.get())
                    .as_shared<FunctionType>();
            if (!specialized_function_type ||
                auto_type_utils::auto_type_flavors_in(
                    specialized_function_type->ret_type.get_shared()) != 0) {
                return nullptr;
            }
            return lambda->semantic_info.call_operator_symbol;
        };

    if (auto* unresolved_member = dyn_cast<UnresolvedMemberExpr>(expr.get())) {
        if (unresolved_member->explicit_template_arguments.has_value() ||
            unresolved_member_still_dependent(unresolved_member)) {
            return true;
        }
        auto owned_member = std::unique_ptr<UnresolvedMemberExpr>(
            static_cast<UnresolvedMemberExpr*>(expr.release()));
        auto rewritten =
            materialize_unresolved_member(
                std::move(owned_member),
                /*allow_overloaded_method_set=*/false);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent member access after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* unresolved_lookup = dyn_cast<UnresolvedLookupExpr>(expr.get())) {
        if (unresolved_lookup->explicit_template_arguments.has_value() ||
            unresolved_lookup_still_dependent(unresolved_lookup)) {
            return true;
        }
        auto owned_lookup = std::unique_ptr<UnresolvedLookupExpr>(
            static_cast<UnresolvedLookupExpr*>(expr.release()));
        auto rewritten =
            materialize_unresolved_lookup(std::move(owned_lookup), false);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve qualified dependent lookup after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* dependent_unary = dyn_cast<DependentUnaryExpr>(expr.get())) {
        strip_stale_dependent_implicit_casts(dependent_unary->operand);
        if (!dependent_unary->operand ||
            type_depends_on_template_parameters(
                dependent_unary->operand->get_type(),
                ast_ctx_.get())) {
            return true;
        }
        auto owned_unary = std::unique_ptr<DependentUnaryExpr>(
            static_cast<DependentUnaryExpr*>(expr.release()));
        auto rewritten = collect_unary_operation(
            owned_unary->uop,
            std::move(owned_unary->operand),
            owned_unary->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent unary expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* dependent_binary = dyn_cast<DependentBinaryExpr>(expr.get())) {
        strip_stale_dependent_implicit_casts(dependent_binary->left);
        strip_stale_dependent_implicit_casts(dependent_binary->right);
        if (!dependent_binary->left ||
            !dependent_binary->right ||
            expression_depends_on_template_parameters(
                dependent_binary->left.get()) ||
            expression_depends_on_template_parameters(
                dependent_binary->right.get())) {
            return true;
        }
        auto owned_binary = std::unique_ptr<DependentBinaryExpr>(
            static_cast<DependentBinaryExpr*>(expr.release()));
        auto rewritten = collect_binary_operation(
            std::move(owned_binary->left),
            std::move(owned_binary->right),
            owned_binary->bop,
            owned_binary->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent binary expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* dependent_subscript =
            dyn_cast<DependentArraySubscriptExpr>(expr.get())) {
        strip_stale_dependent_implicit_casts(dependent_subscript->array);
        strip_stale_dependent_implicit_casts(dependent_subscript->index);
        if (!dependent_subscript->array ||
            !dependent_subscript->index ||
            type_depends_on_template_parameters(
                dependent_subscript->array->get_type(),
                ast_ctx_.get()) ||
            type_depends_on_template_parameters(
                dependent_subscript->index->get_type(),
                ast_ctx_.get())) {
            return true;
        }
        auto owned_subscript = std::unique_ptr<DependentArraySubscriptExpr>(
            static_cast<DependentArraySubscriptExpr*>(expr.release()));
        auto rewritten = collect_array_subscript(
            std::move(owned_subscript->array),
            std::move(owned_subscript->index),
            owned_subscript->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent array subscript after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* dependent_member_access =
            dyn_cast<DependentMemberPointerAccessExpr>(expr.get())) {
        strip_stale_dependent_implicit_casts(dependent_member_access->base);
        strip_stale_dependent_implicit_casts(
            dependent_member_access->member_pointer);
        if (!dependent_member_access->base ||
            !dependent_member_access->member_pointer ||
            type_depends_on_template_parameters(
                dependent_member_access->base->get_type(),
                ast_ctx_.get()) ||
            type_depends_on_template_parameters(
                dependent_member_access->member_pointer->get_type(),
                ast_ctx_.get())) {
            return true;
        }
        auto owned_access = std::unique_ptr<DependentMemberPointerAccessExpr>(
            static_cast<DependentMemberPointerAccessExpr*>(expr.release()));
        auto rewritten = collect_member_pointer_access_expression(
            std::move(owned_access->base),
            std::move(owned_access->member_pointer),
            owned_access->is_arrow != 0,
            owned_access->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent member-pointer access after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* func_call = dyn_cast<FuncCall>(expr.get())) {
        auto owned_call = std::unique_ptr<FuncCall>(
            static_cast<FuncCall*>(expr.release()));
        if (auto specialized_symbol =
                find_stale_lambda_object_call_symbol(owned_call.get())) {
            auto specialized_function_type =
                desugar_type(specialized_symbol->type, ast_ctx_.get())
                    .as_shared<FunctionType>();
            owned_call->func = make_hidden_overload_callee(
                std::move(specialized_symbol),
                owned_call->func ? owned_call->func->location
                                 : owned_call->location);
            owned_call->func = collect_apply_standard_conversions(
                std::move(owned_call->func),
                ExprUseContext::CallCallee);
            if (specialized_function_type) {
                owned_call->ctype = specialized_function_type->ret_type;
            }
            expr = std::move(owned_call);
            return true;
        }
        expr = std::move(owned_call);
    }

    auto* dependent_call = dyn_cast<DependentCallExpr>(expr.get());
    if (!dependent_call) {
        return true;
    }

    auto* unresolved_member =
        dyn_cast<UnresolvedMemberExpr>(dependent_call->callee.get());
    auto* unresolved_lookup =
        dyn_cast<UnresolvedLookupExpr>(dependent_call->callee.get());
    if (!unresolved_member && !unresolved_lookup) {
        auto owned_call = std::unique_ptr<DependentCallExpr>(
            static_cast<DependentCallExpr*>(expr.release()));
        strip_stale_dependent_implicit_casts(owned_call->callee);
        auto rewritten = collect_function_call(
            std::move(owned_call->callee),
            std::move(owned_call->args),
            owned_call->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to finalize dependent call after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if ((unresolved_member &&
         unresolved_member_still_dependent(unresolved_member)) ||
        (unresolved_lookup &&
         unresolved_lookup_still_dependent(unresolved_lookup))) {
        return true;
    }

    auto owned_call = std::unique_ptr<DependentCallExpr>(
        static_cast<DependentCallExpr*>(expr.release()));
    std::vector<TemplateArgument> explicit_template_args;

    if (unresolved_member) {
        auto owned_member = std::unique_ptr<UnresolvedMemberExpr>(
            static_cast<UnresolvedMemberExpr*>(owned_call->callee.release()));
        bool has_explicit_template_args =
            owned_member->explicit_template_arguments.has_value();
        if (has_explicit_template_args) {
            explicit_template_args =
                std::move(*owned_member->explicit_template_arguments);
        }
        auto concrete_callee =
            materialize_unresolved_member(
                std::move(owned_member),
                /*allow_overloaded_method_set=*/true);
        if (!concrete_callee) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to materialize dependent member callee after substitution";
            }
            return false;
        }
        auto rewritten = has_explicit_template_args
            ? collect_explicit_template_call_impl(
                  std::move(concrete_callee),
                  std::move(explicit_template_args),
                  std::move(owned_call->args),
                  owned_call->location)
            : collect_function_call(
                  std::move(concrete_callee),
                  std::move(owned_call->args),
                  owned_call->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    has_explicit_template_args
                        ? "failed to resolve dependent explicit member template call"
                        : "failed to resolve dependent member call after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    auto owned_lookup = std::unique_ptr<UnresolvedLookupExpr>(
        static_cast<UnresolvedLookupExpr*>(owned_call->callee.release()));
    bool has_explicit_template_args =
        owned_lookup->explicit_template_arguments.has_value();
    if (has_explicit_template_args) {
        explicit_template_args =
            std::move(*owned_lookup->explicit_template_arguments);
    }
    auto concrete_callee =
        materialize_unresolved_lookup(std::move(owned_lookup), true);
    if (!concrete_callee) {
        if (error_out && error_out->empty()) {
            *error_out =
                "failed to materialize dependent qualified callee after substitution";
        }
        return false;
    }
    auto rewritten = has_explicit_template_args
        ? collect_explicit_template_call_impl(
              std::move(concrete_callee),
              std::move(explicit_template_args),
              std::move(owned_call->args),
              owned_call->location)
        : collect_function_call(
              std::move(concrete_callee),
              std::move(owned_call->args),
              owned_call->location);
    if (!rewritten) {
        if (error_out && error_out->empty()) {
            *error_out =
                has_explicit_template_args
                    ? "failed to resolve dependent explicit template call"
                    : "failed to resolve dependent qualified call after substitution";
        }
        return false;
    }
    expr = std::move(rewritten);
    return true;
}

std::unique_ptr<Expr> Collect::try_function_object_call_overload(
    std::unique_ptr<FuncCall>& call,
    SrcLoc loc) const {
    if (!lang_opts_.is_cxx_mode()) {
        return nullptr;
    }

    auto callee_record =
        remove_reference_and_desugar(
            call->func->get_type(),
            ast_ctx_.get())
            .as_shared<ObjectType>();
    if (!callee_record) {
        return nullptr;
    }

    // Treat class objects in callee position as potential `operator()` dispatch.
    bool had_member_match = false;
    bool had_template_member_match = false;
    bool saw_private_method = false;
    bool saw_protected_method = false;
    bool saw_template_instantiation = false;
    std::vector<OverloadCallCandidate> overload_candidates;
    if (auto candidate_error = append_member_overload_candidates(
            callee_record.get(),
            "operator()",
            call->func.get(),
            OverloadImplicitObjectArgKind::None,
            overload_candidates,
            had_member_match,
            saw_private_method,
            saw_protected_method,
            loc)) {
        return candidate_error;
    }
    if (auto template_candidate_error =
            append_member_template_overload_candidates(
                callee_record.get(),
                "operator()",
                call->func.get(),
                /*access_expr_is_arrow=*/false,
                call->args,
                overload_candidates,
                had_member_match,
                had_template_member_match,
                saw_private_method,
                saw_protected_method,
                saw_template_instantiation,
                loc)) {
        return template_candidate_error;
    }

    if (had_member_match && overload_candidates.empty()) {
        if (auto inaccessible_error = report_inaccessible_member(
            "operator()",
            saw_private_method,
            saw_protected_method,
            loc)) {
            return inaccessible_error;
        }
        if (had_template_member_match && !saw_template_instantiation) {
            report_error(
                "no matching member function template specialization for 'operator()'",
                loc);
            return collect_make<ErrorExpr>(
                "no matching member function template specialization",
                loc);
        }
        return nullptr;
    }
    if (overload_candidates.empty()) {
        return nullptr;
    }

    std::shared_ptr<Symbol> selected_symbol = nullptr;
    OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
        OverloadImplicitObjectArgKind::None;
    if (auto overload_error = select_overload_candidate(
            "operator()",
            overload_candidates,
            call->args,
            call->func.get(),
            loc,
            selected_symbol,
            selected_implicit_object_arg_kind)) {
        return overload_error;
    }
    if (!selected_symbol) {
        return nullptr;
    }
    if (auto completion_error =
            complete_selected_function_template_specialization_symbol(
                selected_symbol,
                loc,
                "failed to instantiate selected member function template specialization")) {
        return completion_error;
    }

    auto implicit_object_arg = build_overload_implicit_object_arg(
        selected_implicit_object_arg_kind,
        std::move(call->func),
        /*object_expr_is_pointer=*/false,
        loc);
    call->func = make_hidden_overload_callee(std::move(selected_symbol), loc);
    if (selected_implicit_object_arg_kind != OverloadImplicitObjectArgKind::None &&
        implicit_object_arg) {
        call->args.insert(call->args.begin(), std::move(implicit_object_arg));
    }
    return nullptr;
}

std::unique_ptr<Expr> Collect::try_builtin_or_overloaded_varref_call(
    std::unique_ptr<FuncCall>& call,
    SrcLoc loc) const {
    auto* var_ref = dyn_cast<VarRef>(call->func.get());
    if (!var_ref) {
        return nullptr;
    }

    const std::string& callee_name = var_ref->get_name();
    if (callee_name == "__builtin_va_start") {
        if (call->args.size() != 2) {
            report_error("__builtin_va_start requires exactly 2 arguments", loc);
            return collect_make<ErrorExpr>("invalid __builtin_va_start invocation", loc);
        }
        auto current_fn = desugar_type(func_state_.current_function_type).as_shared<FunctionType>();
        if (!current_fn || !current_fn->is_variadic) {
            report_error("cannot use __builtin_va_start in a non-variadic function", loc);
        }
        auto va_list_arg = std::move(call->args[0]);
        auto last_param = collect_apply_standard_conversions(
            std::move(call->args[1]), ExprUseContext::CallArgument);
        return collect_make<VaStartExpr>(
            std::move(va_list_arg), std::move(last_param), loc);
    }
    if (callee_name == "__builtin_va_copy") {
        if (call->args.size() != 2) {
            report_error("__builtin_va_copy requires exactly 2 arguments", loc);
            return collect_make<ErrorExpr>("invalid __builtin_va_copy invocation", loc);
        }
        auto dest_arg = std::move(call->args[0]);
        auto src_arg = std::move(call->args[1]);
        return collect_make<VaCopyExpr>(std::move(dest_arg), std::move(src_arg), loc);
    }
    if (callee_name == "__builtin_va_end") {
        if (call->args.size() != 1) {
            report_error("__builtin_va_end requires exactly 1 argument", loc);
            return collect_make<ErrorExpr>("invalid __builtin_va_end invocation", loc);
        }
        auto va_list_arg = std::move(call->args[0]);
        return collect_make<VaEndExpr>(std::move(va_list_arg), loc);
    }

    if (auto* builtin_info = BuiltinRegistry::instance().lookup(callee_name)) {
        if (!builtin_info->takes_type_arg) {
            int arg_count = static_cast<int>(call->args.size());
            if (arg_count < builtin_info->min_args) {
                report_error(
                    std::string(builtin_info->name) + " requires at least " +
                    std::to_string(builtin_info->min_args) + " argument(s)",
                    loc);
                return collect_make<ErrorExpr>("invalid builtin argument count", loc);
            }
            if (builtin_info->max_args >= 0 && arg_count > builtin_info->max_args) {
                report_error(
                    std::string(builtin_info->name) + " takes at most " +
                    std::to_string(builtin_info->max_args) + " argument(s)",
                    loc);
                return collect_make<ErrorExpr>("invalid builtin argument count", loc);
            }
            for (auto& arg : call->args) {
                arg = collect_apply_standard_conversions(
                    std::move(arg), ExprUseContext::CallArgument);
            }
            return builtin_call_expression(
                builtin_info->kind, std::move(call->args), loc);
        }
    }

    // Non-builtin identifier calls may still denote an overload set.
    if (auto overload_error = resolve_overloaded_function_call(
            call.get(), var_ref, loc)) {
        return overload_error;
    }
    return nullptr;
}

std::unique_ptr<Expr> Collect::try_member_function_overload_call(
    std::unique_ptr<FuncCall>& call,
    MemberCallSelection& member_call_selection,
    SrcLoc loc) const {
    auto* member_callee = dyn_cast<MemberExpr>(call->func.get());
    if (!member_callee) {
        return nullptr;
    }

    std::shared_ptr<ObjectType> record_type = nullptr;
    if (member_callee->base) {
        auto base_type = member_callee->base->get_type();
        auto semantic_base_type = desugar_type(base_type);
        if (member_callee->isArrow) {
            auto ptr_type = semantic_base_type.as_shared<PointerType>();
            if (ptr_type) {
                record_type =
                    desugar_type(ptr_type->pointed_type).as_shared<ObjectType>();
            }
        } else {
            record_type = semantic_base_type.as_shared<ObjectType>();
        }
    }

    bool had_member_match = false;
    bool had_template_member_match = false;
    bool saw_private_method = false;
    bool saw_protected_method = false;
    std::vector<OverloadCallCandidate> overload_candidates;
    if (auto candidate_error = append_member_overload_candidates(
            record_type.get(),
            member_callee->get_member_name(),
            member_callee->base.get(),
            OverloadImplicitObjectArgKind::None,
            overload_candidates,
            had_member_match,
            saw_private_method,
            saw_protected_method,
            loc)) {
        return candidate_error;
    }
    bool saw_template_instantiation = false;
    if (auto template_candidate_error =
            append_member_template_overload_candidates(
                record_type.get(),
                member_callee->get_member_name(),
                member_callee->base.get(),
                member_callee->isArrow != 0,
                call->args,
                overload_candidates,
                had_member_match,
                had_template_member_match,
                saw_private_method,
                saw_protected_method,
                saw_template_instantiation,
                loc)) {
        return template_candidate_error;
    }

    if (had_member_match && overload_candidates.empty()) {
        if (auto inaccessible_error = report_inaccessible_member(
                member_callee->get_member_name(),
                saw_private_method,
                saw_protected_method,
                loc)) {
            return inaccessible_error;
        }
        if (had_template_member_match && !saw_template_instantiation) {
            report_error(
                "no matching member function template specialization for '" +
                    member_callee->get_member_name() + "'",
                loc);
            return collect_make<ErrorExpr>(
                "no matching member function template specialization",
                loc);
        }
        return nullptr;
    }
    if (!(had_member_match && !overload_candidates.empty())) {
        return nullptr;
    }

    std::shared_ptr<Symbol> selected_symbol = nullptr;
    OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
        OverloadImplicitObjectArgKind::None;
    if (auto overload_error = select_overload_candidate(
            member_callee->get_member_name(),
            overload_candidates,
            call->args,
            member_callee->base.get(),
            loc,
            selected_symbol,
            selected_implicit_object_arg_kind)) {
        return overload_error;
    }
    if (!selected_symbol) {
        return nullptr;
    }

    if (auto completion_error =
            complete_selected_function_template_specialization_symbol(
                selected_symbol,
                loc,
                "failed to instantiate selected member function template specialization")) {
        return completion_error;
    }

    auto member_owner = std::unique_ptr<MemberExpr>(
        static_cast<MemberExpr*>(call->func.release()));
    member_call_selection.selected = true;
    member_call_selection.is_arrow = member_owner->isArrow;
    member_call_selection.name = member_owner->get_member_name();
    member_call_selection.suppress_virtual_dispatch =
        member_owner->suppress_virtual_dispatch != 0;
    member_call_selection.has_implicit_object_argument =
        selected_implicit_object_arg_kind != OverloadImplicitObjectArgKind::None;
    member_call_selection.symbol = selected_symbol;
    if (record_type) {
        member_call_selection.record_decl =
            canonical_record_decl(dyn_cast<ObjectDecl>(record_type->get_decl()));
    }
    auto implicit_object_arg = build_overload_implicit_object_arg(
        selected_implicit_object_arg_kind,
        std::move(member_owner->base),
        member_owner->isArrow,
        member_owner->location);

    call->func = collect_identifier_reference(
        member_owner->get_member_name(),
        std::move(selected_symbol),
        member_owner->location);
    if (selected_implicit_object_arg_kind != OverloadImplicitObjectArgKind::None &&
        implicit_object_arg) {
        call->args.insert(call->args.begin(), std::move(implicit_object_arg));
    }
    return nullptr;
}


std::unique_ptr<Expr> Collect::resolve_call_function_type(
    std::unique_ptr<FuncCall>& call,
    SrcLoc loc,
    CallFinalizationContext& context_out) const {
    auto callee_type = desugar_type(call->func->get_type());
    context_out.function_type = callee_type.as_shared<FunctionType>();
    if (!context_out.function_type) {
        auto ptr = callee_type.as_shared<PointerType>();
        if (ptr) {
            context_out.function_type =
                desugar_type(ptr->pointed_type).as_shared<FunctionType>();
        }
    }
    if (!context_out.function_type) {
        auto block_ptr = callee_type.as_shared<BlockPointerType>();
        if (block_ptr) {
            context_out.function_type =
                desugar_type(block_ptr->pointed_type).as_shared<FunctionType>();
        }
    }
    if (!context_out.function_type) {
        if (auto* var_ref = dyn_cast<VarRef>(call->func.get())) {
            if (!var_ref->symref && lang_opts_.implicit_function_declarations) {
                auto fn_type = std::make_shared<FunctionType>();
                fn_type->ret_type = QualType(get_builtin_int());
                fn_type->has_prototype = false;
                fn_type->is_variadic = false;
                var_ref->symref = std::make_shared<Symbol>(
                    var_ref->get_name(),
                    SymbolKind::FUNCTION,
                    QualType(fn_type),
                    StorageClass::EXTERN,
                    VariableLinkage::EXTERNAL);
                context_out.function_type = fn_type;
            }
        }
    }
    if (context_out.function_type) {
        return nullptr;
    }

    if (!lang_opts_.implicit_function_declarations) {
        report_error("function call target is not a function or function pointer", loc);
    }
    call->ctype = QualType(get_builtin_int());
    for (auto& arg : call->args) {
        arg = collect_apply_standard_conversions(
            std::move(arg), ExprUseContext::CallArgument);
    }
    return std::unique_ptr<Expr>(std::move(call));
}

void Collect::capture_call_target_metadata(
    FuncCall* call,
    CallFinalizationContext& context_out) const {
    if (lang_opts_.is_cxx_mode()) {
        if (auto* callee_ref = dyn_cast<VarRef>(call->func.get())) {
            std::shared_ptr<ObjectType> constructor_owner_type = nullptr;
            if (classify_constructor_symbol_call(
                    callee_ref->symref, constructor_owner_type, ast_ctx_.get())) {
                context_out.constructor_call = true;
                context_out.constructor_symbol = callee_ref->symref;
                context_out.constructor_object_type = QualType(constructor_owner_type);
            }
        }
    }
    if (auto* callee_ref = dyn_cast<VarRef>(strip_implicit_casts(call->func.get()))) {
        context_out.callee_symbol = callee_ref->symref;
    }
}

void Collect::configure_call_parameter_counts(
    Expr* raw_member_pointer_callee,
    CallFinalizationContext& context_out,
    SrcLoc loc) const {
    bool has_void_param = (context_out.function_type->parameters.size() == 1 &&
                           context_out.function_type->parameters[0]->isVoid());
    context_out.named_param_count =
        has_void_param ? 0 : context_out.function_type->parameters.size();
    if (context_out.constructor_call && context_out.named_param_count > 0) {
        context_out.implicit_param_count = 1;
    }
    if (context_out.member_pointer_function_call) {
        // Member-pointer function lowering may synthesize an explicit object argument.
        // Detect that pattern by checking owner compatibility with the first parameter.
        auto* member_ptr_callee =
            dyn_cast<MemberPointerAccessExpr>(raw_member_pointer_callee);
        auto member_ptr_type = member_ptr_callee && member_ptr_callee->member_pointer
            ? desugar_type(member_ptr_callee->member_pointer->get_type())
                  .as_shared<MemberPointerType>()
            : nullptr;
        if (member_ptr_type && context_out.named_param_count > 0) {
            QualType first_param_type = remove_reference(decay_parameter_type(
                context_out.function_type->parameters[0]));
            auto first_param_ptr =
                desugar_type(first_param_type).as_shared<PointerType>();
            auto first_param_owner = first_param_ptr
                ? desugar_type(first_param_ptr->pointed_type).as_shared<ObjectType>()
                : nullptr;
            auto member_ptr_owner =
                desugar_type(member_ptr_type->class_type).as_shared<ObjectType>();
            if (first_param_ptr && first_param_owner && member_ptr_owner) {
                bool owner_compatible =
                    first_param_ptr->pointed_type.equals_unqualified(
                        member_ptr_type->class_type) ||
                    can_convert_derived_to_base_object(
                        member_ptr_type->class_type,
                        first_param_ptr->pointed_type) ||
                    can_convert_derived_to_base_object(
                        first_param_ptr->pointed_type,
                        member_ptr_type->class_type);
                if (owner_compatible) {
                    context_out.implicit_param_count = 1;
                }
            }
        }
    }

    if (context_out.named_param_count >= context_out.implicit_param_count) {
        context_out.explicit_named_param_count =
            context_out.named_param_count - context_out.implicit_param_count;
    } else {
        report_error(
            "member-function pointer call target has invalid parameter list",
            loc);
    }

    size_t trailing_default_arg_count = count_trailing_default_arguments_for_call(
        context_out.callee_symbol,
        context_out.named_param_count,
        context_out.implicit_param_count);
    if (trailing_default_arg_count > context_out.explicit_named_param_count) {
        trailing_default_arg_count = context_out.explicit_named_param_count;
    }
    context_out.required_explicit_named_param_count =
        context_out.explicit_named_param_count - trailing_default_arg_count;
}

void Collect::validate_call_argument_count(
    size_t provided_arg_count,
    const CallFinalizationContext& context,
    SrcLoc loc) const {
    if (!context.function_type->has_prototype) {
        return;
    }
    if (context.function_type->is_variadic) {
        if (provided_arg_count < context.required_explicit_named_param_count) {
            report_error("too few arguments to variadic function call", loc);
        }
        return;
    }
    if (provided_arg_count < context.required_explicit_named_param_count ||
        provided_arg_count > context.explicit_named_param_count) {
        report_error("function call argument count does not match declaration", loc);
    }
}

std::unique_ptr<Expr> Collect::prepare_call_finalization(
    std::unique_ptr<FuncCall>& call,
    SrcLoc loc,
    CallFinalizationContext& context_out) const {
    context_out = CallFinalizationContext{};

    Expr* raw_member_pointer_callee = strip_implicit_casts(call->func.get());
    context_out.member_pointer_function_call =
        dyn_cast<MemberPointerAccessExpr>(raw_member_pointer_callee) != nullptr;

    if (auto early_result = resolve_call_function_type(call, loc, context_out)) {
        return early_result;
    }
    capture_call_target_metadata(call.get(), context_out);
    configure_call_parameter_counts(
        raw_member_pointer_callee, context_out, loc);
    validate_call_argument_count(call->args.size(), context_out, loc);
    return nullptr;
}

std::unique_ptr<Expr> Collect::append_missing_call_default_arguments(
    FuncCall* call,
    const CallFinalizationContext& context,
    SrcLoc loc) const {
    if (!context.function_type->has_prototype ||
        call->args.size() >= context.explicit_named_param_count) {
        return nullptr;
    }

    for (size_t arg_index = call->args.size();
         arg_index < context.explicit_named_param_count;
         ++arg_index) {
        size_t param_index = arg_index + context.implicit_param_count;
        const Expr* default_expr =
            lookup_default_argument_for_param(context.callee_symbol, param_index);
        if (!default_expr) {
            report_error("function call argument count does not match declaration", loc);
            return collect_make<ErrorExpr>("missing default argument", loc);
        }
        std::string clone_error;
        // Default args are parsed once on the declaration; clone here so each call
        // owns an independent expression subtree.
        auto cloned_default = clone_expr_tree(
            default_expr, ast_ctx_.get(), &clone_error);
        if (!cloned_default) {
            std::string message = clone_error.empty()
                ? "default argument expression is not supported"
                : "default argument expression is not supported: " + clone_error;
            report_error(message, default_expr->location);
            return collect_make<ErrorExpr>(
                "unsupported default argument expression", loc);
        }
        call->args.push_back(std::move(cloned_default));
    }
    return nullptr;
}

std::unique_ptr<Expr> Collect::convert_call_argument_to_parameter(
    std::unique_ptr<Expr> arg,
    QualType param_type,
    SrcLoc loc) const {
    if (canonical_type_kind(param_type) == TypeKind::Reference) {
        // References keep value category semantics, so we run C++ overload-style
        // conversion checks instead of flattening through standard conversions.
        auto seq = build_cpp_overload_conversion_sequence(arg.get(), param_type);
        if (!seq.viable) {
            report_conversion_failure(
                "function argument",
                arg ? arg->get_type() : QualType(),
                param_type,
                arg ? arg->location : loc);
        } else if (seq.kind == ConversionSequenceKind::UserDefined) {
            SrcLoc arg_loc = arg ? arg->location : loc;
            arg = build_cpp_user_defined_conversion_expr(
                std::move(arg), param_type, arg_loc);
        }
        return arg;
    }

    if (canonical_type_kind(param_type) == TypeKind::Object &&
        dyn_cast<InitListExpr>(Collect::strip_implicit_casts(arg.get()))) {
        SrcLoc arg_loc = arg ? arg->location : loc;
        arg = convert_cpp_braced_init_argument(
            std::move(arg), param_type, arg_loc);
        if (!arg || isa<ErrorExpr>(arg.get())) {
            report_conversion_failure(
                "function argument",
                QualType(),
                param_type,
                arg_loc);
        }
        return arg;
    }

    bool handled_cpp_argument_conversion = false;
    if (lang_opts_.is_cxx_mode()) {
        // Class arguments may need conversion operators/constructors before the
        // regular C argument conversion pipeline.
        auto seq = build_cpp_overload_conversion_sequence(arg.get(), param_type);
        if (!seq.viable) {
            report_conversion_failure(
                "function argument",
                arg ? arg->get_type() : QualType(),
                param_type,
                arg ? arg->location : loc);
        } else if (seq.kind == ConversionSequenceKind::UserDefined) {
            SrcLoc arg_loc = arg ? arg->location : loc;
            arg = build_cpp_user_defined_conversion_expr(
                std::move(arg), param_type, arg_loc);
            arg = cast_if_needed(std::move(arg), param_type);
            handled_cpp_argument_conversion = true;
        } else {
            auto source_canonical =
                remove_reference_and_desugar(
                    arg ? arg->get_type() : QualType(),
                    ast_ctx_.get());
            auto target_canonical = desugar_type(param_type, ast_ctx_.get());
            if (source_canonical &&
                target_canonical &&
                source_canonical->kind == TypeKind::Object &&
                target_canonical->kind == TypeKind::Object &&
                source_canonical.equals_unqualified(target_canonical)) {
                arg = collect_apply_standard_conversions(
                    std::move(arg),
                    ExprUseContext::CallArgument);
                handled_cpp_argument_conversion = true;
            }
        }
    }

    if (!handled_cpp_argument_conversion) {
        arg = collect_apply_standard_conversions(
            std::move(arg), ExprUseContext::CallArgument);
        QualType arg_type = arg ? arg->get_type() : QualType();
        auto seq = build_implicit_conversion_sequence(
            arg_type,
            param_type,
            ExprUseContext::CallArgument);
        bool conversion_viable = seq.viable;
        if (!conversion_viable &&
            (canonical_type_kind(param_type) == TypeKind::Pointer ||
             canonical_type_kind(param_type) == TypeKind::BlockPointer) &&
            is_null_pointer_constant_expr(arg.get())) {
            conversion_viable = true;
        }
        if (!conversion_viable &&
            is_transparent_union_call_argument_viable(
                arg.get(), param_type)) {
            conversion_viable = true;
        }
        if (!conversion_viable && !lang_opts_.is_cxx_mode()) {
            auto param_kind = canonical_type_kind(param_type, ast_ctx_.get());
            auto arg_kind = canonical_type_kind(arg_type, ast_ctx_.get());
            if (param_kind == TypeKind::Pointer && arg_kind == TypeKind::Pointer) {
                auto param_ptr =
                    desugar_type(param_type, ast_ctx_.get()).as_shared<PointerType>();
                auto arg_ptr =
                    desugar_type(arg_type, ast_ctx_.get()).as_shared<PointerType>();
                bool param_void =
                    param_ptr && param_ptr->pointed_type && param_ptr->pointed_type->isVoid();
                bool arg_void =
                    arg_ptr && arg_ptr->pointed_type && arg_ptr->pointed_type->isVoid();
                if (!param_void && !arg_void) {
                    report_warning(
                        "incompatible pointer types passing '" +
                            arg_type.to_string() + "' to parameter of type '" +
                            param_type.to_string() + "'",
                        arg ? arg->location : loc);
                }
                conversion_viable = true;
            } else if (param_kind == TypeKind::BlockPointer &&
                       arg_kind == TypeKind::BlockPointer) {
                conversion_viable = true;
            } else if (param_kind == TypeKind::Pointer && arg_type &&
                       arg_type->isInteger()) {
                if (!is_null_pointer_constant_expr(arg.get())) {
                    report_warning(
                        "incompatible integer to pointer conversion passing '" +
                            arg_type.to_string() + "' to parameter of type '" +
                            param_type.to_string() + "'",
                        arg ? arg->location : loc);
                }
                conversion_viable = true;
            } else if (param_kind == TypeKind::BlockPointer && arg_type &&
                       arg_type->isInteger()) {
                if (!is_null_pointer_constant_expr(arg.get())) {
                    report_warning(
                        "incompatible integer to block pointer conversion passing '" +
                            arg_type.to_string() + "' to parameter of type '" +
                            param_type.to_string() + "'",
                        arg ? arg->location : loc);
                }
                conversion_viable = true;
            } else if (param_type && param_type->isInteger() &&
                       (arg_kind == TypeKind::Pointer ||
                        arg_kind == TypeKind::BlockPointer)) {
                bool param_is_bool = false;
                if (auto param_builtin = desugar_type(param_type, ast_ctx_.get())
                                             .as_shared<BuiltinType>()) {
                    param_is_bool =
                        param_builtin->builtin_kind == BuiltinTypes::Bool;
                }
                if (!param_is_bool) {
                    report_warning(
                        "incompatible pointer to integer conversion passing '" +
                            arg_type.to_string() + "' to parameter of type '" +
                            param_type.to_string() + "'",
                        arg ? arg->location : loc);
                }
                conversion_viable = true;
            }
        }
        if (!conversion_viable) {
            report_conversion_failure(
                "function argument",
                arg_type,
                param_type,
                arg ? arg->location : loc);
        }
        arg = cast_if_needed(std::move(arg), param_type);
    }
    return arg;
}

bool Collect::is_transparent_union_call_argument_viable(
    Expr* arg,
    QualType param_type) const {
    auto param_record = desugar_type(param_type).as_shared<ObjectType>();
    if (!param_record || !param_record->is_union ||
        !param_record->is_transparent_union) {
        return false;
    }

    QualType arg_type = arg ? arg->get_type() : QualType();
    for (const auto& field : get_record_fields_for_type_matching(param_record.get())) {
        QualType member_type = decay_parameter_type(field.type);
        auto member_seq = build_implicit_conversion_sequence(
            arg_type,
            member_type,
            ExprUseContext::CallArgument);
        if (member_seq.viable) {
            return true;
        }
        if (canonical_type_kind(member_type) == TypeKind::Pointer &&
            is_null_pointer_constant_expr(arg)) {
            return true;
        }
    }
    return false;
}

std::unique_ptr<Expr> Collect::apply_variadic_call_argument_conversions(
    std::unique_ptr<Expr> arg) const {
    arg = collect_apply_standard_conversions(
        std::move(arg), ExprUseContext::CallArgument);
    return apply_default_argument_promotions(std::move(arg));
}

void Collect::convert_call_arguments(
    FuncCall* call,
    const CallFinalizationContext& context,
    SrcLoc loc) const {
    for (size_t i = 0; i < call->args.size(); ++i) {
        auto arg = std::move(call->args[i]);
        if (context.function_type->has_prototype) {
            if (i < context.explicit_named_param_count) {
                // Parameter indexing is shifted when the call target carries a hidden
                // implicit object/constructor argument.
                size_t param_index = i + context.implicit_param_count;
                QualType param_type =
                    decay_parameter_type(context.function_type->parameters[param_index]);
                arg = convert_call_argument_to_parameter(
                    std::move(arg), param_type, loc);
            } else if (context.function_type->is_variadic) {
                arg = apply_variadic_call_argument_conversions(std::move(arg));
            }
        } else {
            arg = apply_variadic_call_argument_conversions(std::move(arg));
        }
        call->args[i] = std::move(arg);
    }
}

std::unique_ptr<Expr> Collect::wrap_member_call_expression(
    std::unique_ptr<FuncCall> call,
    const MemberCallSelection& member_call_selection,
    SrcLoc loc) const {
    if (!member_call_selection.selected) {
        return call;
    }

    auto member_call = collect_make<CppMemberCallExpr>(
        std::move(call),
        member_call_selection.name,
        member_call_selection.is_arrow,
        member_call_selection.suppress_virtual_dispatch,
        member_call_selection.has_implicit_object_argument,
        loc);
    if (ast_ctx_ &&
        member_call_selection.has_implicit_object_argument &&
        !member_call_selection.suppress_virtual_dispatch &&
        member_call_selection.symbol) {
        // Record virtual-call metadata on the wrapper node so lowering can decide
        // between direct and vtable dispatch without re-running overload lookup.
        const ObjectDecl* static_record_decl = member_call_selection.record_decl;
        if (!static_record_decl && member_call->lowered_call &&
            !member_call->lowered_call->args.empty()) {
            auto this_type =
                desugar_type(member_call->lowered_call->args.front()->get_type());
            auto this_ptr_type = this_type.as_shared<PointerType>();
            if (this_ptr_type) {
                auto this_record =
                    desugar_type(this_ptr_type->pointed_type).as_shared<ObjectType>();
                if (this_record) {
                    static_record_decl = canonical_record_decl(
                        dyn_cast<ObjectDecl>(this_record->get_decl()));
                }
            }
        }
        if (static_record_decl) {
            VirtualMethodLookupResult selected_method_lookup =
                find_virtual_method_by_symbol(
                    static_record_decl, member_call_selection.symbol);
            const auto* selected_method = selected_method_lookup.method;
            if (selected_method &&
                selected_method->is_virtual &&
                !selected_method->is_static &&
                selected_method->virtual_slot_index >= 0) {
                CppVirtualCallInfo call_info;
                call_info.slot_index =
                    static_cast<uint32_t>(selected_method->virtual_slot_index);
                call_info.this_adjustment = 0;
                if (selected_method_lookup.owner_record_decl &&
                    selected_method_lookup.owner_record_decl !=
                        static_record_decl) {
                    auto maybe_offset = find_base_subobject_offset(
                        static_record_decl,
                        selected_method_lookup.owner_record_decl);
                    if (maybe_offset.has_value() &&
                        *maybe_offset <=
                            static_cast<size_t>(std::numeric_limits<int32_t>::max())) {
                        call_info.this_adjustment =
                            static_cast<int32_t>(*maybe_offset);
                    }
                }
                call_info.static_record_decl = static_record_decl;
                call_info.static_symbol = member_call_selection.symbol;
                ast_ctx_->set_cpp_virtual_call_info(
                    member_call->node_id, std::move(call_info));
            }
        }
    }
    return member_call;
}

std::unique_ptr<Expr> Collect::finalize_call_expression(
    std::unique_ptr<FuncCall> call,
    const MemberCallSelection& member_call_selection,
    SrcLoc loc) const {
    CallFinalizationContext context;
    if (auto early_result = prepare_call_finalization(call, loc, context)) {
        return early_result;
    }
    if (context.callee_symbol) {
        note_specialization_use_for_symbol(context.callee_symbol, loc);
    } else if (context.constructor_call && context.constructor_symbol) {
        note_specialization_use_for_symbol(context.constructor_symbol, loc);
    }
    if (auto default_arg_error = append_missing_call_default_arguments(
            call.get(), context, loc)) {
        return default_arg_error;
    }

    call->func = collect_apply_standard_conversions(
        std::move(call->func), ExprUseContext::CallCallee);
    convert_call_arguments(call.get(), context, loc);

    if (context.constructor_call &&
        context.constructor_symbol &&
        context.constructor_object_type) {
        return collect_make<CppConstructExpr>(
            context.constructor_symbol,
            std::move(call->args),
            context.constructor_object_type,
            false,
            loc);
    }

    call->ctype = context.function_type->ret_type;
    return wrap_member_call_expression(
        std::move(call), member_call_selection, loc);
}
