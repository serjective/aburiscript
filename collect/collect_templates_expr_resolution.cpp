#include "collect.h"
#include "collect_internal.h"
#include "collect_templates_internal.h"
#include "../helpers/auto_type_utils.h"

#include <utility>

using namespace collect_internal;

namespace {
bool type_has_undeduced_auto_placeholder(QualType type) {
    return type &&
           auto_type_utils::auto_type_flavors_in(type.get_shared()) != 0;
}

bool symbol_names_undeduced_auto_variable(const std::shared_ptr<Symbol>& sym) {
    if (!sym || !sym->variable_definition) {
        return false;
    }
    return type_has_undeduced_auto_placeholder(sym->type) ||
           type_has_undeduced_auto_placeholder(
               sym->variable_definition->type);
}

bool any_expr_references_undeduced_auto_variable(
    const std::vector<std::unique_ptr<Expr>>& exprs);

bool expr_references_undeduced_auto_variable(const Expr* expr) {
    if (!expr) {
        return false;
    }

    switch (expr->get_kind()) {
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef:
            return symbol_names_undeduced_auto_variable(
                static_cast<const VarRef*>(expr)->symref);
        case StmtKind::ImplicitCast:
            return expr_references_undeduced_auto_variable(
                static_cast<const ImplicitCast*>(expr)->expr.get());
        case StmtKind::ExplicitCast:
            return expr_references_undeduced_auto_variable(
                static_cast<const ExplicitCast*>(expr)->expr.get());
        case StmtKind::ParenExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const ParenExpr*>(expr)->subexpr.get());
        case StmtKind::UnaryOperation:
            return expr_references_undeduced_auto_variable(
                static_cast<const UnaryOperation*>(expr)->exp.get());
        case StmtKind::DependentUnaryExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const DependentUnaryExpr*>(expr)->operand.get());
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(expr);
            return expr_references_undeduced_auto_variable(binary->left.get()) ||
                   expr_references_undeduced_auto_variable(binary->right.get());
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* binary = static_cast<const DependentBinaryExpr*>(expr);
            return expr_references_undeduced_auto_variable(binary->left.get()) ||
                   expr_references_undeduced_auto_variable(binary->right.get());
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* binary =
                static_cast<const CompoundAssignOperation*>(expr);
            return expr_references_undeduced_auto_variable(binary->left.get()) ||
                   expr_references_undeduced_auto_variable(binary->right.get());
        }
        case StmtKind::CondExpr: {
            const auto* cond = static_cast<const CondExpr*>(expr);
            return expr_references_undeduced_auto_variable(
                       cond->condition.get()) ||
                   expr_references_undeduced_auto_variable(
                       cond->true_expr.get()) ||
                   expr_references_undeduced_auto_variable(
                       cond->false_expr.get());
        }
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(expr);
            return expr_references_undeduced_auto_variable(call->func.get()) ||
                   any_expr_references_undeduced_auto_variable(call->args);
        }
        case StmtKind::DependentCallExpr: {
            const auto* call = static_cast<const DependentCallExpr*>(expr);
            return expr_references_undeduced_auto_variable(
                       call->callee.get()) ||
                   any_expr_references_undeduced_auto_variable(call->args);
        }
        case StmtKind::CppMemberCallExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const CppMemberCallExpr*>(expr)
                    ->lowered_call.get());
        case StmtKind::MemberExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const MemberExpr*>(expr)->base.get());
        case StmtKind::UnresolvedMemberExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const UnresolvedMemberExpr*>(expr)->base.get());
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const ArraySubscriptExpr*>(expr);
            return expr_references_undeduced_auto_variable(
                       subscript->array.get()) ||
                   expr_references_undeduced_auto_variable(
                       subscript->index.get());
        }
        case StmtKind::DependentArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const DependentArraySubscriptExpr*>(expr);
            return expr_references_undeduced_auto_variable(
                       subscript->array.get()) ||
                   expr_references_undeduced_auto_variable(
                       subscript->index.get());
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* access =
                static_cast<const MemberPointerAccessExpr*>(expr);
            return expr_references_undeduced_auto_variable(
                       access->base.get()) ||
                   expr_references_undeduced_auto_variable(
                       access->member_pointer.get());
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            const auto* access =
                static_cast<const DependentMemberPointerAccessExpr*>(expr);
            return expr_references_undeduced_auto_variable(
                       access->base.get()) ||
                   expr_references_undeduced_auto_variable(
                       access->member_pointer.get());
        }
        case StmtKind::CppFunctionStyleCastExpr:
            return any_expr_references_undeduced_auto_variable(
                static_cast<const CppFunctionStyleCastExpr*>(expr)->args);
        case StmtKind::CppConstructExpr:
            return any_expr_references_undeduced_auto_variable(
                static_cast<const CppConstructExpr*>(expr)->args);
        case StmtKind::InitListExpr: {
            const auto* init_list = static_cast<const InitListExpr*>(expr);
            for (const auto& element : init_list->elements) {
                if (expr_references_undeduced_auto_variable(
                        element.value.get())) {
                    return true;
                }
                for (const auto& designator : element.designators) {
                    if (expr_references_undeduced_auto_variable(
                            designator.index.get()) ||
                        expr_references_undeduced_auto_variable(
                            designator.range_end.get())) {
                        return true;
                    }
                }
            }
            return false;
        }
        case StmtKind::CppNewExpr: {
            const auto* new_expr = static_cast<const CppNewExpr*>(expr);
            return any_expr_references_undeduced_auto_variable(
                       new_expr->placement_args) ||
                   expr_references_undeduced_auto_variable(
                       new_expr->initializer.get()) ||
                   any_expr_references_undeduced_auto_variable(
                       new_expr->constructor_args);
        }
        case StmtKind::CppDeleteExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const CppDeleteExpr*>(expr)->operand.get());
        case StmtKind::CppNoexceptExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const CppNoexceptExpr*>(expr)->operand.get());
        case StmtKind::CppPseudoDestructorExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const CppPseudoDestructorExpr*>(expr)->base.get());
        case StmtKind::CppDynamicCastExpr:
            return expr_references_undeduced_auto_variable(
                static_cast<const CppDynamicCastExpr*>(expr)->expr.get());
        case StmtKind::CppTypeIdExpr: {
            const auto* typeid_expr = static_cast<const CppTypeIdExpr*>(expr);
            return !typeid_expr->is_type_operand &&
                   expr_references_undeduced_auto_variable(
                       typeid_expr->expr_operand.get());
        }
        default:
            return false;
    }
}

bool any_expr_references_undeduced_auto_variable(
    const std::vector<std::unique_ptr<Expr>>& exprs) {
    for (const auto& expr : exprs) {
        if (expr_references_undeduced_auto_variable(expr.get())) {
            return true;
        }
    }
    return false;
}

class ScopedLexicalLookupContext {
public:
    ScopedLexicalLookupContext(
        Collect& collect,
        std::shared_ptr<Scope> lookup_scope,
        std::shared_ptr<DeclContext> lookup_context)
        : collect_(collect),
          saved_scope_(collect.collect_current_scope()),
          saved_context_(collect.get_current_decl_context()) {
        if (!lookup_scope && !lookup_context) {
            return;
        }
        active_ = true;
        if (lookup_scope) {
            if (lookup_context) {
                active_scope_ =
                    clone_scope_chain_with_live_decl_contexts(
                        lookup_scope,
                        lookup_context.get());
                collect_.collect_set_current_scope(active_scope_);
            } else {
                collect_.collect_set_current_scope(std::move(lookup_scope));
            }
        }
        if (lookup_context) {
            collect_.set_current_decl_context(std::move(lookup_context));
        }
    }

    ~ScopedLexicalLookupContext() {
        if (!active_) {
            return;
        }
        collect_.collect_set_current_scope(std::move(saved_scope_));
        collect_.set_current_decl_context(std::move(saved_context_));
    }

private:
    Collect& collect_;
    std::shared_ptr<Scope> saved_scope_;
    std::shared_ptr<DeclContext> saved_context_;
    std::shared_ptr<Scope> active_scope_;
    bool active_ = false;

    static std::shared_ptr<Scope> clone_scope_chain_with_live_decl_contexts(
        const std::shared_ptr<Scope>& scope,
        DeclContext* current_context) {
        if (!scope) {
            return nullptr;
        }
        auto cloned = std::make_shared<Scope>(*scope);
        cloned->associated_decl_context = current_context;
        cloned->parent = clone_scope_chain_with_live_decl_contexts(
            scope->parent,
            current_context ? current_context->lexical_parent() : nullptr);
        return cloned;
    }
};

Expr* strip_implicit_casts_and_parens(Expr* expr) {
    Expr* current = Collect::strip_implicit_casts(expr);
    while (auto* paren = dyn_cast<ParenExpr>(current)) {
        current = Collect::strip_implicit_casts(paren->subexpr.get());
    }
    return current;
}

// TODO: we need to do the type on the root of expr node soon, because every expr has an assc type
void store_explicit_expr_type(Expr* candidate, QualType realized_type) {
    if (!candidate || !realized_type) {
        return;
    }
    switch (candidate->get_kind()) {
        case StmtKind::UnresolvedLookupExpr:
            static_cast<UnresolvedLookupExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::LabelAddressExpr:
            static_cast<LabelAddressExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::FuncCall:
            static_cast<FuncCall*>(candidate)->ctype = realized_type;
            return;
        case StmtKind::DependentCallExpr:
            static_cast<DependentCallExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::DependentArraySubscriptExpr:
            static_cast<DependentArraySubscriptExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CppMemberCallExpr:
            static_cast<CppMemberCallExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CppConstructExpr:
            static_cast<CppConstructExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CppValueInitExpr:
            static_cast<CppValueInitExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CppFunctionStyleCastExpr:
            static_cast<CppFunctionStyleCastExpr*>(candidate)->target_type =
                realized_type;
            return;
        case StmtKind::ParenExpr:
            store_explicit_expr_type(
                static_cast<ParenExpr*>(candidate)->subexpr.get(),
                realized_type);
            return;
        case StmtKind::CondExpr:
            static_cast<CondExpr*>(candidate)->type = realized_type;
            return;
        case StmtKind::UnaryOperation:
            static_cast<UnaryOperation*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::DependentUnaryExpr:
            static_cast<DependentUnaryExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::BinaryOperation:
            static_cast<BinaryOperation*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CppBuiltinThreeWayCompareExpr:
            static_cast<CppBuiltinThreeWayCompareExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CompoundAssignOperation:
            static_cast<CompoundAssignOperation*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::DependentBinaryExpr:
            static_cast<DependentBinaryExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::ImplicitCast:
            static_cast<ImplicitCast*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::ExplicitCast:
            static_cast<ExplicitCast*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::ArraySubscriptExpr:
            static_cast<ArraySubscriptExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::MemberExpr:
            static_cast<MemberExpr*>(candidate)->member_type =
                realized_type;
            return;
        case StmtKind::DependentMemberPointerAccessExpr:
            static_cast<DependentMemberPointerAccessExpr*>(candidate)
                ->ctype = realized_type;
            return;
        case StmtKind::CppTypeIdExpr:
            static_cast<CppTypeIdExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CppDynamicCastExpr:
            static_cast<CppDynamicCastExpr*>(candidate)->target_type =
                realized_type;
            return;
        case StmtKind::CppNoexceptExpr:
            static_cast<CppNoexceptExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::CppPseudoDestructorExpr:
            static_cast<CppPseudoDestructorExpr*>(candidate)->ctype =
                realized_type;
            return;
        case StmtKind::BuiltinCallExpr:
            static_cast<BuiltinCallExpr*>(candidate)->result_type =
                realized_type;
            return;
        case StmtKind::ConceptSpecializationExpr:
            static_cast<ConceptSpecializationExpr*>(candidate)->result_type =
                realized_type;
            return;
        default:
            return;
    }
}

}

struct Collect::PostSubstitutionExprResolver {
    explicit PostSubstitutionExprResolver(Collect& collect)
        : collect_(collect), ast_ctx_(collect.ast_ctx_) {}

    bool resolve_dependent_expr_after_substitution(
        std::unique_ptr<Expr>& expr,
        QualType implicit_this_type,
        std::string* error_out,
        PostSubstitutionExprUse expr_use = PostSubstitutionExprUse::Value);

private:
    Collect& collect_;
    std::shared_ptr<ASTContext>& ast_ctx_;

    template <typename NodeT, typename... Args>
    std::unique_ptr<NodeT> collect_make(Args&&... args) const {
        return collect_.template collect_make<NodeT>(
            std::forward<Args>(args)...);
    }

    static Expr* strip_implicit_casts(Expr* expr) {
        return Collect::strip_implicit_casts(expr);
    }

#define ABURI_FORWARD_COLLECT_METHOD(name)                               \
    template <typename... Args>                                           \
    decltype(auto) name(Args&&... args) {                                 \
        return collect_.name(std::forward<Args>(args)...);                \
    }
    ABURI_FORWARD_COLLECT_METHOD(contains_deferred_semantic_type)
    ABURI_FORWARD_COLLECT_METHOD(try_realize_deferred_semantic_type)
    ABURI_FORWARD_COLLECT_METHOD(finalize_deferred_semantic_type)
    ABURI_FORWARD_COLLECT_METHOD(expression_depends_on_template_parameters)
    ABURI_FORWARD_COLLECT_METHOD(normalize_dependent_lookup_qualifier_after_substitution)
    ABURI_FORWARD_COLLECT_METHOD(collect_identifier_reference)
    ABURI_FORWARD_COLLECT_METHOD(collect_apply_standard_conversions)
    ABURI_FORWARD_COLLECT_METHOD(cast_if_needed)
    ABURI_FORWARD_COLLECT_METHOD(check_cpp_const_cast)
    ABURI_FORWARD_COLLECT_METHOD(cpp_static_named_cast)
    ABURI_FORWARD_COLLECT_METHOD(cpp_reinterpret_named_cast)
    ABURI_FORWARD_COLLECT_METHOD(collect_cpp_function_style_cast)
    ABURI_FORWARD_COLLECT_METHOD(collect_cpp_type_list_initialization_expression)
    ABURI_FORWARD_COLLECT_METHOD(resolve_class_template_argument_deduction)
    ABURI_FORWARD_COLLECT_METHOD(collect_cpp_new_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_member_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_conditional_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_finalize_block_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_finalize_cpp_lambda_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_builtin_type_trait_expression)
    ABURI_FORWARD_COLLECT_METHOD(finalize_sizeof_node)
    ABURI_FORWARD_COLLECT_METHOD(finalize_alignof_node)
    ABURI_FORWARD_COLLECT_METHOD(finalize_offsetof_node)
    ABURI_FORWARD_COLLECT_METHOD(collect_cpp_noexcept_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_cpp_named_cast)
    ABURI_FORWARD_COLLECT_METHOD(collect_cpp_delete_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_cpp_pseudo_destructor_expression)
    ABURI_FORWARD_COLLECT_METHOD(materialize_concrete_qualified_lookup_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_explicit_template_id_impl)
    ABURI_FORWARD_COLLECT_METHOD(realize_deferred_expr_type_after_substitution)
    ABURI_FORWARD_COLLECT_METHOD(collect_unary_operation)
    ABURI_FORWARD_COLLECT_METHOD(collect_binary_operation)
    ABURI_FORWARD_COLLECT_METHOD(collect_array_subscript)
    ABURI_FORWARD_COLLECT_METHOD(collect_member_pointer_access_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_function_call)
    ABURI_FORWARD_COLLECT_METHOD(try_function_object_call_overload)
    ABURI_FORWARD_COLLECT_METHOD(try_builtin_or_overloaded_varref_call)
    ABURI_FORWARD_COLLECT_METHOD(try_member_function_overload_call)
    ABURI_FORWARD_COLLECT_METHOD(finalize_call_expression)
    ABURI_FORWARD_COLLECT_METHOD(collect_explicit_template_call_impl)
    ABURI_FORWARD_COLLECT_METHOD(make_hidden_overload_callee)
#undef ABURI_FORWARD_COLLECT_METHOD
};

bool Collect::resolve_dependent_expr_after_substitution(
    std::unique_ptr<Expr>& expr,
    QualType implicit_this_type,
    std::string* error_out,
    PostSubstitutionExprUse expr_use) {
    PostSubstitutionExprResolver resolver(*this);
    return resolver.resolve_dependent_expr_after_substitution(
        expr,
        implicit_this_type,
        error_out,
        expr_use);
}

bool Collect::PostSubstitutionExprResolver::resolve_dependent_expr_after_substitution(
    std::unique_ptr<Expr>& expr,
    QualType implicit_this_type,
    std::string* error_out,
    PostSubstitutionExprUse expr_use) {
    auto implicit_cast_kind_can_be_stripped_after_substitution =
        [](ImplicitCastTypes kind) {
            switch (kind) {
                case ImplicitCastTypes::LVALUE_TO_RVALUE:
                case ImplicitCastTypes::FUNCTION_TO_POINTER:
                case ImplicitCastTypes::ARRAY_TO_POINTER:
                case ImplicitCastTypes::LAMBDA_TO_FUNCTION_POINTER:
                case ImplicitCastTypes::ARITH_CAST:
                case ImplicitCastTypes::RAW_CAST:
                    return true;
                default:
                    return false;
            }
        };

    auto strip_stale_dependent_implicit_casts =
        [&](std::unique_ptr<Expr>& candidate) {
            while (auto* cast = dyn_cast<ImplicitCast>(candidate.get())) {
                if (!cast->expr ||
                    !implicit_cast_kind_can_be_stripped_after_substitution(
                        cast->kind)) {
                    return;
                }
                if (cast->ctype &&
                    contains_deferred_semantic_type(
                        cast->ctype.get_shared())) {
                    QualType realized_type =
                        try_realize_deferred_semantic_type(cast->ctype);
                    if (realized_type) {
                        cast->ctype = realized_type;
                    }
                }
                bool cast_type_stale =
                    cast->ctype &&
                    (type_depends_on_template_parameters(
                         cast->ctype,
                         ast_ctx_.get()) ||
                     contains_deferred_semantic_type(
                         cast->ctype.get_shared()) ||
                     auto_type_utils::auto_type_flavors_in(
                         cast->ctype.get_shared()) != 0);
                QualType source_type = cast->expr->get_type();
                bool source_still_dependent =
                    expression_depends_on_template_parameters(cast->expr.get()) ||
                    type_depends_on_template_parameters(
                        source_type,
                        ast_ctx_.get()) ||
                    (source_type &&
                     contains_deferred_semantic_type(
                         source_type.get_shared()));
                if (!cast_type_stale || source_still_dependent) {
                    return;
                }
                auto owned_cast = std::unique_ptr<ImplicitCast>(
                    static_cast<ImplicitCast*>(candidate.release()));
                candidate = std::move(owned_cast->expr);
            }
        };

    auto materialize_constant_after_substitution =
        [&](std::unique_ptr<Expr>& candidate) -> bool {
        if (!candidate) {
            return false;
        }
        // Stale dependent references to specialized constexpr members can be
        // constant after substitution even when the dependency predicate is
        // conservative. Do not fold operators such as dependent sizeof here.
        Expr* materialization_root = strip_implicit_casts(candidate.get());
        if (!materialization_root ||
            !(isa<VarRef>(materialization_root) ||
              isa<QualifiedVarRef>(materialization_root) ||
              isa<MemberExpr>(materialization_root) ||
              isa<BuiltinCallExpr>(materialization_root) ||
              isa<ConceptSpecializationExpr>(materialization_root))) {
            return false;
        }
        QualType candidate_type = finalize_deferred_semantic_type(
            candidate->get_type(),
            candidate->location);
        if (!candidate_type ||
            type_depends_on_template_parameters(
                candidate_type,
                ast_ctx_.get()) ||
            contains_deferred_semantic_type(candidate_type.get_shared()) ||
            !expression_depends_on_template_parameters(candidate.get())) {
            return false;
        }

        ConstEvalResult eval = evaluate_with_consteval_compat(
            candidate.get(),
            ConstEvalMode::cpp_core_constant_expression());
        if (eval.status != ConstEvalStatus::Constant ||
            !eval.value.has_value()) {
            return false;
        }

        auto argument = TemplateArgument::value_argument(
            candidate_type,
            *eval.value,
            {},
            nullptr);
        auto replacement =
            collect_template_internal::make_constant_expr_for_template_argument(
                argument,
                ast_ctx_.get(),
                candidate->location);
        if (!replacement) {
            return false;
        }
        candidate = std::move(replacement);
        return true;
    };

    auto rebind_qualified_var_ref_after_substitution =
        [&](std::unique_ptr<Expr>& candidate) -> bool {
        auto* qualified_ref = dyn_cast<QualifiedVarRef>(candidate.get());
        if (!qualified_ref) {
            return true;
        }
        const auto* qualified_info = qualified_ref->get_cpp_qualified_info();
        if (!qualified_info ||
            !qualified_info->is_type_qualified ||
            !qualified_info->qualifier_type) {
            return true;
        }

        DependentLookupQualifier qualifier =
            build_dependent_lookup_qualifier(*qualified_info);
        qualifier = normalize_dependent_lookup_qualifier_after_substitution(
            qualifier,
            candidate->location);
        if (dependent_lookup_qualifier_is_dependent(
                qualifier,
                ast_ctx_.get())) {
            return true;
        }

        QualType resolved_owner_type = finalize_deferred_semantic_type(
            qualifier.qualifier_type,
            candidate->location);
        if (!resolved_owner_type ||
            type_depends_on_template_parameters(
                resolved_owner_type,
                ast_ctx_.get())) {
            return true;
        }

        CppQualifiedExprInfo resolved_info =
            build_cpp_qualified_expr_info(qualifier);
        resolved_info.qualifier_type = resolved_owner_type;
        auto owner_analysis =
            analyze_cpp_qualified_expr_owner(&resolved_info, ast_ctx_.get());
        auto qualified_owner_type = owner_analysis.qualifier_record_type;
        if (!qualified_owner_type || !owner_analysis.qualifier_record_decl) {
            return true;
        }

        auto member_lookup = lookup_record_member_name(
            qualified_owner_type.get(),
            qualified_ref->get_name());
        size_t total_matches =
            member_lookup.field_matches +
            member_lookup.static_method_matches +
            member_lookup.static_method_template_matches +
            member_lookup.static_data_matches +
            member_lookup.enumerator_matches +
            member_lookup.nonstatic_method_matches +
            member_lookup.nonstatic_method_template_matches;
        if (total_matches != 1) {
            if (auto* mutable_info = qualified_ref->get_cpp_qualified_info()) {
                *mutable_info = resolved_info;
            }
            return true;
        }

        std::shared_ptr<Symbol> selected_symbol = nullptr;
        if (member_lookup.static_data_matches == 1 &&
            member_lookup.single_static_data_member) {
            selected_symbol = member_lookup.single_static_data_member->symbol;
        } else if (member_lookup.enumerator_matches == 1 &&
                   member_lookup.single_enumerator_member) {
            selected_symbol = member_lookup.single_enumerator_member->symbol;
        } else if (member_lookup.static_method_matches == 1 &&
                   member_lookup.single_static_method) {
            selected_symbol = member_lookup.single_static_method->symbol;
        }
        if (!selected_symbol ||
            selected_symbol.get() == qualified_ref->symref.get()) {
            if (auto* mutable_info = qualified_ref->get_cpp_qualified_info()) {
                *mutable_info = resolved_info;
            }
            return true;
        }

        auto rebound = collect_identifier_reference(
            qualified_ref->get_name(),
            std::move(selected_symbol),
            candidate->location);
        if (!rebound) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to rebind qualified member reference after substitution";
            }
            return false;
        }
        if (isa<VarRef>(rebound.get())) {
            rebound = attach_cpp_qualified_info_to_expr(
                std::move(rebound),
                std::move(resolved_info));
        }
        candidate = std::move(rebound);
        return true;
    };

    if (!rebind_qualified_var_ref_after_substitution(expr)) {
        return false;
    }

    if (expr_references_undeduced_auto_variable(expr.get())) {
        return true;
    }

    if (auto* this_expr = dyn_cast<CppThisExpr>(expr.get())) {
        if (implicit_this_type &&
            (!this_expr->this_type ||
             type_depends_on_template_parameters(
                 this_expr->this_type,
                 ast_ctx_.get()) ||
             contains_deferred_semantic_type(
                 this_expr->this_type.get_shared()) ||
             !types_equivalent_after_template_argument_canonicalization(
                 this_expr->this_type,
                 implicit_this_type,
                 ast_ctx_.get()))) {
            this_expr->this_type = implicit_this_type;
        }
        return true;
    }

    if (auto* implicit_cast = dyn_cast<ImplicitCast>(expr.get())) {
        if (implicit_cast->expr &&
            !resolve_dependent_expr_after_substitution(
                implicit_cast->expr,
                implicit_this_type,
                error_out,
                expr_use)) {
            return false;
        }
        if (implicit_cast->ctype &&
            (contains_deferred_semantic_type(
                 implicit_cast->ctype.get_shared()) ||
             type_depends_on_template_parameters(
                 implicit_cast->ctype,
                 ast_ctx_.get()))) {
            QualType realized_type =
                try_realize_deferred_semantic_type(implicit_cast->ctype);
            if (realized_type) {
                implicit_cast->ctype = realized_type;
            }
        }
        strip_stale_dependent_implicit_casts(expr);
        implicit_cast = dyn_cast<ImplicitCast>(expr.get());
        if (!implicit_cast) {
            return true;
        }
        QualType concrete_cast_type =
            implicit_cast->ctype
                ? desugar_type(implicit_cast->ctype, ast_ctx_.get())
                : QualType();
        if (concrete_cast_type &&
            !contains_deferred_semantic_type(concrete_cast_type.get_shared()) &&
            !type_depends_on_template_parameters(
                concrete_cast_type,
                ast_ctx_.get())) {
            implicit_cast->ctype = concrete_cast_type;
            switch (implicit_cast->kind) {
                case ImplicitCastTypes::UNKNOWN:
                case ImplicitCastTypes::ARITH_CAST:
                case ImplicitCastTypes::RAW_CAST: {
                    auto owned_cast = std::unique_ptr<ImplicitCast>(
                        static_cast<ImplicitCast*>(expr.release()));
                    expr = cast_if_needed(
                        std::move(owned_cast->expr),
                        owned_cast->ctype);
                    return true;
                }
                case ImplicitCastTypes::LVALUE_TO_RVALUE:
                case ImplicitCastTypes::ARRAY_TO_POINTER:
                case ImplicitCastTypes::FUNCTION_TO_POINTER:
                case ImplicitCastTypes::LAMBDA_TO_FUNCTION_POINTER:
                case ImplicitCastTypes::VECTOR_SPLAT:
                case ImplicitCastTypes::REAL_TO_COMPLEX:
                case ImplicitCastTypes::COMPLEX_TO_REAL:
                case ImplicitCastTypes::COMPLEX_TO_COMPLEX:
                    break;
            }
        }
        return true;
    }
    if (auto* explicit_cast = dyn_cast<ExplicitCast>(expr.get())) {
        if (explicit_cast->expr &&
            !resolve_dependent_expr_after_substitution(
                explicit_cast->expr,
                implicit_this_type,
                error_out)) {
            return false;
        }
        if (explicit_cast->ctype &&
            (contains_deferred_semantic_type(
                 explicit_cast->ctype.get_shared()) ||
             type_depends_on_template_parameters(
                 explicit_cast->ctype,
                 ast_ctx_.get()))) {
            QualType realized_type =
                try_realize_deferred_semantic_type(explicit_cast->ctype);
            if (realized_type) {
                explicit_cast->ctype = realized_type;
            }
        }
        if (explicit_cast->cast_kind == ExplicitCastKind::CppConstCast) {
            std::string error;
            auto check =
                check_cpp_const_cast(
                    explicit_cast->expr.get(),
                    explicit_cast->ctype,
                    &error);
            if (check == CppConstCastCheckResult::Invalid) {
                if (error_out) {
                    *error_out = error;
                }
                return false;
            }
            if (check == CppConstCastCheckResult::Valid &&
                canonical_type_kind(explicit_cast->ctype) == TypeKind::Pointer) {
                explicit_cast->expr = collect_apply_standard_conversions(
                    std::move(explicit_cast->expr),
                    ExprUseContext::RValue);
            }
        } else if (explicit_cast->cast_kind == ExplicitCastKind::CppStaticCast) {
            auto owned_cast = std::unique_ptr<ExplicitCast>(
                static_cast<ExplicitCast*>(expr.release()));
            if (canonical_type_kind(owned_cast->ctype, ast_ctx_.get()) !=
                TypeKind::Reference) {
                owned_cast->expr = collect_apply_standard_conversions(
                    std::move(owned_cast->expr),
                    ExprUseContext::RValue);
                if (!owned_cast->expr) {
                    if (error_out) {
                        *error_out = "static_cast operand became invalid after substitution";
                    }
                    expr = std::move(owned_cast);
                    return false;
                }
            }

            QualType source_type =
                remove_reference_and_desugar(
                    owned_cast->expr->get_type(),
                    ast_ctx_.get());
            QualType target_no_ref =
                remove_reference_and_desugar(
                    owned_cast->ctype,
                    ast_ctx_.get());
            auto rebuilt =
                cpp_static_named_cast(
                    std::move(owned_cast->expr),
                    source_type,
                    owned_cast->ctype,
                    target_no_ref,
                    owned_cast->location);
            if (!rebuilt || isa<ErrorExpr>(rebuilt.get())) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "invalid static_cast after template substitution";
                }
                expr = std::move(rebuilt);
                return false;
            }
            expr = std::move(rebuilt);
            return true;
        } else if (explicit_cast->cast_kind == ExplicitCastKind::CppReinterpretCast) {
            auto owned_cast = std::unique_ptr<ExplicitCast>(
                static_cast<ExplicitCast*>(expr.release()));
            if (canonical_type_kind(owned_cast->ctype, ast_ctx_.get()) !=
                TypeKind::Reference) {
                owned_cast->expr = collect_apply_standard_conversions(
                    std::move(owned_cast->expr),
                    ExprUseContext::RValue);
                if (!owned_cast->expr) {
                    if (error_out) {
                        *error_out = "reinterpret_cast operand became invalid after substitution";
                    }
                    expr = std::move(owned_cast);
                    return false;
                }
            }

            QualType source_type =
                remove_reference_and_desugar(
                    owned_cast->expr->get_type(),
                    ast_ctx_.get());
            QualType target_no_ref =
                remove_reference_and_desugar(
                    owned_cast->ctype,
                    ast_ctx_.get());
            auto rebuilt =
                cpp_reinterpret_named_cast(
                    std::move(owned_cast->expr),
                    source_type,
                    owned_cast->ctype,
                    target_no_ref,
                    owned_cast->location);
            if (!rebuilt || isa<ErrorExpr>(rebuilt.get())) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "invalid reinterpret_cast after template substitution";
                }
                expr = std::move(rebuilt);
                return false;
            }
            expr = std::move(rebuilt);
            return true;
        } else if (explicit_cast->expr &&
                   explicit_cast->ctype &&
                   !contains_deferred_semantic_type(
                       explicit_cast->ctype.get_shared()) &&
                   !type_depends_on_template_parameters(
                       explicit_cast->ctype,
                       ast_ctx_.get())) {
            // collect_explicit_cast/collect_cpp_named_cast build non-const
            // explicit casts from rvalue-normalized operands. Dependent lookup
            // can materialize a new glvalue operand only after substitution, so
            // restore the same invariant before codegen sees the cast.
            explicit_cast->expr = collect_apply_standard_conversions(
                std::move(explicit_cast->expr),
                ExprUseContext::RValue);
        }
        return true;
    }
    if (auto* value_init = dyn_cast<CppValueInitExpr>(expr.get())) {
        if (value_init->ctype &&
            contains_deferred_semantic_type(value_init->ctype.get_shared())) {
            QualType realized_type =
                try_realize_deferred_semantic_type(value_init->ctype);
            if (realized_type) {
                value_init->ctype = realized_type;
            }
        }
        return true;
    }
    if (auto* function_style_cast =
            dyn_cast<CppFunctionStyleCastExpr>(expr.get())) {
        if (function_style_cast->target_type &&
            contains_deferred_semantic_type(
                function_style_cast->target_type.get_shared())) {
            QualType realized_type =
                try_realize_deferred_semantic_type(
                    function_style_cast->target_type);
            if (realized_type) {
                function_style_cast->target_type = realized_type;
            }
        }
        for (auto& arg : function_style_cast->args) {
            if (arg &&
                !resolve_dependent_expr_after_substitution(
                    arg,
                    implicit_this_type,
                    error_out)) {
                return false;
            }
        }
        if (type_depends_on_template_parameters(
                function_style_cast->target_type,
                ast_ctx_.get())) {
            return true;
        }
        for (const auto& arg : function_style_cast->args) {
            if (arg &&
                (expression_depends_on_template_parameters(arg.get()) ||
                 type_depends_on_template_parameters(
                     arg->get_type(),
                     ast_ctx_.get()))) {
                if (!function_style_cast->is_list_init) {
                    return true;
                }
            }
        }
        auto owned_cast = std::unique_ptr<CppFunctionStyleCastExpr>(
            static_cast<CppFunctionStyleCastExpr*>(expr.release()));
        std::unique_ptr<Expr> rewritten;
        if (owned_cast->is_list_init) {
            auto init_list = collect_make<InitListExpr>(owned_cast->location);
            init_list->elements.reserve(owned_cast->args.size());
            for (auto& arg : owned_cast->args) {
                InitElement element;
                element.value = std::move(arg);
                element.loc = element.value ? element.value->location
                                            : owned_cast->location;
                init_list->elements.push_back(std::move(element));
            }
            rewritten = collect_cpp_type_list_initialization_expression(
                owned_cast->target_type,
                std::move(init_list),
                owned_cast->location);
        } else {
            rewritten = collect_cpp_function_style_cast(
                owned_cast->target_type,
                std::move(owned_cast->args),
                owned_cast->location);
        }
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve function-style cast after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if (auto* init_list = dyn_cast<InitListExpr>(expr.get())) {
        for (auto& element : init_list->elements) {
            if (element.value &&
                !resolve_dependent_expr_after_substitution(
                    element.value,
                    implicit_this_type,
                    error_out)) {
                return false;
            }
            strip_stale_dependent_implicit_casts(element.value);
            realize_deferred_expr_type_after_substitution(
                element.value.get(),
                /*allow_finalize=*/true);
            for (auto& designator : element.designators) {
                if (designator.index &&
                    !resolve_dependent_expr_after_substitution(
                        designator.index,
                        implicit_this_type,
                        error_out)) {
                    return false;
                }
                if (designator.range_end &&
                    !resolve_dependent_expr_after_substitution(
                        designator.range_end,
                        implicit_this_type,
                        error_out)) {
                    return false;
                }
                strip_stale_dependent_implicit_casts(designator.index);
                strip_stale_dependent_implicit_casts(designator.range_end);
                realize_deferred_expr_type_after_substitution(
                    designator.index.get(),
                    /*allow_finalize=*/true);
                realize_deferred_expr_type_after_substitution(
                    designator.range_end.get(),
                    /*allow_finalize=*/true);
            }
        }
        if (auto placeholder =
                get_class_template_placeholder_type(init_list->type)) {
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
                if (error_out && error_out->empty()) {
                    *error_out =
                        "class template argument deduction requires a class template";
                }
                return false;
            }

            std::vector<Expr*> ctad_args;
            ctad_args.reserve(init_list->elements.size());
            bool deduction_is_still_dependent = false;
            for (const auto& element : init_list->elements) {
                if (!element.designators.empty()) {
                    if (error_out && error_out->empty()) {
                        *error_out =
                            "class template argument deduction does not support designated initializers";
                    }
                    return false;
                }
                ctad_args.push_back(element.value.get());
                if (element.value &&
                    (expression_depends_on_template_parameters(
                         element.value.get()) ||
                     type_depends_on_template_parameters(
                         element.value->get_type(),
                         ast_ctx_.get()))) {
                    deduction_is_still_dependent = true;
                }
            }
            if (deduction_is_still_dependent) {
                return true;
            }

            QualType deduced_type;
            if (!resolve_class_template_argument_deduction(
                    primary_class_template,
                    ctad_args,
                    !init_list->is_paren_init,
                    /*is_copy_initialization=*/false,
                    init_list->location,
                    deduced_type) ||
                !deduced_type) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to resolve class template argument deduction after substitution";
                }
                return false;
            }

            auto owned_list = std::unique_ptr<InitListExpr>(
                static_cast<InitListExpr*>(expr.release()));
            SrcLoc list_loc = owned_list->location;
            owned_list->type = deduced_type;
            auto rebuilt = collect_cpp_type_list_initialization_expression(
                deduced_type,
                std::move(owned_list),
                list_loc);
            if (!rebuilt) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to rebuild class template list-initialization after substitution";
                }
                return false;
            }
            expr = std::move(rebuilt);
            return true;
        }
        realize_deferred_expr_type_after_substitution(
            init_list,
            /*allow_finalize=*/true);
        return true;
    }
    if (auto* new_expr = dyn_cast<CppNewExpr>(expr.get())) {
        auto type_or_expr_still_dependent =
            [&](const std::unique_ptr<Expr>& candidate) {
            if (!candidate) {
                return false;
            }
            return expression_depends_on_template_parameters(candidate.get()) ||
                   type_depends_on_template_parameters(
                       candidate->get_type(),
                       ast_ctx_.get()) ||
                   (candidate->get_type() &&
                    contains_deferred_semantic_type(
                        candidate->get_type().get_shared()));
        };
        auto type_still_dependent = [&](QualType type) {
            return type &&
                   (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                    contains_deferred_semantic_type(type.get_shared()) ||
                    auto_type_utils::auto_type_flavors_in(
                        type.get_shared()) != 0);
        };

        for (auto& arg : new_expr->placement_args) {
            if (arg &&
                !resolve_dependent_expr_after_substitution(
                    arg,
                    implicit_this_type,
                    error_out)) {
                return false;
            }
            strip_stale_dependent_implicit_casts(arg);
            realize_deferred_expr_type_after_substitution(
                arg.get(),
                /*allow_finalize=*/true);
        }
        if (new_expr->initializer &&
            !resolve_dependent_expr_after_substitution(
                new_expr->initializer,
                implicit_this_type,
                error_out)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(new_expr->initializer);
        realize_deferred_expr_type_after_substitution(
            new_expr->initializer.get(),
            /*allow_finalize=*/true);
        for (auto& arg : new_expr->constructor_args) {
            if (arg &&
                !resolve_dependent_expr_after_substitution(
                    arg,
                    implicit_this_type,
                    error_out)) {
                return false;
            }
            strip_stale_dependent_implicit_casts(arg);
            realize_deferred_expr_type_after_substitution(
                arg.get(),
                /*allow_finalize=*/true);
        }
        realize_deferred_expr_type_after_substitution(
            new_expr,
            /*allow_finalize=*/true);

        bool child_still_dependent =
            type_or_expr_still_dependent(new_expr->initializer);
        for (const auto& arg : new_expr->placement_args) {
            child_still_dependent =
                child_still_dependent || type_or_expr_still_dependent(arg);
        }
        for (const auto& arg : new_expr->constructor_args) {
            child_still_dependent =
                child_still_dependent || type_or_expr_still_dependent(arg);
        }

        if (new_expr->allocator_sym ||
            type_still_dependent(new_expr->allocated_type) ||
            child_still_dependent) {
            return true;
        }

        auto owned_new = std::unique_ptr<CppNewExpr>(
            static_cast<CppNewExpr*>(expr.release()));
        auto rewritten = collect_cpp_new_expression(
            owned_new->allocated_type,
            std::move(owned_new->placement_args),
            std::move(owned_new->initializer),
            owned_new->is_global_allocation != 0,
            owned_new->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent new-expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if (auto* member = dyn_cast<MemberExpr>(expr.get())) {
        if (member->base &&
            !resolve_dependent_expr_after_substitution(
                member->base,
                implicit_this_type,
                error_out)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(member->base);
        realize_deferred_expr_type_after_substitution(
            member->base.get(),
            /*allow_finalize=*/true);
        realize_deferred_expr_type_after_substitution(
            member,
            /*allow_finalize=*/true);

        bool base_still_dependent =
            !member->base ||
            expression_depends_on_template_parameters(member->base.get()) ||
            type_depends_on_template_parameters(
                member->base->get_type(),
                ast_ctx_.get());
        bool member_type_still_dependent =
            type_depends_on_template_parameters(
                member->member_type,
                ast_ctx_.get()) ||
            (member->member_type &&
             contains_deferred_semantic_type(
                 member->member_type.get_shared()));
        if (base_still_dependent ||
            (member->member_type && !member_type_still_dependent)) {
            return true;
        }

        auto owned_member = std::unique_ptr<MemberExpr>(
            static_cast<MemberExpr*>(expr.release()));
        auto rewritten = collect_member_expression(
            std::move(owned_member->base),
            owned_member->get_member_name(),
            owned_member->isArrow != 0,
            owned_member->location,
            /*allow_overloaded_method_set=*/
                expr_use == PostSubstitutionExprUse::CallCallee,
            owned_member->suppress_virtual_dispatch != 0);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to rebind member access after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if (auto* paren = dyn_cast<ParenExpr>(expr.get())) {
        if (paren->subexpr &&
            !resolve_dependent_expr_after_substitution(
                paren->subexpr,
                implicit_this_type,
                error_out,
                expr_use)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(paren->subexpr);
        realize_deferred_expr_type_after_substitution(
            paren->subexpr.get(),
            /*allow_finalize=*/true);
        return true;
    }
    if (auto* cond = dyn_cast<CondExpr>(expr.get())) {
        if (cond->condition &&
            !resolve_dependent_expr_after_substitution(
                cond->condition,
                implicit_this_type,
                error_out)) {
            return false;
        }
        if (cond->true_expr &&
            !resolve_dependent_expr_after_substitution(
                cond->true_expr,
                implicit_this_type,
                error_out)) {
            return false;
        }
        if (cond->false_expr &&
            !resolve_dependent_expr_after_substitution(
                cond->false_expr,
                implicit_this_type,
                error_out)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(cond->condition);
        strip_stale_dependent_implicit_casts(cond->true_expr);
        strip_stale_dependent_implicit_casts(cond->false_expr);
        if (!cond->condition || !cond->false_expr) {
            return true;
        }
        if (expression_depends_on_template_parameters(cond->condition.get()) ||
            (cond->true_expr &&
             expression_depends_on_template_parameters(cond->true_expr.get())) ||
            expression_depends_on_template_parameters(cond->false_expr.get())) {
            return true;
        }

        auto owned_cond = std::unique_ptr<CondExpr>(
            static_cast<CondExpr*>(expr.release()));
        auto rewritten = collect_conditional_expression(
            std::move(owned_cond->condition),
            std::move(owned_cond->true_expr),
            std::move(owned_cond->false_expr),
            QualType(),
            owned_cond->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent conditional expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
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
    if (auto* builtin = dyn_cast<BuiltinCallExpr>(expr.get())) {
        if (!is_builtin_type_trait_kind(builtin->kind)) {
            return true;
        }
        auto rewritten = collect_builtin_type_trait_expression(
            builtin->kind,
            builtin->type_args,
            builtin->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve builtin type trait after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if (auto* sizeof_expr = dyn_cast<SizeOfExpr>(expr.get())) {
        QualType target_type = sizeof_expr->type_operand;
        if (sizeof_expr->expr_operand) {
            if (expression_depends_on_template_parameters(
                    sizeof_expr->expr_operand.get())) {
                return true;
            }
            target_type = sizeof_expr->expr_operand->get_type();
        }
        if (type_depends_on_template_parameters(target_type, ast_ctx_.get())) {
            return true;
        }
        finalize_sizeof_node(
            sizeof_expr,
            target_type.get_shared(),
            sizeof_expr->location);
        return true;
    }
    if (auto* alignof_expr = dyn_cast<AlignOfExpr>(expr.get())) {
        QualType target_type = alignof_expr->type_operand;
        if (alignof_expr->expr_operand) {
            if (expression_depends_on_template_parameters(
                    alignof_expr->expr_operand.get())) {
                return true;
            }
            target_type = alignof_expr->expr_operand->get_type();
        }
        if (type_depends_on_template_parameters(target_type, ast_ctx_.get())) {
            return true;
        }
        finalize_alignof_node(
            alignof_expr,
            target_type.get_shared(),
            alignof_expr->location);
        return true;
    }
    if (auto* offsetof_expr = dyn_cast<OffsetOfExpr>(expr.get())) {
        if (offsetof_expr->type_operand &&
            (contains_deferred_semantic_type(
                 offsetof_expr->type_operand.get_shared()) ||
             type_depends_on_template_parameters(
                 offsetof_expr->type_operand,
                 ast_ctx_.get()))) {
            QualType realized_type =
                try_realize_deferred_semantic_type(offsetof_expr->type_operand);
            if (realized_type) {
                offsetof_expr->type_operand = realized_type;
            }
        }

        for (auto& component : offsetof_expr->designator_path) {
            if (!component.array_index_expr) {
                continue;
            }
            if (!resolve_dependent_expr_after_substitution(
                    component.array_index_expr,
                    implicit_this_type,
                    error_out)) {
                return false;
            }
            strip_stale_dependent_implicit_casts(component.array_index_expr);
            realize_deferred_expr_type_after_substitution(
                component.array_index_expr.get(),
                /*allow_finalize=*/true);
            if (expression_depends_on_template_parameters(
                    component.array_index_expr.get()) ||
                type_depends_on_template_parameters(
                    component.array_index_expr->get_type(),
                    ast_ctx_.get())) {
                return true;
            }
        }

        if (type_depends_on_template_parameters(
                offsetof_expr->type_operand,
                ast_ctx_.get())) {
            return true;
        }

        SrcLoc offsetof_loc = offsetof_expr->location;
        auto owned_offsetof = std::unique_ptr<OffsetOfExpr>(
            static_cast<OffsetOfExpr*>(expr.release()));
        expr = finalize_offsetof_node(std::move(owned_offsetof), offsetof_loc);
        return true;
    }
    if (auto* noexcept_expr = dyn_cast<CppNoexceptExpr>(expr.get())) {
        while (auto* cast =
                   dyn_cast<ImplicitCast>(noexcept_expr->operand.get())) {
            if (!cast->expr) {
                break;
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
                break;
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
                    cast = nullptr;
                    break;
            }
            if (!cast) {
                break;
            }
            auto owned_cast = std::unique_ptr<ImplicitCast>(
                static_cast<ImplicitCast*>(noexcept_expr->operand.release()));
            noexcept_expr->operand = std::move(owned_cast->expr);
        }
        if (noexcept_expr->operand &&
            !resolve_dependent_expr_after_substitution(
                noexcept_expr->operand,
                implicit_this_type,
                error_out)) {
            return false;
        }
        if (!noexcept_expr->operand ||
            expression_depends_on_template_parameters(
                noexcept_expr->operand.get()) ||
            type_depends_on_template_parameters(
                noexcept_expr->operand->get_type(),
                ast_ctx_.get())) {
            return true;
        }
        auto owned_noexcept = std::unique_ptr<CppNoexceptExpr>(
            static_cast<CppNoexceptExpr*>(expr.release()));
        auto rewritten = collect_cpp_noexcept_expression(
            std::move(owned_noexcept->operand),
            owned_noexcept->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent noexcept expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if (auto* dynamic_cast_expr = dyn_cast<CppDynamicCastExpr>(expr.get())) {
        auto type_still_dependent_or_deferred =
            [&](QualType type) {
            return type &&
                   (type_depends_on_template_parameters(
                        type,
                        ast_ctx_.get()) ||
                    contains_deferred_semantic_type(type.get_shared()) ||
                    auto_type_utils::auto_type_flavors_in(
                        type.get_shared()) != 0);
        };
        if (dynamic_cast_expr->expr &&
            !resolve_dependent_expr_after_substitution(
                dynamic_cast_expr->expr,
                implicit_this_type,
                error_out)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(dynamic_cast_expr->expr);
        realize_deferred_expr_type_after_substitution(
            dynamic_cast_expr,
            /*allow_finalize=*/true);
        if (!dynamic_cast_expr->expr ||
            expression_depends_on_template_parameters(
                dynamic_cast_expr->expr.get()) ||
            type_still_dependent_or_deferred(
                dynamic_cast_expr->expr->get_type()) ||
            type_still_dependent_or_deferred(
                dynamic_cast_expr->target_type)) {
            return true;
        }

        auto owned_dynamic_cast = std::unique_ptr<CppDynamicCastExpr>(
            static_cast<CppDynamicCastExpr*>(expr.release()));
        auto rewritten = collect_cpp_named_cast(
            CppNamedCastKind::Dynamic,
            std::move(owned_dynamic_cast->expr),
            owned_dynamic_cast->target_type,
            owned_dynamic_cast->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent dynamic_cast expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if (auto* delete_expr = dyn_cast<CppDeleteExpr>(expr.get())) {
        auto type_still_dependent_or_deferred =
            [&](QualType type) {
                return type &&
                       (type_depends_on_template_parameters(
                            type,
                            ast_ctx_.get()) ||
                        contains_deferred_semantic_type(type.get_shared()) ||
                        auto_type_utils::auto_type_flavors_in(
                            type.get_shared()) != 0);
            };
        strip_stale_dependent_implicit_casts(delete_expr->operand);
        if (delete_expr->operand &&
            !resolve_dependent_expr_after_substitution(
                delete_expr->operand,
                implicit_this_type,
                error_out)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(delete_expr->operand);
        realize_deferred_expr_type_after_substitution(
            delete_expr->operand.get(),
            /*allow_finalize=*/true);
        if (!delete_expr->operand ||
            expression_depends_on_template_parameters(
                delete_expr->operand.get()) ||
            type_still_dependent_or_deferred(
                delete_expr->operand->get_type()) ||
            type_still_dependent_or_deferred(
                delete_expr->destroyed_type)) {
            return true;
        }
        auto owned_delete = std::unique_ptr<CppDeleteExpr>(
            static_cast<CppDeleteExpr*>(expr.release()));
        auto rewritten = collect_cpp_delete_expression(
            std::move(owned_delete->operand),
            owned_delete->is_array_form != 0,
            owned_delete->is_global_delete != 0,
            owned_delete->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent delete expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }
    if (auto* pseudo_dtor = dyn_cast<CppPseudoDestructorExpr>(expr.get())) {
        while (auto* cast = dyn_cast<ImplicitCast>(pseudo_dtor->base.get())) {
            if (!cast->expr) {
                break;
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
                break;
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
                    cast = nullptr;
                    break;
            }
            if (!cast) {
                break;
            }
            auto owned_cast = std::unique_ptr<ImplicitCast>(
                static_cast<ImplicitCast*>(pseudo_dtor->base.release()));
            pseudo_dtor->base = std::move(owned_cast->expr);
        }
        if (pseudo_dtor->base &&
            !resolve_dependent_expr_after_substitution(
                pseudo_dtor->base,
                implicit_this_type,
                error_out)) {
            return false;
        }
        if (!pseudo_dtor->base ||
            expression_depends_on_template_parameters(
                pseudo_dtor->base.get()) ||
            type_depends_on_template_parameters(
                pseudo_dtor->destroyed_type,
                ast_ctx_.get())) {
            return true;
        }
        auto owned_pseudo_dtor = std::unique_ptr<CppPseudoDestructorExpr>(
            static_cast<CppPseudoDestructorExpr*>(expr.release()));
        auto rewritten = collect_cpp_pseudo_destructor_expression(
            std::move(owned_pseudo_dtor->base),
            owned_pseudo_dtor->destroyed_type,
            owned_pseudo_dtor->is_arrow != 0,
            owned_pseudo_dtor->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent pseudo-destructor expression after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    auto unresolved_member_still_dependent =
        [&](const UnresolvedMemberExpr* unresolved_member) -> bool {
            if (!unresolved_member) {
                return false;
            }
            if (unresolved_member->explicit_template_arguments.has_value()) {
                for (const auto& argument :
                     *unresolved_member->explicit_template_arguments) {
                    if (template_argument_depends_on_template_parameters(
                            argument,
                            ast_ctx_.get())) {
                        return true;
                    }
                }
            }
            if (unresolved_member->base &&
                cpp_expr_still_dependent_after_substitution(
                    unresolved_member->base.get(),
                    ast_ctx_.get())) {
                return true;
            }
            return cpp_member_lookup_base_still_dependent_after_substitution(
                unresolved_member->base
                    ? unresolved_member->base->get_type()
                    : QualType(nullptr),
                unresolved_member->isArrow != 0,
                ast_ctx_.get());
        };

    auto prepare_unresolved_member_base_after_substitution =
        [&](UnresolvedMemberExpr* unresolved_member) -> bool {
            if (!unresolved_member) {
                return true;
            }
            if (unresolved_member->base &&
                !resolve_dependent_expr_after_substitution(
                    unresolved_member->base,
                    implicit_this_type,
                    error_out)) {
                return false;
            }
            strip_stale_dependent_implicit_casts(unresolved_member->base);
            realize_deferred_expr_type_after_substitution(
                unresolved_member->base.get(),
                /*allow_finalize=*/true);
            return true;
        };

    auto unresolved_lookup_still_dependent =
        [&](const UnresolvedLookupExpr* unresolved_lookup) -> bool {
            if (!unresolved_lookup) {
                return false;
            }
            if (unresolved_lookup->explicit_template_arguments.has_value()) {
                for (const auto& argument :
                     *unresolved_lookup->explicit_template_arguments) {
                    if (template_argument_depends_on_template_parameters(
                            argument,
                            ast_ctx_.get())) {
                        return true;
                    }
                }
            }
            DependentLookupQualifier qualifier =
                normalize_dependent_lookup_qualifier_after_substitution(
                    unresolved_lookup->qualifier,
                    unresolved_lookup->location);
            return dependent_lookup_qualifier_is_dependent(
                qualifier,
                ast_ctx_.get());
        };

    auto call_arguments_still_dependent =
        [&](const std::vector<std::unique_ptr<Expr>>& args) -> bool {
            for (const auto& arg : args) {
                if (!arg) {
                    continue;
                }
                if (expression_depends_on_template_parameters(arg.get()) ||
                    type_depends_on_template_parameters(
                        arg->get_type(),
                        ast_ctx_.get())) {
                    return true;
                }
            }
            return false;
        };

    auto materialize_unresolved_member =
        [&](std::unique_ptr<UnresolvedMemberExpr> owned_member,
            bool allow_overloaded_method_set)
            -> std::unique_ptr<Expr> {
            if (!prepare_unresolved_member_base_after_substitution(
                    owned_member.get())) {
                return nullptr;
            }
            return collect_member_expression(
                std::move(owned_member->base),
                owned_member->member_name,
                owned_member->isArrow != 0,
                owned_member->location,
                allow_overloaded_method_set,
                owned_member->suppress_virtual_dispatch != 0,
                owned_member->requires_template_keyword != 0,
                TemplateDependencyCheckMode::AfterTemplateSubstitution);
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

    auto resolve_call_arguments_after_substitution =
        [&](std::vector<std::unique_ptr<Expr>>& args) -> bool {
        for (auto& arg : args) {
            if (arg &&
                !resolve_dependent_expr_after_substitution(
                    arg,
                    implicit_this_type,
                    error_out)) {
                return false;
            }
        }
        for (auto& arg : args) {
            strip_stale_dependent_implicit_casts(arg);
            realize_deferred_expr_type_after_substitution(
                arg.get(),
                /*allow_finalize=*/true);
        }
        return true;
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
        if (!prepare_unresolved_member_base_after_substitution(
                unresolved_member)) {
            return false;
        }
        if (unresolved_member_still_dependent(unresolved_member)) {
            return true;
        }
        auto owned_member = std::unique_ptr<UnresolvedMemberExpr>(
            static_cast<UnresolvedMemberExpr*>(expr.release()));
        bool has_explicit_template_args =
            owned_member->explicit_template_arguments.has_value();
        if (has_explicit_template_args) {
            expr = std::move(owned_member);
            return true;
        }
        std::vector<TemplateArgument> explicit_template_args;
        auto rewritten = materialize_unresolved_member(
            std::move(owned_member),
            /*allow_overloaded_method_set=*/
                has_explicit_template_args ||
                expr_use == PostSubstitutionExprUse::CallCallee);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent member access after substitution";
            }
            return false;
        }
        if (has_explicit_template_args) {
            SrcLoc template_id_loc = rewritten->location;
            rewritten = collect_explicit_template_id_impl(
                std::move(rewritten),
                std::move(explicit_template_args),
                template_id_loc);
            if (!rewritten) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to resolve dependent explicit member template-id";
                }
                return false;
            }
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* unresolved_lookup = dyn_cast<UnresolvedLookupExpr>(expr.get())) {
        if (unresolved_lookup_still_dependent(unresolved_lookup)) {
            return true;
        }
        auto owned_lookup = std::unique_ptr<UnresolvedLookupExpr>(
            static_cast<UnresolvedLookupExpr*>(expr.release()));
        auto lexical_lookup_scope = owned_lookup->lexical_lookup_scope;
        auto lexical_lookup_context = owned_lookup->lexical_lookup_context;
        bool has_explicit_template_args =
            owned_lookup->explicit_template_arguments.has_value();
        if (has_explicit_template_args &&
            owned_lookup->qualifier.is_type_qualified) {
            expr = std::move(owned_lookup);
            return true;
        }
        std::vector<TemplateArgument> explicit_template_args;
        if (has_explicit_template_args) {
            explicit_template_args =
                std::move(*owned_lookup->explicit_template_arguments);
        }
        ScopedLexicalLookupContext lexical_lookup(
            collect_,
            lexical_lookup_scope,
            lexical_lookup_context);
        auto rewritten = materialize_unresolved_lookup(
            std::move(owned_lookup),
            /*looks_like_call=*/
                expr_use == PostSubstitutionExprUse::CallCallee);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve qualified dependent lookup after substitution";
            }
            return false;
        }
        if (has_explicit_template_args) {
            SrcLoc template_id_loc = rewritten->location;
            rewritten = collect_explicit_template_id_impl(
                std::move(rewritten),
                std::move(explicit_template_args),
                template_id_loc);
            if (!rewritten) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to resolve dependent explicit template-id";
                }
                return false;
            }
        }
        expr = std::move(rewritten);
        return true;
    }

    if (auto* dependent_unary = dyn_cast<DependentUnaryExpr>(expr.get())) {
        strip_stale_dependent_implicit_casts(dependent_unary->operand);
        if (dependent_unary->operand &&
            !resolve_dependent_expr_after_substitution(
                dependent_unary->operand,
                implicit_this_type,
                error_out)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(dependent_unary->operand);
        materialize_constant_after_substitution(dependent_unary->operand);
        if (!dependent_unary->operand ||
            cpp_expr_still_dependent_after_substitution(
                dependent_unary->operand.get(),
                ast_ctx_.get())) {
            return true;
        }
        auto owned_unary = std::unique_ptr<DependentUnaryExpr>(
            static_cast<DependentUnaryExpr*>(expr.release()));
        auto rewritten = collect_unary_operation(
            owned_unary->uop,
            std::move(owned_unary->operand),
            owned_unary->location,
            TemplateDependencyCheckMode::AfterTemplateSubstitution);
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
        if (dependent_binary->left &&
            !resolve_dependent_expr_after_substitution(
                dependent_binary->left,
                implicit_this_type,
                error_out)) {
            return false;
        }
        if (dependent_binary->right &&
            !resolve_dependent_expr_after_substitution(
                dependent_binary->right,
                implicit_this_type,
                error_out)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(dependent_binary->left);
        strip_stale_dependent_implicit_casts(dependent_binary->right);
        materialize_constant_after_substitution(dependent_binary->left);
        materialize_constant_after_substitution(dependent_binary->right);
        realize_deferred_expr_type_after_substitution(
            dependent_binary->left.get(),
            /*allow_finalize=*/true);
        realize_deferred_expr_type_after_substitution(
            dependent_binary->right.get(),
            /*allow_finalize=*/true);
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
            expression_depends_on_template_parameters(
                dependent_member_access->base.get()) ||
            expression_depends_on_template_parameters(
                dependent_member_access->member_pointer.get()) ||
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
        auto realize_call_result_type =
            [&](FuncCall* call) -> bool {
                if (!call) {
                    return true;
                }
                QualType call_type = call->get_type();
                if (!call_type ||
                    !contains_deferred_semantic_type(call_type.get_shared())) {
                    return !call_type ||
                           !type_depends_on_template_parameters(
                               call_type,
                               ast_ctx_.get());
                }
                QualType realized_type =
                    try_realize_deferred_semantic_type(call_type);
                if (!realized_type) {
                    return false;
                }
                store_explicit_expr_type(call, realized_type);
                return !type_depends_on_template_parameters(
                    realized_type,
                    ast_ctx_.get());
            };
        if (owned_call->func &&
            !resolve_dependent_expr_after_substitution(
                owned_call->func,
                implicit_this_type,
                error_out,
                PostSubstitutionExprUse::CallCallee)) {
            return false;
        }
        if (!resolve_call_arguments_after_substitution(owned_call->args)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(owned_call->func);

        auto expr_or_type_still_dependent =
            [&](const std::unique_ptr<Expr>& candidate) -> bool {
                if (!candidate) {
                    return false;
                }
                QualType candidate_type = candidate->get_type();
                if (candidate_type &&
                    contains_deferred_semantic_type(
                        candidate_type.get_shared())) {
                    QualType realized_type =
                        try_realize_deferred_semantic_type(candidate_type);
                    if (!realized_type) {
                        return true;
                    }
                    if (!type_depends_on_template_parameters(
                            realized_type,
                            ast_ctx_.get())) {
                        store_explicit_expr_type(candidate.get(), realized_type);
                    }
                    candidate_type = realized_type;
                }
                if (expression_depends_on_template_parameters(candidate.get())) {
                    return true;
                }
                if (!candidate_type) {
                    return true;
                }
                if (!type_depends_on_template_parameters(
                        candidate_type,
                        ast_ctx_.get())) {
                    return false;
                }
                if (!contains_deferred_semantic_type(
                        candidate_type.get_shared())) {
                    return true;
                }
                QualType realized_type =
                    try_realize_deferred_semantic_type(candidate_type);
                return !realized_type ||
                       type_depends_on_template_parameters(
                           realized_type,
                           ast_ctx_.get());
            };

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

        realize_call_result_type(owned_call.get());

        if (expr_or_type_still_dependent(owned_call->func)) {
            expr = std::move(owned_call);
            return true;
        }
        for (const auto& arg : owned_call->args) {
            if (expr_or_type_still_dependent(arg)) {
                expr = std::move(owned_call);
                return true;
            }
        }
        if (!realize_call_result_type(owned_call.get())) {
            expr = std::move(owned_call);
            return true;
        }

        auto rewritten = collect_function_call(
            std::move(owned_call->func),
            std::move(owned_call->args),
            owned_call->location);
        if (!rewritten) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve function call after substitution";
            }
            return false;
        }
        expr = std::move(rewritten);
        return true;
    }

    auto* dependent_call = dyn_cast<DependentCallExpr>(expr.get());
    if (!dependent_call) {
        return true;
    }

    auto* unresolved_member =
        dyn_cast<UnresolvedMemberExpr>(dependent_call->callee.get());
    auto* unresolved_lookup =
        dyn_cast<UnresolvedLookupExpr>(dependent_call->callee.get());
    if (unresolved_member &&
        !prepare_unresolved_member_base_after_substitution(
            unresolved_member)) {
        return false;
    }
    if (!unresolved_member && !unresolved_lookup) {
        auto owned_call = std::unique_ptr<DependentCallExpr>(
            static_cast<DependentCallExpr*>(expr.release()));
        if (owned_call->callee &&
            !resolve_dependent_expr_after_substitution(
                owned_call->callee,
                implicit_this_type,
                error_out,
                PostSubstitutionExprUse::CallCallee)) {
            return false;
        }
        if (!resolve_call_arguments_after_substitution(owned_call->args)) {
            return false;
        }
        strip_stale_dependent_implicit_casts(owned_call->callee);

        bool arguments_still_dependent = false;
        for (const auto& arg : owned_call->args) {
            if (!arg) {
                continue;
            }
            if (cpp_expr_still_dependent_after_substitution(
                    arg.get(),
                    ast_ctx_.get())) {
                arguments_still_dependent = true;
                break;
            }
        }

        auto collect_concrete_call_after_substitution =
            [&](std::unique_ptr<Expr> callee,
                std::vector<std::unique_ptr<Expr>> args,
                SrcLoc call_loc) -> std::unique_ptr<Expr> {
            auto call = collect_make<FuncCall>(
                std::move(callee),
                std::move(args),
                call_loc);
            if (!call->func) {
                return call;
            }
            MemberCallSelection member_call_selection;
            if (auto error = try_function_object_call_overload(call, call_loc)) {
                return error;
            }
            if (auto early_result =
                    try_builtin_or_overloaded_varref_call(call, call_loc)) {
                return early_result;
            }
            if (auto error = try_member_function_overload_call(
                    call,
                    member_call_selection,
                    call_loc)) {
                return error;
            }
            return finalize_call_expression(
                std::move(call),
                member_call_selection,
                call_loc);
        };

        auto* callee_ref =
            dyn_cast<VarRef>(
                strip_implicit_casts_and_parens(owned_call->callee.get()));
        bool callee_still_dependent =
            owned_call->callee &&
            cpp_expr_still_dependent_after_substitution(
                owned_call->callee.get(),
                ast_ctx_.get());
        bool force_concrete_function_ref_call =
            callee_ref &&
            callee_ref->symref &&
            callee_ref->symref->kind == SymbolKind::FUNCTION &&
            !arguments_still_dependent;
        bool force_concrete_call =
            !callee_still_dependent && !arguments_still_dependent;
        auto rewritten = (force_concrete_function_ref_call || force_concrete_call)
            ? collect_concrete_call_after_substitution(
                  std::move(owned_call->callee),
                  std::move(owned_call->args),
                  owned_call->location)
            : collect_function_call(
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
    if (auto* owned_member =
            dyn_cast<UnresolvedMemberExpr>(owned_call->callee.get())) {
        if (!prepare_unresolved_member_base_after_substitution(
                owned_member)) {
            return false;
        }
    }
    if (!resolve_call_arguments_after_substitution(owned_call->args)) {
        return false;
    }
    if (call_arguments_still_dependent(owned_call->args)) {
        expr = std::move(owned_call);
        return true;
    }

    if (dyn_cast<UnresolvedMemberExpr>(owned_call->callee.get())) {
        auto owned_member = std::unique_ptr<UnresolvedMemberExpr>(
            static_cast<UnresolvedMemberExpr*>(
                owned_call->callee.release()));
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
                  owned_call->location,
                  implicit_this_type)
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
    auto lexical_lookup_scope = owned_lookup->lexical_lookup_scope;
    auto lexical_lookup_context = owned_lookup->lexical_lookup_context;
    bool has_explicit_template_args =
        owned_lookup->explicit_template_arguments.has_value();
    if (has_explicit_template_args) {
        explicit_template_args =
            std::move(*owned_lookup->explicit_template_arguments);
    }
    ScopedLexicalLookupContext lexical_lookup(
        collect_,
        lexical_lookup_scope,
        lexical_lookup_context);
    std::unique_ptr<Expr> concrete_callee;
    if (has_explicit_template_args &&
        !owned_lookup->qualifier.is_type_qualified) {
        concrete_callee = collect_identifier_reference(
            owned_lookup->name,
            nullptr,
            owned_lookup->location);
        if (isa<VarRef>(concrete_callee.get()) &&
            (owned_lookup->qualifier.has_global_qualifier ||
             !owned_lookup->qualifier.qualifiers.empty())) {
            concrete_callee = attach_cpp_qualified_info_to_expr(
                std::move(concrete_callee),
                build_cpp_qualified_expr_info(owned_lookup->qualifier));
        }
    } else {
        concrete_callee =
            materialize_unresolved_lookup(std::move(owned_lookup), true);
    }
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
              owned_call->location,
              implicit_this_type)
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
