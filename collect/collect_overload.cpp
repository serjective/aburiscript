#include "collect.h"
#include "collect_internal.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"
#include <cstdlib>
#include <cstdint>
#include <iostream>

using namespace collect_internal;

namespace {
struct OverloadMetrics {
    uint64_t resolve_calls = 0;
    uint64_t candidate_evaluations = 0;
    uint64_t best_candidate_pairwise_comparisons = 0;
};

bool refactor_metrics_enabled() {
    static const bool enabled = []() {
        const char* env = std::getenv("ABURI_REFACTOR_METRICS");
        return env && env[0] != '\0' && env[0] != '0';
    }();
    return enabled;
}

OverloadMetrics& overload_metrics() {
    static OverloadMetrics metrics;
    return metrics;
}

void emit_overload_metrics_at_exit() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    const auto& metrics = overload_metrics();
    std::cerr
        << "[refactor-metrics] collect.overload "
        << "resolve_calls=" << metrics.resolve_calls
        << " candidate_evals=" << metrics.candidate_evaluations
        << " pairwise_compares=" << metrics.best_candidate_pairwise_comparisons
        << '\n';
}

struct OverloadMetricsReporter {
    ~OverloadMetricsReporter() {
        emit_overload_metrics_at_exit();
    }
};

OverloadMetricsReporter g_overload_metrics_reporter;

void bump_overload_resolve_calls() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().resolve_calls;
}

void bump_overload_candidate_evaluations() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().candidate_evaluations;
}

void bump_overload_pairwise_comparisons() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++overload_metrics().best_candidate_pairwise_comparisons;
}

size_t hash_combine(size_t seed, size_t value) {
    seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6U) + (seed >> 2U);
    return seed;
}

bool is_non_variadic_prototype(const std::shared_ptr<FunctionType>& fn_type) {
    return fn_type && fn_type->has_prototype && !fn_type->is_variadic;
}

bool exception_spec_compatible_for_function_pointer_conversion(
    FunctionExceptionSpecKind source_spec,
    FunctionExceptionSpecKind target_spec) {
    if (source_spec == target_spec) {
        return true;
    }
    return source_spec == FunctionExceptionSpecKind::NonThrowing &&
           target_spec == FunctionExceptionSpecKind::PotentiallyThrowing;
}

bool function_types_compatible_for_lambda_pointer_conversion(
    const std::shared_ptr<FunctionType>& source_fn,
    const std::shared_ptr<FunctionType>& target_fn,
    const ASTContext* ast_ctx) {
    if (!source_fn || !target_fn) {
        return false;
    }
    if (source_fn->is_variadic != target_fn->is_variadic ||
        source_fn->has_prototype != target_fn->has_prototype ||
        source_fn->parameters.size() != target_fn->parameters.size()) {
        return false;
    }
    if (!source_fn->ret_type.equals_qualified(target_fn->ret_type)) {
        return false;
    }
    for (size_t index = 0; index < source_fn->parameters.size(); ++index) {
        QualType source_param =
            desugar_type(source_fn->parameters[index], ast_ctx);
        QualType target_param =
            desugar_type(target_fn->parameters[index], ast_ctx);
        if (!source_param.equals_qualified(target_param)) {
            return false;
        }
    }
    return exception_spec_compatible_for_function_pointer_conversion(
        source_fn->exception_spec,
        target_fn->exception_spec);
}

bool is_strictly_better_conversion_profile(
    const std::vector<Collect::ImplicitConversionSequence>& lhs_conversions,
    const std::shared_ptr<FunctionType>& lhs_function_type,
    const std::vector<Collect::ImplicitConversionSequence>& rhs_conversions,
    const std::shared_ptr<FunctionType>& rhs_function_type) {
    bool strictly_better = false;
    size_t compare_count = std::min(lhs_conversions.size(), rhs_conversions.size());
    for (size_t i = 0; i < compare_count; ++i) {
        auto lhs_rank = static_cast<int>(lhs_conversions[i].rank);
        auto rhs_rank = static_cast<int>(rhs_conversions[i].rank);
        if (lhs_rank > rhs_rank) {
            return false;
        }
        if (lhs_rank < rhs_rank) {
            strictly_better = true;
            continue;
        }
        if (lhs_conversions[i].rank == Collect::ConversionSequenceRank::ExactMatch) {
            int lhs_subrank = exact_match_subrank(lhs_conversions[i]);
            int rhs_subrank = exact_match_subrank(rhs_conversions[i]);
            if (lhs_subrank > rhs_subrank) {
                return false;
            }
            if (lhs_subrank < rhs_subrank) {
                strictly_better = true;
            }
        }
        if (lhs_conversions[i].rank == Collect::ConversionSequenceRank::Conversion) {
            int lhs_tiebreak = conversion_rank_tiebreak(lhs_conversions[i]);
            int rhs_tiebreak = conversion_rank_tiebreak(rhs_conversions[i]);
            if (lhs_tiebreak > rhs_tiebreak) {
                return false;
            }
            if (lhs_tiebreak < rhs_tiebreak) {
                strictly_better = true;
            }
        }
    }

    bool lhs_non_variadic = is_non_variadic_prototype(lhs_function_type);
    bool rhs_non_variadic = is_non_variadic_prototype(rhs_function_type);
    if (!strictly_better && lhs_non_variadic && !rhs_non_variadic) {
        strictly_better = true;
    } else if (!lhs_non_variadic && rhs_non_variadic) {
        return false;
    }
    return strictly_better;
}

bool is_function_template_specialization_symbol(
    const std::shared_ptr<Symbol>& symbol) {
    return symbol &&
        get_symbol_function_template_specialization(symbol.get()) != nullptr;
}

const FunctionTemplateDecl* function_template_primary_for_symbol(
    const std::shared_ptr<Symbol>& symbol) {
    const auto* specialization_info =
        symbol ? get_symbol_function_template_specialization(symbol.get()) : nullptr;
    return specialization_info ? specialization_info->primary_template : nullptr;
}
} // namespace

size_t Collect::OverloadConversionMemoKeyHash::operator()(
    const OverloadConversionMemoKey& key) const {
    size_t seed = 0;
    seed = hash_combine(seed, std::hash<const Expr*>{}(key.arg));
    seed = hash_combine(seed, std::hash<const CType*>{}(key.to_type));
    seed = hash_combine(seed, std::hash<uint8_t>{}(key.to_qualifiers));
    seed = hash_combine(seed, std::hash<bool>{}(key.allow_user_defined));
    return seed;
}

Collect::ImplicitConversionSequence
Collect::build_cpp_overload_conversion_sequence_cached(
    Expr* arg,
    QualType to,
    bool allow_user_defined,
    OverloadConversionMemoCache* conversion_cache) {
    if (!conversion_cache || !arg || !to) {
        return build_cpp_overload_conversion_sequence(
            arg, to, allow_user_defined);
    }
    OverloadConversionMemoKey key;
    key.arg = arg;
    key.to_type = to.get_shared().get();
    key.to_qualifiers = to.get_qualifiers();
    key.allow_user_defined = allow_user_defined;
    auto it = conversion_cache->find(key);
    if (it != conversion_cache->end()) {
        return it->second;
    }
    auto seq = build_cpp_overload_conversion_sequence(
        arg, to, allow_user_defined);
    conversion_cache->emplace(key, seq);
    return seq;
}

std::unique_ptr<Expr> Collect::append_member_overload_candidates(
    const ObjectType* record_type,
    std::string_view member_name,
    Expr* access_expr,
    OverloadImplicitObjectArgKind static_member_arg_kind,
    std::vector<OverloadCallCandidate>& candidates_out,
    bool& had_member_match_out,
    bool& saw_private_member_out,
    bool& saw_protected_member_out,
    SrcLoc loc) const {

    had_member_match_out = false;
    if (!record_type) {
        return nullptr;
    }

    auto methods = find_record_methods(record_type, std::string(member_name));
    if (methods.empty()) {
        return nullptr;
    }

    had_member_match_out = true;
    const ObjectDecl* object_record_decl = record_decl_from_record_type(record_type);
    const ObjectDecl* access_context_decl = nullptr;
    if (lang_opts_.is_cxx_mode() && session_.func_state_.current_function_is_cpp_member) {
        access_context_decl =
            current_record_decl_from_this_type(session_.func_state_.current_function_cpp_this_type);
    }

    candidates_out.reserve(candidates_out.size() + methods.size());
    for (const auto& method_match : methods) {
        const auto* method = method_match.method;
        if (!method) {
            continue;
        }
        if (lang_opts_.is_cxx_mode()) {
            if (method->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_match.owner_record_decl, access_context_decl)) {
                    saw_private_member_out = true;
                    continue;
                }
            }
            if (method->declared_access == RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_match.owner_record_decl,
                    access_context_decl,
                    object_record_decl,
                    method->is_static);
                if (!protected_ok) {
                    saw_protected_member_out = true;
                    continue;
                }
            }
        }
        if (!method->symbol) {
            report_error(
                "internal error: unresolved member function symbol '" +
                    std::string(member_name) + "'",
                loc);
            return collect_make<ErrorExpr>(
                "unresolved member function symbol", loc);
        }

        OverloadCallCandidate call_candidate;
        call_candidate.symbol = method->symbol;
        call_candidate.implicit_object_arg_kind = method->is_static
            ? static_member_arg_kind
            : OverloadImplicitObjectArgKind::MemberObject;
        candidates_out.push_back(std::move(call_candidate));
    }

    return nullptr;
}

std::unique_ptr<Expr> Collect::append_member_template_overload_candidates(
    const ObjectType* record_type,
    std::string_view member_name,
    Expr* access_expr,
    bool access_expr_is_arrow,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    std::vector<OverloadCallCandidate>& candidates_out,
    bool& had_member_match_out,
    bool& had_template_member_match_out,
    bool& saw_private_member_out,
    bool& saw_protected_member_out,
    bool& saw_template_instantiation_out,
    SrcLoc loc) {
    had_template_member_match_out = false;
    if (!record_type) {
        return nullptr;
    }

    auto method_templates =
        find_record_method_templates(record_type, std::string(member_name));
    if (method_templates.empty()) {
        return nullptr;
    }

    had_member_match_out = true;
    had_template_member_match_out = true;
    const ObjectDecl* object_record_decl = record_decl_from_record_type(record_type);
    const ObjectDecl* access_context_decl = nullptr;
    if (lang_opts_.is_cxx_mode() && session_.func_state_.current_function_is_cpp_member) {
        access_context_decl =
            current_record_decl_from_this_type(session_.func_state_.current_function_cpp_this_type);
    }

    for (const auto& method_template_match : method_templates) {
        const auto* method_template = method_template_match.method_template;
        const auto* function_template =
            method_template ? method_template->decl : nullptr;
        if (!method_template || !function_template) {
            continue;
        }
        if (lang_opts_.is_cxx_mode()) {
            if (method_template->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        method_template_match.owner_record_decl,
                        access_context_decl)) {
                    saw_private_member_out = true;
                    continue;
                }
            }
            if (method_template->declared_access ==
                RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    method_template_match.owner_record_decl,
                    access_context_decl,
                    object_record_decl,
                    method_template->is_static);
                if (!protected_ok) {
                    saw_protected_member_out = true;
                    continue;
                }
            }
        }

        std::unique_ptr<Expr> deduction_object_arg;
        std::vector<Expr*> deduction_args;
        deduction_args.reserve(
            explicit_args.size() + (method_template->is_static ? 0u : 1u));
        if (!method_template->is_static) {
            std::string clone_error;
            auto cloned_access_expr =
                clone_expr_tree(access_expr, ast_ctx_.get(), &clone_error);
            if (access_expr && !cloned_access_expr) {
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
                std::move(cloned_access_expr),
                access_expr_is_arrow,
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
        for (const auto& arg : explicit_args) {
            deduction_args.push_back(arg.get());
        }

        std::vector<TemplateArgument> specialization_arguments;
        if (!deduce_function_template_call_arguments(
                function_template,
                deduction_args,
                specialization_arguments)) {
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
        saw_template_instantiation_out = true;

        OverloadCallCandidate candidate;
        candidate.symbol = std::move(specialization_symbol);
        candidate.implicit_object_arg_kind = method_template->is_static
            ? OverloadImplicitObjectArgKind::None
            : OverloadImplicitObjectArgKind::MemberObject;
        candidates_out.push_back(std::move(candidate));
    }

    return nullptr;
}


void Collect::append_unqualified_overload_candidates(
    std::string_view function_name,
    OverloadImplicitObjectArgKind implicit_arg_kind,
    std::vector<OverloadCallCandidate>& candidates_out) {

    if (!session_.current_scope_) {
        return;
    }
    auto function_candidates = LookupEngine::lookup_unqualified_function_candidates(
        std::string(function_name), session_.current_scope_, true);
    candidates_out.reserve(candidates_out.size() + function_candidates.size());
    for (const auto& fn_sym : function_candidates) {
        OverloadCallCandidate call_candidate;
        call_candidate.symbol = fn_sym;
        call_candidate.implicit_object_arg_kind = implicit_arg_kind;
        candidates_out.push_back(std::move(call_candidate));
    }
}


std::unique_ptr<Expr> Collect::select_overload_candidate(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    std::shared_ptr<Symbol>& selected_symbol_out,
    OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) {

    selected_symbol_out = nullptr;
    selected_implicit_object_arg_kind_out = OverloadImplicitObjectArgKind::None;
    if (candidates.empty()) {
        return nullptr;
    }
    if (candidates.size() == 1 && !lang_opts_.is_cxx_mode()) {
        selected_symbol_out = candidates.front().symbol;
        selected_implicit_object_arg_kind_out =
            candidates.front().implicit_object_arg_kind;
        return nullptr;
    }
    return resolve_overloaded_call_candidates(
        callee_name,
        candidates,
        explicit_args,
        implicit_object_arg,
        loc,
        selected_symbol_out,
        selected_implicit_object_arg_kind_out);
}


std::unique_ptr<Expr> Collect::report_inaccessible_member(
    std::string_view member_name,
    bool saw_private_member,
    bool saw_protected_member,
    SrcLoc loc) const {

    if (saw_protected_member) {
        report_error(
            "member '" + std::string(member_name) +
                "' is protected within this context",
            loc);
        return collect_make<ErrorExpr>(
            "inaccessible protected member function", loc);
    }
    if (saw_private_member) {
        report_error(
            "member '" + std::string(member_name) +
                "' is private within this context",
            loc);
        return collect_make<ErrorExpr>(
            "inaccessible private member function", loc);
    }
    return nullptr;
}


std::unique_ptr<Expr> Collect::make_hidden_overload_callee(
    std::shared_ptr<Symbol> selected_symbol,
    SrcLoc loc) const {

    const std::string* internal_call_name =
        ast_ctx_ ? ast_ctx_->intern_identifier("__aburi_overload_call")
                 : nullptr;
    if (internal_call_name) {
        return collect_make<VarRef>(internal_call_name, selected_symbol, loc);
    }
    return collect_make<VarRef>(std::move(selected_symbol), loc);
}

std::optional<Collect::CppConversionConstructorMatch>
Collect::select_cpp_conversion_constructor(Expr* arg,
                                                   QualType target_object_type,
                                                   bool allow_explicit_constructors) {

    if (!lang_opts_.is_cxx_mode() || !arg || !target_object_type) {
        return std::nullopt;
    }

    auto canonical_target =
        desugar_type(remove_reference(target_object_type, ast_ctx_.get()), ast_ctx_.get())
            .as_shared<ObjectType>();
    if (!canonical_target) {
        return std::nullopt;
    }
    const ObjectDecl* record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(canonical_target->get_decl()));
    if (!record_decl) {
        return std::nullopt;
    }
    const RecordSemanticState* record_state =
        record_semantics_cache_lookup(record_decl);
    if (!record_state || record_state->constructors.empty()) {
        return std::nullopt;
    }

    struct ConstructorCandidateEval {
        const RecordSemanticState::Constructor* ctor = nullptr;
        std::shared_ptr<FunctionType> function_type = nullptr;
        size_t user_param_start = 0;
        size_t max_user_param_count = 0;
        size_t required_user_param_count = 0;
        std::vector<ImplicitConversionSequence> conversions;
        bool viable = false;
    };

    std::vector<ConstructorCandidateEval> evaluated;
    evaluated.reserve(record_state->constructors.size());
    for (const auto& ctor : record_state->constructors) {
        ConstructorCandidateEval eval;
        eval.ctor = &ctor;
        eval.function_type =
            desugar_type(ctor.type, ast_ctx_.get()).as_shared<FunctionType>();
        if (!eval.function_type || !ctor.symbol) {
            evaluated.push_back(std::move(eval));
            continue;
        }
        CppConstructorUserParamInfo param_info =
            cpp_compute_constructor_user_param_info(ctor);
        eval.user_param_start = param_info.user_param_start;
        eval.max_user_param_count = param_info.max_user_param_count;
        eval.required_user_param_count = param_info.required_user_param_count;

        if (ctor.is_deleted ||
            (!allow_explicit_constructors && ctor.is_explicit) ||
            !cpp_access_allows_member(ctor.declared_access, false)) {
            evaluated.push_back(std::move(eval));
            continue;
        }

        constexpr size_t provided_arg_count = 1;
        if (provided_arg_count < eval.required_user_param_count ||
            provided_arg_count > eval.max_user_param_count) {
            evaluated.push_back(std::move(eval));
            continue;
        }

        eval.viable = true;
        eval.conversions.reserve(provided_arg_count);
        size_t param_idx = eval.user_param_start;
        if (param_idx >= eval.function_type->parameters.size()) {
            eval.viable = false;
        } else {
            QualType param_type =
                decay_parameter_type(eval.function_type->parameters[param_idx]);
            auto seq = build_cpp_overload_conversion_sequence(
                arg, param_type, /*allow_user_defined=*/false);
            if (!seq.viable) {
                eval.viable = false;
            }
            eval.conversions.push_back(seq);
        }
        evaluated.push_back(std::move(eval));
    }

    std::vector<size_t> viable_indices;
    viable_indices.reserve(evaluated.size());
    for (size_t idx = 0; idx < evaluated.size(); ++idx) {
        if (evaluated[idx].viable) {
            viable_indices.push_back(idx);
        }
    }
    if (viable_indices.empty()) {
        return std::nullopt;
    }

    auto is_better_candidate = [&](size_t lhs_idx, size_t rhs_idx) {
        const auto& lhs = evaluated[lhs_idx];
        const auto& rhs = evaluated[rhs_idx];
        return is_strictly_better_conversion_profile(
            lhs.conversions,
            lhs.function_type,
            rhs.conversions,
            rhs.function_type);
    };

    size_t best_index = std::numeric_limits<size_t>::max();
    for (size_t idx : viable_indices) {
        bool better_than_all = true;
        for (size_t other : viable_indices) {
            if (idx == other) {
                continue;
            }
            if (!is_better_candidate(idx, other)) {
                better_than_all = false;
                break;
            }
        }
        if (!better_than_all) {
            continue;
        }
        if (best_index != std::numeric_limits<size_t>::max()) {
            return std::nullopt;
        }
        best_index = idx;
    }
    if (best_index == std::numeric_limits<size_t>::max()) {
        return std::nullopt;
    }

    const auto& chosen = evaluated[best_index];
    if (!chosen.ctor || !chosen.ctor->symbol || !chosen.function_type) {
        return std::nullopt;
    }

    CppConversionConstructorMatch result;
    result.ctor_symbol = chosen.ctor->symbol;
    result.ctor_function_type = chosen.function_type;
    result.user_param_start = chosen.user_param_start;
    result.max_user_param_count = chosen.max_user_param_count;
    return result;
}

std::optional<Collect::CppUserDefinedConversionMatch>
Collect::select_cpp_user_defined_conversion(
    Expr* arg,
    QualType target_type,
    bool allow_explicit_constructors) {

    if (!lang_opts_.is_cxx_mode() || !arg || !target_type || !ast_ctx_) {
        return std::nullopt;
    }

    QualType conversion_target =
        desugar_type(remove_reference(target_type, ast_ctx_.get()), ast_ctx_.get());
    if (!conversion_target) {
        return std::nullopt;
    }

    auto source_record_type =
        remove_reference_and_desugar(arg->get_type(), ast_ctx_.get())
            .as_shared<ObjectType>();
    const ObjectDecl* source_record_decl =
        source_record_type
            ? dyn_cast<ObjectDecl>(source_record_type->get_decl())
            : nullptr;
    if (source_record_decl &&
        ast_ctx_->has_cpp_lambda_closure_decl_info(source_record_decl->node_id)) {
        const auto* lambda_info =
            ast_ctx_->get_cpp_lambda_closure_decl_info(source_record_decl->node_id);
        auto target_pointer =
            conversion_target.as_shared<PointerType>();
        auto target_function =
            target_pointer
                ? desugar_type(target_pointer->pointed_type, ast_ctx_.get())
                      .as_shared<FunctionType>()
                : nullptr;
        auto invoker_function =
            (lambda_info && lambda_info->function_pointer_invoker_decl)
                ? desugar_type(
                      QualType(lambda_info->function_pointer_invoker_decl->type),
                      ast_ctx_.get())
                      .as_shared<FunctionType>()
                : nullptr;
        if (lambda_info &&
            !lambda_info->has_syntactic_captures &&
            lambda_info->function_pointer_invoker_decl &&
            target_function &&
            function_types_compatible_for_lambda_pointer_conversion(
                invoker_function,
                target_function,
                ast_ctx_.get())) {
            CppUserDefinedConversionMatch result;
            result.kind =
                CppUserDefinedConversionKind::LambdaFunctionPointer;
            result.lambda_function_pointer.closure_owner = source_record_decl;
            result.lambda_function_pointer.invoker_decl =
                lambda_info->function_pointer_invoker_decl;
            result.lambda_function_pointer.invoker_function_type =
                std::move(invoker_function);
            return result;
        }
    }

    if (canonical_type_kind(conversion_target, ast_ctx_.get()) !=
        TypeKind::Object) {
        return std::nullopt;
    }

    auto constructor_match = select_cpp_conversion_constructor(
        arg, conversion_target, allow_explicit_constructors);
    if (!constructor_match.has_value()) {
        return std::nullopt;
    }

    CppUserDefinedConversionMatch result;
    result.kind = CppUserDefinedConversionKind::Constructor;
    result.constructor = *constructor_match;
    return result;
}

std::unique_ptr<Expr> Collect::build_cpp_user_defined_conversion_expr(
    std::unique_ptr<Expr> arg,
    QualType target_type,
    SrcLoc loc) {

    if (!arg || !target_type) {
        return arg;
    }

    QualType target_object_type = remove_reference(target_type, ast_ctx_.get());
    target_object_type = desugar_type(target_object_type, ast_ctx_.get());
    if (canonical_type_kind(target_object_type, ast_ctx_.get()) == TypeKind::Object &&
        dyn_cast<InitListExpr>(Collect::strip_implicit_casts(arg.get()))) {
        auto converted = convert_cpp_braced_init_argument(
            std::move(arg), target_object_type, loc);
        if (!converted) {
            report_error(
                "internal error: missing user-defined conversion constructor for '" +
                    target_object_type.to_string() + "'",
                loc);
            return collect_make<ErrorExpr>(
                "missing user-defined conversion constructor", loc);
        }
        return converted;
    }

    auto conversion_match = select_cpp_user_defined_conversion(
        arg.get(),
        target_type,
        /*allow_explicit_constructors=*/false);
    if (!conversion_match.has_value()) {
        return arg;
    }

    if (conversion_match->kind ==
        CppUserDefinedConversionKind::LambdaFunctionPointer) {
        QualType conversion_target = remove_reference(target_type, ast_ctx_.get());
        return collect_make<ImplicitCast>(
            ImplicitCastTypes::LAMBDA_TO_FUNCTION_POINTER,
            std::move(arg),
            conversion_target);
    }

    if (dyn_cast<InitListExpr>(Collect::strip_implicit_casts(arg.get()))) {
        auto converted = convert_cpp_braced_init_argument(
            std::move(arg), target_object_type, loc);
        if (!converted) {
            report_error(
                "internal error: missing user-defined conversion constructor for '" +
                    target_object_type.to_string() + "'",
                loc);
            return collect_make<ErrorExpr>(
                "missing user-defined conversion constructor", loc);
        }
        return converted;
    }

    if (!conversion_match->constructor.ctor_symbol ||
        !conversion_match->constructor.ctor_function_type) {
        report_error(
            "internal error: missing user-defined conversion constructor for '" +
                target_object_type.to_string() + "'",
            loc);
        return collect_make<ErrorExpr>(
            "missing user-defined conversion constructor", loc);
    }

    std::vector<std::unique_ptr<Expr>> ctor_args;
    ctor_args.reserve(conversion_match->constructor.max_user_param_count);
    ctor_args.push_back(std::move(arg));

    for (size_t arg_index = ctor_args.size();
         arg_index < conversion_match->constructor.max_user_param_count;
         ++arg_index) {
        size_t param_index =
            conversion_match->constructor.user_param_start + arg_index;
        const Expr* default_expr = lookup_default_argument_for_param(
            conversion_match->constructor.ctor_symbol, param_index);
        if (!default_expr) {
            report_error(
                "internal error: missing conversion-constructor default argument metadata",
                loc);
            return collect_make<ErrorExpr>(
                "missing conversion-constructor default argument", loc);
        }
        std::string clone_error;
        auto cloned_default = clone_expr_tree(
            default_expr, ast_ctx_.get(), &clone_error);
        if (!cloned_default) {
            std::string message =
                clone_error.empty()
                    ? "default argument expression is not supported"
                    : "default argument expression is not supported: " +
                          clone_error;
            report_error(message, default_expr->location);
            return collect_make<ErrorExpr>(
                "unsupported conversion-constructor default argument expression",
                loc);
        }
        ctor_args.push_back(std::move(cloned_default));
    }

    std::vector<std::unique_ptr<Expr>> converted_ctor_args;
    converted_ctor_args.reserve(ctor_args.size());
    for (size_t arg_index = 0; arg_index < ctor_args.size(); ++arg_index) {
        size_t param_index =
            conversion_match->constructor.user_param_start + arg_index;
        if (param_index >=
            conversion_match->constructor.ctor_function_type->parameters.size()) {
            report_error(
                "internal error: conversion-constructor parameter index out of range",
                loc);
            return collect_make<ErrorExpr>(
                "conversion-constructor parameter index out of range", loc);
        }
        QualType param_type = decay_parameter_type(
            conversion_match->constructor.ctor_function_type->parameters[param_index]);
        auto ctor_arg = std::move(ctor_args[arg_index]);
        if (canonical_type_kind(param_type, ast_ctx_.get()) ==
            TypeKind::Reference) {
            auto seq = build_cpp_overload_conversion_sequence(
                ctor_arg.get(), param_type, /*allow_user_defined=*/false);
            if (!seq.viable) {
                report_conversion_failure(
                    "conversion constructor argument",
                    ctor_arg ? ctor_arg->get_type() : QualType(),
                    param_type,
                    ctor_arg ? ctor_arg->location : loc);
                return collect_make<ErrorExpr>(
                    "invalid conversion-constructor argument", loc);
            }
        } else {
            ctor_arg = collect_apply_standard_conversions(
                std::move(ctor_arg), ExprUseContext::CallArgument);
            ctor_arg = cast_if_needed(std::move(ctor_arg), param_type);
        }
        converted_ctor_args.push_back(std::move(ctor_arg));
    }

    return collect_make<CppConstructExpr>(
        std::move(conversion_match->constructor.ctor_symbol),
        std::move(converted_ctor_args),
        target_object_type,
        false,
        loc);
}

std::unique_ptr<Expr> Collect::convert_cpp_braced_init_argument(
    std::unique_ptr<Expr> arg,
    QualType target_type,
    SrcLoc loc) {

    if (!lang_opts_.is_cxx_mode() || !arg || !target_type) {
        return arg;
    }

    if (canonical_type_kind(target_type, ast_ctx_.get()) != TypeKind::Object) {
        return arg;
    }

    std::unique_ptr<Expr> working = std::move(arg);
    while (working &&
           !isa<InitListExpr>(working.get()) &&
           (isa<ImplicitCast>(working.get()) ||
            isa<ExplicitCast>(working.get()))) {
        if (auto* implicit_cast = dyn_cast<ImplicitCast>(working.get())) {
            auto inner = std::move(implicit_cast->expr);
            working = std::move(inner);
            continue;
        }
        if (auto* explicit_cast = dyn_cast<ExplicitCast>(working.get())) {
            auto inner = std::move(explicit_cast->expr);
            working = std::move(inner);
            continue;
        }
    }

    auto* init_list = dyn_cast<InitListExpr>(working.get());
    if (!init_list) {
        return working;
    }

    bool is_list_init = !init_list->is_paren_init;
    auto owned_list = std::unique_ptr<InitListExpr>(
        static_cast<InitListExpr*>(working.release()));
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

    auto converted = collect_member_initializer_expression(
        std::move(ctor_args),
        target_type,
        is_list_init,
        loc,
        false);
    if (!converted) {
        report_error(
            "failed to build braced-initializer conversion for '" +
                target_type.to_string() + "'",
            loc);
        return collect_make<ErrorExpr>("invalid braced-initializer argument", loc);
    }
    return converted;
}

bool Collect::probe_cpp_braced_init_argument_conversion(
    Expr* arg,
    QualType target_type,
    SrcLoc loc,
    ImplicitConversionSequence& seq_out) {

    seq_out = ImplicitConversionSequence{};
    seq_out.from = arg ? arg->get_type() : QualType();
    seq_out.to = target_type;

    if (!lang_opts_.is_cxx_mode() || !arg || !target_type) {
        return false;
    }
    if (!dyn_cast<InitListExpr>(strip_implicit_casts(arg)) ||
        canonical_type_kind(target_type, ast_ctx_.get()) != TypeKind::Object) {
        return false;
    }

    std::string clone_error;
    auto cloned = clone_expr_tree(arg, ast_ctx_.get(), &clone_error);
    if (!cloned) {
        seq_out.kind = ConversionSequenceKind::Failed;
        seq_out.rank = ConversionSequenceRank::NoMatch;
        seq_out.viable = false;
        seq_out.note = clone_error.empty()
            ? "braced-init argument clone failed"
            : clone_error;
        return true;
    }

    if (!diag_engine_) {
        seq_out.kind = ConversionSequenceKind::Failed;
        seq_out.rank = ConversionSequenceRank::NoMatch;
        seq_out.viable = false;
        seq_out.note = "missing diagnostic engine for braced-init conversion probe";
        return true;
    }

    auto checkpoint = diag_engine_->checkpoint();
    auto converted = convert_cpp_braced_init_argument(
        std::move(cloned), target_type, loc);
    diag_engine_->restore(checkpoint);

    if (!converted || isa<ErrorExpr>(converted.get())) {
        seq_out.kind = ConversionSequenceKind::Failed;
        seq_out.rank = ConversionSequenceRank::NoMatch;
        seq_out.viable = false;
        seq_out.note = "braced-init argument cannot initialize target type";
        return true;
    }

    if (isa<CppConstructExpr>(converted.get())) {
        seq_out.kind = ConversionSequenceKind::UserDefined;
        seq_out.rank = ConversionSequenceRank::Conversion;
        seq_out.exact_subrank = -1;
    } else {
        seq_out.kind = ConversionSequenceKind::Identity;
        seq_out.rank = ConversionSequenceRank::ExactMatch;
        seq_out.exact_subrank = 0;
    }
    seq_out.viable = true;
    seq_out.note.clear();
    return true;
}

std::unique_ptr<Expr> Collect::build_overload_implicit_object_arg(
    OverloadImplicitObjectArgKind implicit_arg_kind,
    std::unique_ptr<Expr> object_expr,
    bool object_expr_is_pointer,
    SrcLoc loc) {

    if (implicit_arg_kind == OverloadImplicitObjectArgKind::None) {
        return nullptr;
    }
    if (!object_expr) {
        return nullptr;
    }
    if (implicit_arg_kind == OverloadImplicitObjectArgKind::Regular) {
        return object_expr;
    }

    if (object_expr_is_pointer ||
        canonical_type_kind(remove_reference(object_expr->get_type(), ast_ctx_.get()),
                            ast_ctx_.get()) ==
            TypeKind::Pointer) {
        return collect_apply_standard_conversions(
            std::move(object_expr), ExprUseContext::RValue);
    }

    Expr* raw_object = strip_implicit_casts(object_expr.get());
    ValueCategory category = classify_value_category(
        raw_object ? raw_object : object_expr.get());
    if (category == ValueCategory::LValue) {
        return collect_unary_operation(
            UnaryOpTypes::ADDRESS_OF, std::move(object_expr), loc);
    }

    QualType object_type = remove_reference(object_expr->get_type(), ast_ctx_.get());
    if (!object_type) {
        report_error("internal error: missing implicit-object type", loc);
        return collect_make<ErrorExpr>("missing implicit-object type", loc);
    }

    QualType reference_type(
        std::make_shared<ReferenceType>(object_type, ReferenceKind::LValue));
    auto temporary_reference = collect_make<ImplicitCast>(
        ImplicitCastTypes::ARITH_CAST, std::move(object_expr), reference_type);
    auto address_of_temporary = collect_make<UnaryOperation>(
        UnaryOpTypes::ADDRESS_OF, std::move(temporary_reference), loc);
    address_of_temporary->ctype =
        QualType(std::make_shared<PointerType>(object_type));
    return address_of_temporary;
}



Collect::ImplicitConversionSequence
Collect::evaluate_overload_implicit_object_conversion(
    Expr* object_arg,
    QualType param_type,
    OverloadImplicitObjectArgKind implicit_object_arg_kind,
    FunctionRefQualifierKind ref_qualifier,
    OverloadConversionMemoCache* conversion_cache) {

    auto classify_implicit_object_value_category =
        [&](Expr* arg) -> ValueCategory {
        if (!arg) {
            return ValueCategory::Unknown;
        }
        if (implicit_object_arg_kind == OverloadImplicitObjectArgKind::MemberObject) {
            auto canonical_arg_type =
                remove_reference_and_desugar(
                    arg->get_type(),
                    ast_ctx_.get());
            if (canonical_type_kind(canonical_arg_type, ast_ctx_.get()) ==
                TypeKind::Pointer) {
                // For `ptr->method()`, the implicit object expression is `*ptr`
                // and is therefore an lvalue.
                return ValueCategory::LValue;
            }
        }
        return classify_value_category(strip_implicit_casts(arg));
    };

    auto object_arg_category = classify_implicit_object_value_category(object_arg);
    if (ref_qualifier == FunctionRefQualifierKind::LValue &&
        object_arg_category != ValueCategory::LValue) {
        ImplicitConversionSequence rejected;
        rejected.kind = ConversionSequenceKind::Numeric;
        rejected.rank = ConversionSequenceRank::NoMatch;
        rejected.from = object_arg ? object_arg->get_type() : QualType();
        rejected.to = param_type;
        rejected.viable = false;
        rejected.note =
            "implicit object argument is not an lvalue for '&'-qualified method";
        return rejected;
    }
    if (ref_qualifier == FunctionRefQualifierKind::RValue &&
        object_arg_category == ValueCategory::LValue) {
        ImplicitConversionSequence rejected;
        rejected.kind = ConversionSequenceKind::Numeric;
        rejected.rank = ConversionSequenceRank::NoMatch;
        rejected.from = object_arg ? object_arg->get_type() : QualType();
        rejected.to = param_type;
        rejected.viable = false;
        rejected.note =
            "implicit object argument is not an rvalue for '&&'-qualified method";
        return rejected;
    }

    auto seq = build_cpp_overload_conversion_sequence_cached(
        object_arg,
        param_type,
        /*allow_user_defined=*/true,
        conversion_cache);
    if (seq.viable || !object_arg || !param_type) {
        return seq;
    }

    // Dot-call member candidates lower to a hidden object-pointer argument.
    // Ranking must still model object/pointer compatibility even when the
    // source object is a temporary (materialized later during rewriting).
    QualType object_type = remove_reference(object_arg->get_type(), ast_ctx_.get());
    if (!object_type) {
        return seq;
    }
    auto object_kind = canonical_type_kind(object_type, ast_ctx_.get());
    auto param_ptr =
        desugar_type(param_type, ast_ctx_.get()).as_shared<PointerType>();
    QualType pointed_type = param_ptr ? param_ptr->pointed_type : QualType();
    auto pointed_kind = canonical_type_kind(pointed_type, ast_ctx_.get());
    if (object_kind != TypeKind::Object || pointed_kind != TypeKind::Object) {
        return seq;
    }
    if (has_qualification_preserving_match(object_type, pointed_type)) {
        seq.kind = object_type.equals_qualified(pointed_type)
            ? ConversionSequenceKind::Identity
            : ConversionSequenceKind::Qualification;
        seq.rank = ConversionSequenceRank::ExactMatch;
        seq.from = object_type;
        seq.to = param_type;
        seq.viable = true;
        seq.exact_subrank = (seq.kind == ConversionSequenceKind::Identity) ? 0 : 1;
        seq.note.clear();
        return seq;
    }
    if (can_convert_derived_to_base_object(object_type, pointed_type)) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.from = object_type;
        seq.to = param_type;
        seq.viable = true;
        seq.exact_subrank = -1;
        seq.note.clear();
        return seq;
    }
    return seq;
}

Collect::OverloadCandidateEval Collect::evaluate_overload_call_candidate(
    const OverloadCallCandidate& candidate_info,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    OverloadConversionMemoCache* conversion_cache) {

    bump_overload_candidate_evaluations();
    OverloadCandidateEval eval;
    eval.symbol = candidate_info.symbol;
    eval.implicit_object_arg_kind = candidate_info.implicit_object_arg_kind;

    if (!candidate_info.symbol ||
        candidate_info.symbol->kind != SymbolKind::FUNCTION) {
        eval.failure_reason = "candidate is not a function";
        return eval;
    }

    auto candidate_canonical_type =
        desugar_type(candidate_info.symbol->type, ast_ctx_.get());
    auto candidate_fn = candidate_canonical_type.as_shared<FunctionType>();
    if (!candidate_fn) {
        auto candidate_ptr = candidate_canonical_type.as_shared<PointerType>();
        if (candidate_ptr) {
            candidate_fn =
                desugar_type(candidate_ptr->pointed_type, ast_ctx_.get())
                    .as_shared<FunctionType>();
        }
    }
    if (!candidate_fn) {
        eval.failure_reason = "candidate has non-callable type";
        return eval;
    }

    eval.function_type = candidate_fn;
    eval.viable = true;

    bool has_implicit_object_arg =
        eval.implicit_object_arg_kind != OverloadImplicitObjectArgKind::None;
    size_t implicit_arg_count = has_implicit_object_arg ? 1 : 0;
    size_t provided_arg_count = explicit_args.size() + implicit_arg_count;
    bool has_void_param = (candidate_fn->parameters.size() == 1 &&
                           candidate_fn->parameters[0]->isVoid());
    size_t named_param_count = has_void_param ? 0 : candidate_fn->parameters.size();
    // Default arguments reduce the minimum required arity but not the maximum
    // for non-variadic prototype candidates.
    size_t trailing_default_arg_count = count_trailing_default_arguments_for_call(
        candidate_info.symbol, named_param_count, implicit_arg_count);
    if (trailing_default_arg_count > named_param_count) {
        trailing_default_arg_count = named_param_count;
    }
    size_t min_required_param_count =
        named_param_count >= trailing_default_arg_count
            ? named_param_count - trailing_default_arg_count
            : 0;

    if (candidate_fn->has_prototype) {
        if (candidate_fn->is_variadic) {
            if (provided_arg_count < min_required_param_count) {
                eval.viable = false;
                eval.failure_reason =
                    "requires at least " +
                    std::to_string(min_required_param_count) +
                    " argument(s), but " + std::to_string(provided_arg_count) +
                    " provided";
            }
        } else if (provided_arg_count < min_required_param_count) {
            eval.viable = false;
            if (trailing_default_arg_count == 0) {
                eval.failure_reason =
                    "requires " + std::to_string(named_param_count) +
                    " argument(s), but " + std::to_string(provided_arg_count) +
                    " provided";
            } else {
                eval.failure_reason =
                    "requires at least " +
                    std::to_string(min_required_param_count) +
                    " argument(s), but " + std::to_string(provided_arg_count) +
                    " provided";
            }
        } else if (provided_arg_count > named_param_count) {
            eval.viable = false;
            eval.failure_reason =
                "requires " + std::to_string(named_param_count) +
                " argument(s), but " + std::to_string(provided_arg_count) +
                " provided";
        }
    }

    if (!eval.viable) {
        return eval;
    }

    eval.conversions.reserve(provided_arg_count);

    if (has_implicit_object_arg) {
        if (!implicit_object_arg) {
            eval.viable = false;
            eval.failure_reason = "missing implicit object argument";
        } else if (candidate_fn->has_prototype && named_param_count > 0) {
            QualType param_type = decay_parameter_type(candidate_fn->parameters[0]);
            // Member-object calls use stricter object-parameter compatibility
            // than a regular explicit argument conversion sequence.
            auto seq = (eval.implicit_object_arg_kind ==
                        OverloadImplicitObjectArgKind::MemberObject)
                ? evaluate_overload_implicit_object_conversion(
                      implicit_object_arg,
                      param_type,
                      eval.implicit_object_arg_kind,
                      candidate_fn->member_ref_qualifier,
                      conversion_cache)
                : build_cpp_overload_conversion_sequence_cached(
                      implicit_object_arg,
                      param_type,
                      /*allow_user_defined=*/true,
                      conversion_cache);
            if (!seq.viable) {
                std::string from_name = seq.from ? seq.from.to_string() : "<unknown>";
                std::string to_name =
                    param_type ? param_type.to_string() : "<unknown>";
                eval.viable = false;
                eval.failure_reason =
                    "cannot convert argument 1 from '" + from_name + "' to '" +
                    to_name + "'";
            }
            eval.conversions.push_back(seq);
        } else {
            ImplicitConversionSequence seq;
            seq.kind = ConversionSequenceKind::Numeric;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.from = implicit_object_arg->get_type();
            seq.to = nullptr;
            seq.viable = true;
            eval.conversions.push_back(seq);
        }
    }

    for (size_t i = 0; eval.viable && i < explicit_args.size(); ++i) {
        size_t param_index = i + implicit_arg_count;
        if (candidate_fn->has_prototype && param_index < named_param_count) {
            QualType param_type =
                decay_parameter_type(candidate_fn->parameters[param_index]);
            auto seq = build_cpp_overload_conversion_sequence_cached(
                explicit_args[i].get(),
                param_type,
                /*allow_user_defined=*/true,
                conversion_cache);
            if (!seq.viable) {
                std::string from_name = seq.from ? seq.from.to_string() : "<unknown>";
                std::string to_name =
                    param_type ? param_type.to_string() : "<unknown>";
                eval.viable = false;
                eval.failure_reason =
                    "cannot convert argument " +
                    std::to_string(param_index + 1) + " from '" + from_name +
                    "' to '" + to_name + "'";
                eval.conversions.push_back(seq);
                break;
            }
            eval.conversions.push_back(seq);
        } else {
            // Variadic/no-prototype arguments are treated as generic conversion
            // quality for this first-cut overload ranking.
            ImplicitConversionSequence seq;
            seq.kind = ConversionSequenceKind::Numeric;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.from = explicit_args[i] ? explicit_args[i]->get_type() : QualType();
            seq.to = nullptr;
            seq.viable = true;
            eval.conversions.push_back(seq);
        }
    }

    return eval;
}

std::string Collect::overload_candidate_type_name(
    const OverloadCandidateEval& candidate) const {

    return (candidate.symbol && candidate.symbol->type)
        ? candidate.symbol->type.to_string()
        : std::string("<unknown>");
}

int Collect::overload_failure_reason_category(
    const std::string& reason) const {

    if (reason.rfind("requires", 0) == 0) {
        return 0; // arity/prototype mismatch
    }
    if (reason.rfind("cannot convert argument ", 0) == 0) {
        return 1; // conversion mismatch
    }
    return 2; // generic failure
}

int Collect::overload_failure_reason_argument_index(
    const std::string& reason) const {

    constexpr std::string_view kPrefix = "cannot convert argument ";
    if (reason.rfind(kPrefix, 0) != 0) {
        return std::numeric_limits<int>::max();
    }
    size_t idx_begin = kPrefix.size();
    size_t idx_end = idx_begin;
    while (idx_end < reason.size() &&
           std::isdigit(static_cast<unsigned char>(reason[idx_end]))) {
        ++idx_end;
    }
    if (idx_end == idx_begin) {
        return std::numeric_limits<int>::max();
    }
    try {
        return std::stoi(reason.substr(idx_begin, idx_end - idx_begin));
    } catch (...) {
        return std::numeric_limits<int>::max();
    }
}

bool Collect::overload_note_order_less(
    const std::vector<OverloadCandidateEval>& evaluated,
    size_t lhs_idx,
    size_t rhs_idx) const {

    const auto& lhs = evaluated[lhs_idx];
    const auto& rhs = evaluated[rhs_idx];

    if (lhs.viable != rhs.viable) {
        return lhs.viable && !rhs.viable;
    }

    if (lhs.viable && rhs.viable) {
        size_t compare_count = std::min(lhs.conversions.size(), rhs.conversions.size());
        for (size_t i = 0; i < compare_count; ++i) {
            int lhs_rank = static_cast<int>(lhs.conversions[i].rank);
            int rhs_rank = static_cast<int>(rhs.conversions[i].rank);
            if (lhs_rank != rhs_rank) {
                return lhs_rank < rhs_rank;
            }
            if (lhs.conversions[i].rank == ConversionSequenceRank::ExactMatch) {
                int lhs_subrank = exact_match_subrank(lhs.conversions[i]);
                int rhs_subrank = exact_match_subrank(rhs.conversions[i]);
                if (lhs_subrank != rhs_subrank) {
                    return lhs_subrank < rhs_subrank;
                }
            }
            if (lhs.conversions[i].rank == ConversionSequenceRank::Conversion) {
                int lhs_tiebreak = conversion_rank_tiebreak(lhs.conversions[i]);
                int rhs_tiebreak = conversion_rank_tiebreak(rhs.conversions[i]);
                if (lhs_tiebreak != rhs_tiebreak) {
                    return lhs_tiebreak < rhs_tiebreak;
                }
            }
        }

        bool lhs_non_variadic = lhs.function_type &&
            lhs.function_type->has_prototype &&
            !lhs.function_type->is_variadic;
        bool rhs_non_variadic = rhs.function_type &&
            rhs.function_type->has_prototype &&
            !rhs.function_type->is_variadic;
        if (lhs_non_variadic != rhs_non_variadic) {
            return lhs_non_variadic && !rhs_non_variadic;
        }

        bool lhs_has_prototype = lhs.function_type && lhs.function_type->has_prototype;
        bool rhs_has_prototype = rhs.function_type && rhs.function_type->has_prototype;
        if (lhs_has_prototype != rhs_has_prototype) {
            return lhs_has_prototype && !rhs_has_prototype;
        }

        bool lhs_is_template_specialization =
            is_function_template_specialization_symbol(lhs.symbol);
        bool rhs_is_template_specialization =
            is_function_template_specialization_symbol(rhs.symbol);
        if (lhs_is_template_specialization != rhs_is_template_specialization) {
            return !lhs_is_template_specialization &&
                rhs_is_template_specialization;
        }
    } else {
        int lhs_reason_category =
            overload_failure_reason_category(lhs.failure_reason);
        int rhs_reason_category =
            overload_failure_reason_category(rhs.failure_reason);
        if (lhs_reason_category != rhs_reason_category) {
            return lhs_reason_category < rhs_reason_category;
        }
        if (lhs_reason_category == 1) {
            int lhs_arg_idx =
                overload_failure_reason_argument_index(lhs.failure_reason);
            int rhs_arg_idx =
                overload_failure_reason_argument_index(rhs.failure_reason);
            if (lhs_arg_idx != rhs_arg_idx) {
                return lhs_arg_idx < rhs_arg_idx;
            }
        }
    }

    std::string lhs_type_name = overload_candidate_type_name(lhs);
    std::string rhs_type_name = overload_candidate_type_name(rhs);
    if (lhs_type_name != rhs_type_name) {
        return lhs_type_name < rhs_type_name;
    }
    return lhs_idx < rhs_idx;
}

void Collect::emit_overload_candidate_notes(
    std::string_view callee_name,
    const std::vector<OverloadCandidateEval>& evaluated,
    bool include_non_viable,
    SrcLoc loc) const {

    if (!diag_engine_) {
        return;
    }
    std::vector<size_t> note_indices;
    note_indices.reserve(evaluated.size());
    for (size_t idx = 0; idx < evaluated.size(); ++idx) {
        if (!include_non_viable && !evaluated[idx].viable) {
            continue;
        }
        note_indices.push_back(idx);
    }
    std::stable_sort(
        note_indices.begin(),
        note_indices.end(),
        [&](size_t lhs_idx, size_t rhs_idx) {
            return overload_note_order_less(evaluated, lhs_idx, rhs_idx);
        });
    std::string callee_name_str(callee_name);
    for (size_t idx : note_indices) {
        const auto& candidate = evaluated[idx];
        std::string type_name = overload_candidate_type_name(candidate);
        if (candidate.viable) {
            diag_engine_->report_note(
                "candidate function '" + callee_name_str + "' has type '" +
                    type_name + "'",
                loc);
            continue;
        }
        std::string reason =
            candidate.failure_reason.empty() ? "not viable" : candidate.failure_reason;
        diag_engine_->report_note(
            "candidate function '" + callee_name_str + "' has type '" + type_name +
                "' (" + reason + ")",
            loc);
    }
}

bool Collect::is_better_overload_candidate(
    const OverloadCandidateEval& lhs,
    const OverloadCandidateEval& rhs) {
    bool lhs_strictly_better = is_strictly_better_conversion_profile(
        lhs.conversions,
        lhs.function_type,
        rhs.conversions,
        rhs.function_type);
    if (lhs_strictly_better) {
        return true;
    }

    bool rhs_strictly_better = is_strictly_better_conversion_profile(
        rhs.conversions,
        rhs.function_type,
        lhs.conversions,
        lhs.function_type);
    if (rhs_strictly_better) {
        return false;
    }

    bool lhs_is_template_specialization =
        is_function_template_specialization_symbol(lhs.symbol);
    bool rhs_is_template_specialization =
        is_function_template_specialization_symbol(rhs.symbol);
    if (lhs_is_template_specialization != rhs_is_template_specialization) {
        return !lhs_is_template_specialization && rhs_is_template_specialization;
    }
    if (lhs_is_template_specialization && rhs_is_template_specialization) {
        auto* lhs_template = function_template_primary_for_symbol(lhs.symbol);
        auto* rhs_template = function_template_primary_for_symbol(rhs.symbol);
        if (lhs_template != rhs_template) {
            auto ordering =
                compare_function_template_partial_ordering(
                    lhs_template,
                    rhs_template);
            if (ordering == TemplatePartialOrderingResult::LhsMoreSpecialized) {
                return true;
            }
            if (ordering == TemplatePartialOrderingResult::RhsMoreSpecialized) {
                return false;
            }
        }
    }

    return false;
}

std::optional<size_t> Collect::select_best_overload_candidate_index(
    const std::vector<OverloadCandidateEval>& evaluated,
    const std::vector<size_t>& viable_indices) {

    std::optional<size_t> best_index;
    for (size_t idx : viable_indices) {
        bool better_than_all = true;
        for (size_t other : viable_indices) {
            if (idx == other) {
                continue;
            }
            bump_overload_pairwise_comparisons();
            if (!is_better_overload_candidate(
                    evaluated[idx], evaluated[other])) {
                better_than_all = false;
                break;
            }
        }
        if (!better_than_all) {
            continue;
        }
        if (best_index.has_value()) {
            return std::nullopt;
        }
        best_index = idx;
    }
    return best_index;
}

std::unique_ptr<Expr> Collect::resolve_overloaded_call_candidates(
    std::string_view callee_name,
    const std::vector<OverloadCallCandidate>& candidates,
    const std::vector<std::unique_ptr<Expr>>& explicit_args,
    Expr* implicit_object_arg,
    SrcLoc loc,
    std::shared_ptr<Symbol>& selected_symbol_out,
    OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) {

    selected_symbol_out = nullptr;
    selected_implicit_object_arg_kind_out = OverloadImplicitObjectArgKind::None;
    if (!lang_opts_.is_cxx_mode() || candidates.empty()) {
        return nullptr;
    }
    bump_overload_resolve_calls();

    OverloadConversionMemoCache conversion_cache;
    conversion_cache.reserve(candidates.size() * 2);

    std::vector<OverloadCandidateEval> evaluated;
    evaluated.reserve(candidates.size());
    for (const auto& candidate_info : candidates) {
        evaluated.push_back(evaluate_overload_call_candidate(
            candidate_info, explicit_args, implicit_object_arg, &conversion_cache));
    }

    std::vector<size_t> viable_indices;
    viable_indices.reserve(evaluated.size());
    for (size_t idx = 0; idx < evaluated.size(); ++idx) {
        if (evaluated[idx].viable) {
            viable_indices.push_back(idx);
        }
    }

    if (viable_indices.empty()) {
        report_error(
            "no matching function for call to '" + std::string(callee_name) + "'",
            loc);
        emit_overload_candidate_notes(callee_name, evaluated, true, loc);
        return collect_make<ErrorExpr>("no matching overload", loc);
    }

    auto best_index =
        select_best_overload_candidate_index(evaluated, viable_indices);
    if (!best_index.has_value()) {
        report_error("call to '" + std::string(callee_name) + "' is ambiguous", loc);
        emit_overload_candidate_notes(callee_name, evaluated, false, loc);
        return collect_make<ErrorExpr>("ambiguous overload", loc);
    }

    selected_symbol_out = evaluated[*best_index].symbol;
    selected_implicit_object_arg_kind_out =
        evaluated[*best_index].implicit_object_arg_kind;
    return nullptr;
}
