#ifndef ABURI_COLLECT_DECL_INTERNAL_H
#define ABURI_COLLECT_DECL_INTERNAL_H

#include "collect_internal.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"
#include <cerrno>
#include <cstdlib>
#include <functional>
#include <limits>

namespace collect_decl_internal {
namespace {

// Import shared helpers from collect_internal to avoid duplication.
using collect_internal::clone_top_level_incomplete_array;
using collect_internal::describe_consteval_failure;

std::optional<int64_t> try_evaluate_float_cast_array_bound(const Expr* expr) {
    if (!expr) {
        return std::nullopt;
    }
    auto explicit_cast = dyn_cast<const ExplicitCast>(expr);
    if (!explicit_cast || !explicit_cast->ctype || !explicit_cast->ctype->isInteger()) {
        return std::nullopt;
    }

    const Expr* inner = explicit_cast->expr.get();
    while (auto implicit_cast = dyn_cast<const ImplicitCast>(inner)) {
        inner = implicit_cast->expr.get();
    }
    auto float_lit = dyn_cast<const FloatingLiteral>(inner);
    if (!float_lit) {
        return std::nullopt;
    }

    errno = 0;
    char* end = nullptr;
    long double parsed = std::strtold(float_lit->value.c_str(), &end);
    if (end == float_lit->value.c_str()) {
        return std::nullopt;
    }
    if (*end != '\0') {
        bool has_valid_suffix =
            ((end[0] == 'f' || end[0] == 'F' || end[0] == 'l' || end[0] == 'L') &&
             end[1] == '\0');
        if (!has_valid_suffix) {
            return std::nullopt;
        }
    }
    if (errno == ERANGE) {
        return std::nullopt;
    }
    if (parsed < static_cast<long double>(std::numeric_limits<int64_t>::min()) ||
        parsed > static_cast<long double>(std::numeric_limits<int64_t>::max())) {
        return std::nullopt;
    }
    return static_cast<int64_t>(parsed);
}

bool validate_constexpr_initializer_expr(const Collect& collect,
                                         Expr* expr,
                                         std::string& out_failure,
                                         SrcLoc& out_loc) {
    if (!expr) {
        return true;
    }
    if (collect.expression_depends_on_template_parameters(expr)) {
        return true;
    }

    ConstEvalResult const_eval = evaluate_with_consteval_compat(
        expr, ConstEvalMode::c23_constexpr_initializer());
    if (const_eval.status == ConstEvalStatus::Constant) {
        return true;
    }
    out_failure = describe_consteval_failure(const_eval);
    out_loc = expr->location;
    return false;
}

std::shared_ptr<Symbol> lookup_ordinary_symbol(
    const std::shared_ptr<Scope>& scope,
    const std::string& name,
    bool look_parents) {

    return LookupEngine::lookup_unqualified_ordinary(
        name, scope, look_parents, LookupEngine::OrdinaryFilter::Any);
}

bool is_file_or_namespace_scope(const std::shared_ptr<Scope>& scope) {
    return scope && scope_flags_contains(scope->flags, ScopeFlags::FileScope);
}

bool function_signatures_match_ignoring_return_type(const QualType& lhs_type,
                                                    const QualType& rhs_type) {
    auto lhs_fn = lhs_type.as_shared<FunctionType>();
    auto rhs_fn = rhs_type.as_shared<FunctionType>();
    if (!lhs_fn || !rhs_fn) {
        return false;
    }
    FunctionType rhs_with_lhs_return = *rhs_fn;
    rhs_with_lhs_return.ret_type = lhs_fn->ret_type;
    return lhs_fn->equals(rhs_with_lhs_return);
}

LanguageLinkage effective_language_linkage(LanguageLinkage linkage,
                                           bool is_cxx_mode) {
    if (linkage != LanguageLinkage::None) {
        return linkage;
    }
    return is_cxx_mode ? LanguageLinkage::CXX : LanguageLinkage::C;
}

int exact_match_subrank_for_overload(
    const Collect::ImplicitConversionSequence& seq) {
    if (seq.exact_subrank >= 0) {
        return seq.exact_subrank;
    }
    switch (seq.kind) {
        case Collect::ConversionSequenceKind::Identity:
            return 0;
        case Collect::ConversionSequenceKind::Qualification:
            return 1;
        case Collect::ConversionSequenceKind::UserDefined:
            return 2;
        default:
            return 2;
    }
}

bool is_this_parameter_for_record(const QualType& param_type,
                                  const std::shared_ptr<ObjectType>& record_type,
                                  const ASTContext* ast_ctx) {
    if (!param_type || !record_type) {
        return false;
    }
    auto ptr_type = desugar_type(param_type, ast_ctx).as_shared<PointerType>();
    if (!ptr_type || !ptr_type->pointed_type) {
        return false;
    }
    auto pointed_record =
        desugar_type(ptr_type->pointed_type, ast_ctx).as_shared<ObjectType>();
    if (!pointed_record) {
        return false;
    }
    if (pointed_record->get_decl() && record_type->get_decl()) {
        return pointed_record->get_decl() == record_type->get_decl();
    }
    return QualType(pointed_record).equals_unqualified(QualType(record_type));
}

bool is_this_parameter_for_record(const QualType& param_type,
                                  const std::shared_ptr<ObjectType>& record_type) {
    return is_this_parameter_for_record(
        param_type, record_type, get_active_side_table_ast_context());
}
} // namespace
} // namespace collect_decl_internal

#endif // ABURI_COLLECT_DECL_INTERNAL_H
