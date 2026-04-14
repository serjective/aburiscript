#include "collect.h"
#include "collect_internal.h"

using namespace collect_internal;

std::unique_ptr<Expr> Collect::collect_apply_standard_conversions(std::unique_ptr<Expr> expr,
                                                                  ExprUseContext context,
                                                                  QualType target_type) const {

    if (!expr) {
        return nullptr;
    }
    auto expr_type = expr->get_type();
    if (!expr_type) {
        return expr;
    }

    struct ConversionPolicy {
        bool decay_function = false;
        bool decay_array = false;
        bool lvalue_to_rvalue = false;
        bool allow_target_cast = true;
        bool no_conversions = false;
    };

    // Conversion matrix by expression-use context:
    // - RValue: l2r + decay
    // - Condition: l2r + decay
    // - CallCallee/CallArgument: l2r + decay
    // - ArraySubscriptBase: l2r + decay
    // - ArraySubscriptIndex: l2r only
    // - ConditionalOperand: l2r + decay
    // - InitScalar: l2r only
    // - InitAggregate/LValueRequired/Unevaluated: no conversions
    // - ExpressionStatement: l2r + decay
    auto policy_for_context = [](ExprUseContext c) -> ConversionPolicy {
        switch (c) {
            case ExprUseContext::RValue:
                return {true, true, true, true, false};
            case ExprUseContext::Condition:
                return {true, true, true, true, false};
            case ExprUseContext::CallCallee:
                return {true, true, true, true, false};
            case ExprUseContext::CallArgument:
                return {true, true, true, true, false};
            case ExprUseContext::ArraySubscriptBase:
                return {true, true, true, true, false};
            case ExprUseContext::ArraySubscriptIndex:
                return {false, false, true, true, false};
            case ExprUseContext::ConditionalOperand:
                return {true, true, true, true, false};
            case ExprUseContext::InitScalar:
                return {true, true, true, true, false};
            case ExprUseContext::InitAggregate:
                return {false, false, false, true, true};
            case ExprUseContext::LValueRequired:
                return {false, false, false, true, true};
            case ExprUseContext::Unevaluated:
                return {false, false, false, true, true};
            case ExprUseContext::ExpressionStatement:
                return {true, true, true, true, false};
        }
        return {};
    };

    const ConversionPolicy policy = policy_for_context(context);

    if (policy.no_conversions) {
        if (target_type && policy.allow_target_cast) {
            return cast_if_needed(std::move(expr), target_type);
        }
        return expr;
    }

    auto expr_kind = canonical_type_kind(expr_type, ast_ctx_.get());

    if (expr_kind == TypeKind::Function && policy.decay_function) {
        auto fn_type = desugar_type(expr_type, ast_ctx_.get());
        auto ptr_type = QualType(std::make_shared<PointerType>(fn_type));
        expr = collect_make<ImplicitCast>(ImplicitCastTypes::FUNCTION_TO_POINTER, std::move(expr), ptr_type);
        expr_type = expr->get_type();
        expr_kind = canonical_type_kind(expr_type, ast_ctx_.get());
    }

    if (expr_kind == TypeKind::Array && policy.decay_array) {
        auto array_type =
            desugar_type(expr_type, ast_ctx_.get()).as_shared<ArrayType>();
        auto element_type = array_type->element_type.with_qualifiers(expr_type.get_qualifiers());
        auto ptr_type = QualType(std::make_shared<PointerType>(element_type));
        expr = collect_make<ImplicitCast>(ImplicitCastTypes::ARRAY_TO_POINTER, std::move(expr), ptr_type);
        expr_type = expr->get_type();
        expr_kind = canonical_type_kind(expr_type, ast_ctx_.get());
    }

    if (!policy.lvalue_to_rvalue) {
        if (target_type && policy.allow_target_cast) {
            return cast_if_needed(std::move(expr), target_type);
        }
        return expr;
    }

    auto value_category = classify_value_category(expr.get());
    bool needs_glvalue_to_rvalue =
        value_category == ValueCategory::LValue || value_category == ValueCategory::XValue;
    if (!needs_glvalue_to_rvalue || expr->letPassthrough()) {
        if (target_type && policy.allow_target_cast) {
            return cast_if_needed(std::move(expr), target_type);
        }
        return expr;
    }

    if (expr_type->isVoid()) {
        if (target_type && policy.allow_target_cast) {
            return cast_if_needed(std::move(expr), target_type);
        }
        return expr;
    }

    if (expr_kind == TypeKind::Array || expr_kind == TypeKind::Function) {
        if (target_type && policy.allow_target_cast) {
            return cast_if_needed(std::move(expr), target_type);
        }
        return expr;
    }

    QualType l2r_type = expr_type;
    if (expr_kind == TypeKind::Reference) {
        QualType referred = remove_reference(expr_type, ast_ctx_.get());
        if (referred) {
            l2r_type = referred;
        }
    }
    if (auto* member = dyn_cast<MemberExpr>(expr.get())) {
        if (member->is_bitfield && ast_ctx_) {
            const auto* bf_info = ast_ctx_->get_bitfield_info(member->node_id);
            auto int_type = get_builtin_int();
            auto uint_type = get_builtin_uint();
            int64_t int_width = int_type ? int_type->getWidth() : 0;
            if (bf_info && bf_info->bit_width > 0 && int_width > 0) {
                int64_t bit_width = static_cast<int64_t>(bf_info->bit_width);
                if (bit_width < int_width) {
                    l2r_type = QualType(int_type);
                } else if (bit_width == int_width) {
                    if (expr_type->isUnsigned()) {
                        l2r_type = uint_type ? QualType(uint_type) : expr_type;
                    } else {
                        l2r_type = QualType(int_type);
                    }
                }
            }
        }
    }

    expr = collect_make<ImplicitCast>(ImplicitCastTypes::LVALUE_TO_RVALUE, std::move(expr), l2r_type);
    if (target_type && policy.allow_target_cast) {
        expr = cast_if_needed(std::move(expr), target_type);
    }
    return expr;
}


std::unique_ptr<Expr> Collect::collect_value_expression(std::unique_ptr<Expr> expr) const {

    return collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
}


std::unique_ptr<Expr> Collect::collect_condition_expression(std::unique_ptr<Expr> condition, SrcLoc loc, const std::string& stmt_name) const {
    if (lang_opts_.is_cxx_mode() && condition && ast_ctx_) {
        auto condition_type = condition->get_type();
        bool condition_is_dependent =
            expression_depends_on_template_parameters(condition.get()) ||
            (condition_type &&
             type_depends_on_template_parameters(condition_type, ast_ctx_.get()));
        if (!condition_is_dependent &&
            condition_type &&
            !allows_condition_conversion(condition_type, ast_ctx_.get())) {
            QualType bool_type(get_builtin_bool());
            auto conversion_match =
                const_cast<Collect*>(this)->select_cpp_user_defined_conversion(
                    condition.get(),
                    bool_type,
                    /*allow_explicit_constructors=*/false,
                    /*allow_explicit_conversion_functions=*/true);
            if (conversion_match.has_value()) {
                condition =
                    const_cast<Collect*>(this)
                        ->build_cpp_selected_user_defined_conversion_expr(
                            std::move(condition),
                            bool_type,
                            *conversion_match,
                            loc);
            }
        }
    }

    condition = collect_apply_standard_conversions(std::move(condition), ExprUseContext::Condition);
    if (!condition) {
        return nullptr;
    }
    auto condition_type = condition->get_type();
    if (!condition_type) {
        report_error(stmt_name + " condition has unknown type", loc);
        return condition;
    }
    bool condition_is_dependent =
        lang_opts_.is_cxx_mode() &&
        (expression_depends_on_template_parameters(condition.get()) ||
         type_depends_on_template_parameters(condition_type, ast_ctx_.get()));
    if (condition_is_dependent) {
        return condition;
    }
    if (!condition_type->isScalar()) {
        if (!allows_condition_conversion(condition_type, ast_ctx_.get())) {
            report_error("statement requires expression of scalar type ('" +
                condition_type.to_string() + "' invalid)", loc);
        }
    } else if (!allows_condition_conversion(condition_type, ast_ctx_.get())) {
        report_error("statement requires expression of scalar type ('" +
            condition_type.to_string() + "' invalid)", loc);
    }
    return condition;
}
