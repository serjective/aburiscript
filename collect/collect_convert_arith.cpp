#include "collect.h"

QualType Collect::integer_promotion_type(QualType type) const {

    if (!type || !type->isInteger()) {
        return type;
    }
    auto canonical = desugar_type(type);
    auto canonical_kind = canonical ? canonical->kind : TypeKind::Other;
    if (canonical_kind == TypeKind::Enum) {
        return QualType(get_builtin_int());
    }
    auto builtin = canonical.as_shared<BuiltinType>();
    if (!builtin) {
        return canonical;
    }
    auto int_type = get_builtin_int();
    if (!int_type) {
        return canonical;
    }
    auto int_builtin = dyn_cast_shared<BuiltinType>(int_type);
    if (!int_builtin) {
        return canonical;
    }
    if (builtin->getRank() < int_builtin->getRank()) {
        return QualType(int_type);
    }
    return canonical;
}


std::unique_ptr<Expr> Collect::apply_default_argument_promotions(std::unique_ptr<Expr> expr) const {

    if (!expr) {
        return nullptr;
    }
    auto expr_type = expr->get_type();
    if (!expr_type) {
        return expr;
    }
    auto expr_canonical = desugar_type(expr_type);
    if (expr_canonical->isInteger()) {
        auto promoted = integer_promotion_type(expr_canonical);
        return cast_if_needed(std::move(expr), promoted);
    }
    auto builtin = expr_canonical.as_shared<BuiltinType>();
    if (builtin && builtin->builtin_kind == BuiltinTypes::Float) {
        return cast_if_needed(std::move(expr), QualType(get_builtin_double()));
    }
    return expr;
}


QualType Collect::usual_arithmetic_conversion_type(QualType lhs, QualType rhs) const {

    if (!lhs || !rhs) {
        return lhs ? lhs : rhs;
    }
    lhs = desugar_type(lhs);
    rhs = desugar_type(rhs);
    bool either_complex = lhs->isComplex() || rhs->isComplex();
    if (auto c1 = lhs.as_shared<ComplexType>()) {
        lhs = QualType(c1->element_type);
    }
    if (auto c2 = rhs.as_shared<ComplexType>()) {
        rhs = QualType(c2->element_type);
    }

    auto lhs_builtin = lhs.as_shared<BuiltinType>();
    auto rhs_builtin = rhs.as_shared<BuiltinType>();

    auto pick_floating = [&](BuiltinTypes kind) -> QualType {
        auto builtin = ast_ctx_ && ast_ctx_->type_ctx ? ast_ctx_->type_ctx->get_builtin(kind) : nullptr;
        return QualType(builtin);
    };

    QualType common_real = nullptr;
    if ((lhs_builtin && lhs_builtin->builtin_kind == BuiltinTypes::LongDouble) ||
        (rhs_builtin && rhs_builtin->builtin_kind == BuiltinTypes::LongDouble)) {
        common_real = pick_floating(BuiltinTypes::LongDouble);
    } else if ((lhs_builtin && lhs_builtin->builtin_kind == BuiltinTypes::Double) ||
        (rhs_builtin && rhs_builtin->builtin_kind == BuiltinTypes::Double)) {
        common_real = pick_floating(BuiltinTypes::Double);
    } else if ((lhs_builtin && lhs_builtin->builtin_kind == BuiltinTypes::Float) ||
        (rhs_builtin && rhs_builtin->builtin_kind == BuiltinTypes::Float)) {
        common_real = pick_floating(BuiltinTypes::Float);
    } else if ((lhs_builtin && lhs_builtin->builtin_kind == BuiltinTypes::Float16) ||
        (rhs_builtin && rhs_builtin->builtin_kind == BuiltinTypes::Float16)) {
        common_real = pick_floating(BuiltinTypes::Float16);
    } else {
        lhs = integer_promotion_type(lhs);
        rhs = integer_promotion_type(rhs);
        lhs_builtin = lhs.as_shared<BuiltinType>();
        rhs_builtin = rhs.as_shared<BuiltinType>();
        if (!lhs_builtin || !rhs_builtin) {
            return lhs;
        }
        if (lhs_builtin->equals(*rhs_builtin)) {
            common_real = lhs;
        } else {
            bool lhs_signed = !lhs_builtin->isUnsigned();
            bool rhs_signed = !rhs_builtin->isUnsigned();
            if (lhs_signed == rhs_signed) {
                common_real = (lhs_builtin->getRank() < rhs_builtin->getRank()) ? rhs : lhs;
            } else if (!lhs_signed && lhs_builtin->getRank() >= rhs_builtin->getRank()) {
                common_real = lhs;
            } else if (!rhs_signed && rhs_builtin->getRank() >= lhs_builtin->getRank()) {
                common_real = rhs;
            } else if (lhs_signed) {
                if (lhs_builtin->getWidth() > rhs_builtin->getWidth()) {
                    common_real = lhs;
                } else {
                    common_real = unsigned_counterpart(lhs);
                }
            } else {
                if (rhs_builtin->getWidth() > lhs_builtin->getWidth()) {
                    common_real = rhs;
                } else {
                    common_real = unsigned_counterpart(rhs);
                }
            }
        }
    }

    if (!either_complex) {
        return common_real;
    }
    auto real_builtin = common_real.as_shared<BuiltinType>();
    if (!real_builtin || !ast_ctx_ || !ast_ctx_->type_ctx) {
        return common_real;
    }
    auto complex_type = ast_ctx_->type_ctx->get_complex(real_builtin->builtin_kind);
    return QualType(complex_type);
}


QualType Collect::unsigned_counterpart(QualType type) const {

    auto canonical = desugar_type(type);
    auto builtin = canonical.as_shared<BuiltinType>();
    if (!builtin || !ast_ctx_ || !ast_ctx_->type_ctx) {
        return canonical;
    }
    switch (builtin->builtin_kind) {
        case BuiltinTypes::Char:
            return QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::UChar));
        case BuiltinTypes::Short:
            return QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::UShort));
        case BuiltinTypes::Int:
            return QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::UInt));
        case BuiltinTypes::Long:
            return QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::ULong));
        case BuiltinTypes::LongLong:
            return QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::ULongLong));
        case BuiltinTypes::Int128:
            return QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::UInt128));
        default:
            return canonical;
    }
}
