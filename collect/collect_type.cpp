#include "collect.h"

namespace {
bool sizeof_alignof_target_still_dependent(QualType target_type,
                                           const ASTContext* ast_ctx) {
    return target_type &&
           type_depends_on_template_parameters(target_type, ast_ctx);
}
}

void Collect::finalize_sizeof_node(SizeOfExpr* node, const std::shared_ptr<CType>& target_type, SrcLoc loc) {

    if (!node) {
        return;
    }
    auto size_t_type = get_builtin_ulong();
    node->result_type = size_t_type ? QualType(size_t_type) : QualType(get_builtin_int());
    if (!target_type) {
        report_error("sizeof applied to expression with unknown type", loc);
        return;
    }
    QualType target_qt(target_type);
    if (sizeof_alignof_target_still_dependent(target_qt, ast_ctx_.get())) {
        if (node->type_operand) {
            node->type_operand = target_qt;
        }
        node->is_runtime_sizeof = false;
        return;
    }

    auto resolved_target = finalize_deferred_semantic_type(target_qt, loc);
    if (!resolved_target ||
        sizeof_alignof_target_still_dependent(resolved_target, ast_ctx_.get())) {
        if (node->type_operand) {
            node->type_operand = resolved_target ? resolved_target : target_qt;
        }
        node->is_runtime_sizeof = false;
        return;
    }
    auto canonical_target = desugar_type(resolved_target, ast_ctx_.get());
    if (node->type_operand) {
        node->type_operand = canonical_target;
    }
    bool incomplete_array = false;
    if (auto arr = canonical_target.as_shared<ArrayType>()) {
        incomplete_array = (arr->size_kind == ArraySizeKind::Incomplete) ||
            (arr->size_kind == ArraySizeKind::Constant && !arr->size.has_value());
    }
    if ((canonical_target->isIncomplete() && !canonical_target->isVoid()) || incomplete_array) {
        report_error("sizeof cannot be applied to incomplete type", loc);
    }
    node->is_runtime_sizeof = type_contains_vla(canonical_target.get_shared());
}


void Collect::finalize_alignof_node(AlignOfExpr* node, const std::shared_ptr<CType>& target_type, SrcLoc loc) {

    if (!node) {
        return;
    }
    auto size_t_type = get_builtin_ulong();
    node->result_type = size_t_type ? QualType(size_t_type) : QualType(get_builtin_int());
    if (!target_type) {
        report_error("_Alignof applied to expression with unknown type", loc);
        return;
    }
    QualType target_qt(target_type);
    if (sizeof_alignof_target_still_dependent(target_qt, ast_ctx_.get())) {
        node->type_operand = target_qt;
        return;
    }

    auto resolved_target = finalize_deferred_semantic_type(target_qt, loc);
    if (!resolved_target ||
        sizeof_alignof_target_still_dependent(resolved_target, ast_ctx_.get())) {
        node->type_operand = resolved_target ? resolved_target : target_qt;
        return;
    }
    auto canonical_target = desugar_type(resolved_target, ast_ctx_.get());
    node->type_operand = canonical_target;
    bool incomplete_array = false;
    if (auto arr = canonical_target.as_shared<ArrayType>()) {
        incomplete_array = (arr->size_kind == ArraySizeKind::Incomplete) ||
            (arr->size_kind == ArraySizeKind::Constant && !arr->size.has_value());
    }
    if ((!canonical_target->isVoid() && canonical_target->isIncomplete()) || incomplete_array) {
        report_error("_Alignof cannot be applied to incomplete type", loc);
    }
}


std::shared_ptr<CType> Collect::get_builtin_int() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Int);
}


std::shared_ptr<CType> Collect::get_builtin_uint() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::UInt);
}


std::shared_ptr<CType> Collect::get_builtin_longlong() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::LongLong);
}


std::shared_ptr<CType> Collect::get_builtin_double() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Double);
}


std::shared_ptr<CType> Collect::get_builtin_float() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Float);
}


std::shared_ptr<CType> Collect::get_builtin_long_double() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::LongDouble);
}


std::shared_ptr<CType> Collect::get_builtin_long() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Long);
}


std::shared_ptr<CType> Collect::get_builtin_ulong() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::ULong);
}


std::shared_ptr<CType> Collect::get_builtin_char() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Char);
}


std::shared_ptr<CType> Collect::get_builtin_void() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Void);
}


std::shared_ptr<CType> Collect::get_builtin_bool() const {

    if (!ast_ctx_ || !ast_ctx_->type_ctx) {
        return nullptr;
    }
    return ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Bool);
}


QualType Collect::decay_parameter_type(QualType type) const {

    if (!type) {
        return type;
    }
    auto canonical = desugar_type(type, ast_ctx_.get());
    auto canonical_kind = canonical ? canonical->kind : TypeKind::Other;
    if (canonical_kind == TypeKind::Array) {
        auto arr = canonical.as_shared<ArrayType>();
        return QualType(std::make_shared<PointerType>(arr->element_type), type.get_qualifiers());
    }
    if (canonical_kind == TypeKind::Function) {
        return QualType(std::make_shared<PointerType>(canonical));
    }
    return type;
}


std::unique_ptr<Expr> Collect::cast_if_needed(std::unique_ptr<Expr> expr, QualType target_type) const {

    if (!expr || !target_type) {
        return expr;
    }
    auto expr_type = expr->get_type();
    if (!expr_type) {
        return expr;
    }
    if (expr_type->equals(*target_type.get_shared())) {
        return expr;
    }
    if (canonical_type_kind(target_type, ast_ctx_.get()) == TypeKind::Vector &&
        canonical_type_kind(expr_type, ast_ctx_.get()) != TypeKind::Vector) {
        auto vec_ty = desugar_type(target_type, ast_ctx_.get()).as_shared<VectorType>();
        if (vec_ty) {
            expr = cast_if_needed(std::move(expr), vec_ty->element_type);
        }
        return collect_make<ImplicitCast>(ImplicitCastTypes::VECTOR_SPLAT, std::move(expr), target_type);
    }
    return collect_make<ImplicitCast>(std::move(expr), target_type);
}
