#include "types.h"
#include "abi/target_info.h"
#include "abi/bitfield_layout.h"
#include "abi/abi_policy.h"
#include "ast.h"
#include "ast_context.h"
#include "collect/query_context.h"
#include "helpers/casting.h"
#include "helpers/auto_type_utils.h"
#include <algorithm>
#include <cassert>
#include <functional>
#include <sstream>
#include <utility>
#include <unordered_map>
#include <unordered_set>

namespace {
void set_template_binding_error(std::string* error_out,
                                const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
}

const ASTContext* effective_ast_context(const ASTContext* ast_ctx) {
    return ast_ctx ? ast_ctx : get_active_side_table_ast_context();
}

ASTContext* effective_ast_context(ASTContext* ast_ctx) {
    return ast_ctx ? ast_ctx : get_active_side_table_ast_context();
}

const ASTContext* record_semantics_ast_context(const ObjectDecl* record_decl,
                                               const ASTContext* ast_ctx) {
    if (ast_ctx) {
        return ast_ctx;
    }
    if (const auto* owner = get_side_table_ast_context_for(record_decl)) {
        return owner;
    }
    return nullptr;
}

ASTContext* record_semantics_ast_context(const ObjectDecl* record_decl,
                                         ASTContext* ast_ctx) {
    if (ast_ctx) {
        return ast_ctx;
    }
    if (auto* owner = get_side_table_ast_context_for(record_decl)) {
        return owner;
    }
    return nullptr;
}

const ASTContext* enum_semantics_ast_context(const EnumDecl* enum_decl,
                                             const ASTContext* ast_ctx) {
    if (ast_ctx) {
        return ast_ctx;
    }
    if (const auto* owner = get_side_table_ast_context_for(enum_decl)) {
        return owner;
    }
    return nullptr;
}

ASTContext* enum_semantics_ast_context(const EnumDecl* enum_decl,
                                       ASTContext* ast_ctx) {
    if (ast_ctx) {
        return ast_ctx;
    }
    if (auto* owner = get_side_table_ast_context_for(enum_decl)) {
        return owner;
    }
    return nullptr;
}

bool is_builtin_nullptr_type_impl(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    type = desugar_type(type, ast_ctx);
    auto builtin = type.as_shared<BuiltinType>();
    return builtin && builtin->builtin_kind == BuiltinTypes::NullPtr;
}

const TemplateDecl* canonical_template_decl_identity(const TemplateDecl* decl) {
    return decl ? get_template_decl_canonical_decl(decl) : nullptr;
}

std::string template_decl_display_name(const TemplateDecl* decl) {
    if (!decl) {
        return {};
    }
    if (auto* alias_template =
            dyn_cast<AliasTemplateDecl>(const_cast<TemplateDecl*>(decl))) {
        return alias_template->alias_decl() ? alias_template->alias_decl()->name : "";
    }
    if (auto* function_template =
            dyn_cast<FunctionTemplateDecl>(const_cast<TemplateDecl*>(decl))) {
        return function_template->function_decl()
            ? function_template->function_decl()->name
            : "";
    }
    if (auto* variable_template =
            dyn_cast<VariableTemplateDecl>(const_cast<TemplateDecl*>(decl))) {
        return variable_template->variable_decl()
            ? variable_template->variable_decl()->name
            : "";
    }
    if (auto* class_template =
            dyn_cast<ClassTemplateDecl>(const_cast<TemplateDecl*>(decl))) {
        return class_template->record_decl() ? class_template->record_decl()->name : "";
    }
    if (auto* variable_partial =
            dyn_cast<VariableTemplatePartialSpecializationDecl>(
                const_cast<TemplateDecl*>(decl))) {
        return variable_partial->variable_decl()
            ? variable_partial->variable_decl()->name
            : "";
    }
    if (auto* partial_specialization =
            dyn_cast<ClassTemplatePartialSpecializationDecl>(
                const_cast<TemplateDecl*>(decl))) {
        return partial_specialization->record_decl()
            ? partial_specialization->record_decl()->name
            : "";
    }
    return {};
}

const Expr* strip_structural_implicit_casts(const Expr* expr) {
    auto* current = const_cast<Expr*>(expr);
    while (auto* cast = dyn_cast<ImplicitCast>(current)) {
        if (!cast->expr) {
            break;
        }
        current = cast->expr.get();
    }
    return current;
}

bool template_parameter_structurally_matches(
    const TemplateParameterDecl* lhs,
    const TemplateParameterDecl* rhs) {
    if (!lhs || !rhs) {
        return lhs == rhs;
    }
    return lhs->get_kind() == rhs->get_kind() &&
           lhs->depth == rhs->depth &&
           lhs->index == rhs->index &&
           lhs->is_parameter_pack == rhs->is_parameter_pack;
}

bool expr_structurally_matches(const Expr* lhs, const Expr* rhs);

bool template_argument_pack_parameters_structurally_match(
    const TemplateArgument& lhs,
    const TemplateArgument& rhs) {
    if (lhs.expands_parameter_pack != rhs.expands_parameter_pack ||
        lhs.pack_expansion_parameters.size() != rhs.pack_expansion_parameters.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.pack_expansion_parameters.size(); ++idx) {
        if (!template_parameter_structurally_matches(
                lhs.pack_expansion_parameters[idx],
                rhs.pack_expansion_parameters[idx])) {
            return false;
        }
    }
    return true;
}

bool template_argument_structurally_matches(const TemplateArgument& lhs,
                                            const TemplateArgument& rhs) {
    if (lhs.kind != rhs.kind ||
        !template_argument_pack_parameters_structurally_match(lhs, rhs)) {
        return false;
    }

    switch (lhs.kind) {
        case TemplateArgumentKind::Type:
            return lhs.type.equals_qualified(rhs.type);
        case TemplateArgumentKind::Value:
            if (!lhs.value_type.equals_qualified(rhs.value_type) ||
                lhs.is_dependent != rhs.is_dependent) {
                return false;
            }
            if (lhs.is_dependent) {
                if (lhs.referenced_parameter || rhs.referenced_parameter) {
                    return template_parameter_structurally_matches(
                        lhs.referenced_parameter,
                        rhs.referenced_parameter);
                }
                if (lhs.value_expr && rhs.value_expr) {
                    return expr_structurally_matches(
                        lhs.value_expr.get(),
                        rhs.value_expr.get());
                }
                return lhs.value_spelling == rhs.value_spelling;
            }
            return lhs.equals(rhs);
        case TemplateArgumentKind::Template:
            if (lhs.is_dependent != rhs.is_dependent) {
                return false;
            }
            if (lhs.is_dependent) {
                if (lhs.referenced_parameter || rhs.referenced_parameter) {
                    return template_parameter_structurally_matches(
                        lhs.referenced_parameter,
                        rhs.referenced_parameter);
                }
                if (!lhs.dependent_template_member_name.empty() ||
                    !rhs.dependent_template_member_name.empty()) {
                    return lhs.dependent_template_member_name ==
                               rhs.dependent_template_member_name &&
                           lhs.dependent_template_qualifier_type
                               .equals_qualified(
                                   rhs.dependent_template_qualifier_type);
                }
                return lhs.template_name == rhs.template_name;
            }
            return lhs.equals(rhs);
    }
    return false;
}

bool template_argument_list_structurally_matches(
    const std::optional<std::vector<TemplateArgument>>& lhs,
    const std::optional<std::vector<TemplateArgument>>& rhs) {
    if (lhs.has_value() != rhs.has_value()) {
        return false;
    }
    if (!lhs.has_value()) {
        return true;
    }
    if (lhs->size() != rhs->size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs->size(); ++idx) {
        if (!template_argument_structurally_matches((*lhs)[idx], (*rhs)[idx])) {
            return false;
        }
    }
    return true;
}

bool dependent_lookup_qualifier_structurally_matches(
    const DependentLookupQualifier& lhs,
    const DependentLookupQualifier& rhs) {
    return lhs.has_global_qualifier == rhs.has_global_qualifier &&
           lhs.is_type_qualified == rhs.is_type_qualified &&
           lhs.is_current_instantiation == rhs.is_current_instantiation &&
           lhs.names_dependent_base == rhs.names_dependent_base &&
           lhs.qualifiers == rhs.qualifiers &&
           lhs.qualifier_type.equals_qualified(rhs.qualifier_type);
}

bool expr_vector_structurally_matches(
    const std::vector<std::unique_ptr<Expr>>& lhs,
    const std::vector<std::unique_ptr<Expr>>& rhs) {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.size(); ++idx) {
        if (!expr_structurally_matches(lhs[idx].get(), rhs[idx].get())) {
            return false;
        }
    }
    return true;
}

bool expr_structurally_matches(const Expr* lhs, const Expr* rhs) {
    lhs = strip_structural_implicit_casts(lhs);
    rhs = strip_structural_implicit_casts(rhs);
    if (!lhs || !rhs) {
        return lhs == rhs;
    }
    if (lhs->get_kind() != rhs->get_kind()) {
        return false;
    }

    switch (lhs->get_kind()) {
        case StmtKind::IntegerLiteral: {
            const auto* lhs_int = static_cast<const IntegerLiteral*>(lhs);
            const auto* rhs_int = static_cast<const IntegerLiteral*>(rhs);
            return lhs_int->get_value() == rhs_int->get_value();
        }
        case StmtKind::FloatingLiteral: {
            const auto* lhs_float = static_cast<const FloatingLiteral*>(lhs);
            const auto* rhs_float = static_cast<const FloatingLiteral*>(rhs);
            return lhs_float->value == rhs_float->value &&
                   lhs_float->is_imaginary == rhs_float->is_imaginary;
        }
        case StmtKind::CharacterLiteral: {
            const auto* lhs_char = static_cast<const CharacterLiteral*>(lhs);
            const auto* rhs_char = static_cast<const CharacterLiteral*>(rhs);
            return lhs_char->value == rhs_char->value &&
                   lhs_char->int_value == rhs_char->int_value;
        }
        case StmtKind::StringLiteral: {
            const auto* lhs_string = static_cast<const StringLiteral*>(lhs);
            const auto* rhs_string = static_cast<const StringLiteral*>(rhs);
            return lhs_string->value == rhs_string->value;
        }
        case StmtKind::VarRef: {
            const auto* lhs_ref = static_cast<const VarRef*>(lhs);
            const auto* rhs_ref = static_cast<const VarRef*>(rhs);
            if (lhs_ref->get_name() != rhs_ref->get_name()) {
                return false;
            }
            const auto* lhs_parameter =
                lhs_ref->symref ? lhs_ref->symref->template_parameter_decl : nullptr;
            const auto* rhs_parameter =
                rhs_ref->symref ? rhs_ref->symref->template_parameter_decl : nullptr;
            if (lhs_parameter || rhs_parameter) {
                return template_parameter_structurally_matches(
                    lhs_parameter,
                    rhs_parameter);
            }
            return lhs_ref->symref == rhs_ref->symref;
        }
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lhs_lookup =
                static_cast<const UnresolvedLookupExpr*>(lhs);
            const auto* rhs_lookup =
                static_cast<const UnresolvedLookupExpr*>(rhs);
            return lhs_lookup->name == rhs_lookup->name &&
                   lhs_lookup->requires_template_keyword ==
                       rhs_lookup->requires_template_keyword &&
                   lhs_lookup->is_dependent == rhs_lookup->is_dependent &&
                   dependent_lookup_qualifier_structurally_matches(
                       lhs_lookup->qualifier,
                       rhs_lookup->qualifier) &&
                   template_argument_list_structurally_matches(
                       lhs_lookup->explicit_template_arguments,
                       rhs_lookup->explicit_template_arguments);
        }
        case StmtKind::FuncCall: {
            const auto* lhs_call = static_cast<const FuncCall*>(lhs);
            const auto* rhs_call = static_cast<const FuncCall*>(rhs);
            return expr_structurally_matches(
                       lhs_call->func.get(),
                       rhs_call->func.get()) &&
                   expr_vector_structurally_matches(
                       lhs_call->args,
                       rhs_call->args);
        }
        case StmtKind::DependentCallExpr: {
            const auto* lhs_call = static_cast<const DependentCallExpr*>(lhs);
            const auto* rhs_call = static_cast<const DependentCallExpr*>(rhs);
            return lhs_call->known_function_type.equals_qualified(
                       rhs_call->known_function_type) &&
                   expr_structurally_matches(
                       lhs_call->callee.get(),
                       rhs_call->callee.get()) &&
                   expr_vector_structurally_matches(
                       lhs_call->args,
                       rhs_call->args);
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* lhs_call = static_cast<const CppMemberCallExpr*>(lhs);
            const auto* rhs_call = static_cast<const CppMemberCallExpr*>(rhs);
            return lhs_call->member_name == rhs_call->member_name &&
                   lhs_call->isArrow == rhs_call->isArrow &&
                   lhs_call->suppress_virtual_dispatch ==
                       rhs_call->suppress_virtual_dispatch &&
                   lhs_call->has_implicit_object_argument ==
                       rhs_call->has_implicit_object_argument &&
                   expr_structurally_matches(
                       lhs_call->lowered_call.get(),
                       rhs_call->lowered_call.get());
        }
        case StmtKind::MemberExpr: {
            const auto* lhs_member = static_cast<const MemberExpr*>(lhs);
            const auto* rhs_member = static_cast<const MemberExpr*>(rhs);
            return lhs_member->isArrow == rhs_member->isArrow &&
                   lhs_member->get_member_name() == rhs_member->get_member_name() &&
                   expr_structurally_matches(
                       lhs_member->base.get(),
                       rhs_member->base.get());
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* lhs_member =
                static_cast<const UnresolvedMemberExpr*>(lhs);
            const auto* rhs_member =
                static_cast<const UnresolvedMemberExpr*>(rhs);
            return lhs_member->isArrow == rhs_member->isArrow &&
                   lhs_member->is_current_instantiation ==
                       rhs_member->is_current_instantiation &&
                   lhs_member->names_dependent_base ==
                       rhs_member->names_dependent_base &&
                   lhs_member->requires_template_keyword ==
                       rhs_member->requires_template_keyword &&
                   lhs_member->suppress_virtual_dispatch ==
                       rhs_member->suppress_virtual_dispatch &&
                   lhs_member->member_name == rhs_member->member_name &&
                   expr_structurally_matches(
                       lhs_member->base.get(),
                       rhs_member->base.get()) &&
                   template_argument_list_structurally_matches(
                       lhs_member->explicit_template_arguments,
                       rhs_member->explicit_template_arguments);
        }
        case StmtKind::UnaryOperation: {
            const auto* lhs_unary = static_cast<const UnaryOperation*>(lhs);
            const auto* rhs_unary = static_cast<const UnaryOperation*>(rhs);
            return lhs_unary->uop == rhs_unary->uop &&
                   expr_structurally_matches(
                       lhs_unary->exp.get(),
                       rhs_unary->exp.get());
        }
        case StmtKind::DependentUnaryExpr: {
            const auto* lhs_unary =
                static_cast<const DependentUnaryExpr*>(lhs);
            const auto* rhs_unary =
                static_cast<const DependentUnaryExpr*>(rhs);
            return lhs_unary->uop == rhs_unary->uop &&
                   expr_structurally_matches(
                       lhs_unary->operand.get(),
                       rhs_unary->operand.get());
        }
        case StmtKind::BinaryOperation: {
            const auto* lhs_binary = static_cast<const BinaryOperation*>(lhs);
            const auto* rhs_binary = static_cast<const BinaryOperation*>(rhs);
            return lhs_binary->bop == rhs_binary->bop &&
                   expr_structurally_matches(
                       lhs_binary->left.get(),
                       rhs_binary->left.get()) &&
                   expr_structurally_matches(
                       lhs_binary->right.get(),
                       rhs_binary->right.get());
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* lhs_binary =
                static_cast<const CompoundAssignOperation*>(lhs);
            const auto* rhs_binary =
                static_cast<const CompoundAssignOperation*>(rhs);
            return lhs_binary->bop == rhs_binary->bop &&
                   expr_structurally_matches(
                       lhs_binary->left.get(),
                       rhs_binary->left.get()) &&
                   expr_structurally_matches(
                       lhs_binary->right.get(),
                       rhs_binary->right.get());
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* lhs_binary =
                static_cast<const DependentBinaryExpr*>(lhs);
            const auto* rhs_binary =
                static_cast<const DependentBinaryExpr*>(rhs);
            return lhs_binary->bop == rhs_binary->bop &&
                   expr_structurally_matches(
                       lhs_binary->left.get(),
                       rhs_binary->left.get()) &&
                   expr_structurally_matches(
                       lhs_binary->right.get(),
                       rhs_binary->right.get());
        }
        case StmtKind::ExplicitCast: {
            const auto* lhs_cast = static_cast<const ExplicitCast*>(lhs);
            const auto* rhs_cast = static_cast<const ExplicitCast*>(rhs);
            return lhs_cast->ctype.equals_qualified(rhs_cast->ctype) &&
                   expr_structurally_matches(
                       lhs_cast->expr.get(),
                       rhs_cast->expr.get());
        }
        case StmtKind::ArraySubscriptExpr: {
            const auto* lhs_subscript =
                static_cast<const ArraySubscriptExpr*>(lhs);
            const auto* rhs_subscript =
                static_cast<const ArraySubscriptExpr*>(rhs);
            return expr_structurally_matches(
                       lhs_subscript->array.get(),
                       rhs_subscript->array.get()) &&
                   expr_structurally_matches(
                       lhs_subscript->index.get(),
                       rhs_subscript->index.get());
        }
        case StmtKind::DependentArraySubscriptExpr: {
            const auto* lhs_subscript =
                static_cast<const DependentArraySubscriptExpr*>(lhs);
            const auto* rhs_subscript =
                static_cast<const DependentArraySubscriptExpr*>(rhs);
            return expr_structurally_matches(
                       lhs_subscript->array.get(),
                       rhs_subscript->array.get()) &&
                   expr_structurally_matches(
                       lhs_subscript->index.get(),
                       rhs_subscript->index.get());
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* lhs_access =
                static_cast<const MemberPointerAccessExpr*>(lhs);
            const auto* rhs_access =
                static_cast<const MemberPointerAccessExpr*>(rhs);
            return lhs_access->is_arrow == rhs_access->is_arrow &&
                   lhs_access->is_function_member ==
                       rhs_access->is_function_member &&
                   expr_structurally_matches(
                       lhs_access->base.get(),
                       rhs_access->base.get()) &&
                   expr_structurally_matches(
                       lhs_access->member_pointer.get(),
                       rhs_access->member_pointer.get());
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            const auto* lhs_access =
                static_cast<const DependentMemberPointerAccessExpr*>(lhs);
            const auto* rhs_access =
                static_cast<const DependentMemberPointerAccessExpr*>(rhs);
            return lhs_access->is_arrow == rhs_access->is_arrow &&
                   expr_structurally_matches(
                       lhs_access->base.get(),
                       rhs_access->base.get()) &&
                   expr_structurally_matches(
                       lhs_access->member_pointer.get(),
                       rhs_access->member_pointer.get());
        }
        case StmtKind::CppNoexceptExpr: {
            const auto* lhs_noexcept = static_cast<const CppNoexceptExpr*>(lhs);
            const auto* rhs_noexcept = static_cast<const CppNoexceptExpr*>(rhs);
            return expr_structurally_matches(
                lhs_noexcept->operand.get(),
                rhs_noexcept->operand.get());
        }
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* lhs_dtor =
                static_cast<const CppPseudoDestructorExpr*>(lhs);
            const auto* rhs_dtor =
                static_cast<const CppPseudoDestructorExpr*>(rhs);
            return lhs_dtor->is_arrow == rhs_dtor->is_arrow &&
                   lhs_dtor->destroyed_type.equals_qualified(
                       rhs_dtor->destroyed_type) &&
                   expr_structurally_matches(
                       lhs_dtor->base.get(),
                       rhs_dtor->base.get());
        }
        default:
            return false;
    }
}

bool expr_depends_on_template_parameters_for_type(const Expr* expr,
                                                  const ASTContext* ast_ctx) {
    expr = strip_structural_implicit_casts(expr);
    if (!expr) {
        return true;
    }

    switch (expr->get_kind()) {
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lookup = static_cast<const UnresolvedLookupExpr*>(expr);
            if (lookup->is_dependent ||
                type_depends_on_template_parameters(
                    lookup->qualifier.qualifier_type,
                    ast_ctx)) {
                return true;
            }
            if (lookup->explicit_template_arguments.has_value()) {
                for (const auto& argument : *lookup->explicit_template_arguments) {
                    if (template_argument_depends_on_template_parameters(
                            argument,
                            ast_ctx)) {
                        return true;
                    }
                }
            }
            return false;
        }
        case StmtKind::DependentCallExpr:
        case StmtKind::DependentArraySubscriptExpr:
        case StmtKind::DependentUnaryExpr:
        case StmtKind::DependentBinaryExpr:
        case StmtKind::DependentMemberPointerAccessExpr:
        case StmtKind::FoldExpr:
            return true;
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(expr);
            if (expr_depends_on_template_parameters_for_type(
                    call->func.get(),
                    ast_ctx)) {
                return true;
            }
            for (const auto& arg : call->args) {
                if (expr_depends_on_template_parameters_for_type(
                        arg.get(),
                        ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* call = static_cast<const CppMemberCallExpr*>(expr);
            return expr_depends_on_template_parameters_for_type(
                call->lowered_call.get(),
                ast_ctx);
        }
        case StmtKind::MemberExpr:
            return expr_depends_on_template_parameters_for_type(
                static_cast<const MemberExpr*>(expr)->base.get(),
                ast_ctx);
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member =
                static_cast<const UnresolvedMemberExpr*>(expr);
            if (member->is_current_instantiation ||
                member->names_dependent_base ||
                expr_depends_on_template_parameters_for_type(
                    member->base.get(),
                    ast_ctx)) {
                return true;
            }
            if (member->explicit_template_arguments.has_value()) {
                for (const auto& argument : *member->explicit_template_arguments) {
                    if (template_argument_depends_on_template_parameters(
                            argument,
                            ast_ctx)) {
                        return true;
                    }
                }
            }
            return false;
        }
        case StmtKind::UnaryOperation:
            return expr_depends_on_template_parameters_for_type(
                static_cast<const UnaryOperation*>(expr)->exp.get(),
                ast_ctx);
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(expr);
            return expr_depends_on_template_parameters_for_type(
                       binary->left.get(),
                       ast_ctx) ||
                   expr_depends_on_template_parameters_for_type(
                       binary->right.get(),
                       ast_ctx);
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* binary =
                static_cast<const CompoundAssignOperation*>(expr);
            return expr_depends_on_template_parameters_for_type(
                       binary->left.get(),
                       ast_ctx) ||
                   expr_depends_on_template_parameters_for_type(
                       binary->right.get(),
                       ast_ctx);
        }
        case StmtKind::ExplicitCast:
            return expr_depends_on_template_parameters_for_type(
                static_cast<const ExplicitCast*>(expr)->expr.get(),
                ast_ctx);
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const ArraySubscriptExpr*>(expr);
            return expr_depends_on_template_parameters_for_type(
                       subscript->array.get(),
                       ast_ctx) ||
                   expr_depends_on_template_parameters_for_type(
                       subscript->index.get(),
                       ast_ctx);
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* access =
                static_cast<const MemberPointerAccessExpr*>(expr);
            return expr_depends_on_template_parameters_for_type(
                       access->base.get(),
                       ast_ctx) ||
                   expr_depends_on_template_parameters_for_type(
                       access->member_pointer.get(),
                       ast_ctx);
        }
        case StmtKind::SizeOfExpr: {
            const auto* sizeof_expr = static_cast<const SizeOfExpr*>(expr);
            return expr_depends_on_template_parameters_for_type(
                       sizeof_expr->expr_operand.get(),
                       ast_ctx) ||
                   type_depends_on_template_parameters(
                       sizeof_expr->type_operand,
                       ast_ctx);
        }
        case StmtKind::AlignOfExpr: {
            const auto* alignof_expr =
                static_cast<const AlignOfExpr*>(expr);
            return expr_depends_on_template_parameters_for_type(
                       alignof_expr->expr_operand.get(),
                       ast_ctx) ||
                   type_depends_on_template_parameters(
                       alignof_expr->type_operand,
                       ast_ctx);
        }
        case StmtKind::CppNoexceptExpr:
            return expr_depends_on_template_parameters_for_type(
                static_cast<const CppNoexceptExpr*>(expr)->operand.get(),
                ast_ctx);
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(expr);
            return expr_depends_on_template_parameters_for_type(
                       pseudo_dtor->base.get(),
                       ast_ctx) ||
                   type_depends_on_template_parameters(
                       pseudo_dtor->destroyed_type,
                       ast_ctx);
        }
        default:
            break;
    }

    auto expr_type = const_cast<Expr*>(expr)->get_type();
    if (!expr_type) {
        return true;
    }
    return type_depends_on_template_parameters(expr_type, ast_ctx);
}

bool template_argument_pack_expansion_parameters_match(
    const TemplateArgument& lhs,
    const TemplateArgument& rhs) {
    if (lhs.expands_parameter_pack != rhs.expands_parameter_pack ||
        lhs.pack_expansion_parameters.size() !=
            rhs.pack_expansion_parameters.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.pack_expansion_parameters.size(); ++idx) {
        if (lhs.pack_expansion_parameters[idx] !=
            rhs.pack_expansion_parameters[idx]) {
            return false;
        }
    }
    return true;
}

std::string template_parameter_display_name_for_pack(
    const TemplateParameterDecl* parameter) {
    if (!parameter) {
        return "<pack>";
    }
    if (!parameter->get_name().empty()) {
        return parameter->get_name();
    }
    return "template-parameter-" + std::to_string(parameter->depth) + "-" +
           std::to_string(parameter->index);
}

std::string template_argument_pattern_display_string(
    const TemplateArgument& argument) {
    switch (argument.kind) {
        case TemplateArgumentKind::Type: {
            auto template_type =
                argument.type.as_shared<TemplateTypeParmType>();
            if (template_type && template_type->is_parameter_pack &&
                !template_type->name.empty()) {
                return template_type->name;
            }
            std::string text = argument.type.to_string();
            if (argument.expands_parameter_pack && text.rfind("...", 0) == 0) {
                text.erase(0, 3);
            }
            return text;
        }
        case TemplateArgumentKind::Value:
            if (!argument.value_spelling.empty()) {
                return argument.value_spelling;
            }
            if (argument.referenced_parameter) {
                return template_parameter_display_name_for_pack(
                    argument.referenced_parameter);
            }
            return const_value_to_string(argument.value, &argument.value_type);
        case TemplateArgumentKind::Template:
            if (!argument.template_name.empty()) {
                return argument.template_name;
            }
            if (argument.referenced_parameter) {
                return template_parameter_display_name_for_pack(
                    argument.referenced_parameter);
            }
            if (!argument.dependent_template_member_name.empty()) {
                if (argument.dependent_template_qualifier_type) {
                    return argument.dependent_template_qualifier_type.to_string() +
                           "::template " +
                           argument.dependent_template_member_name;
                }
                return argument.dependent_template_member_name;
            }
            if (auto display_name = template_decl_display_name(argument.template_decl);
                !display_name.empty()) {
                return display_name;
            }
            return argument.is_dependent
                ? "<dependent-template-template-arg>"
                : "<template-template-arg>";
    }
    return "<unknown-template-arg>";
}

bool template_template_parameter_types_match(QualType formal_type,
                                             QualType actual_type);

bool template_template_arguments_match(const TemplateArgument& formal_argument,
                                       const TemplateArgument& actual_argument) {
    if (formal_argument.kind != actual_argument.kind ||
        !template_argument_pack_expansion_parameters_match(
            formal_argument,
            actual_argument)) {
        return false;
    }

    switch (formal_argument.kind) {
        case TemplateArgumentKind::Type:
            return template_template_parameter_types_match(
                formal_argument.type,
                actual_argument.type);
        case TemplateArgumentKind::Value:
            if (!template_template_parameter_types_match(
                    formal_argument.value_type,
                    actual_argument.value_type)) {
                return false;
            }
            if (formal_argument.is_dependent || actual_argument.is_dependent) {
                if (formal_argument.referenced_parameter &&
                    actual_argument.referenced_parameter) {
                    return formal_argument.referenced_parameter->depth ==
                               actual_argument.referenced_parameter->depth &&
                           formal_argument.referenced_parameter->index ==
                               actual_argument.referenced_parameter->index &&
                           formal_argument.referenced_parameter->is_parameter_pack ==
                               actual_argument.referenced_parameter->is_parameter_pack;
                }
                return formal_argument.value_spelling ==
                    actual_argument.value_spelling;
            }
            return formal_argument.equals(actual_argument);
        case TemplateArgumentKind::Template:
            if (formal_argument.is_dependent || actual_argument.is_dependent) {
                if (formal_argument.referenced_parameter &&
                    actual_argument.referenced_parameter) {
                    return formal_argument.referenced_parameter->depth ==
                               actual_argument.referenced_parameter->depth &&
                           formal_argument.referenced_parameter->index ==
                               actual_argument.referenced_parameter->index &&
                           formal_argument.referenced_parameter->is_parameter_pack ==
                               actual_argument.referenced_parameter->is_parameter_pack;
                }
                if (!formal_argument.dependent_template_member_name.empty() ||
                    !actual_argument.dependent_template_member_name.empty()) {
                    return formal_argument.dependent_template_member_name ==
                               actual_argument.dependent_template_member_name &&
                           formal_argument.dependent_template_qualifier_type
                               .equals_qualified(
                                   actual_argument
                                       .dependent_template_qualifier_type);
                }
                return formal_argument.template_name ==
                    actual_argument.template_name;
            }
            return formal_argument.equals(actual_argument);
    }
    return false;
}

bool template_template_parameter_types_match(QualType formal_type,
                                             QualType actual_type) {
    if (!formal_type || !actual_type) {
        return formal_type.get_shared() == actual_type.get_shared();
    }

    auto spelled_formal = desugar_typedefs(formal_type);
    auto spelled_actual = desugar_typedefs(actual_type);
    auto formal_raw = spelled_formal.get_shared();
    auto actual_raw = spelled_actual.get_shared();
    if (!formal_raw || !actual_raw) {
        return formal_raw == actual_raw;
    }

    if (auto formal_parm = dyn_cast_shared<TemplateTypeParmType>(formal_raw)) {
        auto actual_parm = dyn_cast_shared<TemplateTypeParmType>(actual_raw);
        return actual_parm &&
               formal_parm->depth == actual_parm->depth &&
               formal_parm->index == actual_parm->index &&
               formal_parm->is_parameter_pack == actual_parm->is_parameter_pack;
    }

    if (auto formal_ptr = dyn_cast_shared<PointerType>(formal_raw)) {
        auto actual_ptr = dyn_cast_shared<PointerType>(actual_raw);
        return actual_ptr &&
               template_template_parameter_types_match(
                   formal_ptr->pointed_type,
                   actual_ptr->pointed_type);
    }

    if (auto formal_ref = dyn_cast_shared<ReferenceType>(formal_raw)) {
        auto actual_ref = dyn_cast_shared<ReferenceType>(actual_raw);
        return actual_ref &&
               formal_ref->reference_kind == actual_ref->reference_kind &&
               template_template_parameter_types_match(
                   formal_ref->referred_type,
                   actual_ref->referred_type);
    }

    if (auto formal_mem_ptr = dyn_cast_shared<MemberPointerType>(formal_raw)) {
        auto actual_mem_ptr = dyn_cast_shared<MemberPointerType>(actual_raw);
        return actual_mem_ptr &&
               template_template_parameter_types_match(
                   formal_mem_ptr->class_type,
                   actual_mem_ptr->class_type) &&
               template_template_parameter_types_match(
                   formal_mem_ptr->member_type,
                   actual_mem_ptr->member_type);
    }

    if (auto formal_block_ptr = dyn_cast_shared<BlockPointerType>(formal_raw)) {
        auto actual_block_ptr = dyn_cast_shared<BlockPointerType>(actual_raw);
        return actual_block_ptr &&
               template_template_parameter_types_match(
                   formal_block_ptr->pointed_type,
                   actual_block_ptr->pointed_type);
    }

    if (auto formal_array = dyn_cast_shared<ArrayType>(formal_raw)) {
        auto actual_array = dyn_cast_shared<ArrayType>(actual_raw);
        return actual_array &&
               formal_array->size_kind == actual_array->size_kind &&
               formal_array->size == actual_array->size &&
               template_template_parameter_types_match(
                   formal_array->element_type,
                   actual_array->element_type);
    }

    if (auto formal_fn = dyn_cast_shared<FunctionType>(formal_raw)) {
        auto actual_fn = dyn_cast_shared<FunctionType>(actual_raw);
        if (!actual_fn ||
            formal_fn->parameters.size() != actual_fn->parameters.size() ||
            formal_fn->is_variadic != actual_fn->is_variadic ||
            !template_template_parameter_types_match(
                formal_fn->ret_type,
                actual_fn->ret_type)) {
            return false;
        }
        for (size_t idx = 0; idx < formal_fn->parameters.size(); ++idx) {
            if (!template_template_parameter_types_match(
                    formal_fn->parameters[idx],
                    actual_fn->parameters[idx])) {
                return false;
            }
        }
        return true;
    }

    if (auto formal_specialization =
            dyn_cast_shared<TemplateSpecializationType>(formal_raw)) {
        auto actual_specialization =
            dyn_cast_shared<TemplateSpecializationType>(actual_raw);
        if (!actual_specialization ||
            formal_specialization->arguments.size() !=
                actual_specialization->arguments.size()) {
            return false;
        }
        if (formal_specialization->primary_template &&
            actual_specialization->primary_template &&
            formal_specialization->primary_template !=
                actual_specialization->primary_template) {
            return false;
        }
        if ((!formal_specialization->primary_template ||
             !actual_specialization->primary_template) &&
            formal_specialization->template_name !=
                actual_specialization->template_name) {
            return false;
        }
        for (size_t idx = 0; idx < formal_specialization->arguments.size(); ++idx) {
            if (!template_template_arguments_match(
                    formal_specialization->arguments[idx],
                    actual_specialization->arguments[idx])) {
                return false;
            }
        }
        return true;
    }

    if (auto formal_vector = dyn_cast_shared<VectorType>(formal_raw)) {
        auto actual_vector = dyn_cast_shared<VectorType>(actual_raw);
        return actual_vector &&
               formal_vector->total_bytes == actual_vector->total_bytes &&
               template_template_parameter_types_match(
                   formal_vector->element_type,
                   actual_vector->element_type);
    }

    auto canonical_formal = desugar_type(spelled_formal);
    auto canonical_actual = desugar_type(spelled_actual);
    if (!canonical_formal || !canonical_actual) {
        return false;
    }
    return canonical_formal.equals_qualified(canonical_actual);
}

const TemplateParameterList* template_template_argument_parameter_list(
    const TemplateArgument& argument) {
    if (argument.kind != TemplateArgumentKind::Template) {
        return nullptr;
    }

    if (!argument.dependent_template_member_name.empty()) {
        return nullptr;
    }

    if (auto* template_parameter = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<TemplateParameterDecl*>(argument.referenced_parameter))) {
        return &template_parameter->parameters;
    }

    if (auto* alias_template =
            dyn_cast<AliasTemplateDecl>(
                const_cast<TemplateDecl*>(argument.template_decl))) {
        return &alias_template->parameters;
    }
    if (auto* variable_template =
            dyn_cast<VariableTemplateDecl>(
                const_cast<TemplateDecl*>(argument.template_decl))) {
        return &variable_template->parameters;
    }
    if (auto* class_template =
            dyn_cast<ClassTemplateDecl>(
                const_cast<TemplateDecl*>(argument.template_decl))) {
        return &class_template->parameters;
    }
    return nullptr;
}

bool template_template_parameters_are_compatible(
    const TemplateParameterDecl* formal_parameter,
    const TemplateParameterDecl* actual_parameter);

bool template_template_parameter_lists_are_compatible(
    const TemplateParameterList& formal_parameters,
    const TemplateParameterList& actual_parameters) {
    const size_t matched_count =
        std::min(formal_parameters.size(), actual_parameters.size());
    for (size_t idx = 0; idx < matched_count; ++idx) {
        if (!template_template_parameters_are_compatible(
                formal_parameters[idx].get(),
                actual_parameters[idx].get())) {
            return false;
        }
    }

    for (size_t idx = matched_count; idx < formal_parameters.size(); ++idx) {
        const auto* formal_parameter = formal_parameters[idx].get();
        if (!formal_parameter || !formal_parameter->is_parameter_pack) {
            return false;
        }
    }

    for (size_t idx = matched_count; idx < actual_parameters.size(); ++idx) {
        const auto* actual_parameter = actual_parameters[idx].get();
        if (!actual_parameter) {
            return false;
        }
        if (!actual_parameter->is_parameter_pack &&
            get_template_parameter_default_argument(actual_parameter) == nullptr) {
            return false;
        }
    }

    return true;
}

bool template_template_parameters_are_compatible(
    const TemplateParameterDecl* formal_parameter,
    const TemplateParameterDecl* actual_parameter) {
    if (!formal_parameter || !actual_parameter) {
        return false;
    }

    if (auto* formal_type_parameter = dyn_cast<TemplateTypeParmDecl>(
            const_cast<TemplateParameterDecl*>(formal_parameter))) {
        (void)formal_type_parameter;
        return isa<TemplateTypeParmDecl>(actual_parameter);
    }

    if (auto* formal_non_type = dyn_cast<TemplateNonTypeParmDecl>(
            const_cast<TemplateParameterDecl*>(formal_parameter))) {
        auto* actual_non_type = dyn_cast<TemplateNonTypeParmDecl>(
            const_cast<TemplateParameterDecl*>(actual_parameter));
        return actual_non_type &&
               template_template_parameter_types_match(
                   formal_non_type->type,
                   actual_non_type->type);
    }

    if (auto* formal_template = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<TemplateParameterDecl*>(formal_parameter))) {
        auto* actual_template = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<TemplateParameterDecl*>(actual_parameter));
        return actual_template &&
               template_template_parameter_lists_are_compatible(
                   formal_template->parameters,
                   actual_template->parameters);
    }

    return false;
}

bool template_parameter_accepts_argument(const TemplateParameterDecl* parameter,
                                         const TemplateArgument& argument,
                                         std::string* error_out = nullptr) {
    if (!parameter) {
        return false;
    }
    if (isa<TemplateTypeParmDecl>(parameter)) {
        if (argument.kind == TemplateArgumentKind::Type) {
            return true;
        }
        set_template_binding_error(
            error_out,
            "template argument kind does not match parameter kind");
        return false;
    }
    if (isa<TemplateNonTypeParmDecl>(parameter)) {
        if (argument.kind == TemplateArgumentKind::Value) {
            return true;
        }
        set_template_binding_error(
            error_out,
            "template argument kind does not match parameter kind");
        return false;
    }
    if (auto* template_parameter = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<TemplateParameterDecl*>(parameter))) {
        if (argument.kind != TemplateArgumentKind::Template) {
            set_template_binding_error(
                error_out,
                "template argument kind does not match parameter kind");
            return false;
        }
        const auto* actual_parameters =
            template_template_argument_parameter_list(argument);
        if (argument.is_dependent && actual_parameters == nullptr) {
            return true;
        }
        if (actual_parameters &&
            template_template_parameter_lists_are_compatible(
                template_parameter->parameters,
                *actual_parameters)) {
            return true;
        }
        set_template_binding_error(
            error_out,
            "template template argument parameter list is not compatible with template template parameter");
        return false;
    }
    return false;
}

bool type_depends_on_template_parameter_for_argument(QualType type,
                                                     const ASTContext* ast_ctx) {
    while (type) {
        auto raw = type.get_shared();
        if (!raw) {
            return false;
        }
        if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
            type = typedef_type->underlying_type;
            continue;
        }
        if (isa<TemplateTypeParmType>(raw.get())) {
            return true;
        }
        if (auto auto_type = dyn_cast_shared<AutoType>(raw)) {
            return auto_type->flavor == AutoTypeFlavor::TemplateNonType;
        }
        if (auto typeof_type = dyn_cast_shared<TypeofExprType>(raw)) {
            if (!typeof_type->expr) {
                return true;
            }
            if (expr_depends_on_template_parameters_for_type(
                    typeof_type->expr.get(),
                    ast_ctx)) {
                return true;
            }
            auto expr_type = typeof_type->expr->get_type();
            if (!expr_type) {
                return true;
            }
            type = expr_type;
            continue;
        }
        if (auto decltype_type = dyn_cast_shared<DecltypeExprType>(raw)) {
            if (!decltype_type->expr) {
                return true;
            }
            if (expr_depends_on_template_parameters_for_type(
                    decltype_type->expr.get(),
                    ast_ctx)) {
                return true;
            }
            auto expr_type = decltype_type->expr->get_type();
            if (!expr_type) {
                return true;
            }
            type = expr_type;
            continue;
        }
        if (auto transform = dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
            type = transform->operand_type;
            continue;
        }
        if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
            if (specialization->is_dependent) {
                return true;
            }
            for (const auto& argument : specialization->arguments) {
                if (template_argument_depends_on_template_parameters(
                        argument,
                        ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
            auto resolved_type =
                lookup_dependent_name_resolved_type(
                    dependent_name.get(),
                    ast_ctx);
            if (!resolved_type) {
                return true;
            }
            type = QualType(resolved_type);
            continue;
        }
        if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
            type = ptr->pointed_type;
            continue;
        }
        if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
            type = ref->referred_type;
            continue;
        }
        if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
            return type_depends_on_template_parameter_for_argument(
                       mem_ptr->class_type,
                       ast_ctx) ||
                   type_depends_on_template_parameter_for_argument(
                       mem_ptr->member_type,
                       ast_ctx);
        }
        if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
            type = blk->pointed_type;
            continue;
        }
        if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
            type = arr->element_type;
            continue;
        }
        if (auto fn = dyn_cast_shared<FunctionType>(raw)) {
            if (type_depends_on_template_parameter_for_argument(
                    fn->ret_type,
                    ast_ctx)) {
                return true;
            }
            for (const auto& parameter : fn->parameters) {
                if (type_depends_on_template_parameter_for_argument(
                        parameter,
                        ast_ctx)) {
                    return true;
                }
            }
            if (fn->exception_spec == FunctionExceptionSpecKind::Dependent ||
                (fn->exception_spec_expr &&
                 expr_depends_on_template_parameters_for_type(
                     fn->exception_spec_expr.get(),
                     ast_ctx))) {
                return true;
            }
            return false;
        }
        if (auto vec = dyn_cast_shared<VectorType>(raw)) {
            type = vec->element_type;
            continue;
        }
        return false;
    }
    return false;
}
} // namespace

bool DecltypeExprType::equals(const CType& other) {
    if (other.kind != TypeKind::DecltypeExpr) {
        return false;
    }
    const auto& rhs = static_cast<const DecltypeExprType&>(other);
    return rhs.use_declared_type_rule == use_declared_type_rule &&
           expr_structurally_matches(expr.get(), rhs.expr.get());
}

bool is_nullptr_type(QualType type, const ASTContext* ast_ctx) {
    return is_builtin_nullptr_type_impl(type, effective_ast_context(ast_ctx));
}

bool is_null_pointer_like_type(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    auto kind = canonical_type_kind(type, ast_ctx);
    return kind == TypeKind::Pointer ||
           kind == TypeKind::MemberPointer ||
           kind == TypeKind::BlockPointer ||
           is_builtin_nullptr_type_impl(type, effective_ast_context(ast_ctx));
}

namespace {
bool is_supported_non_type_template_parameter_type_impl(
    QualType type,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    if (!type) {
        return false;
    }
    if (type_depends_on_template_parameters(type, ast_ctx)) {
        return true;
    }

    type = desugar_type(remove_reference(type, ast_ctx), ast_ctx);
    if (!type) {
        return false;
    }
    if (type->isInteger() || type->kind == TypeKind::Enum) {
        return true;
    }
    if (auto_type_utils::has_cxx_auto_type(type.get_shared())) {
        return true;
    }

    switch (type->kind) {
        case TypeKind::Pointer:
        case TypeKind::Reference:
        case TypeKind::MemberPointer:
            return true;
        case TypeKind::Builtin: {
            auto* builtin = dyn_cast<BuiltinType>(type.get());
            return builtin && builtin->builtin_kind == BuiltinTypes::NullPtr;
        }
        case TypeKind::Array: {
            auto array = type.as_shared<ArrayType>();
            return array && array->size_kind == ArraySizeKind::Constant &&
                   array->size.has_value() &&
                   is_supported_non_type_template_parameter_type_impl(
                       array->element_type,
                       ast_ctx,
                       active_records);
        }
        case TypeKind::Object: {
            auto object = type.as_shared<ObjectType>();
            auto* record_decl =
                object ? dyn_cast<ObjectDecl>(object->get_decl()) : nullptr;
            if (!object || !record_decl || object->is_union ||
                object->isIncomplete() || object->has_bitfields() ||
                object->semantic_has_flexible_array_member()) {
                return false;
            }
            if (!active_records.insert(record_decl).second) {
                return true;
            }
            const RecordSemanticState* state =
                record_semantics_cache_lookup(record_decl, ast_ctx);
            bool ok = state && state->bases.empty() && state->virtual_bases.empty();
            if (ok) {
                for (const auto& field : state->fields) {
                    if (field.is_bitfield || field.is_base_subobject ||
                        field.is_virtual_base_storage ||
                        canonical_type_kind(field.type, ast_ctx) ==
                            TypeKind::Reference ||
                        field.declared_access != RecordMemberAccess::Public ||
                        !is_supported_non_type_template_parameter_type_impl(
                            field.type,
                            ast_ctx,
                            active_records)) {
                        ok = false;
                        break;
                    }
                }
            }
            active_records.erase(record_decl);
            return ok;
        }
        default:
            return false;
    }
}
} // namespace

bool is_supported_non_type_template_parameter_type(QualType type,
                                                   const ASTContext* ast_ctx) {
    std::unordered_set<const ObjectDecl*> active_records;
    return is_supported_non_type_template_parameter_type_impl(
        type,
        effective_ast_context(ast_ctx),
        active_records);
}

TemplateArgument::TemplateArgument(QualType type)
    : kind(TemplateArgumentKind::Type),
      type(std::move(type)) {}

TemplateArgument TemplateArgument::value_argument(QualType value_type,
                                                  ConstValue value,
                                                  std::string spelling,
                                                  std::shared_ptr<Expr> value_expr) {
    TemplateArgument argument;
    argument.kind = TemplateArgumentKind::Value;
    argument.value_type = std::move(value_type);
    argument.value = std::move(value);
    argument.value_spelling = std::move(spelling);
    argument.value_expr = std::move(value_expr);
    return argument;
}

TemplateArgument TemplateArgument::dependent_value_argument(
    QualType value_type,
    std::shared_ptr<Expr> value_expr,
    std::string spelling,
    const TemplateParameterDecl* referenced_parameter) {
    TemplateArgument argument;
    argument.kind = TemplateArgumentKind::Value;
    argument.value_type = std::move(value_type);
    argument.value_expr = std::move(value_expr);
    argument.referenced_parameter = referenced_parameter;
    argument.is_dependent = true;
    argument.value_spelling = std::move(spelling);
    return argument;
}

TemplateArgument TemplateArgument::template_argument(
    const TemplateDecl* template_decl,
    std::string spelling) {
    TemplateArgument argument;
    argument.kind = TemplateArgumentKind::Template;
    argument.template_decl = template_decl;
    argument.template_name = std::move(spelling);
    return argument;
}

TemplateArgument TemplateArgument::dependent_template_argument(
    std::string spelling,
    const TemplateParameterDecl* referenced_parameter) {
    TemplateArgument argument;
    argument.kind = TemplateArgumentKind::Template;
    argument.referenced_parameter = referenced_parameter;
    argument.is_dependent = true;
    argument.template_name = std::move(spelling);
    return argument;
}

TemplateArgument TemplateArgument::as_pack_expansion(
    std::vector<const TemplateParameterDecl*> referenced_pack_parameters) const {
    TemplateArgument argument = *this;
    argument.expands_parameter_pack = true;
    argument.pack_expansion_parameters = std::move(referenced_pack_parameters);
    if (!argument.pack_expansion_parameters.empty()) {
        return argument;
    }
    if (argument.referenced_parameter &&
        argument.referenced_parameter->is_parameter_pack) {
        argument.pack_expansion_parameters.push_back(argument.referenced_parameter);
        return argument;
    }
    if (auto parameter_type = argument.type.as_shared<TemplateTypeParmType>();
        parameter_type && parameter_type->is_parameter_pack &&
        parameter_type->parameter_decl) {
        argument.pack_expansion_parameters.push_back(parameter_type->parameter_decl);
    }
    return argument;
}

bool TemplateArgument::equals(const TemplateArgument& other) const {
    if (kind != other.kind ||
        !template_argument_pack_expansion_parameters_match(*this, other)) {
        return false;
    }
    switch (kind) {
        case TemplateArgumentKind::Type: {
            QualType lhs = desugar_type(type);
            QualType rhs = desugar_type(other.type);
            if (lhs && rhs) {
                return lhs.equals_qualified(rhs);
            }
            return type.equals_qualified(other.type);
        }
        case TemplateArgumentKind::Value:
            if (!value_type.equals_qualified(other.value_type) ||
                is_dependent != other.is_dependent) {
                return false;
            }
            if (is_dependent) {
                if (referenced_parameter && other.referenced_parameter) {
                    return referenced_parameter == other.referenced_parameter;
                }
                return value_spelling == other.value_spelling;
            }
            return const_value_equals(value, other.value);
        case TemplateArgumentKind::Template:
            if (is_dependent != other.is_dependent) {
                return false;
            }
            if (is_dependent) {
                if (referenced_parameter && other.referenced_parameter) {
                    return referenced_parameter == other.referenced_parameter;
                }
                if (!dependent_template_member_name.empty() ||
                    !other.dependent_template_member_name.empty()) {
                    return dependent_template_member_name ==
                               other.dependent_template_member_name &&
                           dependent_template_qualifier_type.equals_qualified(
                               other.dependent_template_qualifier_type);
                }
                return template_name == other.template_name;
            }
            if (const auto* lhs_canonical =
                    canonical_template_decl_identity(template_decl);
                lhs_canonical != nullptr) {
                return lhs_canonical ==
                       canonical_template_decl_identity(other.template_decl);
            }
            return !template_name.empty() &&
                   template_name == other.template_name;
    }
    return false;
}

std::string TemplateArgument::to_string() const {
    std::string text = template_argument_pattern_display_string(*this);
    if (expands_parameter_pack) {
        text += "...";
    }
    return text;
}

std::shared_ptr<CType> lookup_template_specialization_resolved_type(
    const TemplateSpecializationType* type,
    const ASTContext* ast_ctx) {
    if (!type) {
        return nullptr;
    }
    auto effective_ast_ctx = effective_ast_context(ast_ctx);
    if (effective_ast_ctx) {
        if (auto* query_context = get_active_collect_query_context()) {
            if (auto resolved_type =
                    query_context->lookup_template_specialization_resolved_type(
                        type,
                        effective_ast_ctx->semantic_store())) {
                return resolved_type;
            }
        } else if (auto resolved_type =
                       effective_ast_ctx->get_template_specialization_resolved_type(
                           type)) {
            return resolved_type;
        }
    }
    return nullptr;
}

void cache_template_specialization_resolved_type(
    ASTContext* ast_ctx,
    TemplateSpecializationType* type,
    std::shared_ptr<CType> resolved_type) {
    if (!type) {
        return;
    }
    auto effective_ast_ctx = effective_ast_context(ast_ctx);
    if (effective_ast_ctx) {
        if (auto* query_context = get_active_collect_query_context()) {
            query_context->publish_template_specialization_resolved_type(
                type,
                std::move(resolved_type),
                effective_ast_ctx->semantic_store());
        } else {
            effective_ast_ctx->set_template_specialization_resolved_type(
                type,
                std::move(resolved_type));
        }
    }
}

std::shared_ptr<CType> lookup_dependent_name_resolved_type(
    const DependentNameType* type,
    const ASTContext* ast_ctx) {
    if (!type) {
        return nullptr;
    }
    auto effective_ast_ctx = effective_ast_context(ast_ctx);
    if (effective_ast_ctx) {
        if (auto* query_context = get_active_collect_query_context()) {
            if (auto resolved_type =
                    query_context->lookup_dependent_name_resolved_type(
                        type,
                        effective_ast_ctx->semantic_store())) {
                return resolved_type;
            }
        } else if (auto resolved_type =
                       effective_ast_ctx->get_dependent_name_resolved_type(type)) {
            return resolved_type;
        }
    }
    return nullptr;
}

void cache_dependent_name_resolved_type(ASTContext* ast_ctx,
                                        DependentNameType* type,
                                        std::shared_ptr<CType> resolved_type) {
    if (!type) {
        return;
    }
    auto effective_ast_ctx = effective_ast_context(ast_ctx);
    if (effective_ast_ctx) {
        if (auto* query_context = get_active_collect_query_context()) {
            query_context->publish_dependent_name_resolved_type(
                type,
                std::move(resolved_type),
                effective_ast_ctx->semantic_store());
        } else {
            effective_ast_ctx->set_dependent_name_resolved_type(
                type,
                std::move(resolved_type));
        }
    }
}

bool type_depends_on_template_parameters(QualType type) {
    return type_depends_on_template_parameters(
        type,
        get_active_side_table_ast_context());
}

bool type_depends_on_template_parameters(QualType type,
                                         const ASTContext* ast_ctx) {
    return type_depends_on_template_parameter_for_argument(type, ast_ctx);
}

bool template_argument_depends_on_template_parameters(
    const TemplateArgument& argument) {
    return template_argument_depends_on_template_parameters(
        argument,
        get_active_side_table_ast_context());
}

bool template_argument_depends_on_template_parameters(
    const TemplateArgument& argument,
    const ASTContext* ast_ctx) {
    if (argument.expands_parameter_pack) {
        return true;
    }
    switch (argument.kind) {
        case TemplateArgumentKind::Type:
            return type_depends_on_template_parameter_for_argument(
                argument.type,
                ast_ctx);
        case TemplateArgumentKind::Value:
            return argument.is_dependent ||
                   argument.referenced_parameter != nullptr ||
                   (argument.value_expr &&
                    expr_depends_on_template_parameters_for_type(
                        argument.value_expr.get(),
                        ast_ctx)) ||
                   type_depends_on_template_parameter_for_argument(
                       argument.value_type,
                       ast_ctx);
        case TemplateArgumentKind::Template:
            return argument.is_dependent;
    }
    return false;
}

bool function_exception_specs_equal(const FunctionType& lhs,
                                    const FunctionType& rhs) {
    if (lhs.has_explicit_exception_spec != rhs.has_explicit_exception_spec ||
        lhs.exception_spec != rhs.exception_spec) {
        return false;
    }
    if (!lhs.has_explicit_exception_spec) {
        return true;
    }
    if (lhs.exception_spec != FunctionExceptionSpecKind::Dependent) {
        return true;
    }
    return expr_structurally_matches(
        lhs.exception_spec_expr.get(),
        rhs.exception_spec_expr.get());
}

TemplateEnvironmentFrame::TemplateEnvironmentFrame(
    std::vector<const TemplateParameterDecl*> parameters,
    TemplateArgumentBindings bindings,
    const TemplateDecl* template_decl,
    const Decl* owner_decl,
    QualType current_instantiation_type,
    std::optional<uint32_t> template_depth)
    : parameters(std::move(parameters)),
      bindings(std::move(bindings)),
      template_decl(template_decl),
      owner_decl(owner_decl),
      current_instantiation_type(std::move(current_instantiation_type)),
      template_depth(template_depth) {
    if (this->bindings.size() < this->parameters.size()) {
        this->bindings.resize(this->parameters.size());
    }
    if (!this->template_depth.has_value() && !this->parameters.empty() &&
        this->parameters.front()) {
        this->template_depth = this->parameters.front()->depth;
    }
}

const TemplateArgumentBinding* TemplateEnvironmentFrame::lookup(
    const TemplateParameterDecl* parameter) const {
    if (!parameter) {
        return nullptr;
    }
    if (parameter->index < parameters.size() &&
        parameters[parameter->index] == parameter &&
        parameter->index < bindings.size()) {
        return &bindings[parameter->index];
    }
    for (size_t idx = 0; idx < parameters.size(); ++idx) {
        if (parameters[idx] == parameter) {
            return idx < bindings.size() ? &bindings[idx] : nullptr;
        }
    }
    return nullptr;
}

TemplateArgumentBinding* TemplateEnvironmentFrame::lookup(
    const TemplateParameterDecl* parameter) {
    return const_cast<TemplateArgumentBinding*>(
        std::as_const(*this).lookup(parameter));
}

std::optional<size_t> TemplateEnvironmentFrame::pack_binding_size(
    const TemplateParameterDecl* parameter,
    std::string* error_out) const {
    if (!parameter) {
        return std::nullopt;
    }
    if (!parameter->is_parameter_pack) {
        set_template_binding_error(
            error_out,
            "template parameter is not a parameter pack");
        return std::nullopt;
    }
    const auto* binding = lookup(parameter);
    if (!binding || binding->is_unbound()) {
        return std::nullopt;
    }
    if (!binding->is_pack()) {
        set_template_binding_error(
            error_out,
            "template parameter pack is not bound as a pack in the current environment");
        return std::nullopt;
    }
    return binding->arguments.size();
}

void TemplateEnvironment::push_frame(TemplateEnvironmentFrame frame) {
    frames.push_back(std::move(frame));
}

void TemplateEnvironment::pop_frame() {
    if (!frames.empty()) {
        frames.pop_back();
    }
}

bool TemplateEnvironment::empty() const {
    return frames.empty();
}

const TemplateArgumentBinding* TemplateEnvironment::lookup(
    const TemplateParameterDecl* parameter) const {
    if (const auto* frame = lookup_frame(parameter)) {
        return frame->lookup(parameter);
    }
    return nullptr;
}

TemplateArgumentBinding* TemplateEnvironment::lookup(
    const TemplateParameterDecl* parameter) {
    if (auto* frame = lookup_frame(parameter)) {
        return frame->lookup(parameter);
    }
    return nullptr;
}

const TemplateEnvironmentFrame* TemplateEnvironment::lookup_frame(
    const TemplateParameterDecl* parameter) const {
    for (auto it = frames.rbegin(); it != frames.rend(); ++it) {
        if (it->lookup(parameter) != nullptr) {
            return &(*it);
        }
    }
    return nullptr;
}

TemplateEnvironmentFrame* TemplateEnvironment::lookup_frame(
    const TemplateParameterDecl* parameter) {
    return const_cast<TemplateEnvironmentFrame*>(
        std::as_const(*this).lookup_frame(parameter));
}

std::optional<size_t> TemplateEnvironment::pack_binding_size(
    const TemplateParameterDecl* parameter,
    std::string* error_out) const {
    if (const auto* frame = lookup_frame(parameter)) {
        return frame->pack_binding_size(parameter, error_out);
    }
    return std::nullopt;
}

std::optional<size_t> TemplateEnvironment::pack_expansion_arity(
    const std::vector<const TemplateParameterDecl*>& parameters,
    std::string* error_out) const {
    if (parameters.empty()) {
        set_template_binding_error(
            error_out,
            "pack expansion shape does not reference a template parameter pack");
        return std::nullopt;
    }

    std::optional<size_t> expected_size;
    std::vector<const TemplateParameterDecl*> unique_parameters;
    unique_parameters.reserve(parameters.size());
    for (const auto* parameter : parameters) {
        if (!parameter) {
            set_template_binding_error(
                error_out,
                "pack expansion shape references a null template parameter");
            return std::nullopt;
        }
        if (std::find(
                unique_parameters.begin(),
                unique_parameters.end(),
                parameter) == unique_parameters.end()) {
            unique_parameters.push_back(parameter);
        }
    }

    for (const auto* parameter : unique_parameters) {
        auto size = pack_binding_size(parameter, error_out);
        if (!size.has_value()) {
            return std::nullopt;
        }
        if (!expected_size.has_value()) {
            expected_size = size;
            continue;
        }
        if (*expected_size != *size) {
            set_template_binding_error(
                error_out,
                "pack expansion references parameter packs with different arities: '" +
                    template_parameter_display_name_for_pack(
                        unique_parameters.front()) +
                    "' has " + std::to_string(*expected_size) + " element(s) but '" +
                    template_parameter_display_name_for_pack(parameter) +
                    "' has " + std::to_string(*size) + " element(s)");
            return std::nullopt;
        }
    }

    return expected_size;
}

QualType TemplateEnvironment::current_instantiation_type() const {
    for (auto it = frames.rbegin(); it != frames.rend(); ++it) {
        if (it->current_instantiation_type) {
            return it->current_instantiation_type;
        }
    }
    if (pattern_context.has_value()) {
        return pattern_context->current_instantiation_type;
    }
    return QualType(nullptr);
}

namespace {

enum class TemplateArgumentBindingMode : uint8_t {
    Exact,
    ExplicitPartial,
};

bool bind_template_arguments_to_parameters_impl(
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& arguments,
    TemplateArgumentBindings& bindings_out,
    TemplateArgumentBindingMode mode,
    std::string* error_out) {
    bindings_out.clear();
    bindings_out.resize(parameters.size());

    size_t pack_count = 0;
    size_t pack_index = 0;
    for (size_t idx = 0; idx < parameters.size(); ++idx) {
        const auto* parameter = parameters[idx].get();
        if (!parameter) {
            set_template_binding_error(
                error_out,
                "internal error: null template parameter");
            bindings_out.clear();
            return false;
        }
        if (parameter->is_parameter_pack) {
            ++pack_count;
            pack_index = idx;
        }
    }

    auto bind_single_argument =
        [&](size_t parameter_index, size_t argument_index) -> bool {
            if (!template_parameter_accepts_argument(
                    parameters[parameter_index].get(),
                    arguments[argument_index],
                    error_out)) {
                bindings_out.clear();
                return false;
            }
            bindings_out[parameter_index] =
                TemplateArgumentBinding::single(arguments[argument_index]);
            return true;
        };

    auto bind_pack_arguments =
        [&](size_t parameter_index,
            size_t argument_begin,
            size_t argument_count,
            bool materialize_empty_pack) -> bool {
            if (argument_count == 0 && !materialize_empty_pack) {
                return true;
            }

            std::vector<TemplateArgument> pack_arguments;
            pack_arguments.reserve(argument_count);
            for (size_t idx = 0; idx < argument_count; ++idx) {
                if (!template_parameter_accepts_argument(
                        parameters[parameter_index].get(),
                        arguments[argument_begin + idx],
                        error_out)) {
                    bindings_out.clear();
                    return false;
                }
                pack_arguments.push_back(arguments[argument_begin + idx]);
            }
            bindings_out[parameter_index] =
                TemplateArgumentBinding::pack(std::move(pack_arguments));
            return true;
        };

    if (pack_count == 0) {
        if (mode == TemplateArgumentBindingMode::Exact &&
            arguments.size() != parameters.size()) {
            set_template_binding_error(
                error_out,
                "template argument count does not match parameter count");
            bindings_out.clear();
            return false;
        }
        if (mode == TemplateArgumentBindingMode::ExplicitPartial &&
            arguments.size() > parameters.size()) {
            set_template_binding_error(
                error_out,
                "template argument count exceeds parameter count");
            bindings_out.clear();
            return false;
        }
        for (size_t idx = 0; idx < arguments.size(); ++idx) {
            if (!bind_single_argument(idx, idx)) {
                bindings_out.clear();
                return false;
            }
        }
        return true;
    }

    if (pack_count > 1) {
        set_template_binding_error(
            error_out,
            "multiple template parameter packs are not supported by the current argument binder");
        bindings_out.clear();
        return false;
    }

    const size_t leading_count = pack_index;
    const size_t trailing_count = parameters.size() - pack_index - 1;
    if (mode == TemplateArgumentBindingMode::Exact &&
        arguments.size() < leading_count + trailing_count) {
        set_template_binding_error(
            error_out,
            "template argument count does not satisfy fixed non-pack parameters");
        bindings_out.clear();
        return false;
    }

    if (mode == TemplateArgumentBindingMode::ExplicitPartial &&
        arguments.size() < leading_count + trailing_count &&
        arguments.size() > leading_count) {
        set_template_binding_error(
            error_out,
            "explicit template arguments cannot partially bind a non-trailing parameter pack");
        bindings_out.clear();
        return false;
    }

    const bool explicit_split_fully_determined =
        mode == TemplateArgumentBindingMode::Exact ||
        arguments.size() > leading_count;

    for (size_t idx = 0; idx < leading_count; ++idx) {
        if (idx >= arguments.size()) {
            break;
        }
        if (!bind_single_argument(idx, idx)) {
            return false;
        }
    }

    if (explicit_split_fully_determined) {
        const size_t pack_argument_count =
            arguments.size() - leading_count - trailing_count;
        if (!bind_pack_arguments(
                pack_index,
                leading_count,
                pack_argument_count,
                /*materialize_empty_pack=*/true)) {
            return false;
        }

        for (size_t idx = 0; idx < trailing_count; ++idx) {
            const size_t parameter_index = pack_index + 1 + idx;
            const size_t argument_index = leading_count + pack_argument_count + idx;
            if (!bind_single_argument(parameter_index, argument_index)) {
                return false;
            }
        }
    }

    return true;
}

} // namespace

bool bind_template_arguments_to_parameters(
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& arguments,
    TemplateArgumentBindings& bindings_out,
    std::string* error_out) {
    return bind_template_arguments_to_parameters_impl(
        parameters,
        arguments,
        bindings_out,
        TemplateArgumentBindingMode::Exact,
        error_out);
}

bool bind_explicit_template_arguments_prefix_to_parameters(
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& explicit_arguments,
    TemplateArgumentBindings& bindings_out,
    std::string* error_out) {
    return bind_template_arguments_to_parameters_impl(
        parameters,
        explicit_arguments,
        bindings_out,
        TemplateArgumentBindingMode::ExplicitPartial,
        error_out);
}

bool complete_template_argument_bindings_with_defaults(
    const TemplateDecl* template_decl,
    TemplateArgumentBindings& bindings_out,
    std::string* error_out) {
    if (!template_decl) {
        set_template_binding_error(
            error_out,
            "internal error: null template declaration");
        return false;
    }

    if (bindings_out.size() != template_decl->parameters.size()) {
        set_template_binding_error(
            error_out,
            "internal error: template binding count does not match parameter count");
        return false;
    }

    const auto* merged_defaults = get_template_decl_default_arguments(template_decl);
    for (size_t idx = 0; idx < template_decl->parameters.size(); ++idx) {
        const auto* parameter = template_decl->parameters[idx].get();
        if (!parameter || !bindings_out[idx].is_unbound()) {
            continue;
        }
        if (parameter->is_parameter_pack) {
            bindings_out[idx] = TemplateArgumentBinding::pack({});
            continue;
        }

        const TemplateArgument* default_argument =
            (merged_defaults && idx < merged_defaults->size() &&
             (*merged_defaults)[idx].has_value())
                ? &(*merged_defaults)[idx].value()
                : nullptr;
        if (!default_argument) {
            set_template_binding_error(
                error_out,
                "template argument count does not satisfy parameter defaults");
            return false;
        }
        if (!template_parameter_accepts_argument(
                parameter,
                *default_argument,
                error_out)) {
            return false;
        }
        bindings_out[idx] = TemplateArgumentBinding::single(*default_argument);
    }

    return true;
}

std::vector<TemplateArgument> flatten_template_argument_bindings(
    const TemplateArgumentBindings& bindings) {
    std::vector<TemplateArgument> flattened;
    size_t total = 0;
    for (const auto& binding : bindings) {
        total += binding.arguments.size();
    }
    flattened.reserve(total);
    for (const auto& binding : bindings) {
        if (binding.kind == TemplateArgumentBindingKind::Unbound) {
            continue;
        }
        for (const auto& argument : binding.arguments) {
            flattened.push_back(argument);
        }
    }
    return flattened;
}

void record_semantics_cache_clear(ASTContext* ast_ctx) {
    if (!ast_ctx) {
        return;
    }
    ast_ctx->clear_record_semantics_cache();
}

void record_semantics_cache_set(ASTContext* ast_ctx,
                                const ObjectDecl* record_decl,
                                RecordSemanticState state) {
    if (!record_decl) {
        return;
    }
    if (auto* cache_ctx = record_semantics_ast_context(record_decl, ast_ctx)) {
        if (auto* query_context = get_active_collect_query_context()) {
            query_context->publish_record_semantics(
                record_decl,
                std::move(state),
                cache_ctx->semantic_store());
        } else {
            cache_ctx->set_record_semantics(record_decl, std::move(state));
        }
    }
}

void record_semantics_cache_set(const ObjectDecl* record_decl,
                                RecordSemanticState state) {
    record_semantics_cache_set(nullptr, record_decl, std::move(state));
}

void record_semantics_cache_erase(ASTContext* ast_ctx,
                                  const ObjectDecl* record_decl) {
    if (!record_decl) {
        return;
    }
    if (auto* cache_ctx = record_semantics_ast_context(record_decl, ast_ctx)) {
        if (auto* query_context = get_active_collect_query_context()) {
            query_context->erase_record_semantics(
                record_decl,
                cache_ctx->semantic_store());
        } else {
            cache_ctx->erase_record_semantics(record_decl);
        }
    }
}

void record_semantics_cache_erase(const ObjectDecl* record_decl) {
    record_semantics_cache_erase(nullptr, record_decl);
}

const RecordSemanticState* record_semantics_cache_lookup(
    const ObjectDecl* record_decl,
    const ASTContext* ast_ctx) {
    if (!record_decl) {
        return nullptr;
    }
    const ASTContext* cache_ctx = record_semantics_ast_context(record_decl, ast_ctx);
    if (!cache_ctx) {
        // Speculative query overlays can publish semantics for transient
        // declarations before durable side-table ownership is assigned.
        // Fall back to the active ASTContext so those overlay-backed facts stay
        // visible during the same semantic action.
        cache_ctx = effective_ast_context(static_cast<const ASTContext*>(nullptr));
    }
    if (cache_ctx) {
        if (auto* query_context = get_active_collect_query_context()) {
            return query_context->lookup_record_semantics(
                record_decl,
                cache_ctx->semantic_store());
        }
        return cache_ctx->lookup_record_semantics(record_decl);
    }
    return nullptr;
}

const RecordSemanticState* record_semantics_cache_lookup(
    const ObjectDecl* record_decl) {
    return record_semantics_cache_lookup(record_decl, nullptr);
}

uint64_t record_semantics_cache_epoch(const ASTContext* ast_ctx) {
    return ast_ctx ? ast_ctx->record_semantics_cache_epoch() : 0;
}

QualType cpp_written_method_type(QualType method_type,
                                 const ASTContext* ast_ctx) {
    auto fn_type =
        desugar_type(method_type, ast_ctx).as_shared<FunctionType>();
    if (!fn_type || fn_type->parameters.empty()) {
        return method_type;
    }

    auto this_param =
        desugar_type(fn_type->parameters.front(), ast_ctx).as_shared<PointerType>();
    auto this_object = this_param
        ? desugar_type(this_param->pointed_type, ast_ctx).as_shared<ObjectType>()
        : nullptr;
    if (!this_param || !this_object) {
        return method_type;
    }

    auto rebuilt = std::make_shared<FunctionType>();
    rebuilt->ret_type = fn_type->ret_type;
    rebuilt->parameters.reserve(fn_type->parameters.size() - 1);
    for (size_t i = 1; i < fn_type->parameters.size(); ++i) {
        rebuilt->parameters.push_back(fn_type->parameters[i]);
    }
    rebuilt->is_variadic = fn_type->is_variadic;
    rebuilt->has_prototype = fn_type->has_prototype;
    rebuilt->member_ref_qualifier = fn_type->member_ref_qualifier;
    rebuilt->has_explicit_exception_spec =
        fn_type->has_explicit_exception_spec;
    rebuilt->exception_spec = fn_type->exception_spec;
    rebuilt->exception_spec_expr = fn_type->exception_spec_expr;
    return QualType(rebuilt, method_type.get_qualifiers());
}

std::string make_cpp_virtual_slot_key(const std::string& method_name,
                                      QualType method_type,
                                      const ASTContext* ast_ctx) {
    auto fn_type = desugar_type(method_type, ast_ctx).as_shared<FunctionType>();
    if (!fn_type) {
        return method_name + "(<invalid>)";
    }

    auto append_canonical_param = [&](std::ostringstream& os,
                                      QualType param_type) {
        QualType canonical_param = desugar_type(param_type, ast_ctx);
        os << canonical_param.to_string();
    };

    std::ostringstream os;
    os << method_name << "{cv=";
    if (!fn_type->parameters.empty()) {
        auto this_ptr =
            desugar_type(fn_type->parameters.front(), ast_ctx).as_shared<PointerType>();
        if (this_ptr &&
            canonical_type_kind(this_ptr->pointed_type) == TypeKind::Object) {
            uint8_t this_cv = static_cast<uint8_t>(
                this_ptr->pointed_type.get_qualifiers() &
                static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE));
            if (this_cv & QUAL_CONST) {
                os << "c";
            }
            if (this_cv & QUAL_VOLATILE) {
                os << "v";
            }
        }
    }
    os << ",ref=";
    if (fn_type->member_ref_qualifier == FunctionRefQualifierKind::LValue) {
        os << "&";
    } else if (fn_type->member_ref_qualifier ==
               FunctionRefQualifierKind::RValue) {
        os << "&&";
    } else {
        os << "-";
    }
    os << "}(";

    bool wrote_param = false;
    size_t param_start = 0;
    if (!fn_type->parameters.empty()) {
        auto first_param =
            desugar_type(fn_type->parameters.front(), ast_ctx).as_shared<PointerType>();
        if (first_param &&
            canonical_type_kind(first_param->pointed_type) == TypeKind::Object) {
            param_start = 1;
        }
    }
    for (size_t idx = param_start; idx < fn_type->parameters.size(); ++idx) {
        QualType param_type = fn_type->parameters[idx];
        if (param_type && param_type->isVoid() &&
            fn_type->parameters.size() == param_start + 1) {
            break;
        }
        if (wrote_param) {
            os << ",";
        }
        append_canonical_param(os, param_type);
        wrote_param = true;
    }
    if (fn_type->is_variadic) {
        if (wrote_param) {
            os << ",";
        }
        os << "...";
    }
    os << ")";
    return os.str();
}

namespace {

const ObjectDecl* canonical_record_semantics_decl(const ObjectDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto record_type = decl->get_record_type()) {
        if (auto* canonical_decl =
                dyn_cast<ObjectDecl>(record_type->get_decl())) {
            return canonical_decl;
        }
    }
    return decl;
}

struct BaseOffsetQueryResult {
    bool found = false;
    bool ambiguous = false;
    size_t offset = 0;
};

void merge_base_offset_candidate(BaseOffsetQueryResult& aggregate,
                                 size_t candidate_offset) {
    if (!aggregate.found) {
        aggregate.found = true;
        aggregate.offset = candidate_offset;
        return;
    }
    if (aggregate.offset != candidate_offset) {
        aggregate.ambiguous = true;
    }
}

BaseOffsetQueryResult record_base_subobject_offset_impl(
    const ObjectDecl* current_decl,
    const ObjectDecl* target_decl,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_stack) {
    current_decl = canonical_record_semantics_decl(current_decl);
    target_decl = canonical_record_semantics_decl(target_decl);
    if (!current_decl || !target_decl) {
        return {};
    }
    if (current_decl == target_decl) {
        BaseOffsetQueryResult result;
        result.found = true;
        result.offset = 0;
        return result;
    }

    const RecordSemanticState* state =
        record_semantics_cache_lookup(current_decl, ast_ctx);
    if (!state) {
        return {};
    }

    BaseOffsetQueryResult aggregate;
    for (const auto& virtual_base : state->virtual_bases) {
        if (!virtual_base.record_decl || !virtual_base.has_offset) {
            continue;
        }
        const ObjectDecl* virtual_base_decl =
            canonical_record_semantics_decl(virtual_base.record_decl);
        if (virtual_base_decl != target_decl) {
            continue;
        }
        merge_base_offset_candidate(aggregate, virtual_base.offset);
        if (aggregate.ambiguous) {
            return aggregate;
        }
    }
    if (aggregate.found) {
        return aggregate;
    }

    for (const auto& base : state->bases) {
        if (!base.record_decl || base.is_virtual || !base.has_non_virtual_offset) {
            continue;
        }
        const ObjectDecl* base_decl =
            canonical_record_semantics_decl(base.record_decl);
        if (!base_decl || active_stack.contains(base_decl)) {
            continue;
        }

        active_stack.insert(base_decl);
        BaseOffsetQueryResult child = record_base_subobject_offset_impl(
            base_decl,
            target_decl,
            ast_ctx,
            active_stack);
        active_stack.erase(base_decl);
        if (child.ambiguous) {
            aggregate.ambiguous = true;
            return aggregate;
        }
        if (!child.found) {
            continue;
        }
        if (child.offset >
            std::numeric_limits<size_t>::max() - base.non_virtual_offset) {
            continue;
        }
        size_t total_offset = base.non_virtual_offset + child.offset;
        merge_base_offset_candidate(aggregate, total_offset);
        if (aggregate.ambiguous) {
            return aggregate;
        }
    }
    return aggregate;
}

using BasePathStep = std::pair<const ObjectDecl*, bool>;

std::string encode_base_path_key(const std::vector<BasePathStep>& path) {
    std::string key;
    key.reserve(path.size() * 24);
    for (const auto& step : path) {
        key += step.second ? "V:" : "N:";
        key += std::to_string(reinterpret_cast<uintptr_t>(step.first));
        key.push_back(';');
    }
    return key;
}

} // namespace

std::optional<size_t> record_base_subobject_offset(
    const ObjectDecl* from_decl,
    const ObjectDecl* to_decl,
    const ASTContext* ast_ctx) {
    from_decl = canonical_record_semantics_decl(from_decl);
    to_decl = canonical_record_semantics_decl(to_decl);
    if (!from_decl || !to_decl) {
        return std::nullopt;
    }
    if (from_decl == to_decl) {
        return size_t{0};
    }
    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(from_decl);
    BaseOffsetQueryResult result = record_base_subobject_offset_impl(
        from_decl,
        to_decl,
        ast_ctx,
        active_stack);
    if (!result.found || result.ambiguous) {
        return std::nullopt;
    }
    return result.offset;
}

size_t count_record_base_subobjects(const ObjectDecl* derived_decl,
                                    const ObjectDecl* target_base_decl,
                                    bool require_public_path,
                                    const ASTContext* ast_ctx) {
    derived_decl = canonical_record_semantics_decl(derived_decl);
    target_base_decl = canonical_record_semantics_decl(target_base_decl);
    if (!derived_decl || !target_base_decl || derived_decl == target_base_decl) {
        return 0;
    }

    std::unordered_set<std::string> matched_subobjects;
    std::vector<BasePathStep> path;
    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(derived_decl);

    std::function<void(const ObjectDecl*)> walk =
        [&](const ObjectDecl* current_decl) {
        current_decl = canonical_record_semantics_decl(current_decl);
        if (!current_decl) {
            return;
        }
        if (current_decl == target_base_decl) {
            if (!path.empty()) {
                matched_subobjects.insert(encode_base_path_key(path));
            }
            return;
        }

        const RecordSemanticState* state =
            record_semantics_cache_lookup(current_decl, ast_ctx);
        if (!state) {
            return;
        }

        for (const auto& base : state->bases) {
            const ObjectDecl* base_decl =
                canonical_record_semantics_decl(base.record_decl);
            if (!base_decl ||
                (require_public_path &&
                 base.declared_access != RecordMemberAccess::Public) ||
                active_stack.contains(base_decl)) {
                continue;
            }

            auto saved_path = path;
            if (base.is_virtual) {
                path.clear();
                path.emplace_back(base_decl, true);
            } else {
                path.emplace_back(base_decl, false);
            }

            active_stack.insert(base_decl);
            walk(base_decl);
            active_stack.erase(base_decl);
            path = std::move(saved_path);
        }
    };

    walk(derived_decl);
    return matched_subobjects.size();
}

bool has_unambiguous_record_base_path(const ObjectDecl* derived_decl,
                                      const ObjectDecl* target_base_decl,
                                      bool require_public_path,
                                      const ASTContext* ast_ctx) {
    size_t path_count = count_record_base_subobjects(
        derived_decl,
        target_base_decl,
        require_public_path,
        ast_ctx);
    return path_count == 1;
}

namespace {

void accumulate_record_base_paths(
    const ObjectDecl* current_decl,
    const ObjectDecl* target_base_decl,
    bool path_is_public,
    bool saw_virtual_edge,
    size_t current_offset,
    RecordBasePathSummary& summary,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_stack) {
    current_decl = canonical_record_semantics_decl(current_decl);
    target_base_decl = canonical_record_semantics_decl(target_base_decl);
    if (!current_decl || !target_base_decl) {
        return;
    }
    if (current_decl == target_base_decl) {
        if (saw_virtual_edge) {
            summary.has_virtual_path = true;
            return;
        }
        if (path_is_public) {
            if (summary.public_nonvirtual_paths == 0) {
                summary.public_nonvirtual_offset = current_offset;
            }
            ++summary.public_nonvirtual_paths;
        } else {
            ++summary.nonpublic_nonvirtual_paths;
        }
        return;
    }

    const RecordSemanticState* state =
        record_semantics_cache_lookup(current_decl, ast_ctx);
    if (!state) {
        return;
    }

    for (const auto& base : state->bases) {
        const ObjectDecl* base_decl =
            canonical_record_semantics_decl(base.record_decl);
        if (!base_decl || active_stack.contains(base_decl)) {
            continue;
        }

        bool next_path_public =
            path_is_public && base.declared_access == RecordMemberAccess::Public;
        bool next_saw_virtual_edge = saw_virtual_edge || base.is_virtual;
        size_t next_offset = current_offset;
        if (!base.is_virtual) {
            if (!base.has_non_virtual_offset ||
                current_offset >
                    std::numeric_limits<size_t>::max() - base.non_virtual_offset) {
                continue;
            }
            next_offset += base.non_virtual_offset;
        }

        active_stack.insert(base_decl);
        accumulate_record_base_paths(base_decl,
                                     target_base_decl,
                                     next_path_public,
                                     next_saw_virtual_edge,
                                     next_offset,
                                     summary,
                                     ast_ctx,
                                     active_stack);
        active_stack.erase(base_decl);
    }
}

} // namespace

RecordBasePathSummary summarize_record_base_paths(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const ASTContext* ast_ctx) {
    RecordBasePathSummary summary;
    derived_decl = canonical_record_semantics_decl(derived_decl);
    target_base_decl = canonical_record_semantics_decl(target_base_decl);
    if (!derived_decl || !target_base_decl || derived_decl == target_base_decl) {
        return summary;
    }

    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(derived_decl);
    accumulate_record_base_paths(derived_decl,
                                 target_base_decl,
                                 true,
                                 false,
                                 0,
                                 summary,
                                 ast_ctx,
                                 active_stack);
    return summary;
}

void enum_semantics_cache_clear(ASTContext* ast_ctx) {
    if (!ast_ctx) {
        return;
    }
    ast_ctx->clear_enum_semantics_cache();
}

void enum_semantics_cache_set(ASTContext* ast_ctx,
                              const EnumDecl* enum_decl,
                              EnumSemanticState state) {
    if (!enum_decl) {
        return;
    }
    if (auto* cache_ctx = enum_semantics_ast_context(enum_decl, ast_ctx)) {
        if (auto* query_context = get_active_collect_query_context()) {
            query_context->publish_enum_semantics(
                enum_decl,
                std::move(state),
                cache_ctx->semantic_store());
        } else {
            cache_ctx->set_enum_semantics(enum_decl, std::move(state));
        }
    }
}

void enum_semantics_cache_set(const EnumDecl* enum_decl,
                              EnumSemanticState state) {
    enum_semantics_cache_set(nullptr, enum_decl, std::move(state));
}

void enum_semantics_cache_erase(ASTContext* ast_ctx, const EnumDecl* enum_decl) {
    if (!enum_decl) {
        return;
    }
    if (auto* cache_ctx = enum_semantics_ast_context(enum_decl, ast_ctx)) {
        if (auto* query_context = get_active_collect_query_context()) {
            query_context->erase_enum_semantics(
                enum_decl,
                cache_ctx->semantic_store());
        } else {
            cache_ctx->erase_enum_semantics(enum_decl);
        }
    }
}

void enum_semantics_cache_erase(const EnumDecl* enum_decl) {
    enum_semantics_cache_erase(nullptr, enum_decl);
}

bool enum_semantics_cache_lookup(const EnumDecl* enum_decl,
                                 EnumSemanticState& state_out,
                                 const ASTContext* ast_ctx) {
    if (!enum_decl) {
        return false;
    }
    const ASTContext* cache_ctx = enum_semantics_ast_context(enum_decl, ast_ctx);
    if (!cache_ctx) {
        cache_ctx = effective_ast_context(static_cast<const ASTContext*>(nullptr));
    }
    if (cache_ctx) {
        if (auto* query_context = get_active_collect_query_context()) {
            return query_context->lookup_enum_semantics(
                enum_decl,
                state_out,
                cache_ctx->semantic_store());
        }
        return cache_ctx->lookup_enum_semantics(enum_decl, state_out);
    }
    return false;
}

bool enum_semantics_cache_lookup(const EnumDecl* enum_decl,
                                 EnumSemanticState& state_out) {
    return enum_semantics_cache_lookup(enum_decl, state_out, nullptr);
}

namespace {
const ObjectDecl* get_record_decl(const ObjectType* record_type) {
    if (!record_type) {
        return nullptr;
    }
    const auto* tag_decl = record_type->get_decl();
    if (!tag_decl || !tag_decl->is_record_decl()) {
        return nullptr;
    }
    return static_cast<const ObjectDecl*>(tag_decl);
}

const EnumDecl* get_enum_decl(const EnumType* enum_type) {
    if (!enum_type) {
        return nullptr;
    }
    const auto* tag_decl = enum_type->get_decl();
    if (!tag_decl || !tag_decl->is_enum_decl()) {
        return nullptr;
    }
    return static_cast<const EnumDecl*>(tag_decl);
}

bool extract_decl_record_incomplete(const ObjectDecl* record_decl, bool& incomplete_out) {
    if (!record_decl) {
        return false;
    }
    const RecordSemanticState* state = record_semantics_cache_lookup(record_decl);
    if (!state) {
        return false;
    }
    incomplete_out = state->is_incomplete;
    return true;
}

bool extract_decl_record_layout(const ObjectDecl* record_decl,
                                const std::vector<ObjectType::Field>*& fields_out,
                                size_t& size_bits_out,
                                size_t& alignment_out,
                                bool& has_fam_out) {
    if (!record_decl) {
        return false;
    }
    const RecordSemanticState* state = record_semantics_cache_lookup(record_decl);
    if (!state) {
        return false;
    }
    fields_out = &state->fields;
    size_bits_out = state->size_bits;
    alignment_out = state->alignment;
    has_fam_out = state->has_flexible_array_member;
    return true;
}

std::vector<ObjectType::Field> build_decl_record_fields(
    const ObjectDecl* record_decl) {
    std::vector<ObjectType::Field> fields;
    if (!record_decl) {
        return fields;
    }
    for (const auto& member : record_decl->fields) {
        auto* field_decl = dyn_cast<FieldDecl>(member.get());
        if (!field_decl) {
            continue;
        }
        if (field_decl->is_bitfield()) {
            fields.emplace_back(
                field_decl->name,
                field_decl->type,
                0,
                0,
                field_decl->bitfield_width,
                0);
            continue;
        }
        fields.emplace_back(field_decl->name, field_decl->type, 0);
    }
    return fields;
}

bool extract_decl_enum_incomplete(const EnumDecl* enum_decl, bool& incomplete_out) {
    if (!enum_decl) {
        return false;
    }
    EnumSemanticState state;
    if (!enum_semantics_cache_lookup(enum_decl, state)) {
        return false;
    }
    incomplete_out = state.is_incomplete;
    return true;
}

bool extract_decl_enum_has_negative_values(const EnumDecl* enum_decl, bool& has_negative_out) {
    if (!enum_decl) {
        return false;
    }
    EnumSemanticState state;
    if (!enum_semantics_cache_lookup(enum_decl, state)) {
        return false;
    }
    has_negative_out = state.has_negative_values;
    return true;
}

bool extract_decl_enum_scoped(const EnumDecl* enum_decl, bool& is_scoped_out) {
    if (!enum_decl) {
        return false;
    }
    EnumSemanticState state;
    if (!enum_semantics_cache_lookup(enum_decl, state)) {
        return false;
    }
    is_scoped_out = state.is_scoped;
    return true;
}

std::shared_ptr<CType> extract_decl_enum_underlying_type(const EnumDecl* enum_decl) {
    if (!enum_decl) {
        return nullptr;
    }
    EnumSemanticState state;
    if (!enum_semantics_cache_lookup(enum_decl, state)) {
        return nullptr;
    }
    return state.underlying_type;
}
} // namespace

int builtin_integer_rank_from_width(int64_t width_bits) {
    if (width_bits <= 8) {
        return 10;
    }
    if (width_bits <= 16) {
        return 20;
    }
    if (width_bits <= 32) {
        return 30;
    }
    if (width_bits <= 64) {
        return 40;
    }
    return 60;
}

void init_builtins(std::unordered_map<BuiltinTypes, std::shared_ptr<BuiltinType>>& builtins,
                   const TargetInfo* target) {
    builtins[BuiltinTypes::Void] = std::make_shared<BuiltinType>(BuiltinTypes::Void);
    builtins[BuiltinTypes::NullPtr] = std::make_shared<BuiltinType>(BuiltinTypes::NullPtr);
    builtins[BuiltinTypes::Bool] = std::make_shared<BuiltinType>(BuiltinTypes::Bool);
    builtins[BuiltinTypes::Char] = std::make_shared<BuiltinType>(BuiltinTypes::Char);
    builtins[BuiltinTypes::SChar] = std::make_shared<BuiltinType>(
        BuiltinTypes::SChar, 8, 10, 0);
    builtins[BuiltinTypes::UChar] = std::make_shared<BuiltinType>(BuiltinTypes::UChar);
    int64_t wchar_width = target ? target->wchar_width : 32;
    builtins[BuiltinTypes::WChar] = std::make_shared<BuiltinType>(
        BuiltinTypes::WChar,
        wchar_width,
        builtin_integer_rank_from_width(wchar_width),
        target && target->wchar_is_unsigned ? 1 : 0);
    builtins[BuiltinTypes::Char16] = std::make_shared<BuiltinType>(
        BuiltinTypes::Char16, 16, 20, 1);
    builtins[BuiltinTypes::Char32] = std::make_shared<BuiltinType>(
        BuiltinTypes::Char32, 32, 30, 1);
    builtins[BuiltinTypes::Short] = std::make_shared<BuiltinType>(BuiltinTypes::Short);
    builtins[BuiltinTypes::UShort] = std::make_shared<BuiltinType>(BuiltinTypes::UShort);
    builtins[BuiltinTypes::Int] = std::make_shared<BuiltinType>(BuiltinTypes::Int);
    builtins[BuiltinTypes::UInt] = std::make_shared<BuiltinType>(BuiltinTypes::UInt);
    builtins[BuiltinTypes::Long] = std::make_shared<BuiltinType>(BuiltinTypes::Long);
    builtins[BuiltinTypes::ULong] = std::make_shared<BuiltinType>(BuiltinTypes::ULong);
    builtins[BuiltinTypes::LongLong] = std::make_shared<BuiltinType>(BuiltinTypes::LongLong);
    builtins[BuiltinTypes::ULongLong] = std::make_shared<BuiltinType>(BuiltinTypes::ULongLong);
    builtins[BuiltinTypes::Int128] = std::make_shared<BuiltinType>(BuiltinTypes::Int128);
    builtins[BuiltinTypes::UInt128] = std::make_shared<BuiltinType>(BuiltinTypes::UInt128);
    builtins[BuiltinTypes::Float16] = std::make_shared<BuiltinType>(BuiltinTypes::Float16);
    builtins[BuiltinTypes::Float] = std::make_shared<BuiltinType>(BuiltinTypes::Float);
    builtins[BuiltinTypes::Double] = std::make_shared<BuiltinType>(BuiltinTypes::Double);
    builtins[BuiltinTypes::LongDouble] = std::make_shared<BuiltinType>(BuiltinTypes::LongDouble);
}

TypeContext::TypeContext() {
    target = TargetInfo::create_host();
    init_builtins(builtins, target.get());
    cpp_type_info_type = std::make_shared<CppTypeInfoType>(
        target && target->pointer_width > 0 ? target->pointer_width : 64);
}

TypeContext::TypeContext(std::shared_ptr<TargetInfo> ti) : target(std::move(ti)) {
    init_builtins(builtins, target.get());
    cpp_type_info_type = std::make_shared<CppTypeInfoType>(
        target && target->pointer_width > 0 ? target->pointer_width : 64);
}

// using Mac os definitions for now
int64_t BuiltinType::getWidth() {
    if (width_override >= 0) {
        return width_override;
    }
    switch (builtin_kind) {
        case BuiltinTypes::Void:
        case BuiltinTypes::Bool:
        case BuiltinTypes::Char:
        case BuiltinTypes::SChar:
        case BuiltinTypes::UChar: return 8;
        case BuiltinTypes::WChar:
        case BuiltinTypes::Char32:
            return 32;
        case BuiltinTypes::Char16:
            return 16;
        case BuiltinTypes::NullPtr:
            return 64;
        case BuiltinTypes::Short:
        case BuiltinTypes::UShort: return 16;
        case BuiltinTypes::Int:
        case BuiltinTypes::UInt: return 32;
        case BuiltinTypes::Long:
        case BuiltinTypes::ULong: return 64;
        case BuiltinTypes::LongLong:
        case BuiltinTypes::ULongLong: return 64;
        case BuiltinTypes::Int128:
        case BuiltinTypes::UInt128: return 128;
        case BuiltinTypes::Float16: return 16;
        case BuiltinTypes::Float: return 32;
        case BuiltinTypes::Double: return 64;
        case BuiltinTypes::LongDouble: return 64; // Apple ARM64: long double == double (64-bit)
        default: return 0;
    }
}

int BuiltinType::getRank() const {
    if (rank_override >= 0) {
        return rank_override;
    }
    switch (builtin_kind) {
        case BuiltinTypes::Bool: return 1;
        case BuiltinTypes::Char:
        case BuiltinTypes::SChar:
        case BuiltinTypes::UChar: return 10;
        case BuiltinTypes::Char16: return 20;
        case BuiltinTypes::Short:
        case BuiltinTypes::UShort: return 20;
        case BuiltinTypes::WChar:
        case BuiltinTypes::Char32:
            return 30;
        case BuiltinTypes::Int:
        case BuiltinTypes::UInt: return 30;
        case BuiltinTypes::Long:
        case BuiltinTypes::ULong: return 40;
        case BuiltinTypes::LongLong:
        case BuiltinTypes::ULongLong: return 50;
        case BuiltinTypes::Int128:
        case BuiltinTypes::UInt128: return 60;
        // Floating point types don't have integer conversion rank (fp always has "upper hand")
        default: return 0;
    }
}

bool BuiltinType::isUnsigned() const  {
    if (unsigned_override >= 0) {
        return unsigned_override != 0;
    }
    switch (builtin_kind) {
        case BuiltinTypes::Bool:
        case BuiltinTypes::UChar:
        case BuiltinTypes::Char16:
        case BuiltinTypes::Char32:
        case BuiltinTypes::UShort:
        case BuiltinTypes::UInt:
        case BuiltinTypes::ULong:
        case BuiltinTypes::ULongLong:
        case BuiltinTypes::UInt128:
            return true;
        default:
            return false;
    }
}

bool FunctionType::equals(const CType &other) {
    if (other.kind != TypeKind::Function) return false;
    const auto& other1 = static_cast<const FunctionType&>(other);
    auto lhs_ret = desugar_type(ret_type);
    auto rhs_ret = desugar_type(other1.ret_type);
    if (!lhs_ret.equals_unqualified(rhs_ret)) return false;
    if (member_ref_qualifier != other1.member_ref_qualifier) return false;
    if (!function_exception_specs_equal(*this, other1)) return false;
    // K&R style () is compatible with any parameter list (C11 6.7.6.3p15)
    if (!has_prototype || !other1.has_prototype) return true;
    if (parameters.size() != other1.parameters.size()) return false;
    if (is_variadic != other1.is_variadic) return false;
    for (size_t i = 0; i < parameters.size(); ++i) {
        // In C, parameter types are adjusted for function type compatibility:
        // - array parameters become pointers to element type
        // - function parameters become pointers to function
        // (C11 6.7.6.3p7, p15)
        auto decay = [](const QualType& q) -> QualType {
            if (!q) {
                return q;
            }
            auto canonical = desugar_type(q);
            auto kind = canonical ? canonical->kind : TypeKind::Other;
            if (kind == TypeKind::Array) {
                auto arr = canonical.as_shared<ArrayType>();
                if (!arr) {
                    return canonical;
                }
                // Merge array qualifiers into element type: const T[] -> pointer to const T
                auto elem = arr->element_type;
                elem = QualType(elem.get_shared(), elem.get_qualifiers() | canonical.get_qualifiers());
                return QualType(std::make_shared<PointerType>(elem));
            }
            if (kind == TypeKind::Function) {
                return QualType(std::make_shared<PointerType>(canonical));
            }
            return canonical;
        };
        auto p1 = decay(parameters[i]);
        auto p2 = decay(other1.parameters[i]);
        if (p1.equals_unqualified(p2)) {
            continue;
        }

        auto transparent_union_matches = [](const QualType& maybe_union, const QualType& other_param) {
            auto union_canonical = desugar_type(maybe_union);
            auto other_canonical = desugar_type(other_param);
            auto obj = union_canonical.as_shared<ObjectType>();
            if (!obj || !obj->is_union) {
                return false;
            }
            auto fields = get_record_fields_for_type_matching(obj.get());
            // Transparent unions are compatible with any member type. In
            // practice GCC torture cases here use single-member unions.
            if (!obj->is_transparent_union && fields.size() != 1) {
                return false;
            }
            for (const auto& field : fields) {
                if (desugar_type(field.type).equals_unqualified(other_canonical)) {
                    return true;
                }
            }
            return false;
        };
        if (transparent_union_matches(p1, p2) || transparent_union_matches(p2, p1)) {
            continue;
        }
        return false;
    }
    return true;
}

bool PointerType::equals(const CType &other) {
    if (other.kind != TypeKind::Pointer) return false;
    return this->pointed_type.equals_qualified(static_cast<const PointerType&>(other).pointed_type);
}

int64_t PointerType::getWidth() {
    return 64; // Assuming 64-bit architecture for now
}

bool MemberPointerType::equals(const CType& other) {
    if (other.kind != TypeKind::MemberPointer) {
        return false;
    }
    const auto& rhs = static_cast<const MemberPointerType&>(other);
    return class_type.equals_qualified(rhs.class_type) &&
           member_type.equals_qualified(rhs.member_type);
}

int64_t MemberPointerType::getWidth() {
    auto member_canonical = desugar_type(member_type);
    if (member_canonical && member_canonical->kind == TypeKind::Function) {
        // Itanium-style member-function pointer model: {ptr, adj}.
        return 128;
    }
    // Itanium-style data-member pointer model: ptrdiff_t offset.
    return 64;
}

std::string MemberPointerType::to_string() const {
    return member_type.to_string() + " " + class_type.to_string() + "::*";
}

std::string to_string_type_kind(TypeKind tkind) {
    switch (tkind) {
        case TypeKind::Builtin: return "Builtin";
        case TypeKind::Pointer: return "Pointer";
        case TypeKind::MemberPointer: return "MemberPointer";
        case TypeKind::Reference: return "Reference";
        case TypeKind::Array: return "Array";
        case TypeKind::Function: return "Function";
        case TypeKind::Object: return "Record";
        case TypeKind::Enum: return "Enum";
        case TypeKind::CppTypeInfo: return "CppTypeInfo";
        case TypeKind::Typedef: return "Typedef";
        case TypeKind::Vector: return "Vector";
        case TypeKind::Complex: return "Complex";
        case TypeKind::BlockPointer: return "BlockPointer";
        case TypeKind::TemplateTypeParm: return "TemplateTypeParm";
        case TypeKind::TemplateSpecialization: return "TemplateSpecialization";
        case TypeKind::DependentName: return "DependentName";
        case TypeKind::Other: return "Other";
        case TypeKind::Placeholder: return "Placeholder";
        case TypeKind::Auto: return "Auto";
        case TypeKind::TypeofExpr: return "TypeofExpr";
        case TypeKind::DecltypeExpr: return "DecltypeExpr";
        case TypeKind::BuiltinTypeTransform: return "BuiltinTypeTransform";
        default: return "Unknown";
    }
}
std::shared_ptr<CType> convert_arr_to_pointer(std::shared_ptr<ArrayType> arr_type) {
    return std::make_shared<PointerType>(QualType(arr_type->element_type));
}

QualType desugar_typedefs(QualType type) {
    if (!type) {
        return type;
    }
    auto current = type.get_shared();
    uint8_t merged_quals = type.get_qualifiers();
    std::unordered_set<const CType*> seen;
    while (current && current->kind == TypeKind::Typedef) {
        if (!seen.insert(current.get()).second) {
            break;
        }
        auto* td = static_cast<TypedefType*>(current.get());
        if (!td->underlying_type) {
            return QualType();
        }
        merged_quals = static_cast<uint8_t>(
            merged_quals | td->underlying_type.get_qualifiers());
        current = td->underlying_type.get_shared();
    }
    return QualType(current, merged_quals);
}

std::shared_ptr<CType> desugar_typedefs(const std::shared_ptr<CType>& type) {
    return desugar_typedefs(QualType(type)).get_shared();
}

QualType desugar_type(QualType type) {
    return desugar_type(type, get_active_side_table_ast_context());
}

QualType desugar_type(QualType type, const ASTContext* ast_ctx) {
    auto peel_aliases = [&](QualType input) -> QualType {
        QualType peeled = desugar_typedefs(input);
        while (peeled) {
            auto current = peeled.get_shared();
            uint8_t quals = peeled.get_qualifiers();
            if (auto specialization =
                    dyn_cast_shared<TemplateSpecializationType>(current)) {
                if (auto resolved_type = lookup_template_specialization_resolved_type(
                        specialization.get(),
                        ast_ctx)) {
                    peeled = desugar_typedefs(QualType(resolved_type, quals));
                    continue;
                }
            } else if (auto dependent_name =
                           dyn_cast_shared<DependentNameType>(current)) {
                if (auto resolved_type = lookup_dependent_name_resolved_type(
                        dependent_name.get(),
                        ast_ctx)) {
                    peeled = desugar_typedefs(QualType(resolved_type, quals));
                    continue;
                }
            }
            break;
        }
        return peeled;
    };

    auto peeled = peel_aliases(type);
    if (!peeled) {
        return peeled;
    }

    struct LinearLayer {
        enum class Kind : uint8_t {
            Pointer,
            Reference,
            BlockPointer,
        };

        Kind kind = Kind::Pointer;
        std::shared_ptr<CType> original_type = nullptr;
        QualType original_child;
        uint8_t outer_quals = QUAL_NONE;
        ReferenceKind reference_kind = ReferenceKind::LValue;
    };

    std::vector<LinearLayer> linear_layers;
    QualType linear_leaf = peeled;
    while (linear_leaf) {
        auto current = linear_leaf.get_shared();
        uint8_t quals = linear_leaf.get_qualifiers();
        if (auto ptr = dyn_cast_shared<PointerType>(current)) {
            linear_layers.push_back({LinearLayer::Kind::Pointer,
                                     current,
                                     ptr->pointed_type,
                                     quals,
                                     ReferenceKind::LValue});
            linear_leaf = peel_aliases(ptr->pointed_type);
            continue;
        }
        if (auto ref = dyn_cast_shared<ReferenceType>(current)) {
            linear_layers.push_back({LinearLayer::Kind::Reference,
                                     current,
                                     ref->referred_type,
                                     quals,
                                     ref->reference_kind});
            linear_leaf = peel_aliases(ref->referred_type);
            continue;
        }
        if (auto blk = dyn_cast_shared<BlockPointerType>(current)) {
            linear_layers.push_back({LinearLayer::Kind::BlockPointer,
                                     current,
                                     blk->pointed_type,
                                     quals,
                                     ReferenceKind::LValue});
            linear_leaf = peel_aliases(blk->pointed_type);
            continue;
        }
        break;
    }

    auto current = linear_leaf.get_shared();
    uint8_t quals = linear_leaf.get_qualifiers();
    QualType rebuilt = linear_leaf;
    bool changed = false;

    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(current)) {
        auto class_ty = desugar_type(mem_ptr->class_type, ast_ctx);
        auto member_ty = desugar_type(mem_ptr->member_type, ast_ctx);
        if (class_ty.equals_qualified(mem_ptr->class_type) &&
            member_ty.equals_qualified(mem_ptr->member_type)) {
            rebuilt = linear_leaf;
        } else {
            rebuilt = QualType(
                std::make_shared<MemberPointerType>(class_ty, member_ty),
                quals);
            changed = true;
        }
    } else if (auto arr = dyn_cast_shared<ArrayType>(current)) {
        auto elem = desugar_type(arr->element_type, ast_ctx);
        if (elem.equals_qualified(arr->element_type)) {
            rebuilt = linear_leaf;
        } else if (arr->size_kind == ArraySizeKind::Variable) {
            rebuilt = QualType(
                std::make_shared<ArrayType>(elem, arr->size_expr), quals);
            changed = true;
        } else {
            rebuilt = QualType(std::make_shared<ArrayType>(elem, arr->size), quals);
            changed = true;
        }
    } else if (auto func = dyn_cast_shared<FunctionType>(current)) {
        auto ret = desugar_type(func->ret_type, ast_ctx);
        changed = !ret.equals_qualified(func->ret_type);
        std::vector<QualType> params;
        params.reserve(func->parameters.size());
        for (const auto& p : func->parameters) {
            auto rp = desugar_type(p, ast_ctx);
            if (!rp.equals_qualified(p)) {
                changed = true;
            }
            params.push_back(rp);
        }
        if (!changed) {
            rebuilt = linear_leaf;
        } else {
            auto rebuilt_func = std::make_shared<FunctionType>();
            rebuilt_func->ret_type = ret;
            rebuilt_func->parameters = std::move(params);
            rebuilt_func->is_variadic = func->is_variadic;
            rebuilt_func->has_prototype = func->has_prototype;
            rebuilt_func->member_ref_qualifier = func->member_ref_qualifier;
            rebuilt_func->has_explicit_exception_spec =
                func->has_explicit_exception_spec;
            rebuilt_func->exception_spec = func->exception_spec;
            rebuilt_func->exception_spec_expr = func->exception_spec_expr;
            rebuilt = QualType(rebuilt_func, quals);
        }
    } else if (auto vec = dyn_cast_shared<VectorType>(current)) {
        auto elem = desugar_type(vec->element_type, ast_ctx);
        if (elem.equals_qualified(vec->element_type)) {
            rebuilt = linear_leaf;
        } else {
            rebuilt = QualType(
                std::make_shared<VectorType>(elem, vec->total_bytes), quals);
            changed = true;
        }
    }
    for (auto it = linear_layers.rbegin(); it != linear_layers.rend(); ++it) {
        if (!changed && rebuilt.equals_qualified(it->original_child)) {
            rebuilt = QualType(it->original_type, it->outer_quals);
            continue;
        }
        changed = true;
        switch (it->kind) {
            case LinearLayer::Kind::Pointer:
                rebuilt = QualType(
                    std::make_shared<PointerType>(rebuilt),
                    it->outer_quals);
                break;
            case LinearLayer::Kind::Reference:
                rebuilt = QualType(
                    std::make_shared<ReferenceType>(rebuilt, it->reference_kind),
                    it->outer_quals);
                break;
            case LinearLayer::Kind::BlockPointer:
                rebuilt = QualType(
                    std::make_shared<BlockPointerType>(rebuilt),
                    it->outer_quals);
                break;
        }
    }

    return rebuilt;
}

std::shared_ptr<CType> desugar_type(const std::shared_ptr<CType>& type) {
    return desugar_type(type, get_active_side_table_ast_context());
}

std::shared_ptr<CType> desugar_type(const std::shared_ptr<CType>& type,
                                    const ASTContext* ast_ctx) {
    return desugar_type(QualType(type), ast_ctx).get_shared();
}

TypeKind canonical_type_kind(QualType type) {
    return canonical_type_kind(type, get_active_side_table_ast_context());
}

TypeKind canonical_type_kind(QualType type, const ASTContext* ast_ctx) {
    QualType current = desugar_typedefs(type);
    while (current) {
        auto raw = current.get_shared();
        if (!raw) {
            return TypeKind::Other;
        }
        uint8_t quals = current.get_qualifiers();
        if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
            if (auto resolved_type = lookup_template_specialization_resolved_type(
                    specialization.get(),
                    ast_ctx)) {
                current = desugar_typedefs(QualType(resolved_type, quals));
                continue;
            }
        } else if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
            if (auto resolved_type = lookup_dependent_name_resolved_type(
                    dependent_name.get(),
                    ast_ctx)) {
                current = desugar_typedefs(QualType(resolved_type, quals));
                continue;
            }
        }
        return raw->kind;
    }
    return TypeKind::Other;
}

TypeKind canonical_type_kind(const std::shared_ptr<CType>& type) {
    return canonical_type_kind(type, get_active_side_table_ast_context());
}

TypeKind canonical_type_kind(const std::shared_ptr<CType>& type,
                             const ASTContext* ast_ctx) {
    return canonical_type_kind(QualType(type), ast_ctx);
}

bool is_reference_type(QualType type) {
    return is_reference_type(type, get_active_side_table_ast_context());
}

bool is_reference_type(QualType type, const ASTContext* ast_ctx) {
    return canonical_type_kind(type, ast_ctx) == TypeKind::Reference;
}

bool is_reference_type(const std::shared_ptr<CType>& type) {
    return is_reference_type(type, get_active_side_table_ast_context());
}

bool is_reference_type(const std::shared_ptr<CType>& type,
                       const ASTContext* ast_ctx) {
    return is_reference_type(QualType(type), ast_ctx);
}

QualType remove_reference(QualType type) {
    return remove_reference(type, get_active_side_table_ast_context());
}

QualType remove_reference(QualType type, const ASTContext* ast_ctx) {
    auto canonical = desugar_type(type, ast_ctx);
    auto ref = canonical.as_shared<ReferenceType>();
    if (!ref) {
        return type;
    }
    return ref->referred_type;
}

std::shared_ptr<CType> remove_reference(const std::shared_ptr<CType>& type) {
    return remove_reference(type, get_active_side_table_ast_context());
}

std::shared_ptr<CType> remove_reference(const std::shared_ptr<CType>& type,
                                        const ASTContext* ast_ctx) {
    return remove_reference(QualType(type), ast_ctx).get_shared();
}

QualType make_reference_type(QualType referred, ReferenceKind kind) {
    if (!referred) {
        return QualType();
    }

    auto referred_raw = referred.get_shared();
    if (auto existing_ref = dyn_cast_shared<ReferenceType>(referred_raw)) {
        ReferenceKind collapsed_kind =
            (kind == ReferenceKind::LValue ||
             existing_ref->reference_kind == ReferenceKind::LValue)
                ? ReferenceKind::LValue
                : ReferenceKind::RValue;
        return QualType(
            std::make_shared<ReferenceType>(
                existing_ref->referred_type,
                collapsed_kind),
            referred.get_qualifiers());
    }

    return QualType(std::make_shared<ReferenceType>(referred, kind));
}

std::shared_ptr<CType> make_reference_type(
    const std::shared_ptr<CType>& referred,
    ReferenceKind kind) {
    return make_reference_type(QualType(referred), kind).get_shared();
}

namespace {
QualType remove_top_level_qualifiers(QualType type, uint8_t qualifiers_to_strip) {
    if (!type) {
        return type;
    }
    return QualType(
        type.get_shared(),
        static_cast<uint8_t>(type.get_qualifiers() & ~qualifiers_to_strip));
}

bool is_referenceable_type(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    type = desugar_type(type, ast_ctx);
    if (!type) {
        return false;
    }
    return !type->isVoid();
}

const char* builtin_type_transform_name(BuiltinTypeTransformKind kind) {
    switch (kind) {
        case BuiltinTypeTransformKind::RemoveConst:
            return "__remove_const";
        case BuiltinTypeTransformKind::RemoveVolatile:
            return "__remove_volatile";
        case BuiltinTypeTransformKind::RemoveCV:
            return "__remove_cv";
        case BuiltinTypeTransformKind::RemoveCVRef:
            return "__remove_cvref";
        case BuiltinTypeTransformKind::RemoveReference:
            return "__remove_reference";
        case BuiltinTypeTransformKind::UnderlyingType:
            return "__underlying_type";
        case BuiltinTypeTransformKind::RemoveExtent:
            return "__remove_extent";
        case BuiltinTypeTransformKind::RemoveAllExtents:
            return "__remove_all_extents";
        case BuiltinTypeTransformKind::Decay:
            return "__decay";
        case BuiltinTypeTransformKind::AddPointer:
            return "__add_pointer";
        case BuiltinTypeTransformKind::AddLValueReference:
            return "__add_lvalue_reference";
        case BuiltinTypeTransformKind::AddRValueReference:
            return "__add_rvalue_reference";
    }
    return "__builtin_type_transform";
}
} // namespace

bool lookup_builtin_type_transform_kind(
    std::string_view name,
    BuiltinTypeTransformKind& out) {
    if (name == "__remove_const") {
        out = BuiltinTypeTransformKind::RemoveConst;
        return true;
    }
    if (name == "__remove_volatile") {
        out = BuiltinTypeTransformKind::RemoveVolatile;
        return true;
    }
    if (name == "__remove_cv") {
        out = BuiltinTypeTransformKind::RemoveCV;
        return true;
    }
    if (name == "__remove_cvref") {
        out = BuiltinTypeTransformKind::RemoveCVRef;
        return true;
    }
    if (name == "__remove_reference" || name == "__remove_reference_t") {
        out = BuiltinTypeTransformKind::RemoveReference;
        return true;
    }
    if (name == "__underlying_type") {
        out = BuiltinTypeTransformKind::UnderlyingType;
        return true;
    }
    if (name == "__remove_extent") {
        out = BuiltinTypeTransformKind::RemoveExtent;
        return true;
    }
    if (name == "__remove_all_extents") {
        out = BuiltinTypeTransformKind::RemoveAllExtents;
        return true;
    }
    if (name == "__decay") {
        out = BuiltinTypeTransformKind::Decay;
        return true;
    }
    if (name == "__add_pointer") {
        out = BuiltinTypeTransformKind::AddPointer;
        return true;
    }
    if (name == "__add_lvalue_reference") {
        out = BuiltinTypeTransformKind::AddLValueReference;
        return true;
    }
    if (name == "__add_rvalue_reference") {
        out = BuiltinTypeTransformKind::AddRValueReference;
        return true;
    }
    return false;
}

QualType apply_builtin_type_transform(
    BuiltinTypeTransformKind kind,
    QualType operand_type) {
    return apply_builtin_type_transform(
        kind,
        operand_type,
        get_active_side_table_ast_context());
}

QualType apply_builtin_type_transform(
    BuiltinTypeTransformKind kind,
    QualType operand_type,
    const ASTContext* ast_ctx) {
    auto strip_one_array_extent = [&](QualType type) -> QualType {
        auto array_type = desugar_type(type, ast_ctx).as_shared<ArrayType>();
        if (!array_type) {
            return type;
        }
        auto element_type = array_type->element_type;
        uint8_t merged_quals = static_cast<uint8_t>(
            element_type.get_qualifiers() |
            desugar_type(type, ast_ctx).get_qualifiers());
        return QualType(element_type.get_shared(), merged_quals);
    };

    switch (kind) {
        case BuiltinTypeTransformKind::RemoveConst:
            return remove_top_level_qualifiers(operand_type, QUAL_CONST);
        case BuiltinTypeTransformKind::RemoveVolatile:
            return remove_top_level_qualifiers(operand_type, QUAL_VOLATILE);
        case BuiltinTypeTransformKind::RemoveCV:
            return remove_top_level_qualifiers(
                operand_type,
                static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE));
        case BuiltinTypeTransformKind::RemoveCVRef:
            return remove_top_level_qualifiers(
                remove_reference(operand_type, ast_ctx),
                static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE));
        case BuiltinTypeTransformKind::RemoveReference:
            return remove_reference(operand_type, ast_ctx);
        case BuiltinTypeTransformKind::UnderlyingType: {
            auto enum_type =
                desugar_type(
                    remove_top_level_qualifiers(
                        remove_reference(operand_type, ast_ctx),
                        static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE)),
                    ast_ctx)
                    .as_shared<EnumType>();
            if (!enum_type) {
                return QualType();
            }
            auto underlying_type = enum_type->semantic_underlying_type();
            if (!underlying_type) {
                return QualType();
            }
            return QualType(underlying_type);
        }
        case BuiltinTypeTransformKind::RemoveExtent:
            return strip_one_array_extent(operand_type);
        case BuiltinTypeTransformKind::RemoveAllExtents: {
            QualType current = operand_type;
            while (current) {
                auto current_array =
                    desugar_type(current, ast_ctx).as_shared<ArrayType>();
                if (!current_array) {
                    break;
                }
                current = strip_one_array_extent(current);
            }
            return current;
        }
        case BuiltinTypeTransformKind::Decay: {
            auto decayed = remove_reference(operand_type, ast_ctx);
            auto canonical_decayed = desugar_type(decayed, ast_ctx);
            if (!canonical_decayed) {
                return QualType();
            }
            if (auto array_type = canonical_decayed.as_shared<ArrayType>()) {
                return QualType(
                    std::make_shared<PointerType>(array_type->element_type));
            }
            if (canonical_decayed->kind == TypeKind::Function) {
                return QualType(
                    std::make_shared<PointerType>(canonical_decayed));
            }
            return remove_top_level_qualifiers(
                decayed,
                static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE));
        }
        case BuiltinTypeTransformKind::AddPointer: {
            auto pointee_type = remove_reference(operand_type, ast_ctx);
            if (!pointee_type) {
                return QualType();
            }
            auto canonical_pointee = desugar_type(pointee_type, ast_ctx);
            if (!canonical_pointee) {
                return QualType();
            }
            if (!canonical_pointee->isVoid() &&
                !is_referenceable_type(operand_type, ast_ctx)) {
                return operand_type;
            }
            return QualType(std::make_shared<PointerType>(pointee_type));
        }
        case BuiltinTypeTransformKind::AddLValueReference:
            if (!is_referenceable_type(operand_type, ast_ctx)) {
                return operand_type;
            }
            return make_reference_type(operand_type, ReferenceKind::LValue);
        case BuiltinTypeTransformKind::AddRValueReference:
            if (!is_referenceable_type(operand_type, ast_ctx)) {
                return operand_type;
            }
            return make_reference_type(operand_type, ReferenceKind::RValue);
    }
    return operand_type;
}

std::string PointerType::to_string() const {
    return pointed_type.to_string() + " *";
}

std::string ReferenceType::to_string() const {
    return referred_type.to_string() +
        (reference_kind == ReferenceKind::RValue ? " &&" : " &");
}

std::string BuiltinTypeTransformType::to_string() const {
    return std::string(builtin_type_transform_name(transform_kind)) +
        "(" + operand_type.to_string() + ")";
}

std::string ArrayType::to_string() const {
    if (size.has_value()) {
        return element_type.to_string() + "[" + std::to_string(*size) + "]";
    }
    if (isVLA()) {
        return element_type.to_string() + "[...]";
    }
    return element_type.to_string() + "[]";
}

std::string FunctionType::to_string() const {
    std::string result = ret_type.to_string() + "(";
    for (size_t i = 0; i < parameters.size(); ++i) {
        if (i > 0) result += ", ";
        result += parameters[i].to_string();
    }
    if (is_variadic) {
        if (!parameters.empty()) result += ", ";
        result += "...";
    }
    result += ")";
    if (member_ref_qualifier == FunctionRefQualifierKind::LValue) {
        result += " &";
    } else if (member_ref_qualifier == FunctionRefQualifierKind::RValue) {
        result += " &&";
    }
    if (has_explicit_exception_spec) {
        if (exception_spec == FunctionExceptionSpecKind::NonThrowing) {
            result += " noexcept";
        } else if (exception_spec == FunctionExceptionSpecKind::Dependent) {
            result += " noexcept(<dependent>)";
        } else {
            result += " noexcept(false)";
        }
    }
    return result;
}

bool ObjectType::isIncomplete() const {
    const auto* record_decl = get_record_decl(this);
    if (!record_decl) {
        return true;
    }

    bool decl_incomplete = false;
    if (!extract_decl_record_incomplete(record_decl, decl_incomplete)) {
        return true;
    }
    return decl_incomplete;
}

const std::vector<ObjectType::Field>& ObjectType::semantic_fields() const {
    const auto* record_decl = get_record_decl(this);
    if (!record_decl) {
        static const std::vector<ObjectType::Field> empty_fields;
        return empty_fields;
    }
    const RecordSemanticState* state = record_semantics_cache_lookup(record_decl);
    if (!state) {
        static const std::vector<ObjectType::Field> empty_fields;
        return empty_fields;
    }
    return state->fields;
}

bool ObjectType::semantic_has_flexible_array_member() const {
    const auto* record_decl = get_record_decl(this);
    if (!record_decl) {
        return false;
    }
    const RecordSemanticState* state = record_semantics_cache_lookup(record_decl);
    if (!state) {
        return false;
    }
    return state->has_flexible_array_member;
}

int64_t ObjectType::getWidth() {
    if (isIncomplete()) {
        return 0;
    }
    const auto* record_decl = get_record_decl(this);
    if (!record_decl) {
        return 0;
    }
    const RecordSemanticState* state = record_semantics_cache_lookup(record_decl);
    if (!state) {
        return 0;
    }
    return static_cast<int64_t>(state->size_bits);
}

size_t ObjectType::getAlignment() {
    if (isIncomplete()) {
        return 0;
    }
    const auto* record_decl = get_record_decl(this);
    if (!record_decl) {
        return 0;
    }
    const RecordSemanticState* state = record_semantics_cache_lookup(record_decl);
    if (!state) {
        return 0;
    }
    return state->alignment;
}

std::vector<ObjectType::Field> get_record_fields_for_type_matching(
    const ObjectType* record_type) {
    if (!record_type) {
        return {};
    }
    const auto& semantic = record_type->semantic_fields();
    if (!semantic.empty()) {
        return semantic;
    }
    return build_decl_record_fields(get_record_decl(record_type));
}

const ObjectType::Field* ObjectType::findField(const std::string& name) const {
    const auto& view = semantic_fields();
    for (const auto& field : view) {
        if (field.name == name) {
            return &field;
        }
    }
    return nullptr;
}

bool ObjectType::has_bitfields() const {
    const auto& view = semantic_fields();
    for (const auto& field : view) {
        if (field.is_bitfield) {
            return true;
        }
    }
    return false;
}

std::string ObjectType::to_string() const {
    const auto* record_decl = get_record_decl(this);
    std::string display_tag = record_decl ? record_decl->get_tag_name() : "";
    return std::string(is_union ? "union " : "struct ") +
           (display_tag.empty() ? "(anonymous)" : display_tag);
}

bool EnumType::isIncomplete() const {
    const auto* enum_decl = get_enum_decl(this);
    if (!enum_decl) {
        return true;
    }

    bool decl_incomplete = false;
    if (!extract_decl_enum_incomplete(enum_decl, decl_incomplete)) {
        return true;
    }
    return decl_incomplete;
}

bool EnumType::isScoped() const {
    const auto* enum_decl = get_enum_decl(this);
    if (!enum_decl) {
        return false;
    }

    bool decl_is_scoped = false;
    if (!extract_decl_enum_scoped(enum_decl, decl_is_scoped)) {
        return false;
    }
    return decl_is_scoped;
}

bool EnumType::isUnsigned() const {
    auto underlying = semantic_underlying_type();
    return underlying ? underlying->isUnsigned() : false;
}

std::shared_ptr<CType> EnumType::semantic_underlying_type() const {
    const auto* enum_decl = get_enum_decl(this);
    if (!enum_decl) {
        return nullptr;
    }
    auto decl_underlying = extract_decl_enum_underlying_type(enum_decl);
    return decl_underlying;
}

int64_t EnumType::getWidth() {
    auto chosen_underlying = semantic_underlying_type();
    return chosen_underlying ? chosen_underlying->getWidth() : 0;
}

std::string EnumType::to_string() const {
    const auto* enum_decl = get_enum_decl(this);
    std::string display_tag = enum_decl ? enum_decl->get_tag_name() : "";
    std::string prefix = isScoped() ? "enum class " : "enum ";
    return prefix + (display_tag.empty() ? "(anonymous)" : display_tag);
}

bool type_contains_vla(const std::shared_ptr<CType>& type) {
    auto raw = desugar_type(type);
    if (!raw) return false;
    switch (raw->kind) {
        case TypeKind::Array: {
            auto *arr = static_cast<ArrayType*>(raw.get());
            if (arr->isVLA()) return true;
            return type_contains_vla(arr->element_type.get_shared());
        }
        case TypeKind::Pointer:
            return type_contains_vla(static_cast<PointerType*>(raw.get())->pointed_type.get_shared());
        case TypeKind::MemberPointer:
            return type_contains_vla(static_cast<MemberPointerType*>(raw.get())->member_type.get_shared());
        case TypeKind::Reference:
            return type_contains_vla(static_cast<ReferenceType*>(raw.get())->referred_type.get_shared());
        case TypeKind::BlockPointer:
            return type_contains_vla(static_cast<BlockPointerType*>(raw.get())->pointed_type.get_shared());
        case TypeKind::Function: {
            auto *func = static_cast<FunctionType*>(raw.get());
            if (type_contains_vla(func->ret_type.get_shared())) return true;
            for (const auto& param : func->parameters) {
                if (type_contains_vla(param.get_shared())) return true;
            }
            return false;
        }
        case TypeKind::BuiltinTypeTransform:
            return type_contains_vla(
                static_cast<BuiltinTypeTransformType*>(raw.get())
                    ->operand_type
                    .get_shared());
        default:
            // VLAs cannot appear in struct fields (C99 6.7.2.1), so no need to recurse
            return false;
    }
}

size_t object_field_storage_size_bytes(const ObjectType::Field& field) {
    if (field.storage_size_override > 0) {
        return field.storage_size_override;
    }
    if (!field.type) {
        return 0;
    }
    int64_t width_bytes = field.type->getWidthBytes();
    return width_bytes > 0 ? static_cast<size_t>(width_bytes) : 0;
}

size_t object_field_storage_alignment(const ObjectType::Field& field) {
    if (field.storage_alignment_override > 0) {
        return field.storage_alignment_override;
    }
    if (field.forced_alignment > 0) {
        return field.forced_alignment;
    }
    return 0;
}

RecordSemanticState compute_record_semantics(std::vector<ObjectType::Field> fields,
                                             bool is_union,
                                             bool is_packed,
                                             size_t requested_alignment,
                                             size_t pack_alignment,
                                             bool is_incomplete,
                                             const AbiPolicy* abi_policy) {
    RecordSemanticState state;
    state.is_incomplete = is_incomplete;
    state.fields = std::move(fields);
    state.size_bits = 0;
    state.alignment = 1;
    state.non_virtual_size_bits = 0;
    state.non_virtual_alignment = 1;
    state.has_flexible_array_member = false;

    if (state.is_incomplete) {
        return state;
    }
    if (state.fields.empty()) {
        state.size_bits = 8;
        state.non_virtual_size_bits = 8;
        return state;
    }

    bool has_bitfields = false;
    for (const auto& field : state.fields) {
        if (field.is_bitfield) {
            has_bitfields = true;
            break;
        }
    }

    if (has_bitfields) {
        BitfieldLayoutConfig config;
        if (abi_policy) {
            config.abi = abi_policy->bitfield_abi;
            config.plain_int_is_signed = abi_policy->plain_int_bitfield_signed;
            config.lsb_first = abi_policy->endianness == EndiannessKind::Little;
        }
        config.pack_alignment = pack_alignment;
        if (is_packed && config.pack_alignment == 0) {
            config.pack_alignment = 1;
        }
        config.record_packed = is_packed;
        BitfieldLayoutEngine engine(config);
        size_t total_size_bits = 0;
        size_t alignment = 1;
        engine.compute_layout(state.fields, is_union, total_size_bits, alignment);
        state.size_bits = total_size_bits;
        state.alignment = alignment;
        if (requested_alignment > state.alignment) {
            state.alignment = requested_alignment;
            size_t total_bytes = (state.size_bits + 7) / 8;
            if (total_bytes % state.alignment != 0) {
                total_bytes += state.alignment - (total_bytes % state.alignment);
            }
            state.size_bits = total_bytes * 8;
        }
        state.non_virtual_size_bits = state.size_bits;
        state.non_virtual_alignment = state.alignment;
        return state;
    }

    size_t current_offset = 0;
    size_t max_alignment = 1;

    std::function<size_t(const QualType&)> get_type_alignment = [&](const QualType& type) -> size_t {
        QualType canonical = desugar_type(type);
        if (!canonical) {
            return 1;
        }
        if (auto *obj = canonical.as<ObjectType>()) {
            return obj->getAlignment();
        }
        if (auto *arr = canonical.as<ArrayType>()) {
            return get_type_alignment(arr->element_type);
        }
        size_t sz = static_cast<size_t>(canonical->getWidthBytes());
        return sz > 0 ? sz : 1;
    };

    if (is_union) {
        size_t max_size = 0;
        for (auto& field : state.fields) {
            field.offset = 0;
            size_t field_size = object_field_storage_size_bytes(field);
            if (field_size == 0) {
                field_size = 1;
            }

            size_t field_align;
            size_t override_align = object_field_storage_alignment(field);
            if (override_align > 0) {
                field_align = override_align;
            } else if (is_packed) {
                field_align = 1;
            } else {
                field_align = get_type_alignment(field.type);
                if (pack_alignment > 0 && field_align > pack_alignment) {
                    field_align = pack_alignment;
                }
            }

            if (field_size > max_size) {
                max_size = field_size;
            }
            if (!is_packed && field_align > max_alignment) {
                max_alignment = field_align;
            }
        }
        size_t total_bytes = max_size;
        size_t final_align = is_packed ? 1 : max_alignment;
        if (requested_alignment > final_align) {
            final_align = requested_alignment;
        }
        if (total_bytes % final_align != 0) {
            total_bytes += final_align - (total_bytes % final_align);
        }
        state.size_bits = total_bytes * 8;
        state.alignment = final_align;
        state.non_virtual_size_bits = state.size_bits;
        state.non_virtual_alignment = state.alignment;
        return state;
    }

    for (size_t field_index = 0; field_index < state.fields.size(); ++field_index) {
        auto& field = state.fields[field_index];
        size_t natural_align;
        bool is_fam = false;
        if (auto *arr = field.type.as<ArrayType>()) {
            if (arr->size_kind == ArraySizeKind::Incomplete &&
                field_index + 1 == state.fields.size()) {
                is_fam = true;
                natural_align = static_cast<size_t>(arr->element_type->getWidthBytes());
            } else {
                natural_align = get_type_alignment(field.type);
            }
        } else {
            natural_align = get_type_alignment(field.type);
        }
        if (natural_align == 0) {
            natural_align = 1;
        }

        size_t field_align;
        size_t override_align = object_field_storage_alignment(field);
        if (override_align > 0) {
            field_align = override_align;
        } else if (is_packed) {
            field_align = 1;
        } else {
            field_align = natural_align;
            if (pack_alignment > 0 && field_align > pack_alignment) {
                field_align = pack_alignment;
            }
        }

        if (current_offset % field_align != 0) {
            current_offset += field_align - (current_offset % field_align);
        }

        field.offset = current_offset;
        current_offset += object_field_storage_size_bytes(field);
        if (is_fam) {
            state.has_flexible_array_member = true;
        }

        if (field_align > max_alignment) {
            max_alignment = field_align;
        }
    }

    size_t final_align = is_packed ? 1 : max_alignment;
    if (requested_alignment > final_align) {
        final_align = requested_alignment;
    }
    if (current_offset % final_align != 0) {
        current_offset += final_align - (current_offset % final_align);
    }

    state.size_bits = current_offset * 8;
    state.alignment = final_align;
    state.non_virtual_size_bits = state.size_bits;
    state.non_virtual_alignment = state.alignment;
    return state;
}
