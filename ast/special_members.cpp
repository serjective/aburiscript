#include "special_members.h"
#include "../constexpr/consteval_compat.h"

#include "ast.h"
#include "symbols.h"
#include <unordered_set>

namespace {
const ObjectDecl* lookup_record_decl_for_type(
    QualType type,
    const ASTContext* ast_ctx) {
    auto record_type =
        desugar_type(type, ast_ctx).as_shared<ObjectType>();
    if (!record_type) {
        return nullptr;
    }
    return dyn_cast<ObjectDecl>(record_type->get_decl());
}

const RecordSemanticState* lookup_record_state_for_type(
    QualType type,
    const ASTContext* ast_ctx) {
    auto* record_decl = lookup_record_decl_for_type(type, ast_ctx);
    if (!record_decl) {
        return nullptr;
    }
    return record_semantics_cache_lookup(record_decl, ast_ctx);
}

bool cpp_record_is_trivially_destructible(
    const RecordSemanticState* state,
    const ASTContext* ast_ctx);

Expr* strip_implicit_casts_for_noexcept(Expr* expr) {
    auto* current = expr;
    while (auto* cast = dyn_cast<ImplicitCast>(current)) {
        if (!cast->expr) {
            break;
        }
        current = cast->expr.get();
    }
    return current;
}

bool function_type_is_non_throwing(QualType function_like_type,
                                   const ASTContext* ast_ctx) {
    QualType canonical = desugar_type(function_like_type, ast_ctx);
    if (auto ref_type = canonical.as_shared<ReferenceType>()) {
        return function_type_is_non_throwing(ref_type->referred_type, ast_ctx);
    }
    if (auto ptr_type = canonical.as_shared<PointerType>()) {
        return function_type_is_non_throwing(ptr_type->pointed_type, ast_ctx);
    } else if (auto block_ptr_type = canonical.as_shared<BlockPointerType>()) {
        return function_type_is_non_throwing(block_ptr_type->pointed_type, ast_ctx);
    }
    auto function_type = canonical.as_shared<FunctionType>();
    if (!function_type) {
        return false;
    }
    if (function_type->exception_spec == FunctionExceptionSpecKind::NonThrowing) {
        return true;
    }
    if (function_type->exception_spec != FunctionExceptionSpecKind::Dependent ||
        !function_type->exception_spec_expr) {
        return false;
    }
    ConstEvalResult eval = evaluate_with_consteval_compat(
        function_type->exception_spec_expr.get(),
        ConstEvalMode::cpp_core_constant_expression());
    if (eval.status != ConstEvalStatus::Constant || !eval.value.has_value()) {
        return false;
    }
    switch (eval.value->kind) {
        case ConstValueKind::Boolean:
            return eval.value->bool_value;
        case ConstValueKind::Integer:
            return eval.value->int_value.to_unsigned_u64() != 0;
        default:
            return false;
    }
}

bool cpp_subexpression_is_known_noexcept(const Expr* expr,
                                         const ASTContext* ast_ctx) {
    if (!expr) {
        return false;
    }

    auto* stripped =
        strip_implicit_casts_for_noexcept(const_cast<Expr*>(expr));
    if (!stripped) {
        return false;
    }

    if (isa<VarRef>(stripped) ||
        isa<MemberPointerLiteralExpr>(stripped) ||
        isa<CppThisExpr>(stripped)) {
        return true;
    }

    if (auto* member = dyn_cast<MemberExpr>(stripped)) {
        return cpp_subexpression_is_known_noexcept(
            member->base.get(),
            ast_ctx);
    }

    return cpp_expression_is_known_noexcept(stripped, ast_ctx);
}

bool cpp_record_subobjects_are_nothrow_destructible(
    const RecordSemanticState* state,
    const ASTContext* ast_ctx) {
    if (!state || state->is_incomplete) {
        return false;
    }
    for (const auto& base : state->bases) {
        if (!cpp_type_is_nothrow_destructible(base.type, ast_ctx)) {
            return false;
        }
    }
    for (const auto& virtual_base : state->virtual_bases) {
        if (!cpp_type_is_nothrow_destructible(virtual_base.type, ast_ctx)) {
            return false;
        }
    }
    for (const auto& field : state->fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage) {
            continue;
        }
        if (!cpp_type_is_nothrow_destructible(field.type, ast_ctx)) {
            return false;
        }
    }
    return true;
}

bool cpp_constructor_is_user_provided_default_candidate(
    const RecordSemanticState::Constructor& ctor) {
    if (!cpp_constructor_is_viable_default_candidate(
            ctor,
            /*allow_protected_access=*/false)) {
        return false;
    }
    if (ctor.is_implicit || !ctor.decl) {
        return false;
    }
    return !(ctor.decl->is_defaulted &&
             ctor.decl->is_defaulted_on_first_declaration);
}

bool cpp_record_is_const_default_constructible(
    const ObjectDecl* record_decl,
    const RecordSemanticState* state,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records);

bool cpp_type_is_const_default_constructible_impl(
    QualType type,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    if (!type) {
        return false;
    }

    QualType canonical = desugar_type(type, ast_ctx);
    if (!canonical) {
        return false;
    }

    switch (canonical->kind) {
        case TypeKind::Array: {
            auto array_type = canonical.as_shared<ArrayType>();
            if (!array_type ||
                array_type->size_kind != ArraySizeKind::Constant ||
                !array_type->size.has_value()) {
                return false;
            }
            return cpp_type_is_const_default_constructible_impl(
                array_type->element_type,
                ast_ctx,
                active_records);
        }
        case TypeKind::Object: {
            const ObjectDecl* record_decl =
                lookup_record_decl_for_type(canonical, ast_ctx);
            const RecordSemanticState* state =
                record_decl
                    ? record_semantics_cache_lookup(record_decl, ast_ctx)
                    : nullptr;
            return cpp_record_is_const_default_constructible(
                record_decl,
                state,
                ast_ctx,
                active_records);
        }
        default:
            return false;
    }
}

bool cpp_record_is_const_default_constructible(
    const ObjectDecl* record_decl,
    const RecordSemanticState* state,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    if (!record_decl || !state || state->is_incomplete) {
        return false;
    }
    if (!cpp_record_has_viable_default_constructor(
            state,
            /*allow_protected_access=*/false)) {
        return false;
    }
    for (const auto& ctor : state->constructors) {
        if (cpp_constructor_is_user_provided_default_candidate(ctor)) {
            return true;
        }
    }

    if (!active_records.insert(record_decl).second) {
        return true;
    }

    for (const auto& base : state->bases) {
        if (!cpp_type_is_const_default_constructible_impl(
                base.type,
                ast_ctx,
                active_records)) {
            active_records.erase(record_decl);
            return false;
        }
    }
    for (const auto& virtual_base : state->virtual_bases) {
        if (!cpp_type_is_const_default_constructible_impl(
                virtual_base.type,
                ast_ctx,
                active_records)) {
            active_records.erase(record_decl);
            return false;
        }
    }
    for (const auto& field : state->fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage) {
            continue;
        }
        if (!cpp_type_is_const_default_constructible_impl(
                field.type,
                ast_ctx,
                active_records)) {
            active_records.erase(record_decl);
            return false;
        }
    }

    active_records.erase(record_decl);
    return true;
}
} // namespace

bool cpp_access_allows_member(RecordMemberAccess access,
                              bool allow_protected_access) {
    if (allow_protected_access) {
        return access != RecordMemberAccess::Private;
    }
    return access == RecordMemberAccess::Public;
}

CppConstructorUserParamInfo cpp_compute_constructor_user_param_info(
    const RecordSemanticState::Constructor& ctor) {
    CppConstructorUserParamInfo info;

    auto fn_type = desugar_type(ctor.type).as_shared<FunctionType>();
    if (!fn_type) {
        return info;
    }

    info.user_param_start = fn_type->parameters.empty() ? 0 : 1;
    info.max_user_param_count =
        fn_type->parameters.size() > info.user_param_start
            ? fn_type->parameters.size() - info.user_param_start
            : 0;
    if (info.max_user_param_count == 1 &&
        info.user_param_start < fn_type->parameters.size() &&
        fn_type->parameters[info.user_param_start] &&
        fn_type->parameters[info.user_param_start]->isVoid()) {
        info.max_user_param_count = 0;
    }

    info.required_user_param_count = info.max_user_param_count;
    if (ctor.symbol) {
        const auto* defaults = get_symbol_cpp_default_arguments(ctor.symbol.get());
        if (defaults) {
            size_t trailing_defaults = 0;
            for (size_t param_idx =
                     info.user_param_start + info.max_user_param_count;
                 param_idx > info.user_param_start;
                 --param_idx) {
                size_t index = param_idx - 1;
                if (index >= defaults->size() || !(*defaults)[index]) {
                    break;
                }
                ++trailing_defaults;
            }
            if (trailing_defaults > info.required_user_param_count) {
                trailing_defaults = info.required_user_param_count;
            }
            info.required_user_param_count -= trailing_defaults;
        }
    }
    return info;
}

namespace {
bool cpp_constructor_matches_special_member_parameter(
    const RecordSemanticState::Constructor& ctor,
    QualType owner_type,
    const ASTContext* ast_ctx,
    ReferenceKind expected_ref_kind,
    ReferenceKind* param_ref_kind_out) {
    if (!owner_type) {
        return false;
    }

    auto function_type =
        desugar_type(ctor.type, ast_ctx).as_shared<FunctionType>();
    if (!function_type) {
        return false;
    }

    CppConstructorUserParamInfo info =
        cpp_compute_constructor_user_param_info(ctor);
    if (info.max_user_param_count != 1 ||
        info.user_param_start >= function_type->parameters.size()) {
        return false;
    }

    auto param_ref =
        desugar_type(function_type->parameters[info.user_param_start], ast_ctx)
            .as_shared<ReferenceType>();
    if (!param_ref || !param_ref->referred_type) {
        return false;
    }

    QualType canonical_owner =
        remove_reference(owner_type, ast_ctx).without_qualifiers();
    QualType canonical_param =
        remove_reference(param_ref->referred_type, ast_ctx).without_qualifiers();
    if (!canonical_param.equals_unqualified(canonical_owner) ||
        param_ref->reference_kind != expected_ref_kind) {
        return false;
    }

    if (param_ref_kind_out) {
        *param_ref_kind_out = param_ref->reference_kind;
    }
    return true;
}

bool cpp_method_matches_assignment_parameter(
    const RecordSemanticState::Method& method,
    QualType owner_type,
    const ASTContext* ast_ctx,
    ReferenceKind expected_ref_kind,
    ReferenceKind* rhs_ref_kind_out) {
    if (!owner_type || method.is_static || method.name != "operator=") {
        return false;
    }

    auto function_type =
        desugar_type(method.type, ast_ctx).as_shared<FunctionType>();
    if (!function_type || function_type->parameters.size() != 2) {
        return false;
    }

    auto rhs_ref =
        desugar_type(function_type->parameters[1], ast_ctx)
            .as_shared<ReferenceType>();
    if (!rhs_ref || !rhs_ref->referred_type) {
        return false;
    }

    QualType canonical_owner =
        remove_reference(owner_type, ast_ctx).without_qualifiers();
    QualType canonical_rhs =
        remove_reference(rhs_ref->referred_type, ast_ctx).without_qualifiers();
    if (!canonical_rhs.equals_unqualified(canonical_owner) ||
        rhs_ref->reference_kind != expected_ref_kind) {
        return false;
    }

    if (rhs_ref_kind_out) {
        *rhs_ref_kind_out = rhs_ref->reference_kind;
    }
    return true;
}
} // namespace

bool cpp_constructor_is_copy_constructor(
    const RecordSemanticState::Constructor& ctor,
    QualType owner_type,
    const ASTContext* ast_ctx,
    ReferenceKind* param_ref_kind_out) {
    return cpp_constructor_matches_special_member_parameter(
        ctor,
        owner_type,
        ast_ctx,
        ReferenceKind::LValue,
        param_ref_kind_out);
}

bool cpp_constructor_is_move_constructor(
    const RecordSemanticState::Constructor& ctor,
    QualType owner_type,
    const ASTContext* ast_ctx,
    ReferenceKind* param_ref_kind_out) {
    return cpp_constructor_matches_special_member_parameter(
        ctor,
        owner_type,
        ast_ctx,
        ReferenceKind::RValue,
        param_ref_kind_out);
}

bool cpp_method_is_copy_assignment(
    const RecordSemanticState::Method& method,
    QualType owner_type,
    const ASTContext* ast_ctx,
    ReferenceKind* rhs_ref_kind_out) {
    return cpp_method_matches_assignment_parameter(
        method,
        owner_type,
        ast_ctx,
        ReferenceKind::LValue,
        rhs_ref_kind_out);
}

bool cpp_method_is_move_assignment(
    const RecordSemanticState::Method& method,
    QualType owner_type,
    const ASTContext* ast_ctx,
    ReferenceKind* rhs_ref_kind_out) {
    return cpp_method_matches_assignment_parameter(
        method,
        owner_type,
        ast_ctx,
        ReferenceKind::RValue,
        rhs_ref_kind_out);
}

bool cpp_constructor_is_viable_default_candidate(
    const RecordSemanticState::Constructor& ctor,
    bool allow_protected_access) {
    if (ctor.is_deleted) {
        return false;
    }
    if (!cpp_access_allows_member(ctor.declared_access, allow_protected_access)) {
        return false;
    }
    CppConstructorUserParamInfo info = cpp_compute_constructor_user_param_info(ctor);
    return info.required_user_param_count == 0;
}

bool cpp_destructor_is_viable_candidate(
    const RecordSemanticState::Destructor& dtor,
    bool allow_protected_access) {
    if (dtor.is_deleted) {
        return false;
    }
    return cpp_access_allows_member(dtor.declared_access, allow_protected_access);
}

bool cpp_record_has_viable_default_constructor(
    const RecordSemanticState* state,
    bool allow_protected_access) {
    if (!state || state->is_incomplete) {
        return false;
    }
    if (state->constructors.empty()) {
        // Records without constructor metadata are treated as
        // default-constructible in the current supported C++ subset.
        return true;
    }
    for (const auto& ctor : state->constructors) {
        if (cpp_constructor_is_viable_default_candidate(
                ctor, allow_protected_access)) {
            return true;
        }
    }
    return false;
}

bool cpp_record_has_viable_destructor(
    const RecordSemanticState* state,
    bool allow_protected_access) {
    if (!state || state->is_incomplete) {
        return false;
    }
    if (state->destructors.empty()) {
        // Records without destructor metadata are treated as having an
        // implicitly viable destructor in the current supported subset.
        return true;
    }
    for (const auto& dtor : state->destructors) {
        if (cpp_destructor_is_viable_candidate(
                dtor, allow_protected_access)) {
            return true;
        }
    }
    return false;
}

bool cpp_type_is_destructible(
    QualType type,
    bool allow_protected_access,
    const ASTContext* ast_ctx) {
    if (!type) {
        return false;
    }

    QualType canonical = desugar_type(type, ast_ctx);
    if (!canonical) {
        return false;
    }

    if (canonical.as_shared<ReferenceType>()) {
        return true;
    }

    if (canonical->isVoid()) {
        return false;
    }

    switch (canonical->kind) {
        case TypeKind::Function:
            return false;
        case TypeKind::Array: {
            auto array_type = canonical.as_shared<ArrayType>();
            if (!array_type) {
                return false;
            }
            if (array_type->size_kind != ArraySizeKind::Constant ||
                !array_type->size.has_value()) {
                return false;
            }
            return cpp_type_is_destructible(
                array_type->element_type,
                allow_protected_access,
                ast_ctx);
        }
        case TypeKind::Object: {
            const RecordSemanticState* state =
                lookup_record_state_for_type(canonical, ast_ctx);
            return cpp_record_has_viable_destructor(
                state, allow_protected_access);
        }
        case TypeKind::Builtin:
        case TypeKind::Pointer:
        case TypeKind::MemberPointer:
        case TypeKind::Enum:
        case TypeKind::BlockPointer:
        case TypeKind::Vector:
        case TypeKind::Complex:
            return true;
        default:
            return canonical->isScalar();
    }
}

bool cpp_type_is_trivially_destructible(
    QualType type,
    const ASTContext* ast_ctx) {
    if (!cpp_type_is_destructible(type, false, ast_ctx)) {
        return false;
    }

    QualType canonical = desugar_type(type, ast_ctx);
    if (!canonical) {
        return false;
    }

    if (canonical.as_shared<ReferenceType>()) {
        return true;
    }

    switch (canonical->kind) {
        case TypeKind::Array: {
            auto array_type = canonical.as_shared<ArrayType>();
            if (!array_type ||
                array_type->size_kind != ArraySizeKind::Constant ||
                !array_type->size.has_value()) {
                return false;
            }
            return cpp_type_is_trivially_destructible(
                array_type->element_type,
                ast_ctx);
        }
        case TypeKind::Object: {
            const RecordSemanticState* state =
                lookup_record_state_for_type(canonical, ast_ctx);
            return cpp_record_is_trivially_destructible(state, ast_ctx);
        }
        case TypeKind::Builtin:
        case TypeKind::Pointer:
        case TypeKind::MemberPointer:
        case TypeKind::Enum:
        case TypeKind::BlockPointer:
        case TypeKind::Vector:
        case TypeKind::Complex:
            return true;
        default:
            return canonical->isScalar();
    }
}

bool cpp_type_is_nothrow_destructible(
    QualType type,
    const ASTContext* ast_ctx) {
    if (!cpp_type_is_destructible(type, false, ast_ctx)) {
        return false;
    }

    QualType canonical = desugar_type(type, ast_ctx);
    if (!canonical) {
        return false;
    }

    if (canonical.as_shared<ReferenceType>()) {
        return true;
    }

    switch (canonical->kind) {
        case TypeKind::Array: {
            auto array_type = canonical.as_shared<ArrayType>();
            if (!array_type ||
                array_type->size_kind != ArraySizeKind::Constant ||
                !array_type->size.has_value()) {
                return false;
            }
            return cpp_type_is_nothrow_destructible(
                array_type->element_type,
                ast_ctx);
        }
        case TypeKind::Object: {
            const RecordSemanticState* state =
                lookup_record_state_for_type(canonical, ast_ctx);
            if (!state || state->is_incomplete) {
                return false;
            }
            if (state->destructors.empty()) {
                return cpp_record_subobjects_are_nothrow_destructible(
                    state,
                    ast_ctx);
            }
            for (const auto& dtor : state->destructors) {
                if (!cpp_destructor_is_viable_candidate(dtor, false)) {
                    continue;
                }
                if (dtor.is_implicit || dtor.is_defaulted) {
                    return cpp_record_subobjects_are_nothrow_destructible(
                        state,
                        ast_ctx);
                }
                if (function_type_is_non_throwing(dtor.type, ast_ctx) ||
                    function_type_is_non_throwing(
                        dtor.symbol ? dtor.symbol->type : QualType(nullptr),
                        ast_ctx)) {
                    return true;
                }
                return false;
            }
            return false;
        }
        case TypeKind::Builtin:
        case TypeKind::Pointer:
        case TypeKind::MemberPointer:
        case TypeKind::Enum:
        case TypeKind::BlockPointer:
        case TypeKind::Vector:
        case TypeKind::Complex:
            return true;
        default:
            return canonical->isScalar();
    }
}

bool cpp_type_is_const_default_constructible(
    QualType type,
    const ASTContext* ast_ctx) {
    std::unordered_set<const ObjectDecl*> active_records;
    return cpp_type_is_const_default_constructible_impl(
        type,
        ast_ctx,
        active_records);
}

bool cpp_expression_is_known_noexcept(
    const Expr* expr,
    const ASTContext* ast_ctx) {
    if (!expr) {
        return false;
    }
    auto* stripped =
        strip_implicit_casts_for_noexcept(const_cast<Expr*>(expr));
    if (!stripped) {
        return false;
    }

    if (auto* call = dyn_cast<FuncCall>(stripped)) {
        return call->func &&
               function_type_is_non_throwing(call->func->get_type(), ast_ctx);
    }
    if (auto* member_call = dyn_cast<CppMemberCallExpr>(stripped)) {
        return member_call->lowered_call &&
               member_call->lowered_call->func &&
               function_type_is_non_throwing(
                   member_call->lowered_call->func->get_type(),
                   ast_ctx);
    }
    if (auto* member = dyn_cast<MemberExpr>(stripped)) {
        return cpp_subexpression_is_known_noexcept(
            member->base.get(),
            ast_ctx);
    }
    if (auto* member_pointer_access =
            dyn_cast<MemberPointerAccessExpr>(stripped)) {
        return cpp_subexpression_is_known_noexcept(
                   member_pointer_access->base.get(),
                   ast_ctx) &&
               cpp_subexpression_is_known_noexcept(
                   member_pointer_access->member_pointer.get(),
                   ast_ctx);
    }
    if (auto* construct = dyn_cast<CppConstructExpr>(stripped)) {
        if (construct->ctor_sym &&
            function_type_is_non_throwing(construct->ctor_sym->type, ast_ctx)) {
            return true;
        }
        return cpp_type_is_nothrow_destructible(construct->ctype, ast_ctx);
    }
    if (dyn_cast<CppValueInitExpr>(stripped)) {
        return true;
    }
    if (auto* function_style_cast =
            dyn_cast<CppFunctionStyleCastExpr>(stripped)) {
        for (const auto& arg : function_style_cast->args) {
            if (!cpp_subexpression_is_known_noexcept(arg.get(), ast_ctx)) {
                return false;
            }
        }
        return true;
    }
    if (auto* pseudo_dtor = dyn_cast<CppPseudoDestructorExpr>(stripped)) {
        if (pseudo_dtor->destructor_sym &&
            function_type_is_non_throwing(
                pseudo_dtor->destructor_sym->type,
                ast_ctx)) {
            return true;
        }
        return cpp_type_is_nothrow_destructible(
            pseudo_dtor->destroyed_type,
            ast_ctx);
    }
    return false;
}

void cpp_recompute_default_constructor_traits(
    RecordSemanticState::DefinitionData& definition_data,
    const std::vector<RecordSemanticState::Constructor>& constructors) {
    definition_data.has_default_constructor = false;
    definition_data.default_constructor_is_deleted = false;
    for (const auto& ctor : constructors) {
        CppConstructorUserParamInfo info =
            cpp_compute_constructor_user_param_info(ctor);
        if (info.required_user_param_count != 0) {
            continue;
        }
        definition_data.has_default_constructor = true;
        if (ctor.is_deleted) {
            definition_data.default_constructor_is_deleted = true;
        }
    }
}

void cpp_recompute_special_member_definition_data(
    RecordSemanticState::DefinitionData& definition_data,
    QualType owner_type,
    const std::vector<RecordSemanticState::Constructor>& constructors,
    const std::vector<RecordSemanticState::Method>& methods,
    const std::vector<RecordSemanticState::Destructor>& destructors,
    const ASTContext* ast_ctx) {
    definition_data.has_user_declared_constructor = false;
    definition_data.has_default_constructor = false;
    definition_data.default_constructor_is_deleted = false;
    definition_data.has_copy_constructor = false;
    definition_data.has_move_constructor = false;
    definition_data.has_user_declared_copy_constructor = false;
    definition_data.has_user_declared_move_constructor = false;
    definition_data.has_copy_assignment = false;
    definition_data.has_move_assignment = false;
    definition_data.has_user_declared_copy_assignment = false;
    definition_data.has_user_declared_move_assignment = false;
    definition_data.has_user_declared_destructor = false;
    definition_data.has_deleted_destructor = false;

    cpp_recompute_default_constructor_traits(definition_data, constructors);

    for (const auto& ctor : constructors) {
        if (!ctor.is_implicit) {
            definition_data.has_user_declared_constructor = true;
        }
        if (cpp_constructor_is_copy_constructor(ctor, owner_type, ast_ctx)) {
            definition_data.has_copy_constructor = true;
            if (!ctor.is_implicit) {
                definition_data.has_user_declared_copy_constructor = true;
            }
        } else if (cpp_constructor_is_move_constructor(
                       ctor, owner_type, ast_ctx)) {
            definition_data.has_move_constructor = true;
            if (!ctor.is_implicit) {
                definition_data.has_user_declared_move_constructor = true;
            }
        }
    }

    for (const auto& method : methods) {
        if (cpp_method_is_copy_assignment(method, owner_type, ast_ctx)) {
            definition_data.has_copy_assignment = true;
            if (!method.is_implicit) {
                definition_data.has_user_declared_copy_assignment = true;
            }
        } else if (cpp_method_is_move_assignment(method, owner_type, ast_ctx)) {
            definition_data.has_move_assignment = true;
            if (!method.is_implicit) {
                definition_data.has_user_declared_move_assignment = true;
            }
        }
    }

    for (const auto& dtor : destructors) {
        if (!dtor.is_implicit) {
            definition_data.has_user_declared_destructor = true;
        }
        if (dtor.is_deleted) {
            definition_data.has_deleted_destructor = true;
        }
    }
}

namespace {
bool cpp_record_is_trivially_destructible(
    const RecordSemanticState* state,
    const ASTContext* ast_ctx) {
    if (!state || state->is_incomplete) {
        return false;
    }
    if (!cpp_record_has_viable_destructor(state, false)) {
        return false;
    }
    if (state->has_virtual_destructor) {
        return false;
    }

    if (!state->destructors.empty()) {
        for (const auto& dtor : state->destructors) {
            if (!cpp_destructor_is_viable_candidate(dtor, false)) {
                continue;
            }
            if (dtor.is_virtual) {
                return false;
            }
            if (!dtor.is_implicit && !dtor.is_defaulted) {
                return false;
            }
            break;
        }
    }

    for (const auto& base : state->bases) {
        if (!cpp_type_is_trivially_destructible(base.type, ast_ctx)) {
            return false;
        }
    }
    for (const auto& virtual_base : state->virtual_bases) {
        if (!cpp_type_is_trivially_destructible(virtual_base.type, ast_ctx)) {
            return false;
        }
    }
    for (const auto& field : state->fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage) {
            continue;
        }
        if (!cpp_type_is_trivially_destructible(field.type, ast_ctx)) {
            return false;
        }
    }
    return true;
}
} // namespace
