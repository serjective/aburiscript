#ifndef ABURI_SPECIAL_MEMBERS_H
#define ABURI_SPECIAL_MEMBERS_H

#include "types.h"
#include <cstddef>
#include <vector>

class ASTContext;
struct Expr;

struct CppConstructorUserParamInfo {
    size_t user_param_start = 0;
    size_t max_user_param_count = 0;
    size_t required_user_param_count = 0;
};

bool cpp_access_allows_member(RecordMemberAccess access,
                              bool allow_protected_access);

CppConstructorUserParamInfo cpp_compute_constructor_user_param_info(
    const RecordSemanticState::Constructor& ctor);

bool cpp_constructor_is_copy_constructor(
    const RecordSemanticState::Constructor& ctor,
    QualType owner_type,
    const ASTContext* ast_ctx = nullptr,
    ReferenceKind* param_ref_kind_out = nullptr);

bool cpp_constructor_is_move_constructor(
    const RecordSemanticState::Constructor& ctor,
    QualType owner_type,
    const ASTContext* ast_ctx = nullptr,
    ReferenceKind* param_ref_kind_out = nullptr);

bool cpp_method_is_copy_assignment(
    const RecordSemanticState::Method& method,
    QualType owner_type,
    const ASTContext* ast_ctx = nullptr,
    ReferenceKind* rhs_ref_kind_out = nullptr);

bool cpp_method_is_move_assignment(
    const RecordSemanticState::Method& method,
    QualType owner_type,
    const ASTContext* ast_ctx = nullptr,
    ReferenceKind* rhs_ref_kind_out = nullptr);

bool cpp_constructor_is_viable_default_candidate(
    const RecordSemanticState::Constructor& ctor,
    bool allow_protected_access);

bool cpp_destructor_is_viable_candidate(
    const RecordSemanticState::Destructor& dtor,
    bool allow_protected_access);

bool cpp_record_has_viable_default_constructor(
    const RecordSemanticState* state,
    bool allow_protected_access);

bool cpp_record_has_viable_destructor(
    const RecordSemanticState* state,
    bool allow_protected_access);

bool cpp_type_is_destructible(
    QualType type,
    bool allow_protected_access = false,
    const ASTContext* ast_ctx = nullptr);

bool cpp_type_is_trivially_destructible(
    QualType type,
    const ASTContext* ast_ctx = nullptr);

bool cpp_type_is_nothrow_destructible(
    QualType type,
    const ASTContext* ast_ctx = nullptr);

bool cpp_type_is_const_default_constructible(
    QualType type,
    const ASTContext* ast_ctx = nullptr);

bool cpp_expression_is_known_noexcept(
    const Expr* expr,
    const ASTContext* ast_ctx = nullptr);

void cpp_recompute_default_constructor_traits(
    RecordSemanticState::DefinitionData& definition_data,
    const std::vector<RecordSemanticState::Constructor>& constructors);

void cpp_recompute_special_member_definition_data(
    RecordSemanticState::DefinitionData& definition_data,
    QualType owner_type,
    const std::vector<RecordSemanticState::Constructor>& constructors,
    const std::vector<RecordSemanticState::Method>& methods,
    const std::vector<RecordSemanticState::Destructor>& destructors,
    const ASTContext* ast_ctx = nullptr);

#endif // ABURI_SPECIAL_MEMBERS_H
