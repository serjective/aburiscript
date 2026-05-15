#ifndef ABURI_COLLECT_INTERNAL_H
#define ABURI_COLLECT_INTERNAL_H

#include "collect.h"
#include "../ast/special_members.h"
#include <functional>
#include <limits>
#include <optional>
#include <unordered_map>

namespace collect_internal {
namespace {
QualType clone_top_level_incomplete_array(QualType type) {
    if (!type) {
        return type;
    }

    std::function<std::shared_ptr<CType>(const std::shared_ptr<CType>&, bool&)>
        clone_if_incomplete_array =
            [&](const std::shared_ptr<CType>& raw_type, bool& cloned_out)
        -> std::shared_ptr<CType> {
        if (!raw_type) {
            return raw_type;
        }
        if (auto td = dyn_cast_shared<TypedefType>(raw_type)) {
            bool child_cloned = false;
            auto cloned_underlying_raw = clone_if_incomplete_array(
                td->underlying_type.get_shared(), child_cloned);
            if (!child_cloned) {
                return raw_type;
            }
            auto rebuilt = std::make_shared<TypedefType>(
                td->name,
                QualType(cloned_underlying_raw, td->underlying_type.get_qualifiers()),
                td->typedef_decl);
            cloned_out = true;
            return rebuilt;
        }
        auto arr = dyn_cast_shared<ArrayType>(raw_type);
        if (!arr) {
            return raw_type;
        }
        bool is_incomplete_array =
            arr->size_kind == ArraySizeKind::Incomplete ||
            (arr->size_kind == ArraySizeKind::Constant && !arr->size.has_value());
        if (!is_incomplete_array) {
            return raw_type;
        }
        auto cloned = std::make_shared<ArrayType>(arr->element_type, arr->size);
        cloned->size_kind = arr->size_kind;
        cloned->size_expr = arr->size_expr;
        cloned_out = true;
        return cloned;
    };

    bool cloned = false;
    auto cloned_raw = clone_if_incomplete_array(type.get_shared(), cloned);
    if (!cloned) {
        return type;
    }
    return QualType(cloned_raw, type.get_qualifiers());
}

std::string describe_consteval_failure(const ConstEvalResult& result) {
    if (!result.message.empty()) {
        return result.message;
    }
    if (!result.diagnostics.empty() && !result.diagnostics.front().message.empty()) {
        return result.diagnostics.front().message;
    }
    switch (result.status) {
        case ConstEvalStatus::NotEvaluated:
            return "expression could not be evaluated at compile time";
        case ConstEvalStatus::NotConstant:
            return "expression is not constant";
        case ConstEvalStatus::Error:
            return "constant-evaluation failed";
        case ConstEvalStatus::Constant:
            return "expression is not an integer constant expression";
    }
    return "expression is not constant";
}

bool has_qualification_preserving_match(QualType from, QualType to) {
    if (!from || !to) {
        return false;
    }
    if (!from.equals_unqualified(to)) {
        return false;
    }
    return to.has_all_qualifiers_of(from);
}

bool same_type_ignoring_all_qualifiers(QualType lhs,
                                       QualType rhs,
                                       const ASTContext* ast_ctx) {
    lhs = desugar_type(lhs, ast_ctx);
    rhs = desugar_type(rhs, ast_ctx);
    if (!lhs || !rhs) {
        return !lhs && !rhs;
    }
    if (lhs->kind != rhs->kind) {
        return false;
    }

    if (auto lhs_ptr = lhs.as_shared<PointerType>()) {
        auto rhs_ptr = rhs.as_shared<PointerType>();
        return rhs_ptr &&
            same_type_ignoring_all_qualifiers(
                lhs_ptr->pointed_type,
                rhs_ptr->pointed_type,
                ast_ctx);
    }

    if (auto lhs_ref = lhs.as_shared<ReferenceType>()) {
        auto rhs_ref = rhs.as_shared<ReferenceType>();
        return rhs_ref &&
            lhs_ref->reference_kind == rhs_ref->reference_kind &&
            same_type_ignoring_all_qualifiers(
                lhs_ref->referred_type,
                rhs_ref->referred_type,
                ast_ctx);
    }

    if (auto lhs_arr = lhs.as_shared<ArrayType>()) {
        auto rhs_arr = rhs.as_shared<ArrayType>();
        if (!rhs_arr) {
            return false;
        }
        if (lhs_arr->size_kind != rhs_arr->size_kind) {
            return false;
        }
        if (lhs_arr->size_kind == ArraySizeKind::Constant) {
            if (lhs_arr->size.has_value() != rhs_arr->size.has_value()) {
                return false;
            }
            if (lhs_arr->size.has_value() &&
                lhs_arr->size.value() != rhs_arr->size.value()) {
                return false;
            }
        }
        return same_type_ignoring_all_qualifiers(
            lhs_arr->element_type,
            rhs_arr->element_type,
            ast_ctx);
    }

    return lhs.without_qualifiers().equals_unqualified(rhs.without_qualifiers());
}

bool same_type_ignoring_all_qualifiers(QualType lhs, QualType rhs) {
    return same_type_ignoring_all_qualifiers(
        lhs,
        rhs,
        get_active_side_table_ast_context());
}

int count_qualifier_bits(uint8_t qualifiers) {
    int count = 0;
    while (qualifiers != 0) {
        count += qualifiers & 1U;
        qualifiers >>= 1U;
    }
    return count;
}

bool can_convert_by_qualification_conversion(QualType from,
                                             QualType to,
                                             const ASTContext* ast_ctx) {
    from = desugar_type(from, ast_ctx);
    to = desugar_type(to, ast_ctx);
    if (!from || !to) {
        return false;
    }
    if (!to.has_all_qualifiers_of(from)) {
        return false;
    }
    if (from->kind != to->kind) {
        return false;
    }

    if (auto from_ptr = from.as_shared<PointerType>()) {
        auto to_ptr = to.as_shared<PointerType>();
        return to_ptr &&
            can_convert_by_qualification_conversion(
                from_ptr->pointed_type,
                to_ptr->pointed_type,
                ast_ctx);
    }

    if (auto from_block = from.as_shared<BlockPointerType>()) {
        auto to_block = to.as_shared<BlockPointerType>();
        return to_block &&
            can_convert_by_qualification_conversion(
                from_block->pointed_type,
                to_block->pointed_type,
                ast_ctx);
    }

    if (auto from_ref = from.as_shared<ReferenceType>()) {
        auto to_ref = to.as_shared<ReferenceType>();
        return to_ref &&
            from_ref->reference_kind == to_ref->reference_kind &&
            can_convert_by_qualification_conversion(
                from_ref->referred_type,
                to_ref->referred_type,
                ast_ctx);
    }

    if (auto from_member = from.as_shared<MemberPointerType>()) {
        auto to_member = to.as_shared<MemberPointerType>();
        return to_member &&
            can_convert_by_qualification_conversion(
                from_member->class_type,
                to_member->class_type,
                ast_ctx) &&
            can_convert_by_qualification_conversion(
                from_member->member_type,
                to_member->member_type,
                ast_ctx);
    }

    if (auto from_array = from.as_shared<ArrayType>()) {
        auto to_array = to.as_shared<ArrayType>();
        if (!to_array || from_array->size_kind != to_array->size_kind) {
            return false;
        }
        if (from_array->size_kind == ArraySizeKind::Constant &&
            from_array->size != to_array->size) {
            return false;
        }
        return can_convert_by_qualification_conversion(
            from_array->element_type,
            to_array->element_type,
            ast_ctx);
    }

    return from.without_qualifiers().equals_unqualified(
        to.without_qualifiers());
}

bool can_convert_by_qualification_conversion(QualType from, QualType to) {
    return can_convert_by_qualification_conversion(
        from,
        to,
        get_active_side_table_ast_context());
}

int qualification_conversion_added_qualifier_count(QualType from,
                                                   QualType to,
                                                   const ASTContext* ast_ctx) {
    from = desugar_type(from, ast_ctx);
    to = desugar_type(to, ast_ctx);
    if (!from || !to || from->kind != to->kind) {
        return 0;
    }

    int count = count_qualifier_bits(
        static_cast<uint8_t>(to.get_qualifiers() & ~from.get_qualifiers()));

    if (auto from_ptr = from.as_shared<PointerType>()) {
        auto to_ptr = to.as_shared<PointerType>();
        return to_ptr
            ? count + qualification_conversion_added_qualifier_count(
                  from_ptr->pointed_type,
                  to_ptr->pointed_type,
                  ast_ctx)
            : count;
    }

    if (auto from_block = from.as_shared<BlockPointerType>()) {
        auto to_block = to.as_shared<BlockPointerType>();
        return to_block
            ? count + qualification_conversion_added_qualifier_count(
                  from_block->pointed_type,
                  to_block->pointed_type,
                  ast_ctx)
            : count;
    }

    if (auto from_ref = from.as_shared<ReferenceType>()) {
        auto to_ref = to.as_shared<ReferenceType>();
        return to_ref
            ? count + qualification_conversion_added_qualifier_count(
                  from_ref->referred_type,
                  to_ref->referred_type,
                  ast_ctx)
            : count;
    }

    if (auto from_member = from.as_shared<MemberPointerType>()) {
        auto to_member = to.as_shared<MemberPointerType>();
        return to_member
            ? count +
                  qualification_conversion_added_qualifier_count(
                      from_member->class_type,
                      to_member->class_type,
                      ast_ctx) +
                  qualification_conversion_added_qualifier_count(
                      from_member->member_type,
                      to_member->member_type,
                      ast_ctx)
            : count;
    }

    if (auto from_array = from.as_shared<ArrayType>()) {
        auto to_array = to.as_shared<ArrayType>();
        return to_array
            ? count + qualification_conversion_added_qualifier_count(
                  from_array->element_type,
                  to_array->element_type,
                  ast_ctx)
            : count;
    }

    return count;
}

int qualification_conversion_exact_subrank(QualType from,
                                           QualType to,
                                           const ASTContext* ast_ctx,
                                           int base_subrank = 1) {
    int added_qualifiers =
        qualification_conversion_added_qualifier_count(from, to, ast_ctx);
    return base_subrank +
        (added_qualifiers > 0 ? added_qualifiers - 1 : 0);
}

int compare_qualification_conversion_sequences(
    const Collect::ImplicitConversionSequence& lhs,
    const Collect::ImplicitConversionSequence& rhs,
    const ASTContext* ast_ctx) {
    auto is_qualification_orderable_exact_match =
        [](const Collect::ImplicitConversionSequence& seq) {
            return seq.rank == Collect::ConversionSequenceRank::ExactMatch &&
                   (seq.kind == Collect::ConversionSequenceKind::Identity ||
                    seq.kind == Collect::ConversionSequenceKind::Qualification);
        };

    if (!is_qualification_orderable_exact_match(lhs) ||
        !is_qualification_orderable_exact_match(rhs) ||
        !same_type_ignoring_all_qualifiers(lhs.from, rhs.from, ast_ctx)) {
        return 0;
    }

    bool lhs_target_converts_to_rhs =
        can_convert_by_qualification_conversion(lhs.to, rhs.to, ast_ctx);
    bool rhs_target_converts_to_lhs =
        can_convert_by_qualification_conversion(rhs.to, lhs.to, ast_ctx);
    if (lhs_target_converts_to_rhs == rhs_target_converts_to_lhs) {
        return 0;
    }
    return lhs_target_converts_to_rhs ? -1 : 1;
}

int compare_derived_to_base_reference_binding_sequences(
    const Collect::ImplicitConversionSequence& lhs,
    const Collect::ImplicitConversionSequence& rhs,
    const ASTContext* ast_ctx) {
    auto is_reference_derived_to_base_binding =
        [](const Collect::ImplicitConversionSequence& seq) {
        return seq.rank == Collect::ConversionSequenceRank::Conversion &&
               seq.kind == Collect::ConversionSequenceKind::Pointer &&
               seq.detail_kind ==
                   Collect::ConversionSequenceDetailKind::ReferenceDirectBinding;
    };

    if (!is_reference_derived_to_base_binding(lhs) ||
        !is_reference_derived_to_base_binding(rhs) ||
        !same_type_ignoring_all_qualifiers(lhs.from, rhs.from, ast_ctx)) {
        return 0;
    }

    QualType lhs_target = remove_reference(lhs.to, ast_ctx);
    QualType rhs_target = remove_reference(rhs.to, ast_ctx);
    if (!same_type_ignoring_all_qualifiers(lhs_target, rhs_target, ast_ctx)) {
        return 0;
    }

    bool lhs_target_converts_to_rhs =
        can_convert_by_qualification_conversion(lhs_target, rhs_target, ast_ctx);
    bool rhs_target_converts_to_lhs =
        can_convert_by_qualification_conversion(rhs_target, lhs_target, ast_ctx);
    if (lhs_target_converts_to_rhs == rhs_target_converts_to_lhs) {
        return 0;
    }
    return lhs_target_converts_to_rhs ? -1 : 1;
}

const EnumType* enum_type_from_qualtype(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    type = desugar_type(type, ast_ctx);
    if (!type) {
        return nullptr;
    }
    return dyn_cast<EnumType>(type.get());
}

bool is_enum_type(QualType type, const ASTContext* ast_ctx) {
    return enum_type_from_qualtype(type, ast_ctx) != nullptr;
}

bool is_enum_type(QualType type) {
    return is_enum_type(type, get_active_side_table_ast_context());
}

bool is_scoped_enum_type(QualType type, const ASTContext* ast_ctx) {
    auto* enum_type = enum_type_from_qualtype(type, ast_ctx);
    return enum_type && enum_type->isScoped();
}

bool is_scoped_enum_type(QualType type) {
    return is_scoped_enum_type(type, get_active_side_table_ast_context());
}

bool is_unscoped_enum_type(QualType type, const ASTContext* ast_ctx) {
    auto* enum_type = enum_type_from_qualtype(type, ast_ctx);
    return enum_type && !enum_type->isScoped();
}

bool is_unscoped_enum_type(QualType type) {
    return is_unscoped_enum_type(type, get_active_side_table_ast_context());
}

bool same_unqualified_enum_type(QualType lhs,
                                QualType rhs,
                                const ASTContext* ast_ctx) {
    auto* lhs_enum = enum_type_from_qualtype(lhs, ast_ctx);
    auto* rhs_enum = enum_type_from_qualtype(rhs, ast_ctx);
    if (!lhs_enum || !rhs_enum) {
        return false;
    }
    auto* lhs_decl = lhs_enum->get_decl();
    auto* rhs_decl = rhs_enum->get_decl();
    if (lhs_decl && rhs_decl) {
        return lhs_decl == rhs_decl;
    }
    return lhs_enum == rhs_enum;
}

bool same_unqualified_enum_type(QualType lhs, QualType rhs) {
    return same_unqualified_enum_type(
        lhs,
        rhs,
        get_active_side_table_ast_context());
}

bool is_integer_or_enum_type(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    type = desugar_type(type, ast_ctx);
    if (!type) {
        return false;
    }
    return type->isInteger() || type->kind == TypeKind::Enum;
}

bool is_integer_or_enum_type(QualType type) {
    return is_integer_or_enum_type(type, get_active_side_table_ast_context());
}

// "Adjacent" helpers cover the current built-in C++ conversion buckets where
// unscoped enums travel with integer-like categories, while scoped enums stay
// out of those paths.
bool is_integer_adjacent(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    type = desugar_type(type, ast_ctx);
    if (!type) {
        return false;
    }
    if (auto* enum_type = dyn_cast<EnumType>(type.get())) {
        return !enum_type->isScoped();
    }
    return type->isInteger();
}

bool is_integer_adjacent(QualType type) {
    return is_integer_adjacent(
        type,
        get_active_side_table_ast_context());
}

// This arithmetic bucket is currently the built-in operator family that
// accepts arithmetic types plus unscoped enums, but excludes scoped enums.
bool is_arithmetic_adjacent(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    type = desugar_type(type, ast_ctx);
    if (!type) {
        return false;
    }
    if (auto* enum_type = dyn_cast<EnumType>(type.get())) {
        return !enum_type->isScoped();
    }
    return type->isArithmetic();
}

bool is_arithmetic_adjacent(QualType type) {
    return is_arithmetic_adjacent(
        type,
        get_active_side_table_ast_context());
}

bool allows_integral_promotion(QualType type, const ASTContext* ast_ctx) {
    return is_integer_adjacent(type, ast_ctx);
}

bool allows_integral_promotion(QualType type) {
    return allows_integral_promotion(type, get_active_side_table_ast_context());
}

bool allows_condition_conversion(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    type = desugar_type(type, ast_ctx);
    if (!type) {
        return false;
    }
    if (auto* enum_type = dyn_cast<EnumType>(type.get())) {
        return !enum_type->isScoped();
    }
    return type->isScalar();
}

bool allows_condition_conversion(QualType type) {
    return allows_condition_conversion(type, get_active_side_table_ast_context());
}

bool is_pointer_like_type(QualType type, const ASTContext* ast_ctx) {
    type = remove_reference(type, ast_ctx);
    auto kind = canonical_type_kind(type, ast_ctx);
    return kind == TypeKind::Pointer || kind == TypeKind::BlockPointer;
}

bool is_pointer_like_type(QualType type) {
    return is_pointer_like_type(type, get_active_side_table_ast_context());
}

int exact_match_subrank(const Collect::ImplicitConversionSequence& seq) {
    if (seq.exact_subrank >= 0) {
        return seq.exact_subrank;
    }
    switch (seq.kind) {
        case Collect::ConversionSequenceKind::Identity:
            return 0;
        case Collect::ConversionSequenceKind::Qualification:
            return 1;
        case Collect::ConversionSequenceKind::ArrayToPointer:
        case Collect::ConversionSequenceKind::FunctionToPointer:
        case Collect::ConversionSequenceKind::Pointer:
        case Collect::ConversionSequenceKind::LValueToRValue:
        case Collect::ConversionSequenceKind::Numeric:
        case Collect::ConversionSequenceKind::UserDefined:
        case Collect::ConversionSequenceKind::Failed:
        default:
            return 2;
    }
}

int conversion_rank_tiebreak(const Collect::ImplicitConversionSequence& seq) {
    if (seq.rank != Collect::ConversionSequenceRank::Conversion) {
        return 0;
    }
    if (seq.kind == Collect::ConversionSequenceKind::UserDefined) {
        return 1;
    }
    return 0;
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

const std::vector<const Expr*>* symbol_default_arguments(
    const std::shared_ptr<Symbol>& symbol) {
    if (!symbol) {
        return nullptr;
    }
    return get_symbol_cpp_default_arguments(symbol.get());
}

const Expr* function_decl_default_argument_at(const FuncDecl* decl,
                                              size_t param_index) {
    if (!decl || param_index >= decl->parameters.size()) {
        return nullptr;
    }
    auto* param_decl = dyn_cast<ParamDecl>(decl->parameters[param_index].get());
    return param_decl ? get_param_decl_default_argument(param_decl) : nullptr;
}

const FuncDecl* function_template_pattern_for_symbol(
    const std::shared_ptr<Symbol>& symbol) {
    const auto* specialization_info =
        symbol ? get_symbol_function_template_specialization(symbol.get()) : nullptr;
    const auto* primary_template =
        specialization_info ? specialization_info->primary_template : nullptr;
    return primary_template ? primary_template->function_decl() : nullptr;
}

size_t count_trailing_default_arguments_for_call(
    const std::shared_ptr<Symbol>& symbol,
    size_t named_param_count,
    size_t implicit_param_count) {
    const auto* defaults = symbol_default_arguments(symbol);
    if (named_param_count == 0 || named_param_count <= implicit_param_count) {
        return 0;
    }

    auto count_trailing_defaults = [&](auto&& has_default_at) {
        size_t trailing_defaults = 0;
        for (size_t param_index = named_param_count;
             param_index > implicit_param_count;
             --param_index) {
            size_t index = param_index - 1;
            if (!has_default_at(index)) {
                break;
            }
            ++trailing_defaults;
        }
        return trailing_defaults;
    };

    if (defaults) {
        return count_trailing_defaults([&](size_t index) {
            return index < defaults->size() && (*defaults)[index] != nullptr;
        });
    }

    const FuncDecl* default_argument_source =
        symbol && symbol->function_definition
            ? symbol->function_definition
            : function_template_pattern_for_symbol(symbol);
    if (!default_argument_source) {
        return 0;
    }
    return count_trailing_defaults([&](size_t index) {
        return function_decl_default_argument_at(
                   default_argument_source,
                   index) != nullptr;
    });
}

const Expr* lookup_default_argument_for_param(
    const std::shared_ptr<Symbol>& symbol,
    size_t param_index) {
    const auto* defaults = symbol_default_arguments(symbol);
    if (defaults && param_index < defaults->size()) {
        return (*defaults)[param_index];
    }
    if (symbol && symbol->function_definition) {
        if (const Expr* default_expr =
                function_decl_default_argument_at(
                    symbol->function_definition,
                    param_index)) {
            return default_expr;
        }
    }
    if (const FuncDecl* pattern = function_template_pattern_for_symbol(symbol)) {
        return function_decl_default_argument_at(pattern, param_index);
    }
    return nullptr;
}

struct MethodLookupResult {
    const RecordSemanticState::Method* method = nullptr;
    const ObjectDecl* owner_record_decl = nullptr;
    int matches = 0;
};

struct MethodCandidate {
    const RecordSemanticState::Method* method = nullptr;
    const ObjectDecl* owner_record_decl = nullptr;
};

struct MethodTemplateCandidate {
    const RecordSemanticState::MethodTemplate* method_template = nullptr;
    const ObjectDecl* owner_record_decl = nullptr;
};

struct MemberFunctionLookupResult {
    std::vector<MethodCandidate> methods;
    std::vector<MethodTemplateCandidate> method_templates;
};

struct VirtualMethodLookupResult {
    const RecordSemanticState::Method* method = nullptr;
    const ObjectDecl* owner_record_decl = nullptr;
};

struct MemberNameLookupResult {
    size_t field_matches = 0;
    size_t static_method_matches = 0;
    size_t static_method_template_matches = 0;
    size_t static_data_matches = 0;
    size_t enumerator_matches = 0;
    size_t nonstatic_method_matches = 0;
    size_t nonstatic_method_template_matches = 0;
    const RecordSemanticState::Method* single_static_method = nullptr;
    const RecordSemanticState::StaticDataMember* single_static_data_member = nullptr;
    const RecordSemanticState::EnumeratorMember* single_enumerator_member =
        nullptr;

    bool has_member_match() const {
        return field_matches > 0 ||
               static_method_matches > 0 ||
               static_method_template_matches > 0 ||
               static_data_matches > 0 ||
               enumerator_matches > 0 ||
               nonstatic_method_matches > 0 ||
               nonstatic_method_template_matches > 0;
    }
};

const ObjectDecl* object_decl_from_object_qualtype(QualType type,
                                                   const ASTContext* ast_ctx) {
    auto obj_type = desugar_type(type, ast_ctx).as_shared<ObjectType>();
    if (!obj_type) {
        return nullptr;
    }
    auto* decl = dyn_cast<ObjectDecl>(obj_type->get_decl());
    if (!decl) {
        return nullptr;
    }
    if (auto canonical_type = decl->get_record_type()) {
        if (auto* canonical_decl = dyn_cast<ObjectDecl>(canonical_type->get_decl())) {
            return canonical_decl;
        }
    }
    return decl;
}

const ObjectDecl* object_decl_from_object_qualtype(QualType type) {
    return object_decl_from_object_qualtype(
        type, get_active_side_table_ast_context());
}

const ObjectDecl* canonical_record_decl(const ObjectDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto record_type = decl->get_record_type()) {
        if (auto* canonical_decl = dyn_cast<ObjectDecl>(record_type->get_decl())) {
            return canonical_decl;
        }
    }
    return decl;
}

struct RecordMemberLookupCacheKey {
    const ObjectDecl* record_decl = nullptr;
    std::string member_name;

    bool operator==(const RecordMemberLookupCacheKey& other) const {
        return record_decl == other.record_decl &&
               member_name == other.member_name;
    }
};

struct RecordMemberLookupCacheKeyHash {
    size_t operator()(const RecordMemberLookupCacheKey& key) const {
        size_t ptr_hash = std::hash<const ObjectDecl*>{}(key.record_decl);
        size_t name_hash = std::hash<std::string>{}(key.member_name);
        return ptr_hash ^ (name_hash + 0x9e3779b9 + (ptr_hash << 6) + (ptr_hash >> 2));
    }
};

RecordMemberLookupCacheKey make_record_member_lookup_cache_key(
    const ObjectDecl* record_decl,
    const std::string& member_name) {
    return RecordMemberLookupCacheKey{
        canonical_record_decl(record_decl),
        member_name
    };
}

std::unordered_map<RecordMemberLookupCacheKey,
                   MemberFunctionLookupResult,
                   RecordMemberLookupCacheKeyHash>
    g_record_member_function_lookup_cache;
std::unordered_map<RecordMemberLookupCacheKey,
                   MemberNameLookupResult,
                   RecordMemberLookupCacheKeyHash>
    g_record_member_name_lookup_cache;
uint64_t g_record_member_lookup_cache_epoch = 0;
uint32_t g_record_member_lookup_cache_ast_context_id = 0;

void invalidate_record_member_lookup_caches_if_needed() {
    const ASTContext* active_ast_ctx = get_active_side_table_ast_context();
    uint32_t active_ast_ctx_id = active_ast_ctx ? active_ast_ctx->registry_id() : 0;
    uint64_t current_epoch = record_semantics_cache_epoch(active_ast_ctx);
    if (current_epoch == g_record_member_lookup_cache_epoch &&
        active_ast_ctx_id == g_record_member_lookup_cache_ast_context_id) {
        return;
    }
    g_record_member_lookup_cache_epoch = current_epoch;
    g_record_member_lookup_cache_ast_context_id = active_ast_ctx_id;
    g_record_member_function_lookup_cache.clear();
    g_record_member_name_lookup_cache.clear();
}

VirtualMethodLookupResult find_virtual_method_by_symbol_impl(
    const ObjectDecl* record_decl,
    const std::shared_ptr<Symbol>& method_symbol,
    std::unordered_set<const ObjectDecl*>& visited) {
    const ObjectDecl* canonical_decl = canonical_record_decl(record_decl);
    if (!canonical_decl || !method_symbol || visited.contains(canonical_decl)) {
        return {};
    }
    visited.insert(canonical_decl);
    const RecordSemanticState* state = record_semantics_cache_lookup(canonical_decl);
    if (!state) {
        return {};
    }
    for (const auto& method : state->methods) {
        if (method.symbol == method_symbol) {
            return VirtualMethodLookupResult{&method, canonical_decl};
        }
    }
    for (const auto& base : state->bases) {
        if (!base.record_decl) {
            continue;
        }
        auto found = find_virtual_method_by_symbol_impl(
            base.record_decl, method_symbol, visited);
        if (found.method) {
            return found;
        }
    }
    return {};
}

VirtualMethodLookupResult find_virtual_method_by_symbol(
    const ObjectDecl* record_decl,
    const std::shared_ptr<Symbol>& method_symbol) {
    std::unordered_set<const ObjectDecl*> visited;
    return find_virtual_method_by_symbol_impl(record_decl, method_symbol, visited);
}

std::optional<size_t> find_base_subobject_offset(const ObjectDecl* from_decl,
                                                 const ObjectDecl* to_decl) {
    return record_base_subobject_offset(from_decl, to_decl);
}

size_t count_base_subobjects(const ObjectDecl* derived_decl,
                             const ObjectDecl* target_base_decl,
                             bool require_public_path) {
    return count_record_base_subobjects(
        derived_decl,
        target_base_decl,
        require_public_path);
}

size_t count_public_base_subobjects(const ObjectDecl* derived_decl,
                                    const ObjectDecl* target_base_decl) {
    return count_base_subobjects(derived_decl, target_base_decl, true);
}

bool has_unambiguous_base_path(const ObjectDecl* derived_decl,
                               const ObjectDecl* target_base_decl,
                               bool require_public_path) {
    return has_unambiguous_record_base_path(
        derived_decl,
        target_base_decl,
        require_public_path);
}

bool has_public_unambiguous_base_path(const ObjectDecl* derived_decl,
                                      const ObjectDecl* target_base_decl) {
    return has_unambiguous_base_path(derived_decl, target_base_decl, true);
}

bool has_any_access_unambiguous_base_path(const ObjectDecl* derived_decl,
                                          const ObjectDecl* target_base_decl) {
    return has_unambiguous_base_path(derived_decl, target_base_decl, false);
}

bool can_convert_derived_to_base_object(QualType from_object_type,
                                        QualType to_object_type) {
    if (!from_object_type || !to_object_type) {
        return false;
    }
    if (!to_object_type.has_all_qualifiers_of(from_object_type)) {
        return false;
    }
    const auto* derived_decl = object_decl_from_object_qualtype(from_object_type);
    const auto* base_decl = object_decl_from_object_qualtype(to_object_type);
    return has_public_unambiguous_base_path(derived_decl, base_decl);
}

void find_record_member_functions_impl(const ObjectDecl* record_decl,
                                       const std::string& method_name,
                                       MemberFunctionLookupResult& out,
                                       std::unordered_set<const ObjectDecl*>& visited) {
    const ObjectDecl* canonical_decl = canonical_record_decl(record_decl);
    if (!canonical_decl || visited.contains(canonical_decl)) {
        return;
    }
    visited.insert(canonical_decl);
    const RecordSemanticState* state = record_semantics_cache_lookup(canonical_decl);
    if (!state) {
        return;
    }

    bool matched_here = false;
    for (const auto& method : state->methods) {
        if (method.name == method_name) {
            out.methods.push_back(MethodCandidate{&method, canonical_decl});
            matched_here = true;
        }
    }
    for (const auto& method_template : state->method_templates) {
        if (method_template.name == method_name) {
            out.method_templates.push_back(
                MethodTemplateCandidate{&method_template, canonical_decl});
            matched_here = true;
        }
    }
    if (matched_here) {
        return;
    }

    for (const auto& base : state->bases) {
        if (!base.record_decl) {
            continue;
        }
        find_record_member_functions_impl(
            base.record_decl, method_name, out, visited);
    }
}

std::vector<MethodCandidate> find_record_methods(
    const ObjectType* record_type,
    const std::string& method_name) {
    std::vector<MethodCandidate> matches;
    if (!record_type) {
        return matches;
    }
    const auto* record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(record_type->get_decl()));
    if (!record_decl) {
        return matches;
    }

    invalidate_record_member_lookup_caches_if_needed();
    auto cache_key = make_record_member_lookup_cache_key(record_decl, method_name);
    auto cache_it = g_record_member_function_lookup_cache.find(cache_key);
    if (cache_it != g_record_member_function_lookup_cache.end()) {
        return cache_it->second.methods;
    }

    MemberFunctionLookupResult lookup_result;
    std::unordered_set<const ObjectDecl*> visited;
    find_record_member_functions_impl(
        record_decl, method_name, lookup_result, visited);
    matches = lookup_result.methods;
    g_record_member_function_lookup_cache.emplace(
        std::move(cache_key),
        std::move(lookup_result));
    return matches;
}

void find_record_conversion_functions_impl(
    const ObjectDecl* record_decl,
    std::vector<MethodCandidate>& out,
    std::unordered_set<const ObjectDecl*>& visited) {
    const ObjectDecl* canonical_decl = canonical_record_decl(record_decl);
    if (!canonical_decl || visited.contains(canonical_decl)) {
        return;
    }
    visited.insert(canonical_decl);
    const RecordSemanticState* state = record_semantics_cache_lookup(canonical_decl);
    if (!state) {
        return;
    }

    for (const auto& method : state->methods) {
        if (!method.is_conversion_function) {
            continue;
        }
        out.push_back(MethodCandidate{&method, canonical_decl});
    }

    for (const auto& base : state->bases) {
        if (!base.record_decl) {
            continue;
        }
        find_record_conversion_functions_impl(
            base.record_decl,
            out,
            visited);
    }
}

std::vector<MethodCandidate> find_record_conversion_methods(
    const ObjectType* record_type) {
    std::vector<MethodCandidate> matches;
    if (!record_type) {
        return matches;
    }

    const auto* record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(record_type->get_decl()));
    if (!record_decl) {
        return matches;
    }

    std::unordered_set<const ObjectDecl*> visited;
    find_record_conversion_functions_impl(record_decl, matches, visited);
    return matches;
}

std::vector<MethodTemplateCandidate> find_record_method_templates(
    const ObjectType* record_type,
    const std::string& method_name) {
    std::vector<MethodTemplateCandidate> matches;
    if (!record_type) {
        return matches;
    }

    const auto* record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(record_type->get_decl()));
    if (!record_decl) {
        return matches;
    }

    invalidate_record_member_lookup_caches_if_needed();
    auto cache_key = make_record_member_lookup_cache_key(record_decl, method_name);
    auto cache_it = g_record_member_function_lookup_cache.find(cache_key);
    if (cache_it == g_record_member_function_lookup_cache.end()) {
        MemberFunctionLookupResult lookup_result;
        std::unordered_set<const ObjectDecl*> visited;
        find_record_member_functions_impl(
            record_decl, method_name, lookup_result, visited);
        cache_it = g_record_member_function_lookup_cache.emplace(
            std::move(cache_key),
            std::move(lookup_result)).first;
    }

    matches = cache_it->second.method_templates;
    return matches;
}

MethodLookupResult find_record_method(const ObjectType* record_type,
                                      const std::string& method_name) {
    MethodLookupResult result;
    auto matches = find_record_methods(record_type, method_name);
    result.matches = static_cast<int>(matches.size());
    if (!matches.empty()) {
        result.method = matches.front().method;
        result.owner_record_decl = matches.front().owner_record_decl;
    }
    return result;
}

MemberNameLookupResult lookup_record_member_name_impl(
    const ObjectDecl* current_decl,
    const std::string& member_name,
    std::unordered_set<const ObjectDecl*>& visited) {
    MemberNameLookupResult local_result;
    current_decl = canonical_record_decl(current_decl);
    if (!current_decl || visited.contains(current_decl)) {
        return local_result;
    }
    visited.insert(current_decl);
    const RecordSemanticState* state = record_semantics_cache_lookup(current_decl);
    if (!state) {
        return local_result;
    }

    for (const auto& field : state->fields) {
        if (field.name == member_name) {
            ++local_result.field_matches;
        }
    }
    for (const auto& method : state->methods) {
        if (method.name != member_name) {
            continue;
        }
        if (method.is_static) {
            ++local_result.static_method_matches;
            if (!local_result.single_static_method) {
                local_result.single_static_method = &method;
            }
            continue;
        }
        ++local_result.nonstatic_method_matches;
    }
    for (const auto& method_template : state->method_templates) {
        if (method_template.name != member_name) {
            continue;
        }
        if (method_template.is_static) {
            ++local_result.static_method_template_matches;
            continue;
        }
        ++local_result.nonstatic_method_template_matches;
    }
    for (const auto& static_member : state->static_data_members) {
        if (static_member.name != member_name) {
            continue;
        }
        ++local_result.static_data_matches;
        if (!local_result.single_static_data_member) {
            local_result.single_static_data_member = &static_member;
        }
    }
    for (const auto& enumerator : state->enumerator_members) {
        if (enumerator.name != member_name) {
            continue;
        }
        ++local_result.enumerator_matches;
        if (!local_result.single_enumerator_member) {
            local_result.single_enumerator_member = &enumerator;
        }
    }
    if (local_result.has_member_match()) {
        return local_result;
    }

    MemberNameLookupResult inherited_result;
    for (const auto& base : state->bases) {
        if (!base.record_decl) {
            continue;
        }
        MemberNameLookupResult base_result =
            lookup_record_member_name_impl(base.record_decl, member_name, visited);
        inherited_result.field_matches += base_result.field_matches;
        inherited_result.static_method_matches += base_result.static_method_matches;
        inherited_result.static_method_template_matches +=
            base_result.static_method_template_matches;
        inherited_result.static_data_matches += base_result.static_data_matches;
        inherited_result.enumerator_matches += base_result.enumerator_matches;
        inherited_result.nonstatic_method_matches += base_result.nonstatic_method_matches;
        inherited_result.nonstatic_method_template_matches +=
            base_result.nonstatic_method_template_matches;
        if (!inherited_result.single_static_method &&
            base_result.single_static_method &&
            base_result.static_method_matches == 1) {
            inherited_result.single_static_method =
                base_result.single_static_method;
        }
        if (!inherited_result.single_static_data_member &&
            base_result.single_static_data_member &&
            base_result.static_data_matches == 1) {
            inherited_result.single_static_data_member =
                base_result.single_static_data_member;
        }
        if (!inherited_result.single_enumerator_member &&
            base_result.single_enumerator_member &&
            base_result.enumerator_matches == 1) {
            inherited_result.single_enumerator_member =
                base_result.single_enumerator_member;
        }
    }
    if (inherited_result.static_method_matches != 1) {
        inherited_result.single_static_method = nullptr;
    }
    if (inherited_result.static_data_matches != 1) {
        inherited_result.single_static_data_member = nullptr;
    }
    if (inherited_result.enumerator_matches != 1) {
        inherited_result.single_enumerator_member = nullptr;
    }
    return inherited_result;
}

MemberNameLookupResult lookup_record_member_name(const ObjectType* record_type,
                                                 const std::string& member_name) {
    MemberNameLookupResult result;
    if (!record_type) {
        return result;
    }

    const auto* record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(record_type->get_decl()));
    if (!record_decl) {
        return result;
    }

    invalidate_record_member_lookup_caches_if_needed();
    auto cache_key = make_record_member_lookup_cache_key(record_decl, member_name);
    auto cache_it = g_record_member_name_lookup_cache.find(cache_key);
    if (cache_it != g_record_member_name_lookup_cache.end()) {
        return cache_it->second;
    }

    std::unordered_set<const ObjectDecl*> visited;
    result = lookup_record_member_name_impl(record_decl, member_name, visited);
    g_record_member_name_lookup_cache.emplace(std::move(cache_key), result);
    return result;
}

std::shared_ptr<ObjectType> class_template_pattern_record_type_from_specialization(
    QualType type,
    const ASTContext* ast_ctx) {
    (void)ast_ctx;
    auto specialization_type =
        dyn_cast_shared<TemplateSpecializationType>(
            desugar_typedefs(type).get_shared());
    if (!specialization_type) {
        return nullptr;
    }
    auto* class_template =
        dyn_cast<ClassTemplateDecl>(specialization_type->primary_template);
    if (!class_template) {
        return nullptr;
    }
    const ObjectDecl* pattern_decl = class_template->pattern_semantic_decl();
    if (!pattern_decl) {
        return nullptr;
    }
    return pattern_decl->get_record_type();
}

std::shared_ptr<ObjectType> current_record_from_this_type(QualType this_type,
                                                          const ASTContext* ast_ctx) {
    auto this_ptr = desugar_type(this_type, ast_ctx).as_shared<PointerType>();
    if (!this_ptr) {
        return nullptr;
    }
    QualType pointed_type = desugar_type(this_ptr->pointed_type, ast_ctx);
    if (auto record_type = pointed_type.as_shared<ObjectType>()) {
        return record_type;
    }
    return class_template_pattern_record_type_from_specialization(
        pointed_type,
        ast_ctx);
}

std::shared_ptr<ObjectType> current_record_from_this_type(QualType this_type) {
    return current_record_from_this_type(
        this_type, get_active_side_table_ast_context());
}

const ObjectDecl* record_decl_from_record_type(const ObjectType* record_type) {
    if (!record_type) {
        return nullptr;
    }
    return canonical_record_decl(dyn_cast<ObjectDecl>(record_type->get_decl()));
}

const ObjectDecl* current_access_context_record_decl(
    bool current_function_is_cpp_member,
    QualType current_function_cpp_this_type,
    QualType current_function_cpp_friend_access_type,
    QualType current_cpp_record_lookup_type,
    const ASTContext* ast_ctx) {
    auto lookup_record =
        desugar_type(current_cpp_record_lookup_type, ast_ctx)
            .as_shared<ObjectType>();
    if (const ObjectDecl* lookup_decl =
            record_decl_from_record_type(lookup_record.get())) {
        return lookup_decl;
    }

    if (current_function_is_cpp_member) {
        auto current_record =
            current_record_from_this_type(
                current_function_cpp_this_type,
                ast_ctx);
        if (const ObjectDecl* current_decl =
                record_decl_from_record_type(current_record.get())) {
            return current_decl;
        }
    }
    auto friend_access_record =
        desugar_type(current_function_cpp_friend_access_type, ast_ctx)
            .as_shared<ObjectType>();
    if (const ObjectDecl* friend_access_decl =
            record_decl_from_record_type(friend_access_record.get())) {
        return friend_access_decl;
    }
    return nullptr;
}

const ObjectDecl* current_record_decl_from_this_type(QualType this_type) {
    auto record = current_record_from_this_type(this_type);
    if (!record) {
        return nullptr;
    }
    return record_decl_from_record_type(record.get());
}

struct CppQualifiedOwnerAnalysis {
    const CppQualifiedExprInfo* qualified_info = nullptr;
    QualType qualifier_type = nullptr;
    std::shared_ptr<ObjectType> qualifier_record_type = nullptr;
    const ObjectDecl* qualifier_record_decl = nullptr;
    bool is_dependent = false;
    bool is_current_instantiation = false;

    bool is_dependent_context() const {
        return is_dependent || is_current_instantiation;
    }
};

CppQualifiedOwnerAnalysis analyze_cpp_qualified_expr_owner(
    const CppQualifiedExprInfo* qualified_info,
    const ASTContext* ast_ctx) {
    CppQualifiedOwnerAnalysis analysis;
    analysis.qualified_info = qualified_info;
    if (!qualified_info) {
        return analysis;
    }

    analysis.qualifier_type = qualified_info->qualifier_type;
    analysis.is_current_instantiation =
        qualified_info->is_current_instantiation;
    analysis.is_dependent =
        type_depends_on_template_parameters(
            qualified_info->qualifier_type,
            ast_ctx);
    analysis.qualifier_record_type =
        desugar_type(
            remove_reference(qualified_info->qualifier_type, ast_ctx),
            ast_ctx)
            .as_shared<ObjectType>();
    analysis.qualifier_record_decl = canonical_record_decl(
        dyn_cast<ObjectDecl>(
            analysis.qualifier_record_type
                ? analysis.qualifier_record_type->get_decl()
                : nullptr));
    return analysis;
}

CppQualifiedOwnerAnalysis analyze_cpp_qualified_expr_owner(
    const CppQualifiedExprInfo* qualified_info) {
    return analyze_cpp_qualified_expr_owner(
        qualified_info,
        get_active_side_table_ast_context());
}

bool dependent_lookup_qualifier_is_dependent(
    const DependentLookupQualifier& qualifier,
    const ASTContext* ast_ctx) {
    if (!qualifier.is_type_qualified) {
        return false;
    }
    auto qualified_info = build_cpp_qualified_expr_info(qualifier);
    return analyze_cpp_qualified_expr_owner(&qualified_info, ast_ctx)
        .is_dependent;
}

bool dependent_lookup_qualifier_is_dependent(
    const DependentLookupQualifier& qualifier) {
    return dependent_lookup_qualifier_is_dependent(
        qualifier,
        get_active_side_table_ast_context());
}

struct CppMemberLookupBaseAnalysis {
    QualType object_type = nullptr;
    std::shared_ptr<ObjectType> object_record_type = nullptr;
    const ObjectDecl* object_record_decl = nullptr;
    bool is_dependent = false;
    bool is_current_instantiation = false;

    bool is_dependent_context() const {
        return is_dependent || is_current_instantiation;
    }
};

CppMemberLookupBaseAnalysis analyze_cpp_member_lookup_base(
    QualType base_type,
    bool is_arrow,
    QualType current_this_type,
    const ASTContext* ast_ctx) {
    CppMemberLookupBaseAnalysis analysis;
    if (!base_type) {
        return analysis;
    }

    QualType object_type =
        desugar_type(remove_reference(base_type, ast_ctx), ast_ctx);
    if (is_arrow) {
        auto ptr_type = object_type.as_shared<PointerType>();
        object_type =
            ptr_type
                ? desugar_type(
                      remove_reference(ptr_type->pointed_type, ast_ctx),
                      ast_ctx)
                : QualType(nullptr);
    }

    analysis.object_type = object_type;
    analysis.is_dependent =
        type_depends_on_template_parameters(object_type, ast_ctx);
    analysis.object_record_type =
        object_type
            ? desugar_type(
                  remove_reference(object_type, ast_ctx),
                  ast_ctx)
                  .as_shared<ObjectType>()
            : nullptr;
    if (!analysis.object_record_type) {
        analysis.object_record_type =
            class_template_pattern_record_type_from_specialization(
                object_type,
                ast_ctx);
    }
    analysis.object_record_decl =
        record_decl_from_record_type(analysis.object_record_type.get());

    const ObjectDecl* current_record_decl =
        current_record_decl_from_this_type(current_this_type);
    analysis.is_current_instantiation =
        current_record_decl && analysis.object_record_decl &&
        analysis.object_record_decl == current_record_decl;
    return analysis;
}

CppMemberLookupBaseAnalysis analyze_cpp_member_lookup_base(
    QualType base_type,
    bool is_arrow,
    QualType current_this_type) {
    return analyze_cpp_member_lookup_base(
        base_type,
        is_arrow,
        current_this_type,
        get_active_side_table_ast_context());
}

bool classify_constructor_symbol_call(const std::shared_ptr<Symbol>& sym,
                                      std::shared_ptr<ObjectType>& owner_type_out,
                                      const ASTContext* ast_ctx) {
    owner_type_out = nullptr;
    if (!sym || sym->kind != SymbolKind::FUNCTION) {
        return false;
    }
    auto fn_type = desugar_type(sym->type, ast_ctx).as_shared<FunctionType>();
    if (!fn_type || fn_type->parameters.empty()) {
        return false;
    }
    if (!fn_type->ret_type || !fn_type->ret_type->isVoid()) {
        return false;
    }

    auto this_ptr =
        desugar_type(fn_type->parameters.front(), ast_ctx).as_shared<PointerType>();
    if (!this_ptr) {
        return false;
    }
    auto owner_type =
        desugar_type(this_ptr->pointed_type, ast_ctx).as_shared<ObjectType>();
    if (!owner_type) {
        return false;
    }
    const auto* owner_decl = dyn_cast<ObjectDecl>(owner_type->get_decl());
    if (!owner_decl) {
        return false;
    }
    const RecordSemanticState* owner_state = record_semantics_cache_lookup(owner_decl);
    if (!owner_state) {
        return false;
    }
    for (const auto& ctor : owner_state->constructors) {
        if (ctor.symbol == sym) {
            owner_type_out = owner_type;
            return true;
        }
    }
    return false;
}

bool classify_constructor_symbol_call(const std::shared_ptr<Symbol>& sym,
                                      std::shared_ptr<ObjectType>& owner_type_out) {
    return classify_constructor_symbol_call(
        sym, owner_type_out, get_active_side_table_ast_context());
}

bool is_same_record_or_any_access_derived(const ObjectDecl* derived_or_same,
                                          const ObjectDecl* base_decl) {
    derived_or_same = canonical_record_decl(derived_or_same);
    base_decl = canonical_record_decl(base_decl);
    if (!derived_or_same || !base_decl) {
        return false;
    }
    auto same_record_identity_or_tag =
        [](const ObjectDecl* lhs, const ObjectDecl* rhs) {
            if (!lhs || !rhs) {
                return false;
            }
            if (lhs == rhs) {
                return true;
            }
            return lhs->tag == rhs->tag;
        };
    if (same_record_identity_or_tag(derived_or_same, base_decl)) {
        return true;
    }
    return has_any_access_unambiguous_base_path(derived_or_same, base_decl);
}

bool can_access_protected_member_in_context(
    const ObjectDecl* member_owner_decl,
    const ObjectDecl* access_context_decl,
    const ObjectDecl* object_record_decl,
    bool is_static_member) {
    if (!is_same_record_or_any_access_derived(access_context_decl, member_owner_decl)) {
        return false;
    }
    if (is_static_member) {
        return true;
    }
    // For non-static protected members, object type must be the access context
    // class or a class derived from it.
    return is_same_record_or_any_access_derived(object_record_decl, access_context_decl);
}

bool can_access_private_member_in_context(const ObjectDecl* member_owner_decl,
                                          const ObjectDecl* access_context_decl) {
    const ObjectDecl* owner_decl = canonical_record_decl(member_owner_decl);
    const ObjectDecl* context_decl = canonical_record_decl(access_context_decl);
    return owner_decl &&
           context_decl &&
           (owner_decl == context_decl || owner_decl->tag == context_decl->tag);
}

bool is_local_variable_or_parameter_symbol(const std::shared_ptr<Symbol>& sym) {
    if (!sym || sym->kind != SymbolKind::VARIABLE) {
        return false;
    }
    return sym->linkage == VariableLinkage::NONE &&
           sym->storage_class != StorageClass::EXTERN;
}

QualType remove_reference_and_desugar(QualType type) {
    if (!type) {
        return type;
    }
    return desugar_type(remove_reference(type));
}

QualType remove_reference_and_desugar(QualType type, const ASTContext* ast_ctx) {
    if (!type) {
        return type;
    }
    return desugar_type(remove_reference(type, ast_ctx), ast_ctx);
}

bool type_can_participate_in_cpp_operator_overload(QualType type,
                                                   const ASTContext* ast_ctx) {
    auto canonical = remove_reference_and_desugar(type, ast_ctx);
    auto kind = canonical_type_kind(canonical, ast_ctx);
    return kind == TypeKind::Object || kind == TypeKind::Enum;
}

bool type_can_participate_in_cpp_operator_overload(QualType type) {
    return type_can_participate_in_cpp_operator_overload(
        type,
        get_active_side_table_ast_context());
}

std::string_view unary_operator_function_suffix(UnaryOpTypes uop) {
    switch (uop) {
        case UnaryOpTypes::NEG:
            return "-";
        case UnaryOpTypes::POSITIVE:
            return "+";
        case UnaryOpTypes::BITWISE_NOT:
            return "~";
        case UnaryOpTypes::LOGICAL_NOT:
            return "!";
        case UnaryOpTypes::INCREMENT_PREFIX:
        case UnaryOpTypes::INCREMENT_POSTFIX:
            return "++";
        case UnaryOpTypes::DECREMENT_PREFIX:
        case UnaryOpTypes::DECREMENT_POSTFIX:
            return "--";
        default:
            return {};
    }
}

bool unary_operator_is_postfix_incdec(UnaryOpTypes uop) {
    return uop == UnaryOpTypes::INCREMENT_POSTFIX ||
           uop == UnaryOpTypes::DECREMENT_POSTFIX;
}

constexpr size_t kOperatorArrowMaxRewriteDepth = 16;

std::string_view binary_operator_function_suffix(BinOpTypes bop) {
    switch (bop) {
        case BinOpTypes::ASSIGN:
            return "=";
        case BinOpTypes::ADD:
            return "+";
        case BinOpTypes::SUB:
            return "-";
        case BinOpTypes::MULT:
            return "*";
        case BinOpTypes::DIV:
            return "/";
        case BinOpTypes::MOD:
            return "%";
        case BinOpTypes::BITWISE_AND:
            return "&";
        case BinOpTypes::BITWISE_OR:
            return "|";
        case BinOpTypes::BITWISE_XOR:
            return "^";
        case BinOpTypes::SHIFT_LEFT:
            return "<<";
        case BinOpTypes::SHIFT_RIGHT:
            return ">>";
        case BinOpTypes::THREE_WAY_COMPARE:
            return "<=>";
        case BinOpTypes::LESS_THAN:
            return "<";
        case BinOpTypes::LESS_EQUAL_THAN:
            return "<=";
        case BinOpTypes::GREATER_THAN:
            return ">";
        case BinOpTypes::GREATER_EQUAL_THAN:
            return ">=";
        case BinOpTypes::EQUAL:
            return "==";
        case BinOpTypes::NOT_EQUAL:
            return "!=";
        default:
            return {};
    }
}
} // namespace
} // namespace collect_internal

#endif // ABURI_COLLECT_INTERNAL_H
