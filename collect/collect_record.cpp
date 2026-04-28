#include "collect.h"

#include "../ast/special_members.h"
#include "../helpers/qualified_name_utils.h"

#include <cstdint>
#include <functional>
#include <limits>

namespace {

const char* cpp_record_kind_spelling(CppRecordKind kind) {
    switch (kind) {
        case CppRecordKind::Class: return "class";
        case CppRecordKind::Struct: return "struct";
        case CppRecordKind::Union: return "union";
    }
    return "record";
}

RecordMemberAccess encode_cpp_access(CppAccessSpecifier access) {
    switch (access) {
        case CppAccessSpecifier::Public: return RecordMemberAccess::Public;
        case CppAccessSpecifier::Protected: return RecordMemberAccess::Protected;
        case CppAccessSpecifier::Private: return RecordMemberAccess::Private;
        case CppAccessSpecifier::None: break;
    }
    return RecordMemberAccess::Public;
}

std::string cpp_base_specifier_name(const CppBaseSpecifier& base_spec) {
    if (!base_spec.type_name.empty()) {
        return base_spec.type_name;
    }
    return base_spec.type ? base_spec.type.to_string() : std::string();
}

const ObjectDecl* cpp_base_record_decl_from_type(QualType base_type) {
    auto base_object = desugar_type(base_type).as_shared<ObjectType>();
    return base_object ? dyn_cast<ObjectDecl>(base_object->get_decl()) : nullptr;
}

std::optional<size_t> collect_aligned_attribute_value(Collect& collect,
                                                      const AttributeArg& arg,
                                                      std::string* error_out) {
    int64_t raw_alignment = 0;
    if (arg.kind == AttributeArg::Kind::INTEGER) {
        raw_alignment = arg.int_value;
    } else if (arg.kind == AttributeArg::Kind::EXPR && arg.expr_value) {
        if (collect.expression_depends_on_template_parameters(arg.expr_value.get())) {
            return std::nullopt;
        }
        auto evaluated = try_evaluate_with_consteval_compat(
            arg.expr_value.get(),
            ConstEvalMode::c_ice());
        if (!evaluated.has_value()) {
            if (error_out && error_out->empty()) {
                *error_out = "_Alignas requires a constant expression";
            }
            return std::nullopt;
        }
        raw_alignment = *evaluated;
    } else {
        return std::nullopt;
    }

    if (raw_alignment < 0) {
        if (error_out && error_out->empty()) {
            *error_out = "_Alignas requires a non-negative alignment";
        }
        return std::nullopt;
    }
    if (raw_alignment == 0) {
        return size_t{0};
    }
    if ((raw_alignment & (raw_alignment - 1)) != 0) {
        if (error_out && error_out->empty()) {
            *error_out = "_Alignas requires a power-of-two alignment";
        }
        return std::nullopt;
    }
    return static_cast<size_t>(raw_alignment);
}

size_t collect_requested_alignment_from_attrs(Collect& collect,
                                              ASTContext* ast_ctx,
                                              uint32_t node_id,
                                              SrcLoc loc,
                                              std::string* error_out = nullptr,
                                              SrcLoc* error_loc_out = nullptr) {
    if (!ast_ctx || !ast_ctx->has_attrs(node_id)) {
        return 0;
    }

    size_t best = 0;
    for (const auto& attr : ast_ctx->get_attrs(node_id).attrs) {
        if (attr.resolved_kind != AttributeKind::ALIGNED || attr.args.empty()) {
            continue;
        }
        std::string local_error;
        auto requested = collect_aligned_attribute_value(
            collect,
            attr.args.front(),
            &local_error);
        SrcLoc attr_loc = attr.loc.isInvalid() ? loc : attr.loc;
        if (!local_error.empty()) {
            if (error_out && error_out->empty()) {
                *error_out = local_error;
            }
            if (error_loc_out) {
                *error_loc_out = attr_loc;
            }
            return 0;
        }
        if (!requested.has_value()) {
            continue;
        }
        if (*requested > best) {
            best = *requested;
        }
    }
    return best;
}

bool cpp_base_type_is_dependent(QualType base_type) {
    auto dependent_base_raw = desugar_type(base_type).get_shared();
    if (!dependent_base_raw) {
        return false;
    }

    if (dependent_base_raw->kind == TypeKind::TemplateTypeParm ||
        dependent_base_raw->kind == TypeKind::DependentName) {
        return true;
    }

    if (auto specialization =
            dyn_cast_shared<TemplateSpecializationType>(dependent_base_raw)) {
        return specialization->is_dependent;
    }

    return false;
}

std::string make_virtual_slot_key(const std::string& method_name,
                                  QualType method_type) {
    return make_cpp_virtual_slot_key(method_name, method_type);
}

const ObjectDecl* canonical_cpp_record_decl(const ObjectDecl* decl) {
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

size_t count_public_base_subobjects(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl) {
    derived_decl = canonical_cpp_record_decl(derived_decl);
    target_base_decl = canonical_cpp_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl ||
        derived_decl == target_base_decl) {
        return 0;
    }

    std::unordered_set<std::string> matched_subobjects;
    std::vector<BasePathStep> path;
    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(derived_decl);

    std::function<void(const ObjectDecl*)> walk =
        [&](const ObjectDecl* current_decl) {
        current_decl = canonical_cpp_record_decl(current_decl);
        if (!current_decl) {
            return;
        }
        if (current_decl == target_base_decl) {
            if (!path.empty()) {
                matched_subobjects.insert(encode_base_path_key(path));
            }
            return;
        }
        auto walk_base_edge =
            [&](const RecordSemanticState::Base& base) {
            const ObjectDecl* base_decl =
                canonical_cpp_record_decl(base.record_decl);
            if (!base_decl ||
                base.declared_access != RecordMemberAccess::Public ||
                active_stack.contains(base_decl)) {
                return;
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
        };

        if (current_decl == current_record_decl) {
            for (const auto& base : current_record_bases) {
                walk_base_edge(base);
            }
            return;
        }

        const RecordSemanticState* state =
            record_semantics_cache_lookup(current_decl);
        if (!state) {
            return;
        }

        for (const auto& base : state->bases) {
            walk_base_edge(base);
        }
    };

    walk(derived_decl);
    return matched_subobjects.size();
}

bool has_public_unambiguous_base_path(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl) {
    size_t count = count_public_base_subobjects(
        derived_decl,
        target_base_decl,
        current_record_bases,
        current_record_decl);
    return count == 1;
}

struct CovariantReturnTarget {
    enum class Kind : uint8_t {
        Invalid,
        Pointer,
        LValueReference,
        RValueReference,
    };
    Kind kind = Kind::Invalid;
    QualType object_type;
    const ObjectDecl* object_decl = nullptr;
};

CovariantReturnTarget extract_covariant_return_target(QualType return_type) {
    CovariantReturnTarget target;
    if (!return_type) {
        return target;
    }
    auto canonical_return = desugar_type(return_type);
    if (auto ptr_type = canonical_return.as_shared<PointerType>()) {
        target.kind = CovariantReturnTarget::Kind::Pointer;
        target.object_type = ptr_type->pointed_type;
    } else if (auto ref_type =
                   canonical_return.as_shared<ReferenceType>()) {
        target.kind = ref_type->isRValueReference()
            ? CovariantReturnTarget::Kind::RValueReference
            : CovariantReturnTarget::Kind::LValueReference;
        target.object_type = ref_type->referred_type;
    } else {
        return target;
    }

    auto object_type =
        desugar_type(target.object_type).as_shared<ObjectType>();
    if (!object_type) {
        target.kind = CovariantReturnTarget::Kind::Invalid;
        target.object_type = QualType();
        return target;
    }
    target.object_decl =
        canonical_cpp_record_decl(dyn_cast<ObjectDecl>(object_type->get_decl()));
    if (!target.object_decl) {
        target.kind = CovariantReturnTarget::Kind::Invalid;
        target.object_type = QualType();
    }
    return target;
}

bool returns_are_covariant(
    QualType overriding_return,
    QualType overridden_return,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl) {
    if (!overriding_return || !overridden_return) {
        return false;
    }
    if (overriding_return.equals_unqualified(overridden_return)) {
        return true;
    }

    CovariantReturnTarget overriding_target =
        extract_covariant_return_target(overriding_return);
    CovariantReturnTarget overridden_target =
        extract_covariant_return_target(overridden_return);
    if (overriding_target.kind == CovariantReturnTarget::Kind::Invalid ||
        overridden_target.kind == CovariantReturnTarget::Kind::Invalid ||
        overriding_target.kind != overridden_target.kind ||
        !overriding_target.object_type ||
        !overridden_target.object_type ||
        !overriding_target.object_decl ||
        !overridden_target.object_decl) {
        return false;
    }

    if (!overridden_target.object_type.has_all_qualifiers_of(
            overriding_target.object_type)) {
        return false;
    }
    if (overriding_target.object_decl == overridden_target.object_decl) {
        return true;
    }
    return has_public_unambiguous_base_path(
        overriding_target.object_decl,
        overridden_target.object_decl,
        current_record_bases,
        current_record_decl);
}

struct VirtualSlotState {
    size_t slot_index = 0;
    bool is_pure = false;
    bool is_final = false;
    bool is_destructor = false;
    std::shared_ptr<Symbol> final_symbol = nullptr;
    std::string name;
};

const RecordSemanticState::Method* find_copy_assignment_method(
    const RecordSemanticState* state,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!state || !owner_type) {
        return nullptr;
    }

    for (const auto& method : state->methods) {
        if (!cpp_method_is_copy_assignment(method, owner_type, ast_ctx)) {
            continue;
        }
        return &method;
    }

    return nullptr;
}

const RecordSemanticState::Method* find_move_assignment_method(
    const RecordSemanticState* state,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!state || !owner_type) {
        return nullptr;
    }

    for (const auto& method : state->methods) {
        if (!cpp_method_is_move_assignment(method, owner_type, ast_ctx)) {
            continue;
        }
        return &method;
    }

    return nullptr;
}

const RecordSemanticState::Method* find_assignment_method_for_value_category(
    const RecordSemanticState* state,
    QualType owner_type,
    bool use_move,
    const ASTContext* ast_ctx) {
    if (use_move) {
        if (const auto* move_assign =
                find_move_assignment_method(state, owner_type, ast_ctx)) {
            return move_assign;
        }
    }
    return find_copy_assignment_method(state, owner_type, ast_ctx);
}

const RecordSemanticState::Constructor* find_copy_constructor(
    const RecordSemanticState* state,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!state || !owner_type) {
        return nullptr;
    }
    for (const auto& ctor : state->constructors) {
        if (cpp_constructor_is_copy_constructor(ctor, owner_type, ast_ctx)) {
            return &ctor;
        }
    }
    return nullptr;
}

const RecordSemanticState::Constructor* find_move_constructor(
    const RecordSemanticState* state,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!state || !owner_type) {
        return nullptr;
    }
    for (const auto& ctor : state->constructors) {
        if (cpp_constructor_is_move_constructor(ctor, owner_type, ast_ctx)) {
            return &ctor;
        }
    }
    return nullptr;
}

const RecordSemanticState::Constructor* find_constructor_for_value_category(
    const RecordSemanticState* state,
    QualType owner_type,
    bool use_move,
    const ASTContext* ast_ctx) {
    if (use_move) {
        if (const auto* move_ctor =
                find_move_constructor(state, owner_type, ast_ctx)) {
            return move_ctor;
        }
    }
    return find_copy_constructor(state, owner_type, ast_ctx);
}

bool type_supports_generated_special_member_construction(
    QualType type,
    bool use_move,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records);

bool record_supports_generated_special_member_construction(
    const ObjectDecl* record_decl,
    bool use_move,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    record_decl = canonical_cpp_record_decl(record_decl);
    if (!record_decl) {
        return false;
    }
    if (active_records.contains(record_decl)) {
        return true;
    }

    const RecordSemanticState* state =
        record_semantics_cache_lookup(record_decl, ast_ctx);
    if (!state || state->is_incomplete) {
        return false;
    }

    QualType owner_type(record_decl->get_record_type());
    if (const auto* ctor =
            find_constructor_for_value_category(
                state, owner_type, use_move, ast_ctx)) {
        return !ctor->is_deleted;
    }

    active_records.insert(record_decl);
    for (const auto& base : state->bases) {
        if (!type_supports_generated_special_member_construction(
                base.type, use_move, ast_ctx, active_records)) {
            active_records.erase(record_decl);
            return false;
        }
    }
    for (const auto& field : state->fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage) {
            continue;
        }
        if (!type_supports_generated_special_member_construction(
                field.type, use_move, ast_ctx, active_records)) {
            active_records.erase(record_decl);
            return false;
        }
    }
    active_records.erase(record_decl);
    return true;
}

bool type_supports_generated_special_member_construction(
    QualType type,
    bool use_move,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
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

    if (auto array_type = canonical.as_shared<ArrayType>()) {
        if (array_type->size_kind != ArraySizeKind::Constant ||
            !array_type->size.has_value()) {
            return false;
        }
        return type_supports_generated_special_member_construction(
            array_type->element_type,
            use_move,
            ast_ctx,
            active_records);
    }

    if (auto object_type = canonical.as_shared<ObjectType>()) {
        return record_supports_generated_special_member_construction(
            dyn_cast<ObjectDecl>(object_type->get_decl()),
            use_move,
            ast_ctx,
            active_records);
    }

    return true;
}

bool type_supports_generated_copy_construction(
    QualType type,
    const ASTContext* ast_ctx) {
    std::unordered_set<const ObjectDecl*> active_records;
    return type_supports_generated_special_member_construction(
        type, false, ast_ctx, active_records);
}

bool type_supports_generated_move_construction(
    QualType type,
    const ASTContext* ast_ctx) {
    std::unordered_set<const ObjectDecl*> active_records;
    return type_supports_generated_special_member_construction(
        type, true, ast_ctx, active_records);
}

bool type_supports_generated_assignment(
    QualType type,
    bool use_move,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records);

bool record_supports_generated_assignment(
    const ObjectDecl* record_decl,
    bool use_move,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    record_decl = canonical_cpp_record_decl(record_decl);
    if (!record_decl) {
        return false;
    }
    if (active_records.contains(record_decl)) {
        return true;
    }

    const RecordSemanticState* state =
        record_semantics_cache_lookup(record_decl, ast_ctx);
    if (!state || state->is_incomplete) {
        return false;
    }

    QualType owner_type(record_decl->get_record_type());
    if (const auto* assignment =
            find_assignment_method_for_value_category(
                state, owner_type, use_move, ast_ctx)) {
        return !assignment->is_deleted;
    }

    active_records.insert(record_decl);
    for (const auto& base : state->bases) {
        if (!type_supports_generated_assignment(
                base.type, use_move, ast_ctx, active_records)) {
            active_records.erase(record_decl);
            return false;
        }
    }
    for (const auto& field : state->fields) {
        if (field.is_base_subobject || field.is_virtual_base_storage) {
            continue;
        }
        if (!type_supports_generated_assignment(
                field.type, use_move, ast_ctx, active_records)) {
            active_records.erase(record_decl);
            return false;
        }
    }
    active_records.erase(record_decl);
    return true;
}

bool type_supports_generated_assignment(
    QualType type,
    bool use_move,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    if (!type) {
        return false;
    }
    if (type.is_const()) {
        return false;
    }

    QualType canonical = desugar_type(type, ast_ctx);
    if (!canonical) {
        return false;
    }

    if (canonical.as_shared<ReferenceType>()) {
        return false;
    }

    if (auto array_type = canonical.as_shared<ArrayType>()) {
        if (array_type->size_kind != ArraySizeKind::Constant ||
            !array_type->size.has_value()) {
            return false;
        }
        return type_supports_generated_assignment(
            array_type->element_type, use_move, ast_ctx, active_records);
    }

    if (auto object_type = canonical.as_shared<ObjectType>()) {
        return record_supports_generated_assignment(
            dyn_cast<ObjectDecl>(object_type->get_decl()),
            use_move,
            ast_ctx,
            active_records);
    }

    return true;
}

bool type_supports_generated_copy_assignment(
    QualType type,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    return type_supports_generated_assignment(
        type, false, ast_ctx, active_records);
}

bool type_supports_generated_copy_assignment(
    QualType type,
    const ASTContext* ast_ctx) {
    std::unordered_set<const ObjectDecl*> active_records;
    return type_supports_generated_copy_assignment(
        type, ast_ctx, active_records);
}

bool type_supports_generated_move_assignment(
    QualType type,
    const ASTContext* ast_ctx,
    std::unordered_set<const ObjectDecl*>& active_records) {
    return type_supports_generated_assignment(
        type, true, ast_ctx, active_records);
}

bool type_supports_generated_move_assignment(
    QualType type,
    const ASTContext* ast_ctx) {
    std::unordered_set<const ObjectDecl*> active_records;
    return type_supports_generated_move_assignment(
        type, ast_ctx, active_records);
}

std::optional<size_t> find_direct_base_assignment_offset(
    const RecordSemanticState& owner_state,
    const RecordSemanticState::Base& base) {
    if (!base.record_decl) {
        return std::nullopt;
    }
    if (!base.is_virtual) {
        if (base.has_non_virtual_offset) {
            return base.non_virtual_offset;
        }
        return std::nullopt;
    }

    const ObjectDecl* canonical_base = canonical_cpp_record_decl(base.record_decl);
    for (const auto& virtual_base : owner_state.virtual_bases) {
        if (!virtual_base.record_decl || !virtual_base.has_offset) {
            continue;
        }
        if (canonical_cpp_record_decl(virtual_base.record_decl) ==
            canonical_base) {
            return virtual_base.offset;
        }
    }
    return std::nullopt;
}

std::shared_ptr<Symbol> ensure_synthesized_param_symbol(
    ParamDecl* param_decl,
    const std::string& fallback_name) {
    if (!param_decl) {
        return nullptr;
    }
    if (param_decl->sym) {
        return param_decl->sym;
    }
    param_decl->sym = std::make_shared<Symbol>(
        fallback_name,
        SymbolKind::VARIABLE,
        param_decl->type,
        param_decl->storage_class);
    return param_decl->sym;
}

std::unique_ptr<Expr> make_param_reference_expr(Collect& collect,
                                                ParamDecl* param_decl,
                                                const std::string& fallback_name,
                                                SrcLoc loc) {
    if (!param_decl) {
        return nullptr;
    }
    auto sym = ensure_synthesized_param_symbol(param_decl, fallback_name);
    if (sym) {
        return collect.collect_make<VarRef>(std::move(sym), loc);
    }
    if (param_decl->has_name()) {
        return collect.collect_make<VarRef>(param_decl->get_name_ptr(), loc);
    }
    return nullptr;
}

std::unique_ptr<Expr> make_base_subobject_expr(
    Collect& collect,
    const ASTContext* ast_ctx,
    const std::shared_ptr<CType>& char_type,
    const std::shared_ptr<CType>& ulong_type,
    std::unique_ptr<Expr> object_pointer_expr,
    QualType base_type,
    size_t byte_offset,
    SrcLoc loc) {
    if (!object_pointer_expr || !base_type) {
        return nullptr;
    }

    auto object_ptr_type =
        desugar_type(
            object_pointer_expr->get_type(),
            ast_ctx)
            .as_shared<PointerType>();
    if (!object_ptr_type || !object_ptr_type->pointed_type) {
        return nullptr;
    }

    uint8_t pointee_quals = object_ptr_type->pointed_type.get_qualifiers();
    QualType byte_pointee(char_type, pointee_quals);
    QualType byte_ptr_type(std::make_shared<PointerType>(byte_pointee));
    auto byte_ptr_expr =
        collect.collect_explicit_cast(std::move(object_pointer_expr), byte_ptr_type, loc);
    if (!byte_ptr_expr) {
        return nullptr;
    }

    if (byte_offset != 0) {
        auto offset_expr = collect.collect_integer_literal(
            std::to_string(byte_offset),
            ulong_type,
            loc);
        byte_ptr_expr = collect.collect_binary_operation(
            std::move(byte_ptr_expr),
            std::move(offset_expr),
            BinOpTypes::ADD,
            loc);
        if (!byte_ptr_expr) {
            return nullptr;
        }
    }

    QualType qualified_base_type(base_type.get_shared(), static_cast<uint8_t>(
        base_type.get_qualifiers() | pointee_quals));
    QualType base_ptr_type(std::make_shared<PointerType>(qualified_base_type));
    auto cast_base_ptr =
        collect.collect_explicit_cast(std::move(byte_ptr_expr), base_ptr_type, loc);
    if (!cast_base_ptr) {
        return nullptr;
    }
    return collect.collect_unary_operation(
        UnaryOpTypes::DEREFERENCE,
        std::move(cast_base_ptr),
        loc);
}

std::unique_ptr<Expr> maybe_materialize_generated_move_source(
    Collect& collect,
    QualType target_type,
    const ASTContext* ast_ctx,
    std::unique_ptr<Expr> source_expr,
    SrcLoc loc) {
    if (!source_expr ||
        canonical_type_kind(target_type, ast_ctx) != TypeKind::Object) {
        return source_expr;
    }
    QualType source_ref_type(std::make_shared<ReferenceType>(
        remove_reference(target_type, ast_ctx),
        ReferenceKind::RValue));
    return collect.collect_explicit_cast(
        std::move(source_expr),
        source_ref_type,
        loc);
}

bool emit_generated_assignment_statements_for_type(
    Collect& collect,
    const ASTContext* ast_ctx,
    const std::shared_ptr<CType>& ulong_type,
    QualType type,
    bool use_move,
    const std::function<std::unique_ptr<Expr>()>& make_lhs,
    const std::function<std::unique_ptr<Expr>()>& make_rhs,
    std::vector<std::unique_ptr<Stmt>>& statements_out,
    SrcLoc loc) {
    if (!type || !make_lhs || !make_rhs) {
        return false;
    }

    if (auto array_type =
            desugar_type(type, ast_ctx).as_shared<ArrayType>()) {
        if (array_type->size_kind != ArraySizeKind::Constant ||
            !array_type->size.has_value()) {
            return false;
        }
        for (size_t idx = 0; idx < *array_type->size; ++idx) {
            auto lhs_builder = [&collect, &make_lhs, &ulong_type, idx, loc]() {
                auto index_expr = collect.collect_integer_literal(
                    std::to_string(idx),
                    ulong_type,
                    loc);
                return collect.collect_array_subscript(
                    make_lhs(),
                    std::move(index_expr),
                    loc);
            };
            auto rhs_builder = [&collect, &make_rhs, &ulong_type, idx, loc]() {
                auto index_expr = collect.collect_integer_literal(
                    std::to_string(idx),
                    ulong_type,
                    loc);
                auto rhs_expr = collect.collect_array_subscript(
                    make_rhs(),
                    std::move(index_expr),
                    loc);
                return rhs_expr;
            };
            if (!emit_generated_assignment_statements_for_type(
                    collect,
                    ast_ctx,
                    ulong_type,
                    array_type->element_type,
                    use_move,
                    lhs_builder,
                    rhs_builder,
                    statements_out,
                    loc)) {
                return false;
            }
        }
        return true;
    }

    auto rhs_expr = make_rhs();
    if (use_move) {
        rhs_expr = maybe_materialize_generated_move_source(
            collect,
            type,
            ast_ctx,
            std::move(rhs_expr),
            loc);
        if (!rhs_expr) {
            return false;
        }
    }

    auto assignment = collect.collect_binary_operation(
        make_lhs(),
        std::move(rhs_expr),
        BinOpTypes::ASSIGN,
        loc);
    if (!assignment || isa<ErrorExpr>(assignment.get())) {
        return false;
    }
    statements_out.push_back(
        collect.collect_expression_statement(std::move(assignment), loc));
    return !statements_out.empty();
}

std::unique_ptr<Expr> build_generated_constructor_initializer_expr(
    Collect& collect,
    const ASTContext* ast_ctx,
    const std::shared_ptr<CType>& ulong_type,
    QualType type,
    bool use_move,
    const std::function<std::unique_ptr<Expr>()>& make_source_expr,
    SrcLoc loc) {
    if (!type || !make_source_expr) {
        return nullptr;
    }

    if (auto array_type =
            desugar_type(type, ast_ctx).as_shared<ArrayType>()) {
        if (array_type->size_kind != ArraySizeKind::Constant ||
            !array_type->size.has_value()) {
            return nullptr;
        }

        auto init_list = collect.collect_make<InitListExpr>(loc);
        init_list->is_paren_init = false;
        init_list->elements.reserve(*array_type->size);
        for (size_t idx = 0; idx < *array_type->size; ++idx) {
            auto element_builder =
                [&collect, &make_source_expr, &ulong_type, idx, loc]() {
                auto index_expr = collect.collect_integer_literal(
                    std::to_string(idx),
                    ulong_type,
                    loc);
                return collect.collect_array_subscript(
                    make_source_expr(),
                    std::move(index_expr),
                    loc);
            };
            InitElement element;
            element.value = build_generated_constructor_initializer_expr(
                collect,
                ast_ctx,
                ulong_type,
                array_type->element_type,
                use_move,
                element_builder,
                loc);
            element.loc = loc;
            if (!element.value) {
                return nullptr;
            }
            init_list->elements.push_back(std::move(element));
        }
        return collect.collect_member_initializer_expression(
            std::move(init_list),
            type,
            loc);
    }

    if (canonical_type_kind(type, ast_ctx) == TypeKind::Object) {
        std::vector<std::unique_ptr<Expr>> ctor_args;
        auto source_expr = make_source_expr();
        if (!source_expr) {
            return nullptr;
        }
        if (use_move) {
            source_expr = maybe_materialize_generated_move_source(
                collect,
                type,
                ast_ctx,
                std::move(source_expr),
                loc);
            if (!source_expr) {
                return nullptr;
            }
        }
        ctor_args.push_back(std::move(source_expr));
        return collect.collect_member_initializer_expression(
            std::move(ctor_args),
            type,
            false,
            loc,
            false);
    }

    return collect.collect_member_initializer_expression(
        make_source_expr(),
        type,
        loc);
}

} // namespace

class CollectRecordBuilder {
public:
    CollectRecordBuilder(
        Collect& collect,
        const CppRecordDecl& record,
        std::optional<std::string> semantic_tag_name,
        std::vector<std::unique_ptr<Decl>>* transient_decls_out,
        Collect::CppRecordDeferredBodyCallback deferred_body_callback)
        : collect_(collect),
          record_(record),
          semantic_tag_name_(std::move(semantic_tag_name)),
          transient_decls_out_(transient_decls_out),
          deferred_body_callback_(std::move(deferred_body_callback)) {}

    std::unique_ptr<Decl> build() {
        if (record_.name.empty()) {
            return nullptr;
        }

        bool is_union_record = record_.record_kind == CppRecordKind::Union;
        const std::string& record_name = record_.name;
        std::string semantic_tag = semantic_tag_name_.has_value()
            ? std::move(*semantic_tag_name_)
            : record_name;
        const std::string& tag = semantic_tag;

        ObjectDecl* existing_obj_decl = nullptr;
        if (auto* existing_tag_decl = collect_.collect_lookup_tag_decl(tag, false)) {
            existing_obj_decl = dyn_cast<ObjectDecl>(existing_tag_decl);
            if (!existing_obj_decl) {
                collect_.report_error(
                    "tag '" + tag + "' was previously declared with a different kind",
                    record_.location);
            }
        }

        std::shared_ptr<ObjectType> record_type = existing_obj_decl
            ? existing_obj_decl->get_record_type()
            : std::make_shared<ObjectType>(
                  tag, is_union_record, !record_.is_definition);
        if (!record_type) {
            collect_.report_error(
                "failed to build semantic record type for " +
                    std::string(cpp_record_kind_spelling(record_.record_kind)) +
                    " '" + tag + "'",
                record_.location);
        }
        if (record_type && record_type->is_union != is_union_record) {
            collect_.report_error(
                "tag '" + tag + "' was previously declared as a different kind",
                record_.location);
        }
        if (record_.is_definition && existing_obj_decl && record_type &&
            !record_type->isIncomplete()) {
            collect_.report_error(
                "redefinition of " +
                    std::string(cpp_record_kind_spelling(record_.record_kind)) +
                    " '" + tag + "'",
                record_.location);
        }

        auto semantic_decl = collect_.collect_record_declaration(
            tag,
            record_type,
            is_union_record,
            record_.location);
        if (!semantic_decl) {
            return nullptr;
        }

        RecordSemanticState semantic_state;
        if (record_.is_definition) {
            Collect::CollectRecordBuildContext ctx{
                &record_,
                record_.location,
                record_name,
                tag,
                is_union_record,
                record_type,
                semantic_decl.get(),
                transient_decls_out_,
                std::move(deferred_body_callback_)};
            ctx.semantic_state.is_incomplete = false;
            ctx.semantic_state.alignment = 1;
            ctx.semantic_state.non_virtual_alignment = 1;
            if (const auto* definition_data = record_.get_definition_data()) {
                ctx.semantic_state.definition_data = *definition_data;
            }
            if (record_type) {
                std::string alignment_error;
                SrcLoc alignment_error_loc = record_.location;
                size_t requested_alignment = collect_requested_alignment_from_attrs(
                    collect_,
                    collect_.ast_ctx_.get(),
                    record_.node_id,
                    record_.location,
                    &alignment_error,
                    &alignment_error_loc);
                if (!alignment_error.empty()) {
                    collect_.report_error(alignment_error, alignment_error_loc);
                }
                if (requested_alignment > record_type->requested_alignment) {
                    record_type->requested_alignment = requested_alignment;
                }
            }
            ctx.fields.reserve(record_.members.size());
            ctx.methods.reserve(record_.members.size());
            ctx.method_templates.reserve(record_.members.size());
            ctx.static_data_members.reserve(record_.members.size());
            ctx.nested_types.reserve(record_.members.size());
            ctx.nested_templates.reserve(record_.members.size());
            ctx.enumerator_members.reserve(record_.members.size());
            ctx.seen_static_data_member_names.reserve(record_.members.size());
            ctx.constructors.reserve(record_.members.size());
            ctx.destructors.reserve(record_.members.size());
            ctx.required_ctor_member_init_fields.reserve(record_.members.size());

            collect_.collect_record_resolve_bases(ctx);
            collect_.collect_record_walk_virtual_bases(ctx);
            collect_.collect_record_collect_members(ctx);
            collect_.collect_record_synthesize_implicit_members(ctx);
            collect_.collect_record_resolve_virtual_dispatch(ctx);
            collect_.collect_record_compute_layout(ctx);
            collect_.collect_record_materialize_defaulted_method_bodies(ctx);
            collect_.collect_record_publish_semantics(ctx);
            if (ctx.record_type) {
                ctx.record_type->set_decl(ctx.semantic_decl);
            }

            if (ctx.deferred_body_callback) {
                ctx.deferred_body_callback(
                    *ctx.record,
                    ctx.record_type,
                    ctx.semantic_state);
            }

            semantic_state = std::move(ctx.semantic_state);
        } else if (existing_obj_decl) {
            if (const auto* existing_state =
                    collect_.query_lookup_record_semantics(existing_obj_decl)) {
                semantic_state = *existing_state;
            }
        } else {
            semantic_state = RecordSemanticState{};
            if (record_type) {
                record_type->set_decl(semantic_decl.get());
            }
        }

        collect_.query_publish_record_semantics(semantic_decl.get(),
                                                std::move(semantic_state));
        collect_.collect_add_tag_decl(tag, semantic_decl.get());
        return semantic_decl;
    }

private:
    Collect& collect_;
    const CppRecordDecl& record_;
    std::optional<std::string> semantic_tag_name_;
    std::vector<std::unique_ptr<Decl>>* transient_decls_out_ = nullptr;
    Collect::CppRecordDeferredBodyCallback deferred_body_callback_;
};

std::unique_ptr<Decl> Collect::collect_build_cpp_record_semantic_decl(
    const CppRecordDecl& record,
    std::optional<std::string> semantic_tag_name,
    std::vector<std::unique_ptr<Decl>>* transient_decls_out,
    CppRecordDeferredBodyCallback deferred_body_callback) {
    CollectRecordBuilder builder(*this,
                                 record,
                                 std::move(semantic_tag_name),
                                 transient_decls_out,
                                 std::move(deferred_body_callback));
    return builder.build();
}

void Collect::collect_record_register_function_default_arguments(
    const std::shared_ptr<Symbol>& sym,
    const FuncDecl* decl,
    SrcLoc fallback_loc) const {
    if (!lang_opts_.is_cxx_mode() || !sym || !decl ||
        sym->kind != SymbolKind::FUNCTION) {
        return;
    }

    std::vector<const Expr*> incoming_defaults(decl->parameters.size(), nullptr);
    bool has_incoming_defaults = false;
    for (size_t index = 0; index < decl->parameters.size(); ++index) {
        auto* param_decl = dyn_cast<ParamDecl>(decl->parameters[index].get());
        if (!param_decl) {
            continue;
        }
        incoming_defaults[index] = get_param_decl_default_argument(param_decl);
        if (incoming_defaults[index]) {
            has_incoming_defaults = true;
        }
    }
    if (!has_incoming_defaults &&
        !get_symbol_cpp_default_arguments(sym.get())) {
        return;
    }

    size_t conflict_index = std::numeric_limits<size_t>::max();
    if (merge_symbol_cpp_default_arguments(
            sym.get(),
            incoming_defaults,
            &conflict_index)) {
        return;
    }

    SrcLoc conflict_loc = fallback_loc;
    if (conflict_index < decl->parameters.size()) {
        auto* param_decl =
            dyn_cast<ParamDecl>(decl->parameters[conflict_index].get());
        if (param_decl) {
            if (const Expr* expr = get_param_decl_default_argument(param_decl)) {
                conflict_loc = expr->location;
            } else if (!param_decl->location.isInvalid()) {
                conflict_loc = param_decl->location;
            }
        }
    }
    report_error("redefinition of default argument", conflict_loc);
}

void Collect::collect_record_resolve_bases(CollectRecordBuildContext& ctx) const {
    if (!ctx.record) {
        report_error(
            "internal error: record base resolution requires parsed record syntax",
            ctx.loc);
        return;
    }
    ctx.bases.reserve(ctx.record->bases.size());
    std::unordered_set<const ObjectDecl*> seen_direct_bases;
    seen_direct_bases.reserve(ctx.record->bases.size());
    for (const auto& base_spec : ctx.record->bases) {
        RecordSemanticState::Base semantic_base;
        std::string base_name = cpp_base_specifier_name(base_spec);
        semantic_base.name = base_name;
        semantic_base.declared_access = encode_cpp_access(base_spec.access);
        semantic_base.is_virtual = base_spec.is_virtual_base;
        semantic_base.spec = &base_spec;

        if (base_name.empty()) {
            report_error(
                "expected base class name in base-specifier",
                base_spec.location);
        }

        QualType resolved_base_type = base_spec.type;
        if (resolved_base_type &&
            !cpp_base_type_is_dependent(resolved_base_type)) {
            resolved_base_type =
                const_cast<Collect*>(this)
                    ->collect_try_realize_deferred_semantic_type(
                        resolved_base_type);
        }
        auto* base_record_decl = cpp_base_record_decl_from_type(resolved_base_type);
        if (!base_record_decl && !resolved_base_type) {
            auto* base_tag_decl =
                collect_lookup_tag_decl(base_name, true);
            base_record_decl = dyn_cast<ObjectDecl>(base_tag_decl);
            if (!base_record_decl) {
                resolved_base_type =
                    collect_lookup_type_name(base_name, true, true);
                base_record_decl =
                    cpp_base_record_decl_from_type(resolved_base_type);
            }
        }

        if (!base_record_decl) {
            if (!resolved_base_type ||
                !cpp_base_type_is_dependent(resolved_base_type)) {
                report_error(
                    "base type '" + base_name +
                        "' does not name a class or struct",
                    base_spec.location);
            }
            semantic_base.type = resolved_base_type;
            ctx.bases.push_back(std::move(semantic_base));
            continue;
        }
        const ObjectDecl* canonical_base_decl = base_record_decl;
        if (base_record_decl->get_record_type()) {
            if (auto* canonical =
                    dyn_cast<ObjectDecl>(
                        base_record_decl->get_record_type()->get_decl())) {
                canonical_base_decl = canonical;
            }
        }

        if (canonical_base_decl == ctx.semantic_decl ||
            base_name == ctx.record_name) {
            report_error(
                "class '" + ctx.tag + "' cannot derive from itself",
                base_spec.location);
        }
        if (seen_direct_bases.contains(canonical_base_decl)) {
            report_error(
                "duplicate direct base class '" + base_name + "'",
                base_spec.location);
        }
        if (canonical_base_decl->is_union) {
            report_error(
                "base type '" + base_name +
                    "' is a union; only class/struct bases are supported",
                base_spec.location);
        }
        const RecordSemanticState* base_state =
            record_semantics_cache_lookup(canonical_base_decl);
        if (!base_state || base_state->is_incomplete) {
            report_error(
                "base class '" + base_name + "' is incomplete",
                base_spec.location);
        }

        seen_direct_bases.insert(canonical_base_decl);
        semantic_base.record_decl = canonical_base_decl;
        semantic_base.type = QualType(canonical_base_decl->get_record_type());
        ctx.bases.push_back(std::move(semantic_base));
    }
}

void Collect::collect_record_walk_virtual_bases(
    CollectRecordBuildContext& ctx) const {
    std::unordered_set<const ObjectDecl*> seen_virtual_base_decls;
    std::unordered_set<const ObjectDecl*> visited_base_graph;
    auto append_virtual_base = [&](const RecordSemanticState::Base& base_edge) {
        const ObjectDecl* virtual_base_decl = base_edge.record_decl;
        if (!virtual_base_decl) {
            return;
        }
        if (!seen_virtual_base_decls.insert(virtual_base_decl).second) {
            return;
        }
        RecordSemanticState::VirtualBase virtual_base;
        virtual_base.name = !base_edge.name.empty()
            ? base_edge.name
            : virtual_base_decl->tag;
        virtual_base.type = QualType(virtual_base_decl->get_record_type());
        virtual_base.declared_access = base_edge.declared_access;
        virtual_base.record_decl = virtual_base_decl;
        ctx.virtual_bases.push_back(std::move(virtual_base));
    };
    std::function<void(const ObjectDecl*)> walk_base_graph =
        [&](const ObjectDecl* current_decl) {
        if (!current_decl || visited_base_graph.contains(current_decl)) {
            return;
        }
        visited_base_graph.insert(current_decl);
        const RecordSemanticState* current_state =
            record_semantics_cache_lookup(current_decl);
        if (!current_state) {
            return;
        }
        for (const auto& inherited_base : current_state->bases) {
            if (!inherited_base.record_decl) {
                continue;
            }
            if (inherited_base.is_virtual) {
                append_virtual_base(inherited_base);
            }
            walk_base_graph(inherited_base.record_decl);
        }
    };
    for (const auto& direct_base : ctx.bases) {
        if (direct_base.is_virtual) {
            append_virtual_base(direct_base);
        }
        walk_base_graph(direct_base.record_decl);
    }
}

void Collect::collect_record_collect_members(CollectRecordBuildContext& ctx) {
    if (!ctx.record) {
        report_error(
            "internal error: record member collection requires parsed record syntax",
            ctx.loc);
        return;
    }
    auto ensure_namespace_qualifier_prefix = [&](std::string& qualifier_prefix) {
        if (!lang_opts_.is_cxx_mode()) {
            return;
        }
        qualified_name_utils::ensure_namespace_qualifier_prefix_for_scope(
            collect_current_scope(),
            qualifier_prefix);
    };
    std::function<QualType(QualType)> realize_nested_record_member_type =
        [&](QualType type) -> QualType {
        if (!type) {
            return type;
        }

        auto raw = type.get_shared();
        if (!raw) {
            return type;
        }
        auto quals = type.get_qualifiers();

        if (auto object_type = dyn_cast_shared<ObjectType>(raw)) {
            auto* object_decl = dyn_cast<ObjectDecl>(object_type->get_decl());
            const RecordSemanticState* object_state =
                object_decl ? record_semantics_cache_lookup(object_decl) : nullptr;
            if (object_decl && (!object_state || object_state->is_incomplete)) {
                for (const auto& nested_type : ctx.nested_types) {
                    auto nested_object =
                        desugar_type(nested_type.type).as_shared<ObjectType>();
                    auto* nested_decl = nested_object
                        ? dyn_cast<ObjectDecl>(nested_object->get_decl())
                        : nullptr;
                    if (!nested_decl || nested_decl == object_decl) {
                        continue;
                    }
                    if (nested_decl->tag == object_decl->tag) {
                        return QualType(nested_object, quals);
                    }
                }
            }
            return type;
        }

        if (auto pointer_type = dyn_cast_shared<PointerType>(raw)) {
            auto rewritten_pointee =
                realize_nested_record_member_type(pointer_type->pointed_type);
            if (rewritten_pointee.equals_qualified(pointer_type->pointed_type)) {
                return type;
            }
            return QualType(
                std::make_shared<PointerType>(rewritten_pointee),
                quals);
        }

        if (auto reference_type = dyn_cast_shared<ReferenceType>(raw)) {
            auto rewritten_referred =
                realize_nested_record_member_type(reference_type->referred_type);
            if (rewritten_referred.equals_qualified(reference_type->referred_type)) {
                return type;
            }
            return QualType(
                std::make_shared<ReferenceType>(
                    rewritten_referred,
                    reference_type->reference_kind),
                quals);
        }

        if (auto array_type = dyn_cast_shared<ArrayType>(raw)) {
            auto rewritten_element =
                realize_nested_record_member_type(array_type->element_type);
            if (rewritten_element.equals_qualified(array_type->element_type)) {
                return type;
            }
            if (array_type->size.has_value()) {
                return QualType(
                    std::make_shared<ArrayType>(
                        rewritten_element,
                        array_type->size),
                    quals);
            }
            auto rebuilt =
                std::make_shared<ArrayType>(rewritten_element, array_type->size_expr);
            rebuilt->size_kind = array_type->size_kind;
            rebuilt->size = array_type->size;
            return QualType(rebuilt, quals);
        }

        if (auto function_type = dyn_cast_shared<FunctionType>(raw)) {
            auto rewritten_ret =
                realize_nested_record_member_type(function_type->ret_type);
            bool changed = !rewritten_ret.equals_qualified(function_type->ret_type);
            std::vector<QualType> rewritten_params;
            rewritten_params.reserve(function_type->parameters.size());
            for (const auto& param_type : function_type->parameters) {
                auto rewritten_param =
                    realize_nested_record_member_type(param_type);
                changed |= !rewritten_param.equals_qualified(param_type);
                rewritten_params.push_back(rewritten_param);
            }
            if (!changed) {
                return type;
            }
            auto rebuilt = std::make_shared<FunctionType>(*function_type);
            rebuilt->ret_type = rewritten_ret;
            rebuilt->parameters = std::move(rewritten_params);
            return QualType(rebuilt, quals);
        }

        if (auto member_pointer_type = dyn_cast_shared<MemberPointerType>(raw)) {
            auto rewritten_class =
                realize_nested_record_member_type(member_pointer_type->class_type);
            auto rewritten_member =
                realize_nested_record_member_type(member_pointer_type->member_type);
            if (rewritten_class.equals_qualified(member_pointer_type->class_type) &&
                rewritten_member.equals_qualified(member_pointer_type->member_type)) {
                return type;
            }
            return QualType(
                std::make_shared<MemberPointerType>(
                    rewritten_class,
                    rewritten_member),
                quals);
        }

        if (auto transform_type = dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
            auto rewritten_operand =
                realize_nested_record_member_type(transform_type->operand_type);
            if (rewritten_operand.equals_qualified(transform_type->operand_type)) {
                return type;
            }
            return QualType(
                std::make_shared<BuiltinTypeTransformType>(
                    transform_type->transform_kind,
                    rewritten_operand),
                quals);
        }

        return type;
    };
    RecordMemberAccess current_access = encode_cpp_access(ctx.record->default_access);
    for (const auto& member : ctx.record->members) {
        if (const auto* access_spec = dyn_cast<CppAccessSpecDecl>(member.get())) {
            current_access = encode_cpp_access(access_spec->access);
            continue;
        }

        if (const auto* nested_record = dyn_cast<CppRecordDecl>(member.get())) {
            if (!nested_record->name.empty()) {
                auto nested_semantic = collect_build_cpp_record_semantic_decl(
                    *nested_record,
                    std::nullopt,
                    ctx.transient_decls_out,
                    ctx.deferred_body_callback);
                if (nested_semantic) {
                    auto* nested_object = dyn_cast<ObjectDecl>(nested_semantic.get());
                    if (nested_object && nested_object->get_record_type()) {
                        RecordSemanticState::NestedType nested_type;
                        nested_type.name = nested_record->name;
                        nested_type.type = QualType(nested_object->get_record_type());
                        nested_type.declared_access = current_access;
                        nested_type.decl = nested_object;
                        ctx.nested_types.push_back(std::move(nested_type));
                    }
                    if (ctx.transient_decls_out) {
                        ctx.transient_decls_out->push_back(std::move(nested_semantic));
                    } else {
                        report_error(
                            "internal error: missing transient storage for nested record semantic owner",
                            nested_record->location);
                    }
                }
            }
            continue;
        }

        if (const auto* typedef_decl = dyn_cast<TypedefDecl>(member.get())) {
            RecordSemanticState::NestedType nested_type;
            nested_type.name = typedef_decl->name;
            nested_type.type = typedef_decl->type;
            nested_type.declared_access = current_access;
            nested_type.decl = typedef_decl;
            nested_type.symbol = typedef_decl->sym;
            ctx.nested_types.push_back(std::move(nested_type));
            continue;
        }

        if (const auto* alias_template = dyn_cast<AliasTemplateDecl>(member.get())) {
            if (const auto* alias_decl = alias_template->alias_decl()) {
                RecordSemanticState::NestedTemplate nested_template;
                nested_template.name = alias_decl->name;
                nested_template.declared_access = current_access;
                nested_template.kind =
                    RecordSemanticState::NestedTemplateKind::Alias;
                nested_template.decl = alias_template;
                ctx.nested_templates.push_back(std::move(nested_template));
            }
            continue;
        }

        if (const auto* class_template = dyn_cast<ClassTemplateDecl>(member.get())) {
            if (const auto* nested_record = class_template->record_decl();
                nested_record && !nested_record->name.empty()) {
                RecordSemanticState::NestedTemplate nested_template;
                nested_template.name = nested_record->name;
                nested_template.declared_access = current_access;
                nested_template.kind =
                    RecordSemanticState::NestedTemplateKind::Class;
                nested_template.decl = class_template;
                ctx.nested_templates.push_back(std::move(nested_template));
            }
            continue;
        }

        if (const auto* enum_decl = dyn_cast<EnumDecl>(member.get())) {
            if (!enum_decl->tag.empty()) {
                RecordSemanticState::NestedType nested_type;
                nested_type.name = enum_decl->tag;
                nested_type.type = QualType(enum_decl->get_enum_type());
                nested_type.declared_access = current_access;
                nested_type.decl = enum_decl;
                ctx.nested_types.push_back(std::move(nested_type));
            }
            if (!enum_decl->is_scoped()) {
                for (const auto& constant : enum_decl->constants) {
                    if (!constant) {
                        continue;
                    }
                    RecordSemanticState::EnumeratorMember enumerator_member;
                    enumerator_member.name = constant->name;
                    enumerator_member.declared_access = current_access;
                    enumerator_member.enum_decl = enum_decl;
                    enumerator_member.decl = constant.get();
                    enumerator_member.symbol = constant->sym;
                    ctx.enumerator_members.push_back(std::move(enumerator_member));
                }
            }
            continue;
        }

        auto* static_data_decl = dyn_cast<VariableDecl>(member.get());
        if (static_data_decl) {
            if (static_data_decl->storage_class != StorageClass::STATIC) {
                report_error(
                    "non-static class data members are not supported in variable declaration form",
                    static_data_decl->location);
            }
            if (static_data_decl->name.empty()) {
                report_error(
                    "static data member declaration requires an identifier",
                    static_data_decl->location);
            }
            if (!ctx.seen_static_data_member_names.insert(static_data_decl->name).second) {
                report_error(
                    "redefinition of static data member '" + ctx.tag + "::" +
                        static_data_decl->name + "'",
                    static_data_decl->location);
            }

            std::string static_member_prefix = ctx.tag;
            ensure_namespace_qualifier_prefix(static_member_prefix);
            VariableDeclFlags static_member_flags{
                static_data_decl->is_constexpr != 0,
                static_data_decl->is_inline != 0,
                false,
                true,
                false,
                static_data_decl->is_thread_local != 0,
                static_data_decl->is_block_byref != 0,
                false,
                false};
            bool is_definition_bearing_static_member =
                is_definition_bearing_variable_declaration(
                    StorageClass::STATIC,
                    static_member_flags,
                    static_data_decl->init.get());
            bool blocks_out_of_line_definition =
                is_definition_bearing_static_member &&
                !(static_data_decl->is_constexpr && !static_data_decl->is_inline);

            std::shared_ptr<Symbol> static_member_sym = static_data_decl->sym;
            if (!static_member_sym) {
                static_member_sym = std::make_shared<Symbol>(
                    static_data_decl->name,
                    SymbolKind::VARIABLE,
                    desugar_type(static_data_decl->type),
                    StorageClass::STATIC,
                    VariableLinkage::EXTERNAL,
                    static_data_decl->is_inline != 0);
                static_member_sym->is_constexpr = static_data_decl->is_constexpr;
                static_member_sym->set_language_linkage(
                    static_data_decl->get_language_linkage());
                static_member_sym->is_defined = blocks_out_of_line_definition;
                if (is_definition_bearing_static_member) {
                    static_member_sym->variable_definition = static_data_decl;
                }
                collect_add_global_symbol(static_member_sym);
                static_data_decl->sym = static_member_sym;
            } else {
                static_member_sym->type = desugar_type(static_data_decl->type);
                static_member_sym->storage_class = StorageClass::STATIC;
                static_member_sym->is_constexpr = static_data_decl->is_constexpr;
                if (static_data_decl->is_inline) {
                    static_member_sym->is_inline = true;
                } else {
                    static_member_sym->had_non_inline_declaration = true;
                }
                if (blocks_out_of_line_definition) {
                    static_member_sym->is_defined = true;
                }
                if (is_definition_bearing_static_member) {
                    static_member_sym->variable_definition = static_data_decl;
                }
                if (static_member_sym->get_language_linkage() ==
                    LanguageLinkage::None) {
                    static_member_sym->set_language_linkage(
                        static_data_decl->get_language_linkage());
                }
                if (static_member_sym->uid.empty()) {
                    collect_add_global_symbol(static_member_sym);
                }
            }
            set_symbol_cxx_qualifier_prefix(
                static_member_sym.get(),
                static_member_prefix);
            set_symbol_owner_record_type(
                static_member_sym.get(),
                QualType(ctx.record_type));

            if (ast_ctx_) {
                CppMemberDeclInfo member_info;
                member_info.declared_access = static_cast<uint8_t>(current_access);
                member_info.is_method = false;
                member_info.is_static = true;
                member_info.is_constructor = false;
                member_info.is_destructor = false;
                member_info.is_constexpr = static_data_decl->is_constexpr;
                ast_ctx_->set_cpp_member_decl_info(
                    static_data_decl->node_id,
                    member_info);
            }

            RecordSemanticState::StaticDataMember static_member;
            static_member.name = static_data_decl->name;
            static_member.type = static_data_decl->type;
            static_member.declared_access = current_access;
            static_member.decl = static_data_decl;
            static_member.symbol = std::move(static_member_sym);
            ctx.static_data_members.push_back(std::move(static_member));
            continue;
        }

        auto* field_decl = dyn_cast<FieldDecl>(member.get());
        if (field_decl) {
            QualType realized_field_type =
                realize_nested_record_member_type(field_decl->type);
            field_decl->type = realized_field_type;
            if (ast_ctx_) {
                CppMemberDeclInfo member_info;
                member_info.declared_access = static_cast<uint8_t>(current_access);
                member_info.is_method = false;
                member_info.is_static = false;
                member_info.is_constructor = false;
                member_info.is_destructor = false;
                ast_ctx_->set_cpp_member_decl_info(field_decl->node_id, member_info);
            }
            std::string alignment_error;
            SrcLoc alignment_error_loc = field_decl->location;
            size_t forced_alignment = collect_requested_alignment_from_attrs(
                *this,
                ast_ctx_.get(),
                field_decl->node_id,
                field_decl->location,
                &alignment_error,
                &alignment_error_loc);
            if (!alignment_error.empty()) {
                report_error(alignment_error, alignment_error_loc);
            }
            if (field_decl->is_bitfield()) {
                ctx.fields.emplace_back(
                    field_decl->name,
                    field_decl->type,
                    0,
                    0,
                    field_decl->bitfield_width,
                    0,
                    current_access);
                ctx.fields.back().forced_alignment = forced_alignment;
            } else {
                ctx.fields.emplace_back(
                    field_decl->name,
                    field_decl->type,
                    0,
                    current_access);
                ctx.fields.back().forced_alignment = forced_alignment;
            }
            bool requires_ctor_member_init =
                field_decl->type.is_const() ||
                canonical_type_kind(field_decl->type) == TypeKind::Reference;
            if (requires_ctor_member_init) {
                ctx.required_ctor_member_init_fields.push_back(field_decl);
            }
            continue;
        }

        auto* ctor_decl = dyn_cast<CppConstructorDecl>(member.get());
        if (ctor_decl) {
            std::string ctor_prefix;
            if (auto* existing_prefix = get_func_decl_cxx_qualifier_prefix(ctor_decl)) {
                ctor_prefix = *existing_prefix;
            }
            if (ctor_prefix.empty()) {
                ctor_prefix = ctx.tag;
            }
            ensure_namespace_qualifier_prefix(ctor_prefix);
            set_func_decl_cxx_qualifier_prefix(ctor_decl, ctor_prefix);
            set_func_decl_owner_record_type(ctor_decl, QualType(ctx.record_type));

            bool is_definition = function_decl_defines_entity(ctor_decl);
            bool ctor_is_delegating = false;
            for (const auto& mem_init : ctor_decl->ctor_initializers) {
                if (mem_init.is_delegating_initializer) {
                    ctor_is_delegating = true;
                    break;
                }
            }
            if (is_definition &&
                !ctor_is_delegating &&
                !ctx.required_ctor_member_init_fields.empty()) {
                std::unordered_set<std::string> ctor_initialized_members;
                ctor_initialized_members.reserve(ctor_decl->ctor_initializers.size());
                for (const auto& mem_init : ctor_decl->ctor_initializers) {
                    if (!mem_init.member_name.empty()) {
                        ctor_initialized_members.insert(mem_init.member_name);
                    }
                }
                for (const auto* required_field : ctx.required_ctor_member_init_fields) {
                    if (!required_field) {
                        continue;
                    }
                    std::string member_name =
                        required_field->name.empty() ? "<anonymous>" : required_field->name;
                    if (!required_field->name.empty() &&
                        ctor_initialized_members.contains(required_field->name)) {
                        continue;
                    }
                    report_error(
                        "constructor for '" + ctx.tag + "' must initialize member '" +
                            member_name +
                            "' (const/reference member initialization list is required)",
                        ctor_decl->location);
                }
            }
            auto ctor_sym = collect_declare_function_symbol(
                ctor_decl->name,
                ctor_decl->type,
                ctor_decl->storage_class,
                ctor_decl->is_constexpr,
                ctor_decl->is_inline,
                is_definition,
                ctor_decl->location,
                ctor_decl->get_language_linkage(),
                true,
                ctor_decl->is_deleted,
                ctor_decl->is_defaulted);
            collect_record_register_function_default_arguments(
                ctor_sym,
                ctor_decl,
                ctor_decl->location);
            if (ctor_sym) {
                set_symbol_cxx_qualifier_prefix(ctor_sym.get(), ctor_prefix);
                set_symbol_owner_record_type(
                    ctor_sym.get(),
                    QualType(ctx.record_type));
                if (ctor_decl->asm_label && !ctor_sym->asm_label.has_value()) {
                    ctor_sym->asm_label = *ctor_decl->asm_label;
                }
                if (is_definition) {
                    ctor_sym->function_definition = ctor_decl;
                }
            }

            if (ast_ctx_) {
                CppMemberDeclInfo member_info;
                member_info.declared_access = static_cast<uint8_t>(current_access);
                member_info.is_method = true;
                member_info.is_static = false;
                member_info.is_constructor = true;
                member_info.is_destructor = false;
                member_info.is_explicit = ctor_decl->is_explicit;
                member_info.is_constexpr = ctor_decl->is_constexpr;
                ast_ctx_->set_cpp_member_decl_info(ctor_decl->node_id, member_info);
            }

            RecordSemanticState::Constructor ctor;
            ctor.name = ctor_decl->name;
            ctor.type = ctor_decl->type;
            ctor.declared_access = current_access;
            ctor.is_implicit = false;
            ctor.is_explicit = ctor_decl->is_explicit;
            ctor.is_deleted = ctor_decl->is_deleted;
            ctor.decl = ctor_decl;
            ctor.symbol = std::move(ctor_sym);
            ctx.constructors.push_back(std::move(ctor));

            ctx.semantic_state.definition_data.has_user_declared_constructor = true;
            auto ctor_fn_type = dyn_cast_shared<FunctionType>(ctor_decl->type);
            if (ctor_fn_type) {
                const auto& ctor_state = ctx.constructors.back();
                CppConstructorUserParamInfo param_info =
                    cpp_compute_constructor_user_param_info(ctor_state);

                if (param_info.required_user_param_count == 0) {
                    ctx.semantic_state.definition_data.has_default_constructor = true;
                    if (ctor_decl->is_deleted) {
                        ctx.semantic_state.definition_data.default_constructor_is_deleted = true;
                    }
                } else if (param_info.max_user_param_count == 1 &&
                           param_info.user_param_start <
                               ctor_fn_type->parameters.size()) {
                    auto param_type = desugar_type(
                        ctor_fn_type->parameters[param_info.user_param_start]);
                    auto ref_type = param_type.as_shared<ReferenceType>();
                    if (ref_type && ref_type->referred_type) {
                        auto referred_record = desugar_type(
                            ref_type->referred_type).as_shared<ObjectType>();
                        if (referred_record && ctx.record_type &&
                            referred_record->get_decl() == ctx.record_type->get_decl()) {
                            if (ref_type->isRValueReference()) {
                                ctx.semantic_state.definition_data.has_move_constructor = true;
                            } else {
                                ctx.semantic_state.definition_data.has_copy_constructor = true;
                            }
                        }
                    }
                }
            }
            continue;
        }

        auto* dtor_decl = dyn_cast<CppDestructorDecl>(member.get());
        if (dtor_decl) {
            std::string dtor_prefix;
            if (auto* existing_prefix = get_func_decl_cxx_qualifier_prefix(dtor_decl)) {
                dtor_prefix = *existing_prefix;
            }
            if (dtor_prefix.empty()) {
                dtor_prefix = ctx.tag;
            }
            ensure_namespace_qualifier_prefix(dtor_prefix);
            set_func_decl_cxx_qualifier_prefix(dtor_decl, dtor_prefix);
            set_func_decl_owner_record_type(dtor_decl, QualType(ctx.record_type));

            bool is_definition = function_decl_defines_entity(dtor_decl);
            auto dtor_sym = collect_declare_function_symbol(
                dtor_decl->name,
                dtor_decl->type,
                dtor_decl->storage_class,
                dtor_decl->is_constexpr,
                dtor_decl->is_inline,
                is_definition,
                dtor_decl->location,
                dtor_decl->get_language_linkage(),
                true,
                dtor_decl->is_deleted,
                dtor_decl->is_defaulted);
            if (dtor_sym) {
                set_symbol_cxx_qualifier_prefix(dtor_sym.get(), dtor_prefix);
                set_symbol_owner_record_type(
                    dtor_sym.get(),
                    QualType(ctx.record_type));
                if (dtor_decl->asm_label && !dtor_sym->asm_label.has_value()) {
                    dtor_sym->asm_label = *dtor_decl->asm_label;
                }
                if (is_definition) {
                    dtor_sym->function_definition = dtor_decl;
                }
            }

            if (ast_ctx_) {
                CppMemberDeclInfo member_info;
                member_info.declared_access = static_cast<uint8_t>(current_access);
                member_info.is_method = true;
                member_info.is_static = false;
                member_info.is_constructor = false;
                member_info.is_destructor = true;
                member_info.is_virtual = dtor_decl->is_virtual;
                member_info.is_override = dtor_decl->is_override;
                member_info.is_final = dtor_decl->is_final;
                member_info.is_pure = dtor_decl->is_pure;
                member_info.is_constexpr = dtor_decl->is_constexpr;
                ast_ctx_->set_cpp_member_decl_info(dtor_decl->node_id, member_info);
            }

            RecordSemanticState::Destructor dtor;
            dtor.name = dtor_decl->name;
            dtor.type = dtor_decl->type;
            dtor.declared_access = current_access;
            dtor.is_implicit = false;
            dtor.is_defaulted = dtor_decl->is_defaulted;
            dtor.is_deleted = dtor_decl->is_deleted;
            dtor.is_virtual = dtor_decl->is_virtual;
            dtor.is_override = dtor_decl->is_override;
            dtor.is_final = dtor_decl->is_final;
            dtor.is_pure = dtor_decl->is_pure;
            dtor.decl = dtor_decl;
            dtor.symbol = std::move(dtor_sym);
            ctx.destructors.push_back(std::move(dtor));

            ctx.semantic_state.definition_data.has_user_declared_destructor = true;
            if (dtor_decl->is_deleted) {
                ctx.semantic_state.definition_data.has_deleted_destructor = true;
            }
            continue;
        }

        auto* method_decl = dyn_cast<CppMethodDecl>(member.get());
        if (const auto* method_template =
                dyn_cast<FunctionTemplateDecl>(member.get())) {
            auto* templated_function = method_template->function_decl();
            auto* templated_method =
                dyn_cast<CppMethodDecl>(templated_function);
            auto* templated_ctor =
                dyn_cast<CppConstructorDecl>(templated_function);
            if (!templated_method && !templated_ctor) {
                continue;
            }

            std::string method_prefix;
            if (auto* existing_prefix =
                    get_func_decl_cxx_qualifier_prefix(templated_function)) {
                method_prefix = *existing_prefix;
            }
            if (method_prefix.empty()) {
                method_prefix = ctx.tag;
            }
            ensure_namespace_qualifier_prefix(method_prefix);
            set_func_decl_cxx_qualifier_prefix(templated_function, method_prefix);
            set_func_decl_owner_record_type(
                templated_function,
                QualType(ctx.record_type));

            if (ast_ctx_) {
                CppMemberDeclInfo member_info;
                member_info.declared_access = static_cast<uint8_t>(current_access);
                member_info.is_method = true;
                member_info.is_static =
                    templated_method &&
                    templated_method->storage_class == StorageClass::STATIC;
                member_info.is_constructor = templated_ctor != nullptr;
                member_info.is_destructor = false;
                member_info.is_explicit = templated_ctor
                    ? templated_ctor->is_explicit
                    : templated_method->is_explicit_conversion;
                member_info.is_virtual =
                    templated_method ? templated_method->is_virtual : false;
                member_info.is_override =
                    templated_method ? templated_method->is_override : false;
                member_info.is_final =
                    templated_method ? templated_method->is_final : false;
                member_info.is_pure =
                    templated_method ? templated_method->is_pure : false;
                member_info.is_constexpr = templated_function->is_constexpr;
                ast_ctx_->set_cpp_member_decl_info(
                    templated_function->node_id,
                    member_info);
            }

            RecordSemanticState::MethodTemplate method_template_state;
            method_template_state.name = templated_function->name;
            method_template_state.declared_access = current_access;
            method_template_state.is_static =
                templated_method &&
                templated_method->storage_class == StorageClass::STATIC;
            method_template_state.decl = method_template;
            ctx.method_templates.push_back(std::move(method_template_state));
            if (templated_ctor) {
                ctx.semantic_state.definition_data.has_user_declared_constructor =
                    true;
            }
            continue;
        }
        if (!method_decl) {
            continue;
        }

        std::string method_prefix;
        if (auto* existing_prefix = get_func_decl_cxx_qualifier_prefix(method_decl)) {
            method_prefix = *existing_prefix;
        }
        if (method_prefix.empty()) {
            method_prefix = ctx.tag;
        }
        ensure_namespace_qualifier_prefix(method_prefix);
        set_func_decl_cxx_qualifier_prefix(method_decl, method_prefix);
        set_func_decl_owner_record_type(method_decl, QualType(ctx.record_type));

        bool is_static_method = method_decl->storage_class == StorageClass::STATIC;
        bool is_operator_new_delete =
            method_decl->name == "operatornew" ||
            method_decl->name == "operatornew[]" ||
            method_decl->name == "operatordelete" ||
            method_decl->name == "operatordelete[]";
        bool is_definition = function_decl_defines_entity(method_decl);
        auto method_sym = collect_declare_function_symbol(
            method_decl->name,
            method_decl->type,
            method_decl->storage_class,
            method_decl->is_constexpr,
            method_decl->is_inline,
            is_definition,
            method_decl->location,
            method_decl->get_language_linkage(),
            true,
            method_decl->is_deleted,
            method_decl->is_defaulted);
        collect_record_register_function_default_arguments(
            method_sym,
            method_decl,
            method_decl->location);
        if (method_sym) {
            set_symbol_cxx_qualifier_prefix(method_sym.get(), method_prefix);
            set_symbol_owner_record_type(
                method_sym.get(),
                QualType(ctx.record_type));
            if (method_decl->asm_label && !method_sym->asm_label.has_value()) {
                method_sym->asm_label = *method_decl->asm_label;
            }
            if (is_definition) {
                method_sym->function_definition = method_decl;
            }
        }

        if (ast_ctx_) {
            CppMemberDeclInfo member_info;
            member_info.declared_access = static_cast<uint8_t>(current_access);
            member_info.is_method = true;
            member_info.is_static = is_static_method || is_operator_new_delete;
            member_info.is_constructor = false;
            member_info.is_destructor = false;
            member_info.is_explicit = method_decl->is_explicit_conversion;
            member_info.is_virtual = method_decl->is_virtual;
            member_info.is_override = method_decl->is_override;
            member_info.is_final = method_decl->is_final;
            member_info.is_pure = method_decl->is_pure;
            member_info.is_constexpr = method_decl->is_constexpr;
            ast_ctx_->set_cpp_member_decl_info(method_decl->node_id, member_info);
        }

        RecordSemanticState::Method method;
        method.name = method_decl->name;
        method.type = method_decl->type;
        method.declared_access = current_access;
        method.is_implicit = false;
        method.is_static = is_static_method || is_operator_new_delete;
        method.is_deleted = method_decl->is_deleted;
        method.is_defaulted = method_decl->is_defaulted;
        method.is_explicit = method_decl->is_explicit_conversion;
        method.is_virtual = method_decl->is_virtual;
        method.is_override = method_decl->is_override;
        method.is_final = method_decl->is_final;
        method.is_pure = method_decl->is_pure;
        method.is_conversion_function = method_decl->is_conversion_function;
        method.conversion_target_type = method_decl->conversion_target_type;
        method.decl = method_decl;
        method.symbol = std::move(method_sym);
        ctx.methods.push_back(std::move(method));
    }
}

void Collect::collect_record_synthesize_implicit_members(
    CollectRecordBuildContext& ctx) const {
    if (!ctx.record_type) {
        return;
    }

    QualType owner_type(ctx.record_type);
    cpp_recompute_special_member_definition_data(
        ctx.semantic_state.definition_data,
        owner_type,
        ctx.constructors,
        ctx.methods,
        ctx.destructors,
        ast_ctx_.get());

    RecordSemanticState assignment_offset_state;
    assignment_offset_state.virtual_bases = ctx.virtual_bases;
    auto* mutable_self = const_cast<Collect*>(this);
    auto ensure_namespace_qualifier_prefix = [&](std::string& qualifier_prefix) {
        if (!lang_opts_.is_cxx_mode()) {
            return;
        }
        qualified_name_utils::ensure_namespace_qualifier_prefix_for_scope(
            collect_current_scope(),
            qualifier_prefix);
    };

    auto make_empty_compound_stmt = [&]() -> std::unique_ptr<Stmt> {
        return collect_make<CompoundStmt>(
            std::vector<std::unique_ptr<Stmt>>{},
            ctx.loc);
    };

    auto retain_synthesized_decl = [&](std::unique_ptr<Decl> decl) -> Decl* {
        if (!decl || !ast_ctx_) {
            return nullptr;
        }
        Decl* raw_decl = decl.get();
        ast_ctx_->retain_external_decl(std::move(decl));
        return raw_decl;
    };

    auto synthesize_implicit_constructor =
        [&](std::optional<ReferenceKind> source_ref_kind,
            bool is_deleted) {
        auto ctor_type = std::make_shared<FunctionType>();
        ctor_type->ret_type = QualType(get_builtin_void());
        ctor_type->is_variadic = false;
        ctor_type->has_prototype = true;

        QualType this_param_type(
            std::make_shared<PointerType>(owner_type));
        ctor_type->parameters.push_back(this_param_type);

        std::vector<std::unique_ptr<Decl>> parameters;
        parameters.push_back(collect_make<ParamDecl>(
            this_param_type,
            "__this",
            std::make_shared<Symbol>(
                "__this",
                SymbolKind::VARIABLE,
                this_param_type,
                StorageClass::NONE),
            StorageClass::NONE,
            ctx.loc));

        if (source_ref_kind.has_value()) {
            QualType rhs_record_type(owner_type.get_shared());
            if (*source_ref_kind == ReferenceKind::LValue) {
                rhs_record_type = rhs_record_type.with_const();
            }
            QualType rhs_param_type(std::make_shared<ReferenceType>(
                rhs_record_type,
                *source_ref_kind));
            ctor_type->parameters.push_back(rhs_param_type);
            parameters.push_back(collect_make<ParamDecl>(
                rhs_param_type,
                "__rhs",
                std::make_shared<Symbol>(
                    "__rhs",
                    SymbolKind::VARIABLE,
                    rhs_param_type,
                    StorageClass::NONE),
                StorageClass::NONE,
                ctx.loc));
        }

        auto ctor_decl = collect_make<CppConstructorDecl>(ctx.loc);
        ctor_decl->name = ctx.record_name;
        ctor_decl->type = ctor_type;
        ctor_decl->parameters = std::move(parameters);
        ctor_decl->body = make_empty_compound_stmt();
        ctor_decl->storage_class = StorageClass::NONE;
        ctor_decl->is_inline = true;
        ctor_decl->is_explicit = false;
        ctor_decl->is_deleted = is_deleted;
        ctor_decl->is_defaulted = true;
        ctor_decl->set_language_linkage(LanguageLinkage::CXX);

        std::string ctor_prefix = ctx.tag;
        ensure_namespace_qualifier_prefix(ctor_prefix);
        set_func_decl_cxx_qualifier_prefix(ctor_decl.get(), ctor_prefix);
        set_func_decl_owner_record_type(ctor_decl.get(), owner_type);

        std::shared_ptr<Symbol> ctor_sym = nullptr;
        if (source_ref_kind.has_value()) {
            ctor_sym = mutable_self->collect_declare_function_symbol(
                ctor_decl->name,
                QualType(ctor_decl->type),
                ctor_decl->storage_class,
                ctor_decl->is_constexpr,
                ctor_decl->is_inline,
                true,
                ctx.loc,
                ctor_decl->get_language_linkage(),
                true,
                ctor_decl->is_deleted,
                ctor_decl->is_defaulted);
            if (ctor_sym) {
                set_symbol_cxx_qualifier_prefix(ctor_sym.get(), ctor_prefix);
                set_symbol_owner_record_type(ctor_sym.get(), owner_type);
                ctor_sym->function_definition = ctor_decl.get();
            }
        }

        if (ast_ctx_) {
            CppMemberDeclInfo member_info;
            member_info.declared_access =
                static_cast<uint8_t>(CppAccessSpecifier::Public);
            member_info.is_method = true;
            member_info.is_static = false;
            member_info.is_constructor = true;
            member_info.is_destructor = false;
            ast_ctx_->set_cpp_member_decl_info(ctor_decl->node_id, member_info);
        }

        auto* retained_ctor_decl = static_cast<CppConstructorDecl*>(
            retain_synthesized_decl(std::move(ctor_decl)));

        RecordSemanticState::Constructor ctor;
        ctor.name = ctx.record_name;
        ctor.type = QualType(ctor_type);
        ctor.declared_access = RecordMemberAccess::Public;
        ctor.is_implicit = true;
        ctor.is_explicit = false;
        ctor.is_deleted = is_deleted;
        ctor.decl = retained_ctor_decl;
        ctor.symbol = std::move(ctor_sym);
        ctx.constructors.push_back(std::move(ctor));
    };

    auto synthesize_implicit_assignment =
        [&](ReferenceKind rhs_ref_kind,
            bool is_deleted) {
        auto method_type = std::make_shared<FunctionType>();
        method_type->ret_type = QualType(std::make_shared<ReferenceType>(
            owner_type,
            ReferenceKind::LValue));
        method_type->is_variadic = false;
        method_type->has_prototype = true;

        QualType this_param_type(
            std::make_shared<PointerType>(owner_type));
        QualType rhs_record_type(owner_type.get_shared());
        if (rhs_ref_kind == ReferenceKind::LValue) {
            rhs_record_type = rhs_record_type.with_const();
        }
        QualType rhs_param_type(std::make_shared<ReferenceType>(
            rhs_record_type,
            rhs_ref_kind));

        method_type->parameters.push_back(this_param_type);
        method_type->parameters.push_back(rhs_param_type);

        std::vector<std::unique_ptr<Decl>> parameters;
        parameters.push_back(collect_make<ParamDecl>(
            this_param_type,
            "__this",
            std::make_shared<Symbol>(
                "__this",
                SymbolKind::VARIABLE,
                this_param_type,
                StorageClass::NONE),
            StorageClass::NONE,
            ctx.loc));
        parameters.push_back(collect_make<ParamDecl>(
            rhs_param_type,
            "__rhs",
            std::make_shared<Symbol>(
                "__rhs",
                SymbolKind::VARIABLE,
                rhs_param_type,
                StorageClass::NONE),
            StorageClass::NONE,
            ctx.loc));

        auto method_decl = collect_make<CppMethodDecl>(ctx.loc);
        method_decl->name = "operator=";
        method_decl->type = method_type;
        method_decl->parameters = std::move(parameters);
        method_decl->storage_class = StorageClass::NONE;
        method_decl->is_inline = true;
        method_decl->is_deleted = is_deleted;
        method_decl->is_defaulted = true;
        method_decl->set_language_linkage(LanguageLinkage::CXX);

        std::string method_prefix = ctx.tag;
        ensure_namespace_qualifier_prefix(method_prefix);
        set_func_decl_cxx_qualifier_prefix(method_decl.get(), method_prefix);
        set_func_decl_owner_record_type(method_decl.get(), owner_type);

        auto method_sym = mutable_self->collect_declare_function_symbol(
            method_decl->name,
            QualType(method_decl->type),
            method_decl->storage_class,
            method_decl->is_constexpr,
            method_decl->is_inline,
            true,
            ctx.loc,
            method_decl->get_language_linkage(),
            true,
            method_decl->is_deleted,
            method_decl->is_defaulted);
        if (method_sym) {
            set_symbol_cxx_qualifier_prefix(method_sym.get(), method_prefix);
            set_symbol_owner_record_type(method_sym.get(), owner_type);
            method_sym->function_definition = method_decl.get();
        }

        if (ast_ctx_) {
            CppMemberDeclInfo member_info;
            member_info.declared_access =
                static_cast<uint8_t>(CppAccessSpecifier::Public);
            member_info.is_method = true;
            member_info.is_static = false;
            member_info.is_constructor = false;
            member_info.is_destructor = false;
            ast_ctx_->set_cpp_member_decl_info(method_decl->node_id, member_info);
        }

        auto* retained_method_decl = static_cast<CppMethodDecl*>(
            retain_synthesized_decl(std::move(method_decl)));

        RecordSemanticState::Method method;
        method.name = "operator=";
        method.type = QualType(method_type);
        method.declared_access = RecordMemberAccess::Public;
        method.is_implicit = true;
        method.is_static = false;
        method.is_deleted = is_deleted;
        method.is_defaulted = true;
        method.is_explicit = false;
        method.is_virtual = false;
        method.is_override = false;
        method.is_final = false;
        method.is_pure = false;
        method.is_conversion_function = false;
        method.conversion_target_type = nullptr;
        method.decl = retained_method_decl;
        method.symbol = std::move(method_sym);
        ctx.methods.push_back(std::move(method));
    };

    if (!ctx.semantic_state.definition_data.has_user_declared_constructor) {
        bool implicit_default_ctor_deleted = false;

        for (const auto& field : ctx.fields) {
            if (field.type.is_const() ||
                canonical_type_kind(field.type) == TypeKind::Reference) {
                implicit_default_ctor_deleted = true;
                break;
            }
        }

        if (!implicit_default_ctor_deleted) {
            for (const auto& base : ctx.bases) {
                if (!base.type ||
                    canonical_type_kind(base.type) != TypeKind::Object) {
                    continue;
                }
                const RecordSemanticState* base_state =
                    record_semantics_cache_lookup(base.record_decl);
                if (!cpp_record_has_viable_default_constructor(
                        base_state,
                        true)) {
                    implicit_default_ctor_deleted = true;
                    break;
                }
            }
        }

        if (!implicit_default_ctor_deleted) {
            for (const auto& virtual_base : ctx.virtual_bases) {
                if (!virtual_base.type ||
                    canonical_type_kind(virtual_base.type) != TypeKind::Object) {
                    continue;
                }
                const RecordSemanticState* virtual_base_state =
                    record_semantics_cache_lookup(virtual_base.record_decl);
                if (!cpp_record_has_viable_default_constructor(
                        virtual_base_state,
                        true)) {
                    implicit_default_ctor_deleted = true;
                    break;
                }
            }
        }

        if (!implicit_default_ctor_deleted) {
            for (const auto& field : ctx.fields) {
                auto field_record =
                    desugar_type(field.type).as_shared<ObjectType>();
                if (!field_record) {
                    continue;
                }
                const ObjectDecl* field_decl =
                    canonical_cpp_record_decl(
                        dyn_cast<ObjectDecl>(field_record->get_decl()));
                const RecordSemanticState* field_state =
                    field_decl ? record_semantics_cache_lookup(field_decl) : nullptr;
                if (!cpp_record_has_viable_default_constructor(
                        field_state,
                        false)) {
                    implicit_default_ctor_deleted = true;
                    break;
                }
            }
        }

        synthesize_implicit_constructor(std::nullopt, implicit_default_ctor_deleted);
    }

    if (!ctx.semantic_state.definition_data.has_user_declared_destructor) {
        bool implicit_destructor_deleted = false;
        for (const auto& base : ctx.bases) {
            if (!base.type ||
                canonical_type_kind(base.type) != TypeKind::Object) {
                continue;
            }
            const RecordSemanticState* base_state =
                record_semantics_cache_lookup(base.record_decl);
            if (!cpp_record_has_viable_destructor(base_state, true)) {
                implicit_destructor_deleted = true;
                break;
            }
        }

        if (!implicit_destructor_deleted) {
            for (const auto& virtual_base : ctx.virtual_bases) {
                if (!virtual_base.type ||
                    canonical_type_kind(virtual_base.type) != TypeKind::Object) {
                    continue;
                }
                const RecordSemanticState* virtual_base_state =
                    record_semantics_cache_lookup(virtual_base.record_decl);
                if (!cpp_record_has_viable_destructor(
                        virtual_base_state,
                        true)) {
                    implicit_destructor_deleted = true;
                    break;
                }
            }
        }

        if (!implicit_destructor_deleted) {
            for (const auto& field : ctx.fields) {
                auto field_record =
                    desugar_type(field.type).as_shared<ObjectType>();
                if (!field_record) {
                    continue;
                }
                const ObjectDecl* field_decl =
                    canonical_cpp_record_decl(
                        dyn_cast<ObjectDecl>(field_record->get_decl()));
                const RecordSemanticState* field_state =
                    field_decl ? record_semantics_cache_lookup(field_decl) : nullptr;
                if (!cpp_record_has_viable_destructor(field_state, false)) {
                    implicit_destructor_deleted = true;
                    break;
                }
            }
        }

        auto implicit_dtor_type = std::make_shared<FunctionType>();
        implicit_dtor_type->ret_type = QualType(get_builtin_void());
        implicit_dtor_type->is_variadic = false;
        implicit_dtor_type->has_prototype = true;
        QualType this_param_type(
            std::make_shared<PointerType>(QualType(ctx.record_type)));
        implicit_dtor_type->parameters.push_back(this_param_type);

        RecordSemanticState::Destructor implicit_dtor;
        implicit_dtor.name = "~" + ctx.record_name;
        implicit_dtor.type = QualType(implicit_dtor_type);
        implicit_dtor.declared_access = RecordMemberAccess::Public;
        implicit_dtor.is_implicit = true;
        implicit_dtor.is_defaulted = false;
        implicit_dtor.is_deleted = implicit_destructor_deleted;
        implicit_dtor.is_virtual = false;
        implicit_dtor.is_override = false;
        implicit_dtor.is_final = false;
        implicit_dtor.is_pure = false;
        implicit_dtor.decl = nullptr;
        implicit_dtor.symbol = nullptr;
        ctx.destructors.push_back(std::move(implicit_dtor));

        if (implicit_destructor_deleted) {
            ctx.semantic_state.definition_data.has_deleted_destructor = true;
        }
    }

    if (!ctx.semantic_state.definition_data.has_user_declared_copy_constructor) {
        bool implicit_copy_ctor_deleted =
            ctx.semantic_state.definition_data.has_user_declared_move_constructor ||
            ctx.semantic_state.definition_data.has_user_declared_move_assignment;
        if (!implicit_copy_ctor_deleted) {
            for (const auto& base : ctx.bases) {
                if (!type_supports_generated_copy_construction(
                        base.type, ast_ctx_.get())) {
                    implicit_copy_ctor_deleted = true;
                    break;
                }
            }
        }
        if (!implicit_copy_ctor_deleted) {
            for (const auto& field : ctx.fields) {
                if (field.is_base_subobject || field.is_virtual_base_storage) {
                    continue;
                }
                if (!type_supports_generated_copy_construction(
                        field.type, ast_ctx_.get())) {
                    implicit_copy_ctor_deleted = true;
                    break;
                }
            }
        }
        synthesize_implicit_constructor(
            ReferenceKind::LValue,
            implicit_copy_ctor_deleted);
    }

    if (!ctx.semantic_state.definition_data.has_user_declared_move_constructor &&
        !ctx.semantic_state.definition_data.has_user_declared_copy_constructor &&
        !ctx.semantic_state.definition_data.has_user_declared_copy_assignment &&
        !ctx.semantic_state.definition_data.has_user_declared_move_assignment &&
        !ctx.semantic_state.definition_data.has_user_declared_destructor) {
        bool implicit_move_ctor_deleted = false;
        for (const auto& base : ctx.bases) {
            if (!type_supports_generated_move_construction(
                    base.type, ast_ctx_.get())) {
                implicit_move_ctor_deleted = true;
                break;
            }
        }
        if (!implicit_move_ctor_deleted) {
            for (const auto& field : ctx.fields) {
                if (field.is_base_subobject || field.is_virtual_base_storage) {
                    continue;
                }
                if (!type_supports_generated_move_construction(
                        field.type, ast_ctx_.get())) {
                    implicit_move_ctor_deleted = true;
                    break;
                }
            }
        }
        synthesize_implicit_constructor(
            ReferenceKind::RValue,
            implicit_move_ctor_deleted);
    }

    if (!ctx.semantic_state.definition_data.has_user_declared_copy_assignment) {
        bool implicit_copy_assignment_deleted =
            ctx.semantic_state.definition_data.has_user_declared_move_constructor ||
            ctx.semantic_state.definition_data.has_user_declared_move_assignment;
        if (!implicit_copy_assignment_deleted) {
            for (const auto& base : ctx.bases) {
                if (!type_supports_generated_copy_assignment(
                        base.type, ast_ctx_.get()) ||
                    !find_direct_base_assignment_offset(assignment_offset_state, base)
                         .has_value()) {
                    implicit_copy_assignment_deleted = true;
                    break;
                }
            }
        }
        if (!implicit_copy_assignment_deleted) {
            for (const auto& field : ctx.fields) {
                if (field.is_base_subobject || field.is_virtual_base_storage) {
                    continue;
                }
                if (!type_supports_generated_copy_assignment(
                        field.type, ast_ctx_.get())) {
                    implicit_copy_assignment_deleted = true;
                    break;
                }
                if (field.name.empty()) {
                    implicit_copy_assignment_deleted = true;
                    break;
                }
            }
        }
        synthesize_implicit_assignment(
            ReferenceKind::LValue,
            implicit_copy_assignment_deleted);
    }

    if (!ctx.semantic_state.definition_data.has_user_declared_move_assignment &&
        !ctx.semantic_state.definition_data.has_user_declared_copy_constructor &&
        !ctx.semantic_state.definition_data.has_user_declared_move_constructor &&
        !ctx.semantic_state.definition_data.has_user_declared_copy_assignment &&
        !ctx.semantic_state.definition_data.has_user_declared_destructor) {
        bool implicit_move_assignment_deleted = false;
        for (const auto& base : ctx.bases) {
            if (!type_supports_generated_move_assignment(
                    base.type, ast_ctx_.get()) ||
                !find_direct_base_assignment_offset(assignment_offset_state, base)
                     .has_value()) {
                implicit_move_assignment_deleted = true;
                break;
            }
        }
        if (!implicit_move_assignment_deleted) {
            for (const auto& field : ctx.fields) {
                if (field.is_base_subobject || field.is_virtual_base_storage) {
                    continue;
                }
                if (!type_supports_generated_move_assignment(
                        field.type, ast_ctx_.get())) {
                    implicit_move_assignment_deleted = true;
                    break;
                }
                if (field.name.empty()) {
                    implicit_move_assignment_deleted = true;
                    break;
                }
            }
        }
        synthesize_implicit_assignment(
            ReferenceKind::RValue,
            implicit_move_assignment_deleted);
    }

    cpp_recompute_special_member_definition_data(
        ctx.semantic_state.definition_data,
        owner_type,
        ctx.constructors,
        ctx.methods,
        ctx.destructors,
        ast_ctx_.get());
}

void Collect::collect_record_materialize_defaulted_method_bodies(
    CollectRecordBuildContext& ctx) {
    if (!ctx.semantic_decl) {
        return;
    }

    RecordSemanticState owner_state = ctx.semantic_state;
    owner_state.bases = ctx.bases;
    owner_state.virtual_bases = ctx.virtual_bases;
    owner_state.fields = ctx.semantic_state.fields;
    owner_state.methods = ctx.methods;
    owner_state.method_templates = ctx.method_templates;
    owner_state.static_data_members = ctx.static_data_members;
    owner_state.nested_types = ctx.nested_types;
    owner_state.nested_templates = ctx.nested_templates;
    owner_state.enumerator_members = ctx.enumerator_members;
    owner_state.constructors = ctx.constructors;
    owner_state.destructors = ctx.destructors;

    // Defaulted method synthesis uses normal Collect expression helpers like
    // `this->field` and base-subobject access. Those helpers consult the
    // record-semantics cache to decide whether the current record type is
    // complete. Publish the computed in-progress state first so synthesis can
    // see the record as complete before the final state is moved into place.
    auto publish_owner_state = [&]() {
        query_publish_record_semantics(ctx.semantic_decl, owner_state);
        if (const ObjectDecl* canonical_decl =
                canonical_cpp_record_decl(ctx.semantic_decl);
            canonical_decl && canonical_decl != ctx.semantic_decl) {
            query_publish_record_semantics(canonical_decl, owner_state);
        }
    };
    publish_owner_state();

    for (auto& ctor : ctx.constructors) {
        auto* ctor_decl =
            const_cast<CppConstructorDecl*>(ctor.decl);
        if (!ctor_decl || !ctor_decl->is_defaulted) {
            continue;
        }

        bool materialized = collect_materialize_defaulted_constructor(
            ctor_decl,
            ctx.semantic_decl,
            owner_state);
        if (!materialized) {
            continue;
        }

        ctor.is_deleted = ctor_decl->is_deleted;
        if (ctor.symbol) {
            ctor.symbol->is_deleted = ctor_decl->is_deleted;
            ctor.symbol->is_defined =
                ctor_decl->body != nullptr || ctor_decl->is_deleted;
            ctor.symbol->function_definition = ctor_decl;
        }

        for (auto& cached_ctor : owner_state.constructors) {
            if (cached_ctor.decl != ctor_decl) {
                continue;
            }
            cached_ctor.is_deleted = ctor_decl->is_deleted;
            if (ctor.symbol) {
                cached_ctor.symbol = ctor.symbol;
            }
            break;
        }
        publish_owner_state();
    }

    for (auto& method : ctx.methods) {
        auto* method_decl =
            const_cast<CppMethodDecl*>(method.decl);
        if (!method_decl || !method_decl->is_defaulted) {
            continue;
        }

        bool materialized = false;
        if (collect_materialize_defaulted_copy_assignment_body(
                method_decl,
                ctx.semantic_decl,
                owner_state)) {
            materialized = true;
        } else if (collect_materialize_defaulted_move_assignment_body(
                       method_decl,
                       ctx.semantic_decl,
                       owner_state)) {
            materialized = true;
        }
        if (!materialized) {
            continue;
        }

        method.is_deleted = method_decl->is_deleted;
        if (method.symbol) {
            method.symbol->is_deleted = method_decl->is_deleted;
            method.symbol->is_defined =
                method_decl->body != nullptr || method_decl->is_deleted;
            method.symbol->function_definition = method_decl;
        }

        for (auto& cached_method : owner_state.methods) {
            if (cached_method.decl != method_decl) {
                continue;
            }
            cached_method.is_deleted = method_decl->is_deleted;
            if (method.symbol) {
                cached_method.symbol = method.symbol;
            }
            break;
        }
        publish_owner_state();
    }

    cpp_recompute_special_member_definition_data(
        ctx.semantic_state.definition_data,
        QualType(ctx.record_type),
        ctx.constructors,
        ctx.methods,
        ctx.destructors,
        ast_ctx_.get());
}

bool Collect::collect_materialize_defaulted_constructor(
    CppConstructorDecl* ctor_decl,
    const ObjectDecl* owner_record_decl,
    const RecordSemanticState& owner_state) {
    if (!ctor_decl || !owner_record_decl || !ctor_decl->is_defaulted) {
        return false;
    }

    RecordSemanticState::Constructor ctor_state;
    ctor_state.type = QualType(ctor_decl->type);
    QualType owner_type(owner_record_decl->get_record_type());
    bool use_move = false;
    if (cpp_constructor_is_move_constructor(
            ctor_state,
            owner_type,
            ast_ctx_.get())) {
        use_move = true;
    } else if (!cpp_constructor_is_copy_constructor(
                   ctor_state,
                   owner_type,
                   ast_ctx_.get())) {
        return false;
    }

    auto* rhs_param =
        ctor_decl->parameters.size() > 1
            ? dyn_cast<ParamDecl>(ctor_decl->parameters[1].get())
            : nullptr;
    if (!rhs_param) {
        ctor_decl->is_deleted = true;
        ctor_decl->body.reset();
        ctor_decl->ctor_initializers.clear();
        return true;
    }

    if (!owner_state.is_incomplete) {
        for (const auto& base : owner_state.bases) {
            bool supported = use_move
                ? type_supports_generated_move_construction(
                      base.type,
                      ast_ctx_.get())
                : type_supports_generated_copy_construction(
                      base.type,
                      ast_ctx_.get());
            if (!supported) {
                ctor_decl->is_deleted = true;
                ctor_decl->body.reset();
                ctor_decl->ctor_initializers.clear();
                return true;
            }
        }
        for (const auto& field : owner_state.fields) {
            if (field.is_base_subobject || field.is_virtual_base_storage) {
                continue;
            }
            bool supported = use_move
                ? type_supports_generated_move_construction(
                      field.type,
                      ast_ctx_.get())
                : type_supports_generated_copy_construction(
                      field.type,
                      ast_ctx_.get());
            if (!supported) {
                ctor_decl->is_deleted = true;
                ctor_decl->body.reset();
                ctor_decl->ctor_initializers.clear();
                return true;
            }
            if (field.name.empty() &&
                canonical_type_kind(field.type, ast_ctx_.get()) !=
                    TypeKind::Array) {
                ctor_decl->is_deleted = true;
                ctor_decl->body.reset();
                ctor_decl->ctor_initializers.clear();
                return true;
            }
        }
    }

    std::vector<CppCtorInitializer> synthesized_initializers;
    std::vector<std::unique_ptr<Stmt>> union_body_statements;
    auto char_type = get_builtin_char();
    auto ulong_type = get_builtin_ulong();
    bool build_ok = with_function_definition_state(
        ctor_decl,
        [&]() {
            auto make_rhs_ref = [&]() -> std::unique_ptr<Expr> {
                return make_param_reference_expr(
                    *this,
                    rhs_param,
                    "__rhs",
                    ctor_decl->location);
            };

            auto make_this_expr = [&]() -> std::unique_ptr<Expr> {
                uint8_t pointee_quals = QUAL_NONE;
                if (auto function_type =
                        QualType(ctor_decl->type).as_shared<FunctionType>();
                    function_type && !function_type->parameters.empty()) {
                    if (auto this_ptr =
                            function_type->parameters.front().as_shared<PointerType>()) {
                        pointee_quals = this_ptr->pointed_type.get_qualifiers();
                    }
                }
                QualType qualified_owner(
                    owner_type.get_shared(),
                    static_cast<uint8_t>(
                        owner_type.get_qualifiers() | pointee_quals));
                QualType this_type(
                    std::make_shared<PointerType>(qualified_owner));
                return collect_make<CppThisExpr>(this_type, ctor_decl->location);
            };

            auto make_this_deref = [&]() -> std::unique_ptr<Expr> {
                auto this_expr = make_this_expr();
                if (!this_expr) {
                    return nullptr;
                }
                return collect_unary_operation(
                    UnaryOpTypes::DEREFERENCE,
                    std::move(this_expr),
                    ctor_decl->location);
            };

            if (owner_record_decl->get_record_type() &&
                owner_record_decl->get_record_type()->is_union) {
                auto lhs = make_this_deref();
                auto rhs = make_rhs_ref();
                if (!lhs || !rhs) {
                    return false;
                }
                if (use_move) {
                    rhs = maybe_materialize_generated_move_source(
                        *this,
                        owner_type,
                        ast_ctx_.get(),
                        std::move(rhs),
                        ctor_decl->location);
                    if (!rhs) {
                        return false;
                    }
                }
                auto assignment = collect_make<BinaryOperation>(
                    std::move(lhs),
                    std::move(rhs),
                    BinOpTypes::ASSIGN);
                assignment->location = ctor_decl->location;
                assignment->ctype = owner_type;
                union_body_statements.push_back(
                    collect_expression_statement(
                        std::move(assignment),
                        ctor_decl->location));
                return true;
            }

            for (const auto& base : owner_state.bases) {
                auto maybe_offset =
                    find_direct_base_assignment_offset(owner_state, base);
                if (!maybe_offset.has_value()) {
                    return false;
                }
                auto base_source_builder =
                    [this,
                     &make_rhs_ref,
                     ctor_decl,
                     char_type,
                     ulong_type,
                     base_type = base.type,
                     offset = *maybe_offset]() {
                    auto rhs_ref = make_rhs_ref();
                    if (!rhs_ref) {
                        return std::unique_ptr<Expr>();
                    }
                    auto rhs_addr = collect_unary_operation(
                        UnaryOpTypes::ADDRESS_OF,
                        std::move(rhs_ref),
                        ctor_decl->location);
                    return make_base_subobject_expr(
                        *this,
                        ast_ctx_.get(),
                        char_type,
                        ulong_type,
                        std::move(rhs_addr),
                        base_type,
                        offset,
                        ctor_decl->location);
                };
                auto init_expr = build_generated_constructor_initializer_expr(
                    *this,
                    ast_ctx_.get(),
                    ulong_type,
                    base.type,
                    use_move,
                    base_source_builder,
                    ctor_decl->location);
                if (!init_expr || isa<ErrorExpr>(init_expr.get())) {
                    return false;
                }
                CppCtorInitializer base_init;
                base_init.member_name = base.name;
                base_init.is_base_initializer = true;
                base_init.location = ctor_decl->location;
                base_init.init_expr = std::move(init_expr);
                synthesized_initializers.push_back(std::move(base_init));
            }

            for (const auto& field : owner_state.fields) {
                if (field.is_base_subobject || field.is_virtual_base_storage) {
                    continue;
                }
                if (field.name.empty()) {
                    return false;
                }
                auto field_source_builder =
                    [this,
                     &make_rhs_ref,
                     ctor_decl,
                     field_name = field.name]() {
                    auto rhs_ref = make_rhs_ref();
                    if (!rhs_ref) {
                        return std::unique_ptr<Expr>();
                    }
                    return collect_member_expression(
                        std::move(rhs_ref),
                        field_name,
                        false,
                        ctor_decl->location);
                };
                auto init_expr = build_generated_constructor_initializer_expr(
                    *this,
                    ast_ctx_.get(),
                    ulong_type,
                    field.type,
                    use_move,
                    field_source_builder,
                    ctor_decl->location);
                if (!init_expr || isa<ErrorExpr>(init_expr.get())) {
                    return false;
                }
                CppCtorInitializer field_init;
                field_init.member_name = field.name;
                field_init.location = ctor_decl->location;
                field_init.member_expr = collect_member_expression(
                    make_this_expr(),
                    field.name,
                    true,
                    ctor_decl->location);
                if (!field_init.member_expr ||
                    isa<ErrorExpr>(field_init.member_expr.get())) {
                    return false;
                }
                field_init.init_expr = std::move(init_expr);
                synthesized_initializers.push_back(std::move(field_init));
            }

            return true;
        });

    if (!build_ok) {
        ctor_decl->is_deleted = true;
        ctor_decl->body.reset();
        ctor_decl->ctor_initializers.clear();
        return true;
    }

    ctor_decl->ctor_initializers = std::move(synthesized_initializers);
    if (owner_record_decl->get_record_type() &&
        owner_record_decl->get_record_type()->is_union) {
        auto body_stmt = collect_compound_statement(
            std::move(union_body_statements),
            ctor_decl->scope,
            ctor_decl->location);
        ctor_decl->body = std::unique_ptr<CompoundStmt>(
            dyn_cast<CompoundStmt>(body_stmt.release()));
        return ctor_decl->body != nullptr;
    }

    if (!ctor_decl->body) {
        ctor_decl->body = std::unique_ptr<Stmt>(
            collect_make<CompoundStmt>(
                std::vector<std::unique_ptr<Stmt>>{},
                ctor_decl->location)
                .release());
    }
    return true;
}

bool Collect::collect_materialize_defaulted_assignment_body(
    CppMethodDecl* method_decl,
    const ObjectDecl* owner_record_decl,
    const RecordSemanticState& owner_state,
    bool use_move) {
    if (!method_decl || !owner_record_decl || !method_decl->is_defaulted) {
        return false;
    }
    if (method_decl->body || method_decl->is_deleted) {
        return true;
    }

    QualType owner_type(owner_record_decl->get_record_type());
    RecordSemanticState::Method method_state;
    method_state.name = method_decl->name;
    method_state.type = QualType(method_decl->type);
    bool matches = use_move
        ? cpp_method_is_move_assignment(
              method_state,
              owner_type,
              ast_ctx_.get())
        : cpp_method_is_copy_assignment(
              method_state,
              owner_type,
              ast_ctx_.get());
    if (!matches) {
        return false;
    }

    auto* rhs_param =
        method_decl->parameters.size() > 1
            ? dyn_cast<ParamDecl>(method_decl->parameters[1].get())
            : nullptr;
    if (!rhs_param) {
        method_decl->is_deleted = true;
        method_decl->body.reset();
        return true;
    }

    if (!owner_state.is_incomplete) {
        for (const auto& base : owner_state.bases) {
            bool supported = use_move
                ? type_supports_generated_move_assignment(
                      base.type,
                      ast_ctx_.get())
                : type_supports_generated_copy_assignment(
                      base.type,
                      ast_ctx_.get());
            if (!supported) {
                method_decl->is_deleted = true;
                method_decl->body.reset();
                return true;
            }
            if (!find_direct_base_assignment_offset(owner_state, base).has_value()) {
                method_decl->is_deleted = true;
                method_decl->body.reset();
                return true;
            }
        }
        for (const auto& field : owner_state.fields) {
            if (field.is_base_subobject || field.is_virtual_base_storage) {
                continue;
            }
            bool supported = use_move
                ? type_supports_generated_move_assignment(
                      field.type,
                      ast_ctx_.get())
                : type_supports_generated_copy_assignment(
                      field.type,
                      ast_ctx_.get());
            if (!supported) {
                method_decl->is_deleted = true;
                method_decl->body.reset();
                return true;
            }
            if (field.name.empty()) {
                method_decl->is_deleted = true;
                method_decl->body.reset();
                return true;
            }
        }
    }

    std::vector<std::unique_ptr<Stmt>> body_statements;
    auto char_type = get_builtin_char();
    auto ulong_type = get_builtin_ulong();
    bool build_ok = with_function_definition_state(
        method_decl,
        [&]() {
            auto make_semantic_this_expr = [&]() -> std::unique_ptr<Expr> {
                uint8_t pointee_quals = QUAL_NONE;
                if (auto function_type =
                        QualType(method_decl->type).as_shared<FunctionType>();
                    function_type && !function_type->parameters.empty()) {
                    if (auto this_ptr =
                            function_type->parameters.front().as_shared<PointerType>()) {
                        pointee_quals = this_ptr->pointed_type.get_qualifiers();
                    }
                }
                QualType qualified_owner(
                    owner_type.get_shared(),
                    static_cast<uint8_t>(
                        owner_type.get_qualifiers() | pointee_quals));
                QualType this_type(
                    std::make_shared<PointerType>(qualified_owner));
                return collect_make<CppThisExpr>(this_type, method_decl->location);
            };

            auto make_this_deref = [&]() -> std::unique_ptr<Expr> {
                auto this_expr = make_semantic_this_expr();
                if (!this_expr) {
                    return nullptr;
                }
                return collect_unary_operation(
                    UnaryOpTypes::DEREFERENCE,
                    std::move(this_expr),
                    method_decl->location);
            };

            auto make_raw_record_assignment =
                [&]() -> std::unique_ptr<Expr> {
                auto lhs = make_this_deref();
                auto rhs = make_param_reference_expr(
                    *this, rhs_param, "__rhs", method_decl->location);
                if (!lhs || !rhs) {
                    return nullptr;
                }
                if (use_move) {
                    rhs = maybe_materialize_generated_move_source(
                        *this,
                        owner_type,
                        ast_ctx_.get(),
                        std::move(rhs),
                        method_decl->location);
                    if (!rhs) {
                        return nullptr;
                    }
                }
                auto assignment = collect_make<BinaryOperation>(
                    std::move(lhs),
                    std::move(rhs),
                    BinOpTypes::ASSIGN);
                assignment->location = method_decl->location;
                assignment->ctype = owner_type;
                return assignment;
            };

            if (owner_record_decl->get_record_type() &&
                owner_record_decl->get_record_type()->is_union) {
                auto assignment = make_raw_record_assignment();
                if (!assignment) {
                    return false;
                }
                body_statements.push_back(
                    collect_expression_statement(
                        std::move(assignment),
                        method_decl->location));
            } else {
                for (const auto& base : owner_state.bases) {
                    auto maybe_offset =
                        find_direct_base_assignment_offset(owner_state, base);
                    if (!maybe_offset.has_value()) {
                        return false;
                    }
                    auto lhs_builder =
                        [this,
                         &make_semantic_this_expr,
                         method_decl,
                         char_type,
                         ulong_type,
                         base_type = base.type,
                         offset = *maybe_offset]() {
                        return make_base_subobject_expr(
                            *this,
                            ast_ctx_.get(),
                            char_type,
                            ulong_type,
                            make_semantic_this_expr(),
                            base_type,
                            offset,
                            method_decl->location);
                    };
                    auto rhs_builder =
                        [this,
                         rhs_param,
                         method_decl,
                         char_type,
                         ulong_type,
                         base_type = base.type,
                         offset = *maybe_offset]() {
                        auto rhs_ref = make_param_reference_expr(
                            *this, rhs_param, "__rhs", method_decl->location);
                        if (!rhs_ref) {
                            return std::unique_ptr<Expr>();
                        }
                        auto rhs_addr = collect_unary_operation(
                            UnaryOpTypes::ADDRESS_OF,
                            std::move(rhs_ref),
                            method_decl->location);
                        return make_base_subobject_expr(
                            *this,
                            ast_ctx_.get(),
                            char_type,
                            ulong_type,
                            std::move(rhs_addr),
                            base_type,
                            offset,
                            method_decl->location);
                    };
                    if (!emit_generated_assignment_statements_for_type(
                            *this,
                            ast_ctx_.get(),
                            ulong_type,
                            base.type,
                            use_move,
                            lhs_builder,
                            rhs_builder,
                            body_statements,
                            method_decl->location)) {
                        return false;
                    }
                }

                for (const auto& field : owner_state.fields) {
                    if (field.is_base_subobject || field.is_virtual_base_storage) {
                        continue;
                    }
                    if (field.name.empty()) {
                        return false;
                    }
                    auto lhs_builder =
                        [this,
                         &make_semantic_this_expr,
                         method_decl,
                         field_name = field.name]() {
                        return collect_member_expression(
                            make_semantic_this_expr(),
                            field_name,
                            true,
                            method_decl->location);
                    };
                    auto rhs_builder =
                        [this, rhs_param, method_decl, field_name = field.name]() {
                        auto rhs_ref = make_param_reference_expr(
                            *this, rhs_param, "__rhs", method_decl->location);
                        if (!rhs_ref) {
                            return std::unique_ptr<Expr>();
                        }
                        return collect_member_expression(
                            std::move(rhs_ref),
                            field_name,
                            false,
                            method_decl->location);
                    };
                    if (!emit_generated_assignment_statements_for_type(
                            *this,
                            ast_ctx_.get(),
                            ulong_type,
                            field.type,
                            use_move,
                            lhs_builder,
                            rhs_builder,
                            body_statements,
                            method_decl->location)) {
                        return false;
                    }
                }
            }

            auto return_stmt = collect_return_statement(
                make_this_deref(),
                method_decl->location,
                QualType(method_decl->type).as_shared<FunctionType>()
                    ? QualType(method_decl->type).as_shared<FunctionType>()->ret_type
                    : QualType());
            if (!return_stmt) {
                return false;
            }
            body_statements.push_back(std::move(return_stmt));
            return true;
        });

    if (!build_ok) {
        method_decl->is_deleted = true;
        method_decl->body.reset();
        return true;
    }

    auto body_stmt = collect_compound_statement(
        std::move(body_statements),
        method_decl->scope,
        method_decl->location);
    method_decl->body = std::unique_ptr<CompoundStmt>(
        dyn_cast<CompoundStmt>(body_stmt.release()));
    return method_decl->body != nullptr;
}

bool Collect::collect_materialize_defaulted_copy_assignment_body(
    CppMethodDecl* method_decl,
    const ObjectDecl* owner_record_decl,
    const RecordSemanticState& owner_state) {
    return collect_materialize_defaulted_assignment_body(
        method_decl,
        owner_record_decl,
        owner_state,
        false);
}

bool Collect::collect_materialize_defaulted_move_assignment_body(
    CppMethodDecl* method_decl,
    const ObjectDecl* owner_record_decl,
    const RecordSemanticState& owner_state) {
    return collect_materialize_defaulted_assignment_body(
        method_decl,
        owner_record_decl,
        owner_state,
        true);
}

void Collect::collect_record_resolve_virtual_dispatch(
    CollectRecordBuildContext& ctx) const {
    const ObjectDecl* current_record_decl =
        canonical_cpp_record_decl(ctx.semantic_decl);

    std::vector<const RecordSemanticState*> linear_base_states;
    std::unordered_set<const ObjectDecl*> seen_base_chain;
    auto append_base_chain = [&](const RecordSemanticState* state,
                                 const auto& self_ref) -> void {
        if (!state) {
            return;
        }
        for (const auto& base : state->bases) {
            if (!base.record_decl || seen_base_chain.contains(base.record_decl)) {
                continue;
            }
            const RecordSemanticState* base_state =
                record_semantics_cache_lookup(base.record_decl);
            if (!base_state) {
                continue;
            }
            seen_base_chain.insert(base.record_decl);
            self_ref(base_state, self_ref);
            linear_base_states.push_back(base_state);
        }
    };
    for (const auto& base : ctx.bases) {
        if (!base.record_decl || seen_base_chain.contains(base.record_decl)) {
            continue;
        }
        const RecordSemanticState* base_state =
            record_semantics_cache_lookup(base.record_decl);
        if (!base_state) {
            continue;
        }
        seen_base_chain.insert(base.record_decl);
        append_base_chain(base_state, append_base_chain);
        linear_base_states.push_back(base_state);
    }

    std::unordered_map<std::string, VirtualSlotState> virtual_slots;
    bool any_base_polymorphic = false;
    for (const auto* base_state : linear_base_states) {
        if (!base_state) {
            continue;
        }
        any_base_polymorphic = any_base_polymorphic || base_state->is_polymorphic;

        if (!base_state->virtual_slots.empty()) {
            for (const auto& inherited_slot : base_state->virtual_slots) {
                auto inherited_it = virtual_slots.find(inherited_slot.key);
                if (inherited_it != virtual_slots.end()) {
                    size_t slot_index = inherited_it->second.slot_index;
                    if (slot_index < ctx.semantic_virtual_slots.size()) {
                        ctx.semantic_virtual_slots[slot_index] = inherited_slot;
                    }
                    inherited_it->second.is_pure = inherited_slot.is_pure;
                    inherited_it->second.is_final = inherited_slot.is_final;
                    inherited_it->second.is_destructor =
                        inherited_slot.is_destructor;
                    inherited_it->second.final_symbol =
                        inherited_slot.final_symbol;
                    inherited_it->second.name = inherited_slot.name;
                    continue;
                }
                size_t inherited_index = ctx.semantic_virtual_slots.size();
                ctx.semantic_virtual_slots.push_back(inherited_slot);
                virtual_slots[inherited_slot.key] = VirtualSlotState{
                    inherited_index,
                    inherited_slot.is_pure,
                    inherited_slot.is_final,
                    inherited_slot.is_destructor,
                    inherited_slot.final_symbol,
                    inherited_slot.name};
            }
            continue;
        }

        for (const auto& base_method : base_state->methods) {
            if (!base_method.is_virtual || base_method.is_static) {
                continue;
            }
            std::string slot_key = make_virtual_slot_key(
                base_method.name,
                base_method.type);
            auto inherited_it = virtual_slots.find(slot_key);
            if (inherited_it != virtual_slots.end()) {
                size_t slot_index = inherited_it->second.slot_index;
                if (slot_index < ctx.semantic_virtual_slots.size()) {
                    auto& slot = ctx.semantic_virtual_slots[slot_index];
                    slot.key = slot_key;
                    slot.name = base_method.name;
                    slot.is_destructor = false;
                    slot.is_pure = base_method.is_pure;
                    slot.is_final = base_method.is_final;
                    slot.final_symbol = base_method.symbol;
                }
                inherited_it->second.is_pure = base_method.is_pure;
                inherited_it->second.is_final = base_method.is_final;
                inherited_it->second.is_destructor = false;
                inherited_it->second.final_symbol = base_method.symbol;
                inherited_it->second.name = base_method.name;
                continue;
            }
            size_t inherited_index = ctx.semantic_virtual_slots.size();
            RecordSemanticState::VirtualSlot inherited_slot;
            inherited_slot.key = slot_key;
            inherited_slot.name = base_method.name;
            inherited_slot.is_destructor = false;
            inherited_slot.is_pure = base_method.is_pure;
            inherited_slot.is_final = base_method.is_final;
            inherited_slot.final_symbol = base_method.symbol;
            ctx.semantic_virtual_slots.push_back(std::move(inherited_slot));
            virtual_slots[slot_key] = VirtualSlotState{
                inherited_index,
                base_method.is_pure,
                base_method.is_final,
                false,
                base_method.symbol,
                base_method.name};
        }
        for (const auto& base_dtor : base_state->destructors) {
            if (!base_dtor.is_virtual) {
                continue;
            }
            auto inherited_it = virtual_slots.find("<destructor>");
            if (inherited_it != virtual_slots.end()) {
                size_t slot_index = inherited_it->second.slot_index;
                if (slot_index < ctx.semantic_virtual_slots.size()) {
                    auto& slot = ctx.semantic_virtual_slots[slot_index];
                    slot.key = "<destructor>";
                    slot.name = base_dtor.name;
                    slot.is_destructor = true;
                    slot.is_pure = base_dtor.is_pure;
                    slot.is_final = base_dtor.is_final;
                    slot.final_symbol = base_dtor.symbol;
                }
                inherited_it->second.is_pure = base_dtor.is_pure;
                inherited_it->second.is_final = base_dtor.is_final;
                inherited_it->second.is_destructor = true;
                inherited_it->second.final_symbol = base_dtor.symbol;
                inherited_it->second.name = base_dtor.name;
                continue;
            }
            size_t inherited_index = ctx.semantic_virtual_slots.size();
            RecordSemanticState::VirtualSlot inherited_slot;
            inherited_slot.key = "<destructor>";
            inherited_slot.name = base_dtor.name;
            inherited_slot.is_destructor = true;
            inherited_slot.is_pure = base_dtor.is_pure;
            inherited_slot.is_final = base_dtor.is_final;
            inherited_slot.final_symbol = base_dtor.symbol;
            ctx.semantic_virtual_slots.push_back(std::move(inherited_slot));
            virtual_slots["<destructor>"] = VirtualSlotState{
                inherited_index,
                base_dtor.is_pure,
                base_dtor.is_final,
                true,
                base_dtor.symbol,
                base_dtor.name};
        }
    }

    ctx.semantic_state.is_polymorphic = any_base_polymorphic;
    ctx.semantic_state.has_virtual_destructor =
        virtual_slots.contains("<destructor>");

    for (auto& method : ctx.methods) {
        if (method.is_static) {
            method.is_virtual = false;
            method.overrides_base_virtual = false;
            method.is_pure = false;
            method.virtual_slot_index = -1;
            if (method.decl && ast_ctx_) {
                if (auto* info =
                        ast_ctx_->get_cpp_member_decl_info(method.decl->node_id)) {
                    info->is_virtual = false;
                    info->is_override = method.is_override;
                    info->is_final = method.is_final;
                    info->is_pure = false;
                }
            }
            continue;
        }

        std::string slot_key = make_virtual_slot_key(method.name, method.type);
        auto inherited_slot_it = virtual_slots.find(slot_key);
        bool overrides_base = inherited_slot_it != virtual_slots.end();
        bool inherited_final =
            overrides_base && inherited_slot_it->second.is_final;

        SrcLoc method_loc = method.decl ? method.decl->location : ctx.loc;
        if (overrides_base && inherited_slot_it->second.final_symbol) {
            auto overriding_type =
                desugar_type(method.type).as_shared<FunctionType>();
            auto overridden_type = desugar_type(
                inherited_slot_it->second.final_symbol->type)
                .as_shared<FunctionType>();
            if (overriding_type && overridden_type &&
                !returns_are_covariant(
                    overriding_type->ret_type,
                    overridden_type->ret_type,
                    ctx.bases,
                    current_record_decl)) {
                report_error(
                    "return type of overriding virtual function '" +
                        method.name +
                        "' is not covariant with the base virtual function",
                    method_loc);
            }
        }
        if (inherited_final) {
            report_error(
                "cannot override final virtual function '" + method.name + "'",
                method_loc);
        }
        if (method.is_override && !overrides_base) {
            report_error(
                "'" + method.name +
                    "' marked 'override' but does not override a base virtual function",
                method_loc);
        }

        bool effective_virtual =
            method.is_virtual || method.is_override || overrides_base;
        if (method.is_final && !effective_virtual) {
            report_error(
                "'" + method.name + "' marked 'final' but is not virtual",
                method_loc);
        }
        if (method.is_pure && !effective_virtual) {
            report_error(
                "pure-specifier can only be specified for virtual member functions",
                method_loc);
        }

        method.is_virtual = effective_virtual;
        method.overrides_base_virtual = overrides_base;
        if (method.is_virtual) {
            ctx.semantic_state.is_polymorphic = true;
            if (overrides_base) {
                size_t slot_index = inherited_slot_it->second.slot_index;
                method.virtual_slot_index = static_cast<int32_t>(slot_index);
                if (slot_index < ctx.semantic_virtual_slots.size()) {
                    auto& slot = ctx.semantic_virtual_slots[slot_index];
                    slot.name = method.name;
                    slot.is_destructor = false;
                    slot.is_pure = method.is_pure;
                    slot.is_final = method.is_final;
                    slot.final_symbol = method.symbol;
                }
                inherited_slot_it->second.is_pure = method.is_pure;
                inherited_slot_it->second.is_final = method.is_final;
                inherited_slot_it->second.is_destructor = false;
                inherited_slot_it->second.final_symbol = method.symbol;
                inherited_slot_it->second.name = method.name;
            } else {
                size_t slot_index = ctx.semantic_virtual_slots.size();
                method.virtual_slot_index = static_cast<int32_t>(slot_index);
                RecordSemanticState::VirtualSlot slot;
                slot.key = slot_key;
                slot.name = method.name;
                slot.is_destructor = false;
                slot.is_pure = method.is_pure;
                slot.is_final = method.is_final;
                slot.final_symbol = method.symbol;
                ctx.semantic_virtual_slots.push_back(std::move(slot));
                virtual_slots[slot_key] = VirtualSlotState{
                    slot_index,
                    method.is_pure,
                    method.is_final,
                    false,
                    method.symbol,
                    method.name};
            }
        } else {
            method.virtual_slot_index = -1;
        }

        if (method.decl && ast_ctx_) {
            if (auto* info = ast_ctx_->get_cpp_member_decl_info(method.decl->node_id)) {
                info->is_virtual = method.is_virtual;
                info->is_override = method.is_override;
                info->is_final = method.is_final;
                info->is_pure = method.is_pure;
            }
        }
    }

    for (auto& dtor : ctx.destructors) {
        auto inherited_slot_it = virtual_slots.find("<destructor>");
        bool overrides_base = inherited_slot_it != virtual_slots.end();
        bool inherited_final =
            overrides_base && inherited_slot_it->second.is_final;

        SrcLoc dtor_loc = dtor.decl ? dtor.decl->location : ctx.loc;
        if (inherited_final) {
            report_error("cannot override final virtual destructor", dtor_loc);
        }
        if (dtor.is_override && !overrides_base) {
            report_error(
                "destructor marked 'override' but does not override a base virtual destructor",
                dtor_loc);
        }

        bool effective_virtual =
            dtor.is_virtual || dtor.is_override || overrides_base;
        if (dtor.is_final && !effective_virtual) {
            report_error(
                "destructor marked 'final' but is not virtual",
                dtor_loc);
        }
        if (dtor.is_pure && !effective_virtual) {
            report_error(
                "pure-specifier can only be specified for virtual member functions",
                dtor_loc);
        }

        dtor.is_virtual = effective_virtual;
        dtor.overrides_base_virtual = overrides_base;
        if (dtor.is_virtual) {
            ctx.semantic_state.is_polymorphic = true;
            ctx.semantic_state.has_virtual_destructor = true;
            if (overrides_base) {
                size_t slot_index = inherited_slot_it->second.slot_index;
                dtor.virtual_slot_index = static_cast<int32_t>(slot_index);
                if (slot_index < ctx.semantic_virtual_slots.size()) {
                    auto& slot = ctx.semantic_virtual_slots[slot_index];
                    slot.name = dtor.name;
                    slot.is_destructor = true;
                    slot.is_pure = dtor.is_pure;
                    slot.is_final = dtor.is_final;
                    slot.final_symbol = dtor.symbol;
                }
                inherited_slot_it->second.is_pure = dtor.is_pure;
                inherited_slot_it->second.is_final = dtor.is_final;
                inherited_slot_it->second.is_destructor = true;
                inherited_slot_it->second.final_symbol = dtor.symbol;
                inherited_slot_it->second.name = dtor.name;
            } else {
                size_t slot_index = ctx.semantic_virtual_slots.size();
                dtor.virtual_slot_index = static_cast<int32_t>(slot_index);
                RecordSemanticState::VirtualSlot slot;
                slot.key = "<destructor>";
                slot.name = dtor.name;
                slot.is_destructor = true;
                slot.is_pure = dtor.is_pure;
                slot.is_final = dtor.is_final;
                slot.final_symbol = dtor.symbol;
                ctx.semantic_virtual_slots.push_back(std::move(slot));
                virtual_slots["<destructor>"] = VirtualSlotState{
                    slot_index,
                    dtor.is_pure,
                    dtor.is_final,
                    true,
                    dtor.symbol,
                    dtor.name};
            }
        } else {
            dtor.virtual_slot_index = -1;
        }

        if (dtor.decl && ast_ctx_) {
            if (auto* info = ast_ctx_->get_cpp_member_decl_info(dtor.decl->node_id)) {
                info->is_virtual = dtor.is_virtual;
                info->is_override = dtor.is_override;
                info->is_final = dtor.is_final;
                info->is_pure = dtor.is_pure;
            }
        }
    }

    ctx.semantic_state.virtual_slots = ctx.semantic_virtual_slots;
    ctx.semantic_state.is_abstract = false;
    for (const auto& slot : ctx.semantic_state.virtual_slots) {
        if (slot.is_pure) {
            ctx.semantic_state.is_abstract = true;
            break;
        }
    }
}

void Collect::collect_record_compute_layout(CollectRecordBuildContext& ctx) const {
    RecordSemanticState::DefinitionData definition_data =
        ctx.semantic_state.definition_data;
    bool record_is_incomplete = ctx.semantic_state.is_incomplete;
    bool semantic_is_polymorphic = ctx.semantic_state.is_polymorphic;
    bool semantic_requires_vptr =
        semantic_is_polymorphic || !ctx.virtual_bases.empty();
    bool semantic_is_abstract = ctx.semantic_state.is_abstract;
    bool semantic_has_virtual_destructor =
        ctx.semantic_state.has_virtual_destructor;
    auto computed_virtual_slots = std::move(ctx.semantic_state.virtual_slots);
    const AbiPolicy* abi_policy =
        ast_ctx_ && ast_ctx_->abi_policy ? ast_ctx_->abi_policy.get() : nullptr;

    size_t primary_non_virtual_base_index = std::numeric_limits<size_t>::max();
    for (size_t base_index = 0; base_index < ctx.bases.size(); ++base_index) {
        const auto& base = ctx.bases[base_index];
        if (base.is_virtual ||
            !base.type ||
            canonical_type_kind(base.type) != TypeKind::Object) {
            continue;
        }
        primary_non_virtual_base_index = base_index;
        break;
    }

    bool primary_base_provides_vptr = false;
    if (semantic_requires_vptr &&
        primary_non_virtual_base_index != std::numeric_limits<size_t>::max()) {
        const auto& primary_base = ctx.bases[primary_non_virtual_base_index];
        const RecordSemanticState* primary_base_state =
            record_semantics_cache_lookup(primary_base.record_decl);
        primary_base_provides_vptr =
            primary_base_state &&
            !primary_base_state->is_incomplete &&
            (primary_base_state->is_polymorphic ||
             !primary_base_state->virtual_bases.empty());
    }
    bool inject_own_vptr_field =
        semantic_requires_vptr && !ctx.is_union_record && !primary_base_provides_vptr;

    std::vector<ObjectType::Field> layout_fields;
    layout_fields.reserve(
        ctx.fields.size() + ctx.bases.size() + (inject_own_vptr_field ? 1 : 0));
    size_t requested_alignment =
        ctx.record_type ? ctx.record_type->requested_alignment : 0;
    std::vector<size_t> direct_base_layout_field_indices(
        ctx.bases.size(),
        std::numeric_limits<size_t>::max());
    if (inject_own_vptr_field) {
        auto void_type = get_builtin_void();
        if (void_type) {
            QualType vptr_type(std::make_shared<PointerType>(QualType(void_type)));
            layout_fields.push_back(
                ObjectType::Field("", vptr_type, 0, RecordMemberAccess::Private));
        }
    }
    for (size_t base_index = 0; base_index < ctx.bases.size(); ++base_index) {
        const auto& base = ctx.bases[base_index];
        if (base.is_virtual ||
            !base.type ||
            canonical_type_kind(base.type) != TypeKind::Object) {
            continue;
        }
        direct_base_layout_field_indices[base_index] = layout_fields.size();
        size_t base_size_override = 0;
        size_t base_alignment_override = 1;
        if (const RecordSemanticState* base_state =
                record_semantics_cache_lookup(base.record_decl)) {
            base_size_override = (base_state->non_virtual_size_bits + 7) / 8;
            base_alignment_override = base_state->non_virtual_alignment;
        }
        if (base_size_override == 0 && base.type) {
            int64_t fallback_width = base.type->getWidthBytes();
            if (fallback_width > 0) {
                base_size_override = static_cast<size_t>(fallback_width);
            }
        }
        if (base_size_override == 0) {
            base_size_override = 1;
        }
        if (base_alignment_override == 0 && base.type) {
            if (auto base_obj = desugar_type(base.type).as_shared<ObjectType>()) {
                base_alignment_override = base_obj->getAlignment();
            }
        }
        if (base_alignment_override == 0) {
            base_alignment_override = 1;
        }
        ObjectType::Field base_field("", base.type, 0, base.declared_access);
        base_field.is_base_subobject = true;
        base_field.storage_size_override = base_size_override;
        base_field.storage_alignment_override = base_alignment_override;
        layout_fields.push_back(std::move(base_field));
    }
    for (const auto& field : ctx.fields) {
        layout_fields.push_back(field);
    }
    ctx.semantic_state = compute_record_semantics(
        std::move(layout_fields),
        ctx.is_union_record,
        false,
        requested_alignment,
        0,
        record_is_incomplete,
        abi_policy);
    ctx.semantic_state.definition_data = definition_data;
    ctx.semantic_state.non_virtual_size_bits = ctx.semantic_state.size_bits;
    ctx.semantic_state.non_virtual_alignment = ctx.semantic_state.alignment;
    for (size_t base_index = 0; base_index < ctx.bases.size(); ++base_index) {
        auto& base = ctx.bases[base_index];
        base.has_non_virtual_offset = false;
        base.non_virtual_offset = 0;
        size_t layout_field_index = direct_base_layout_field_indices[base_index];
        if (layout_field_index == std::numeric_limits<size_t>::max()) {
            continue;
        }
        if (layout_field_index >= ctx.semantic_state.fields.size()) {
            continue;
        }
        base.has_non_virtual_offset = true;
        base.non_virtual_offset = ctx.semantic_state.fields[layout_field_index].offset;
    }
    if (!ctx.virtual_bases.empty()) {
        auto complete_layout_fields = ctx.semantic_state.fields;
        complete_layout_fields.reserve(
            complete_layout_fields.size() + ctx.virtual_bases.size());
        std::vector<size_t> virtual_base_layout_field_indices(
            ctx.virtual_bases.size(),
            std::numeric_limits<size_t>::max());
        auto uchar_type =
            ast_ctx_ && ast_ctx_->type_ctx
                ? ast_ctx_->type_ctx->get_builtin(BuiltinTypes::UChar)
                : nullptr;
        if (!uchar_type && ast_ctx_ && ast_ctx_->type_ctx) {
            uchar_type = ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Char);
        }

        for (size_t vb_index = 0; vb_index < ctx.virtual_bases.size(); ++vb_index) {
            auto& virtual_base = ctx.virtual_bases[vb_index];
            size_t vb_size_override = 0;
            size_t vb_alignment_override = 1;
            if (const RecordSemanticState* virtual_base_state =
                    record_semantics_cache_lookup(virtual_base.record_decl)) {
                vb_size_override =
                    (virtual_base_state->non_virtual_size_bits + 7) / 8;
                vb_alignment_override =
                    virtual_base_state->non_virtual_alignment;
            }
            if (vb_size_override == 0 && virtual_base.type) {
                int64_t fallback_width = virtual_base.type->getWidthBytes();
                if (fallback_width > 0) {
                    vb_size_override = static_cast<size_t>(fallback_width);
                }
            }
            if (vb_size_override == 0) {
                vb_size_override = 1;
            }
            if (vb_alignment_override == 0 && virtual_base.type) {
                if (auto virtual_obj =
                        desugar_type(virtual_base.type).as_shared<ObjectType>()) {
                    vb_alignment_override = virtual_obj->getAlignment();
                }
            }
            if (vb_alignment_override == 0) {
                vb_alignment_override = 1;
            }

            QualType virtual_storage_type = virtual_base.type;
            if (uchar_type) {
                virtual_storage_type = QualType(
                    std::make_shared<ArrayType>(
                        QualType(uchar_type),
                        std::optional<size_t>(vb_size_override)));
            }
            ObjectType::Field virtual_storage_field(
                "",
                virtual_storage_type,
                0,
                virtual_base.declared_access);
            virtual_storage_field.is_base_subobject = true;
            virtual_storage_field.is_virtual_base_storage = true;
            virtual_storage_field.storage_size_override = vb_size_override;
            virtual_storage_field.storage_alignment_override = vb_alignment_override;
            virtual_base_layout_field_indices[vb_index] =
                complete_layout_fields.size();
            complete_layout_fields.push_back(std::move(virtual_storage_field));
        }

        RecordSemanticState complete_layout_state = compute_record_semantics(
            std::move(complete_layout_fields),
            ctx.is_union_record,
            false,
            requested_alignment,
            0,
            record_is_incomplete,
            abi_policy);
        complete_layout_state.definition_data = definition_data;
        ctx.semantic_state.fields = std::move(complete_layout_state.fields);
        ctx.semantic_state.size_bits = complete_layout_state.size_bits;
        ctx.semantic_state.alignment = complete_layout_state.alignment;
        ctx.semantic_state.has_flexible_array_member =
            complete_layout_state.has_flexible_array_member;

        for (size_t vb_index = 0; vb_index < ctx.virtual_bases.size(); ++vb_index) {
            size_t layout_field_index = virtual_base_layout_field_indices[vb_index];
            if (layout_field_index >= ctx.semantic_state.fields.size()) {
                continue;
            }
            ctx.virtual_bases[vb_index].has_offset = true;
            ctx.virtual_bases[vb_index].offset =
                ctx.semantic_state.fields[layout_field_index].offset;
        }
    }

    ctx.semantic_state.is_polymorphic = semantic_is_polymorphic;
    ctx.semantic_state.is_abstract = semantic_is_abstract;
    ctx.semantic_state.has_virtual_destructor = semantic_has_virtual_destructor;
    ctx.semantic_state.virtual_slots = std::move(computed_virtual_slots);
}

void Collect::collect_record_publish_state(
    ObjectDecl* semantic_decl,
    const std::shared_ptr<ObjectType>& record_type,
    const RecordSemanticState& state) {
    if (record_type) {
        record_type->set_decl(semantic_decl);
    }
    query_publish_record_semantics(semantic_decl, state);
}

void Collect::collect_record_publish_semantics(
    CollectRecordBuildContext& ctx) {
    ctx.semantic_state.bases = std::move(ctx.bases);
    ctx.semantic_state.virtual_bases = std::move(ctx.virtual_bases);
    ctx.semantic_state.methods = std::move(ctx.methods);
    ctx.semantic_state.method_templates = std::move(ctx.method_templates);
    ctx.semantic_state.static_data_members = std::move(ctx.static_data_members);
    ctx.semantic_state.nested_types = std::move(ctx.nested_types);
    ctx.semantic_state.nested_templates = std::move(ctx.nested_templates);
    ctx.semantic_state.enumerator_members = std::move(ctx.enumerator_members);
    ctx.semantic_state.constructors = std::move(ctx.constructors);
    ctx.semantic_state.destructors = std::move(ctx.destructors);
    collect_record_publish_state(
        ctx.semantic_decl,
        ctx.record_type,
        std::move(ctx.semantic_state));
}
