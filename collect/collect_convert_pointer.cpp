#include "collect.h"

namespace {
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

using BasePathStep = std::pair<const ObjectDecl*, bool>; // bool = via virtual edge

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

size_t count_public_base_subobjects(const ObjectDecl* derived_decl,
                                    const ObjectDecl* target_base_decl) {
    derived_decl = canonical_record_decl(derived_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl || derived_decl == target_base_decl) {
        return 0;
    }

    std::unordered_set<std::string> matched_subobjects;
    std::vector<BasePathStep> path;
    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(derived_decl);

    std::function<void(const ObjectDecl*)> walk =
        [&](const ObjectDecl* current_decl) {
        current_decl = canonical_record_decl(current_decl);
        if (!current_decl) {
            return;
        }
        if (current_decl == target_base_decl) {
            if (!path.empty()) {
                matched_subobjects.insert(encode_base_path_key(path));
            }
            return;
        }

        const RecordSemanticState* state = record_semantics_cache_lookup(current_decl);
        if (!state) {
            return;
        }

        for (const auto& base : state->bases) {
            const ObjectDecl* base_decl = canonical_record_decl(base.record_decl);
            if (!base_decl ||
                base.declared_access != RecordMemberAccess::Public ||
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

bool has_public_unambiguous_base_path(const ObjectDecl* derived_decl,
                                      const ObjectDecl* target_base_decl) {
    derived_decl = canonical_record_decl(derived_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl || derived_decl == target_base_decl) {
        return false;
    }
    size_t path_count = count_public_base_subobjects(
        derived_decl, target_base_decl);
    if (path_count == 0 && target_base_decl) {
        std::function<size_t(const ObjectDecl*,
                             std::unordered_set<const ObjectDecl*>&)>
            count_by_name = [&](const ObjectDecl* current_decl,
                                std::unordered_set<const ObjectDecl*>& seen)
        -> size_t {
            if (!current_decl || seen.contains(current_decl)) {
                return 0;
            }
            seen.insert(current_decl);
            const RecordSemanticState* state =
                record_semantics_cache_lookup(current_decl);
            if (!state) {
                return 0;
            }
            size_t matches = 0;
            for (const auto& base : state->bases) {
                const ObjectDecl* base_decl =
                    canonical_record_decl(base.record_decl);
                if (!base_decl ||
                    base.declared_access != RecordMemberAccess::Public) {
                    continue;
                }
                if (base.name == target_base_decl->tag ||
                    base_decl->tag == target_base_decl->tag) {
                    ++matches;
                    continue;
                }
                matches += count_by_name(base_decl, seen);
            }
            return matches;
        };
        std::unordered_set<const ObjectDecl*> by_name_seen;
        path_count = count_by_name(derived_decl, by_name_seen);
    }
    return path_count == 1;
}

struct NonVirtualMemberBasePathSummary {
    size_t public_paths = 0;
    size_t nonpublic_paths = 0;
    size_t public_offset = 0;
};

void accumulate_nonvirtual_member_base_paths(
    const ObjectDecl* current_decl,
    const ObjectDecl* target_base_decl,
    bool path_is_public,
    size_t current_offset,
    NonVirtualMemberBasePathSummary& summary,
    std::unordered_set<const ObjectDecl*>& active_stack) {

    current_decl = canonical_record_decl(current_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    if (!current_decl || !target_base_decl) {
        return;
    }
    if (current_decl == target_base_decl) {
        if (path_is_public) {
            if (summary.public_paths == 0) {
                summary.public_offset = current_offset;
            }
            ++summary.public_paths;
        } else {
            ++summary.nonpublic_paths;
        }
        return;
    }

    const RecordSemanticState* state = record_semantics_cache_lookup(current_decl);
    if (!state) {
        return;
    }

    for (const auto& base : state->bases) {
        if (!base.record_decl || base.is_virtual || !base.has_non_virtual_offset) {
            continue;
        }
        const ObjectDecl* base_decl = canonical_record_decl(base.record_decl);
        if (!base_decl || active_stack.contains(base_decl)) {
            continue;
        }
        if (current_offset >
            std::numeric_limits<size_t>::max() - base.non_virtual_offset) {
            continue;
        }
        bool next_path_public =
            path_is_public && base.declared_access == RecordMemberAccess::Public;
        size_t next_offset = current_offset + base.non_virtual_offset;
        active_stack.insert(base_decl);
        accumulate_nonvirtual_member_base_paths(
            base_decl,
            target_base_decl,
            next_path_public,
            next_offset,
            summary,
            active_stack);
        active_stack.erase(base_decl);
    }
}

NonVirtualMemberBasePathSummary summarize_nonvirtual_member_base_paths(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl) {

    NonVirtualMemberBasePathSummary summary;
    derived_decl = canonical_record_decl(derived_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl || derived_decl == target_base_decl) {
        return summary;
    }
    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(derived_decl);
    accumulate_nonvirtual_member_base_paths(
        derived_decl,
        target_base_decl,
        true,
        0,
        summary,
        active_stack);
    return summary;
}

bool has_virtual_base_path(const ObjectDecl* derived_decl,
                           const ObjectDecl* target_base_decl) {
    derived_decl = canonical_record_decl(derived_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl || derived_decl == target_base_decl) {
        return false;
    }

    std::unordered_set<const ObjectDecl*> active_stack;
    std::function<bool(const ObjectDecl*, bool)> walk =
        [&](const ObjectDecl* current_decl, bool saw_virtual_edge) {
        current_decl = canonical_record_decl(current_decl);
        if (!current_decl) {
            return false;
        }
        if (current_decl == target_base_decl) {
            return saw_virtual_edge;
        }

        const RecordSemanticState* state = record_semantics_cache_lookup(current_decl);
        if (!state) {
            return false;
        }

        for (const auto& base : state->bases) {
            const ObjectDecl* base_decl = canonical_record_decl(base.record_decl);
            if (!base_decl || active_stack.contains(base_decl)) {
                continue;
            }
            bool next_saw_virtual = saw_virtual_edge || base.is_virtual;
            active_stack.insert(base_decl);
            bool found = walk(base_decl, next_saw_virtual);
            active_stack.erase(base_decl);
            if (found) {
                return true;
            }
        }
        return false;
    };

    active_stack.insert(derived_decl);
    return walk(derived_decl, false);
}

bool is_incomplete_array_bound(const std::shared_ptr<ArrayType>& arr) {
    if (!arr) {
        return false;
    }
    return arr->size_kind == ArraySizeKind::Incomplete ||
        (arr->size_kind == ArraySizeKind::Constant && !arr->size.has_value());
}

bool are_compatible_pointer_targets(QualType lhs,
                                    QualType rhs,
                                    const ASTContext* ast_ctx) {
    if (!lhs || !rhs) {
        return false;
    }
    lhs = desugar_type(lhs, ast_ctx);
    rhs = desugar_type(rhs, ast_ctx);
    if (lhs.equals_unqualified(rhs)) {
        return true;
    }

    auto lhs_arr = lhs.as_shared<ArrayType>();
    auto rhs_arr = rhs.as_shared<ArrayType>();
    if (lhs_arr && rhs_arr) {
        if (!are_compatible_pointer_targets(lhs_arr->element_type,
                                            rhs_arr->element_type,
                                            ast_ctx)) {
            return false;
        }
        bool lhs_incomplete = is_incomplete_array_bound(lhs_arr);
        bool rhs_incomplete = is_incomplete_array_bound(rhs_arr);
        if (lhs_incomplete || rhs_incomplete) {
            return true;
        }
        // VLA bounds are runtime values. For pointer-target compatibility,
        // treat any VLA bound as compatible with the corresponding constant
        // or variable bound as long as element types are compatible.
        if (lhs_arr->size_kind == ArraySizeKind::Variable ||
            rhs_arr->size_kind == ArraySizeKind::Variable) {
            return true;
        }
        bool lhs_const = lhs_arr->size_kind == ArraySizeKind::Constant && lhs_arr->size.has_value();
        bool rhs_const = rhs_arr->size_kind == ArraySizeKind::Constant && rhs_arr->size.has_value();
        if (lhs_const && rhs_const) {
            return lhs_arr->size.value() == rhs_arr->size.value();
        }
        return lhs_arr->size_kind == rhs_arr->size_kind;
    }

    auto lhs_ptr = lhs.as_shared<PointerType>();
    auto rhs_ptr = rhs.as_shared<PointerType>();
    if (lhs_ptr && rhs_ptr) {
        return are_compatible_pointer_targets(lhs_ptr->pointed_type,
                                              rhs_ptr->pointed_type,
                                              ast_ctx);
    }

    auto lhs_obj = lhs.as_shared<ObjectType>();
    auto rhs_obj = rhs.as_shared<ObjectType>();
    if (lhs_obj && rhs_obj) {
        const auto* lhs_decl = canonical_record_decl(
            dyn_cast<ObjectDecl>(lhs_obj->get_decl()));
        const auto* rhs_decl = canonical_record_decl(
            dyn_cast<ObjectDecl>(rhs_obj->get_decl()));
        if (lhs_decl && rhs_decl) {
            if (has_public_unambiguous_base_path(lhs_decl, rhs_decl) ||
                has_public_unambiguous_base_path(rhs_decl, lhs_decl)) {
                return true;
            }
        }
    }
    return false;
}
}

Expr* Collect::strip_implicit_casts(Expr* expr) {

    auto cur = expr;
    while (auto* cast = dyn_cast<ImplicitCast>(cur)) {
        cur = cast->expr.get();
    }
    return cur;
}


bool Collect::is_null_pointer_constant_expr(Expr* expr) const {

    auto raw = strip_implicit_casts(expr);
    if (!raw) {
        return false;
    }
    auto type = raw->get_type();
    auto canonical_type = desugar_type(type, ast_ctx_.get());
    if (auto builtin = canonical_type.as_shared<BuiltinType>()) {
        if (builtin->builtin_kind == BuiltinTypes::NullPtr) {
            return true;
        }
    }
    if (!type || !type->isInteger()) {
        return false;
    }
    auto value = try_evaluate_with_consteval_compat(raw, ConstEvalMode::c_ice());
    return value.has_value() && *value == 0;
}


bool Collect::are_char_family_compatible(const CType& a, const CType& b) const {

    auto* ba = dyn_cast<const BuiltinType>(&a);
    auto* bb = dyn_cast<const BuiltinType>(&b);
    if (!ba || !bb) {
        return false;
    }
    auto is_char = [](BuiltinTypes kind) {
        return kind == BuiltinTypes::Char || kind == BuiltinTypes::UChar;
    };
    return is_char(ba->builtin_kind) && is_char(bb->builtin_kind);
}


bool Collect::pointers_to_compatible_types(QualType lhs, QualType rhs) const {

    auto lhs_canonical = desugar_type(lhs, ast_ctx_.get());
    auto rhs_canonical = desugar_type(rhs, ast_ctx_.get());
    auto lhs_ptr = lhs_canonical.as<PointerType>();
    auto rhs_ptr = rhs_canonical.as<PointerType>();
    if (!lhs_ptr || !rhs_ptr) {
        return false;
    }
    if (are_compatible_pointer_targets(lhs_ptr->pointed_type,
                                       rhs_ptr->pointed_type,
                                       ast_ctx_.get())) {
        return true;
    }
    if (!lhs_ptr->pointed_type || !rhs_ptr->pointed_type) {
        return false;
    }
    QualType lhs_pointed = desugar_type(lhs_ptr->pointed_type, ast_ctx_.get());
    QualType rhs_pointed = desugar_type(rhs_ptr->pointed_type, ast_ctx_.get());
    auto enum_int_compatible = [](QualType enum_ty, QualType int_ty) -> bool {
        auto* en = enum_ty.as<EnumType>();
        auto* bi = int_ty.as<BuiltinType>();
        if (!en || !bi) {
            return false;
        }
        auto underlying = en->semantic_underlying_type();
        if (!underlying) {
            return false;
        }
        return QualType(underlying).equals_unqualified(int_ty);
    };
    if (enum_int_compatible(lhs_pointed, rhs_pointed) ||
        enum_int_compatible(rhs_pointed, lhs_pointed)) {
        return true;
    }
    if (!lhs_pointed || !rhs_pointed) {
        return false;
    }
    return are_char_family_compatible(*lhs_pointed, *rhs_pointed);
}

bool Collect::member_pointers_to_compatible_types(QualType lhs, QualType rhs) const {
    return member_pointer_convertible_to(lhs, rhs) ||
           member_pointer_convertible_to(rhs, lhs);
}


Collect::MemberPointerConversionResult Collect::analyze_member_pointer_conversion(
    QualType from, QualType to) const {

    MemberPointerConversionResult result;
    auto from_canonical = desugar_type(from, ast_ctx_.get());
    auto to_canonical = desugar_type(to, ast_ctx_.get());
    auto from_mem = from_canonical.as_shared<MemberPointerType>();
    auto to_mem = to_canonical.as_shared<MemberPointerType>();
    if (!from_mem || !to_mem) {
        result.issue = MemberPointerConversionIssue::NotMemberPointerType;
        return result;
    }
    if (!from_mem->member_type || !to_mem->member_type ||
        !from_mem->member_type.equals_unqualified(to_mem->member_type)) {
        result.issue = MemberPointerConversionIssue::MemberTypeMismatch;
        return result;
    }
    if (!to_mem->member_type.has_all_qualifiers_of(from_mem->member_type)) {
        result.issue = MemberPointerConversionIssue::QualificationDrops;
        return result;
    }

    auto from_owner_type =
        desugar_type(from_mem->class_type, ast_ctx_.get()).as_shared<ObjectType>();
    auto to_owner_type =
        desugar_type(to_mem->class_type, ast_ctx_.get()).as_shared<ObjectType>();
    const auto* from_owner_decl = from_owner_type
        ? canonical_record_decl(dyn_cast<ObjectDecl>(from_owner_type->get_decl()))
        : nullptr;
    const auto* to_owner_decl = to_owner_type
        ? canonical_record_decl(dyn_cast<ObjectDecl>(to_owner_type->get_decl()))
        : nullptr;
    if (!from_owner_decl || !to_owner_decl) {
        result.issue = MemberPointerConversionIssue::UnrelatedClass;
        return result;
    }
    if (from_owner_decl == to_owner_decl) {
        result.viable = true;
        result.issue = MemberPointerConversionIssue::None;
        result.owner_adjustment = 0;
        return result;
    }

    auto path_summary = summarize_nonvirtual_member_base_paths(
        /*derived=*/to_owner_decl,
        /*base=*/from_owner_decl);
    if (has_virtual_base_path(to_owner_decl, from_owner_decl)) {
        result.issue = MemberPointerConversionIssue::VirtualBase;
        return result;
    }
    if (path_summary.public_paths > 1) {
        result.issue = MemberPointerConversionIssue::AmbiguousBase;
        return result;
    }
    if (path_summary.public_paths == 1) {
        if (path_summary.public_offset >
            static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
            result.issue = MemberPointerConversionIssue::UnrelatedClass;
            return result;
        }
        result.viable = true;
        result.issue = MemberPointerConversionIssue::None;
        result.owner_adjustment = static_cast<int64_t>(path_summary.public_offset);
        return result;
    }
    if (path_summary.nonpublic_paths > 0) {
        result.issue = MemberPointerConversionIssue::InaccessibleBase;
        return result;
    }

    result.issue = MemberPointerConversionIssue::UnrelatedClass;
    return result;
}


bool Collect::member_pointer_convertible_to(QualType from, QualType to) const {
    return analyze_member_pointer_conversion(from, to).viable;
}


bool Collect::is_const_qualified_lvalue(Expr* expr) const {

    if (!expr) {
        return false;
    }
    auto expr_type = expr->get_type();
    if (expr_type && expr_type.is_const()) {
        return true;
    }
    if (auto* var_ref = dyn_cast<VarRef>(expr)) {
        return var_ref->symref && var_ref->symref->is_const();
    }
    if (auto* unary = dyn_cast<UnaryOperation>(expr)) {
        if (unary->uop == UnaryOpTypes::DEREFERENCE) {
            auto ptr = unary->exp
                ? desugar_type(unary->exp->get_type(), ast_ctx_.get())
                      .as_shared<PointerType>()
                : nullptr;
            return ptr && ptr->pointed_type.is_const();
        }
        return false;
    }
    if (auto* member = dyn_cast<MemberExpr>(expr)) {
        if (member->member_type.is_const()) {
            return true;
        }
        // For member access, const-ness should come from the selected member type.
        // In particular, `p->field` must not inherit top-level const from `p` itself.
        return false;
    }
    if (auto* subscript = dyn_cast<ArraySubscriptExpr>(expr)) {
        return subscript->get_type().is_const();
    }
    return false;
}


bool Collect::is_modifiable_lvalue(Expr* expr) const {

    if (!expr) {
        return false;
    }
    if (isa<UnresolvedMemberExpr>(expr)) {
        return true;
    }
    bool is_lvalue = expr->isLValue();
    if (lang_opts_.is_cxx_mode()) {
        is_lvalue = classify_value_category(expr) == ValueCategory::LValue;
    }
    if (!is_lvalue) {
        return false;
    }
    auto type = expr->get_type();
    if (!type) {
        return false;
    }
    auto kind = canonical_type_kind(type, ast_ctx_.get());
    if (type->isVoid() || kind == TypeKind::Array || kind == TypeKind::Function) {
        return false;
    }
    if (is_const_qualified_lvalue(expr)) {
        return false;
    }
    return true;
}


QualType Collect::pick_common_type(QualType lhs, QualType rhs) const {

    if (!lhs) return rhs;
    if (!rhs) return lhs;
    auto l = desugar_type(lhs, ast_ctx_.get());
    auto r = desugar_type(rhs, ast_ctx_.get());
    if (!l || !r) {
        return lhs ? lhs : rhs;
    }

    auto l_kind = l->kind;
    auto r_kind = r->kind;
    if (l_kind == TypeKind::Pointer && (r_kind == TypeKind::Pointer || r->isInteger())) {
        return lhs;
    }
    if (r_kind == TypeKind::Pointer && l->isInteger()) {
        return rhs;
    }

    if ((l->isArithmetic() && r->isArithmetic()) || l->isComplex() || r->isComplex()) {
        auto common = usual_arithmetic_conversion_type(lhs, rhs);
        if (common) {
            return common;
        }
    }
    return lhs;
}
