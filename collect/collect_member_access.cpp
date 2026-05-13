#include "collect.h"
#include "collect_internal.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"

using namespace collect_internal;

namespace {
bool record_has_dependent_bases(const ObjectDecl* record_decl) {
    const RecordSemanticState* state = record_semantics_cache_lookup(record_decl);
    if (!state) {
        return false;
    }
    for (const auto& base : state->bases) {
        if (!base.record_decl && base.type) {
            return true;
        }
    }
    return false;
}
} // namespace

QualType Collect::try_synthesize_dependent_member_type(
    QualType base_type,
    bool is_arrow,
    const std::string& member_name,
    SrcLoc loc,
    QualType* declared_member_type_out) {
    if (declared_member_type_out) {
        *declared_member_type_out = QualType(nullptr);
    }
    if (!base_type) {
        return QualType(nullptr);
    }

    QualType object_type =
        desugar_type(remove_reference(base_type, ast_ctx_.get()), ast_ctx_.get());
    if (is_arrow) {
        auto ptr_type = object_type.as_shared<PointerType>();
        object_type = ptr_type
            ? desugar_type(
                  remove_reference(ptr_type->pointed_type, ast_ctx_.get()),
                  ast_ctx_.get())
            : QualType(nullptr);
    }
    if (!object_type) {
        return QualType(nullptr);
    }

    std::shared_ptr<ObjectType> lookup_record_type =
        desugar_type(object_type, ast_ctx_.get()).as_shared<ObjectType>();
    const ClassTemplateDecl* class_template = nullptr;
    const TemplateSpecializationType* specialization = nullptr;

    if (!lookup_record_type) {
        auto specialization_type =
            dyn_cast_shared<TemplateSpecializationType>(
                desugar_typedefs(object_type).get_shared());
        if (!specialization_type) {
            return QualType(nullptr);
        }
        class_template =
            dyn_cast<ClassTemplateDecl>(specialization_type->primary_template);
        if (!class_template) {
            return QualType(nullptr);
        }
        const ObjectDecl* pattern_decl = class_template->pattern_semantic_decl();
        if (!pattern_decl) {
            return QualType(nullptr);
        }
        lookup_record_type = pattern_decl->get_record_type();
        specialization = specialization_type.get();
    }
    if (!lookup_record_type) {
        return QualType(nullptr);
    }

    FieldLookupResult lookup;
    std::vector<uint32_t> path;
    find_field_recursive(lookup_record_type.get(), member_name, path, 0, lookup);
    if (lookup.matches == 0 || lookup.field == nullptr) {
        return QualType(nullptr);
    }
    if (lookup.matches > 1) {
        report_error("member '" + member_name + "' is ambiguous", loc);
        return QualType(nullptr);
    }

    const ObjectDecl* object_record_decl =
        record_decl_from_record_type(lookup_record_type.get());
    const ObjectDecl* access_context_decl =
        current_access_context_record_decl(
            session_.func_state_.current_function_is_cpp_member,
            session_.func_state_.current_function_cpp_this_type,
            session_.func_state_.current_function_cpp_friend_access_type,
            session_.current_cpp_record_lookup_type_,
            ast_ctx_.get());
    auto current_scope_matches_owner =
        [&](const ObjectDecl* owner_decl) {
            auto current_record_scope =
                desugar_type(session_.current_cpp_record_lookup_type_, ast_ctx_.get())
                    .as_shared<ObjectType>();
            const ObjectDecl* scope_decl =
                record_decl_from_record_type(current_record_scope.get());
            if (!owner_decl || !scope_decl) {
                return false;
            }
            owner_decl = canonical_record_decl(owner_decl);
            scope_decl = canonical_record_decl(scope_decl);
            return owner_decl == scope_decl || owner_decl->tag == scope_decl->tag;
        };

    if (lookup.field->declared_access == RecordMemberAccess::Protected &&
        !can_access_protected_member_in_context(
            lookup.owner_record_decl,
            access_context_decl,
            object_record_decl,
            false) &&
        !current_scope_matches_owner(lookup.owner_record_decl)) {
        report_error(
            "member '" + member_name + "' is protected within this context",
            loc);
        return QualType(nullptr);
    }
    if (lookup.field->declared_access == RecordMemberAccess::Private &&
        !can_access_private_member_in_context(
            lookup.owner_record_decl, access_context_decl) &&
        !current_scope_matches_owner(lookup.owner_record_decl)) {
        report_error(
            "member '" + member_name + "' is private within this context",
            loc);
        return QualType(nullptr);
    }

    QualType member_type = lookup.field->type;
    if (class_template && specialization) {
        member_type = partially_substitute_template_type(
            member_type,
            class_template->parameters,
            specialization->arguments,
            loc);
    }
    if (declared_member_type_out) {
        *declared_member_type_out = member_type;
    }

    uint8_t base_quals = QUAL_NONE;
    if (is_arrow) {
        auto ptr_type =
            remove_reference_and_desugar(base_type, ast_ctx_.get())
                .as_shared<PointerType>();
        if (ptr_type) {
            base_quals = ptr_type->pointed_type.get_qualifiers();
        }
    } else {
        base_quals =
            remove_reference(base_type, ast_ctx_.get()).get_qualifiers();
    }
    if (base_quals != QUAL_NONE && member_type) {
        member_type = member_type.with_qualifiers(base_quals);
    }
    return member_type;
}

std::unique_ptr<Expr> Collect::collect_array_subscript(std::unique_ptr<Expr> array, std::unique_ptr<Expr> index, SrcLoc loc) {

    if (lang_opts_.is_cxx_mode()) {
        auto array_record =
            remove_reference_and_desugar(
                array ? array->get_type() : QualType(),
                ast_ctx_.get())
                .as_shared<ObjectType>();
        if (array_record) {
            bool had_member_match = false;
            bool saw_private_method = false;
            bool saw_protected_method = false;
            std::vector<OverloadCallCandidate> overload_candidates;
            if (auto candidate_error = append_member_overload_candidates(
                    array_record.get(),
                    "operator[]",
                    array.get(),
                    OverloadImplicitObjectArgKind::Regular,
                    overload_candidates,
                    had_member_match,
                    saw_private_method,
                    saw_protected_method,
                    loc)) {
                return candidate_error;
            }

            if (had_member_match && overload_candidates.empty()) {
                if (auto inaccessible_error = report_inaccessible_member(
                        "operator[]",
                        saw_private_method,
                        saw_protected_method,
                        loc)) {
                    return inaccessible_error;
                }
            }

            if (!overload_candidates.empty()) {
                std::vector<std::unique_ptr<Expr>> operator_args;
                operator_args.push_back(std::move(index));

                std::shared_ptr<Symbol> selected_symbol = nullptr;
                OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
                    OverloadImplicitObjectArgKind::None;
                if (auto overload_error = select_overload_candidate(
                        "operator[]",
                        overload_candidates,
                        operator_args,
                        array.get(),
                        loc,
                        selected_symbol,
                        selected_implicit_object_arg_kind)) {
                    return overload_error;
                }

                if (selected_symbol) {
                    auto implicit_object_arg =
                        build_overload_implicit_object_arg(
                            selected_implicit_object_arg_kind,
                            std::move(array),
                            /*object_expr_is_pointer=*/false,
                            loc);

                    if (selected_implicit_object_arg_kind !=
                            OverloadImplicitObjectArgKind::None &&
                        implicit_object_arg) {
                        operator_args.insert(
                            operator_args.begin(), std::move(implicit_object_arg));
                    }

                    auto callee_expr = make_hidden_overload_callee(
                        std::move(selected_symbol), loc);
                    return collect_function_call(
                        std::move(callee_expr), std::move(operator_args), loc);
                }
            }
        }
    }

    array = collect_apply_standard_conversions(std::move(array), ExprUseContext::ArraySubscriptBase);
    index = collect_apply_standard_conversions(std::move(index), ExprUseContext::ArraySubscriptIndex);
    auto array_type = array ? array->get_type() : QualType();
    auto index_type = index ? index->get_type() : QualType();

    bool array_is_dependent =
        (array && expression_depends_on_template_parameters(array.get())) ||
        type_depends_on_template_parameters(array_type, ast_ctx_.get());
    bool index_is_dependent =
        (index && expression_depends_on_template_parameters(index.get())) ||
        type_depends_on_template_parameters(index_type, ast_ctx_.get());
    if (array_is_dependent || index_is_dependent) {
        return collect_make<DependentArraySubscriptExpr>(
            std::move(array),
            std::move(index),
            QualType(nullptr),
            loc);
    }

    auto is_subscript_base = [&](QualType t) -> bool {
        auto kind = canonical_type_kind(t, ast_ctx_.get());
        return kind == TypeKind::Pointer || kind == TypeKind::Array || kind == TypeKind::Vector;
    };

    // C defines a[b] as *(a + b), so 1[p] is valid and equivalent to p[1].
    if (!is_subscript_base(array_type) && is_subscript_base(index_type) &&
        array_type && array_type->isInteger()) {
        std::swap(array, index);
        std::swap(array_type, index_type);
        // Re-apply conversion by semantic role after commutative swap
        // so the eventual base is normalized as pointer-like.
        array = collect_apply_standard_conversions(std::move(array), ExprUseContext::ArraySubscriptBase);
        index = collect_apply_standard_conversions(std::move(index), ExprUseContext::ArraySubscriptIndex);
        array_type = array ? array->get_type() : QualType();
        index_type = index ? index->get_type() : QualType();
    }

    if (!array_type || !is_subscript_base(array_type)) {
        report_error("subscripted value is not an array, pointer, or vector", loc);
    }
    if (!index_type || !index_type->isInteger()) {
        report_error("array subscript is not an integer", loc);
    }

    QualType result_type = nullptr;
    auto semantic_array_type = desugar_type(array_type, ast_ctx_.get());
    if (auto ptr_type = semantic_array_type.as_shared<PointerType>()) {
        result_type = ptr_type->pointed_type;
    } else if (auto vec_type = semantic_array_type.as_shared<VectorType>()) {
        result_type = vec_type->element_type;
    } else if (auto arr_type = semantic_array_type.as_shared<ArrayType>()) {
        result_type = arr_type->element_type;
    }
    return collect_make<ArraySubscriptExpr>(std::move(array), std::move(index), result_type, loc);
}

std::unique_ptr<Expr> Collect::collect_member_pointer_literal_expression(
    const std::string& owner_name,
    const std::string& member_name,
    SrcLoc loc) const {

    auto owner_type_raw = collect_lookup_tag_type(owner_name, true);
    auto owner_type =
        dyn_cast_shared<ObjectType>(desugar_type(owner_type_raw, ast_ctx_.get()));
    if (!owner_type) {
        report_error("pointer-to-member owner '" + owner_name +
                     "' is not a class/struct/union type", loc);
        return collect_make<ErrorExpr>("invalid pointer-to-member owner", loc);
    }
    if (owner_type->isIncomplete()) {
        report_error("cannot form pointer-to-member of incomplete type '" +
                     owner_name + "'", loc);
        return collect_make<ErrorExpr>("incomplete pointer-to-member owner", loc);
    }

    FieldLookupResult lookup;
    std::vector<uint32_t> path;
    find_field_recursive(owner_type.get(), member_name, path, 0, lookup);
    if (lookup.matches == 0 || !lookup.field) {
        auto method_lookup = find_record_method(owner_type.get(), member_name);
        if (method_lookup.matches == 1 && method_lookup.method) {
            if (method_lookup.method->is_static) {
                report_error(
                    "cannot form pointer-to-member for static member function '" +
                        member_name + "'",
                    loc);
                return collect_make<ErrorExpr>(
                    "invalid member pointer target", loc);
            }
            if (!method_lookup.method->symbol) {
                report_error(
                    "internal error: unresolved member function symbol '" +
                        member_name + "'",
                    loc);
                return collect_make<ErrorExpr>(
                    "unresolved member function symbol", loc);
            }
            auto method_owner_type = method_lookup.owner_record_decl
                ? method_lookup.owner_record_decl->get_record_type()
                : nullptr;
            if (!method_owner_type) {
                report_error(
                    "internal error: unresolved member-function owner for '" +
                        member_name + "'",
                    loc);
                return collect_make<ErrorExpr>(
                    "invalid member-function owner", loc);
            }

            QualType owner_qual(owner_type);
            QualType method_owner_qual(method_owner_type);
            QualType member_qual = cpp_written_method_type(
                method_lookup.method->type,
                ast_ctx_.get());
            QualType member_ptr_type(
                std::make_shared<MemberPointerType>(owner_qual, member_qual));
            QualType method_owner_member_ptr_type(std::make_shared<MemberPointerType>(
                method_owner_qual, member_qual));

            auto conversion = analyze_member_pointer_conversion(
                method_owner_member_ptr_type, member_ptr_type);
            if (!conversion.viable) {
                report_error(
                    "member-function owner '" +
                        method_owner_qual.to_string() +
                        "' is not compatible with pointer owner '" +
                        owner_qual.to_string() + "'",
                    loc);
                return collect_make<ErrorExpr>(
                    "incompatible member-function pointer owner", loc);
            }

            int32_t virtual_slot_index = -1;
            if (method_lookup.method->is_virtual &&
                method_lookup.method->virtual_slot_index >= 0) {
                virtual_slot_index = method_lookup.method->virtual_slot_index;
            }
            return collect_make<MemberPointerLiteralExpr>(
                member_ptr_type,
                conversion.owner_adjustment,
                /*is_function_member=*/true,
                method_lookup.method->symbol,
                virtual_slot_index,
                ast_ctx_ ? ast_ctx_->intern_identifier(member_name) : nullptr,
                loc);
        }
        if (method_lookup.matches > 1) {
            report_error("member '" + member_name + "' is ambiguous", loc);
            return collect_make<ErrorExpr>("ambiguous member pointer target", loc);
        }
        report_error("type has no member named '" + member_name + "'", loc);
        return collect_make<ErrorExpr>("invalid member pointer target", loc);
    }
    if (lookup.matches > 1) {
        report_error("member '" + member_name + "' is ambiguous", loc);
        return collect_make<ErrorExpr>("ambiguous member pointer target", loc);
    }
    if (lookup.field->is_bitfield) {
        report_error("cannot take address of bit-field", loc);
        return collect_make<ErrorExpr>("bit-field member pointer target", loc);
    }

    QualType owner_qual(owner_type);
    QualType member_qual = lookup.field->type;
    QualType member_ptr_type(
        std::make_shared<MemberPointerType>(owner_qual, member_qual));

    return collect_make<MemberPointerLiteralExpr>(
        member_ptr_type,
        static_cast<int64_t>(lookup.byte_offset),
        /*is_function_member=*/false,
        /*method_symbol=*/nullptr,
        /*virtual_slot_index=*/-1,
        ast_ctx_ ? ast_ctx_->intern_identifier(member_name) : nullptr,
        loc);
}

std::unique_ptr<Expr> Collect::collect_member_pointer_access_expression(
    std::unique_ptr<Expr> base,
    std::unique_ptr<Expr> member_pointer,
    bool is_arrow,
    SrcLoc loc) const {

    member_pointer =
        collect_apply_standard_conversions(std::move(member_pointer), ExprUseContext::RValue);
    if (is_arrow) {
        base = collect_apply_standard_conversions(
            std::move(base),
            ExprUseContext::RValue);
    }

    QualType base_type = base ? base->get_type() : QualType();
    QualType member_ptr_type = member_pointer ? member_pointer->get_type() : QualType();
    if ((base &&
         expression_depends_on_template_parameters(base.get())) ||
        (member_pointer &&
         expression_depends_on_template_parameters(member_pointer.get())) ||
        type_depends_on_template_parameters(member_ptr_type, ast_ctx_.get()) ||
        type_depends_on_template_parameters(base_type, ast_ctx_.get())) {
        return collect_make<DependentMemberPointerAccessExpr>(
            std::move(base),
            std::move(member_pointer),
            QualType(std::make_shared<AutoType>(AutoTypeFlavor::Cxx)),
            is_arrow,
            loc);
    }
    auto member_ptr_canonical =
        desugar_type(member_ptr_type, ast_ctx_.get()).as_shared<MemberPointerType>();
    if (!member_ptr_canonical) {
        report_error("right operand of member-pointer access is not a pointer-to-member", loc);
        return collect_make<ErrorExpr>("invalid member-pointer operand", loc);
    }
    if (!member_ptr_canonical->member_type) {
        report_error("invalid pointer-to-member type", loc);
        return collect_make<ErrorExpr>("invalid member-pointer type", loc);
    }
    bool is_function_member =
        canonical_type_kind(member_ptr_canonical->member_type, ast_ctx_.get()) ==
        TypeKind::Function;

    auto owner_object_type =
        desugar_type(member_ptr_canonical->class_type, ast_ctx_.get())
            .as_shared<ObjectType>();
    if (!owner_object_type) {
        report_error("pointer-to-member owner type is not a class/struct/union", loc);
        return collect_make<ErrorExpr>("invalid member-pointer owner", loc);
    }

    QualType base_object_type = nullptr;
    if (is_arrow) {
        base_type = base ? base->get_type() : QualType();
        auto base_ptr =
            desugar_type(remove_reference(base_type, ast_ctx_.get()), ast_ctx_.get())
                .as_shared<PointerType>();
        if (!base_ptr) {
            report_error("left operand of '->*' must be pointer type", loc);
            return collect_make<ErrorExpr>("invalid arrow-star base", loc);
        }
        auto pointed_owner =
            desugar_type(base_ptr->pointed_type, ast_ctx_.get()).as_shared<ObjectType>();
        if (!pointed_owner) {
            report_error("left operand of '->*' must be pointer to class/struct/union type",
                         loc);
            return collect_make<ErrorExpr>("invalid arrow-star base", loc);
        }
        base_object_type = base_ptr->pointed_type;
    } else {
        auto semantic_base =
            desugar_type(remove_reference(base_type, ast_ctx_.get()), ast_ctx_.get())
                .as_shared<ObjectType>();
        if (!semantic_base) {
            report_error("left operand of '.*' must be class/struct/union type", loc);
            return collect_make<ErrorExpr>("invalid dot-star base", loc);
        }
        base_object_type = remove_reference(base_type, ast_ctx_.get());
    }

    auto base_object_canonical =
        desugar_type(base_object_type, ast_ctx_.get()).as_shared<ObjectType>();
    if (!base_object_canonical) {
        report_error("member-pointer access base is not an object type", loc);
        return collect_make<ErrorExpr>("invalid member-pointer base", loc);
    }

    bool same_owner = base_object_type.equals_unqualified(member_ptr_canonical->class_type);
    if (!same_owner) {
        QualType target_owner =
            desugar_type(base_object_type, ast_ctx_.get()).without_qualifiers();
        QualType converted_member_ptr_type(std::make_shared<MemberPointerType>(
            target_owner, member_ptr_canonical->member_type));
        auto conversion = analyze_member_pointer_conversion(
            member_ptr_type, converted_member_ptr_type);
        if (!conversion.viable) {
            report_error("member-pointer owner '" +
                             member_ptr_canonical->class_type.to_string() +
                             "' is not compatible with base type '" +
                             target_owner.to_string() + "'",
                         loc);
            return collect_make<ErrorExpr>("incompatible member-pointer base", loc);
        }
        member_pointer = cast_if_needed(std::move(member_pointer), converted_member_ptr_type);
        member_ptr_type = converted_member_ptr_type;
        member_ptr_canonical =
            desugar_type(member_ptr_type, ast_ctx_.get()).as_shared<MemberPointerType>();
        if (!member_ptr_canonical) {
            report_error("invalid pointer-to-member type", loc);
            return collect_make<ErrorExpr>("invalid member-pointer type", loc);
        }
    }

    QualType result_type = member_ptr_canonical->member_type;
    uint8_t base_quals = QUAL_NONE;
    if (is_arrow) {
        auto base_ptr =
            desugar_type(remove_reference(base_type, ast_ctx_.get()), ast_ctx_.get())
                .as_shared<PointerType>();
        if (base_ptr) {
            base_quals = base_ptr->pointed_type.get_qualifiers();
        }
    } else if (base_object_type) {
        base_quals = base_object_type.get_qualifiers();
    }
    if (!is_function_member && base_quals != QUAL_NONE && result_type) {
        result_type = result_type.with_qualifiers(base_quals);
    }

    return collect_make<MemberPointerAccessExpr>(
        std::move(base),
        std::move(member_pointer),
        result_type,
        is_arrow,
        is_function_member,
        loc);
}


std::unique_ptr<Expr> Collect::collect_member_expression(
    std::unique_ptr<Expr> base,
    const std::string& member_name,
    bool is_arrow,
    SrcLoc loc,
    bool allow_overloaded_method_set,
    bool suppress_virtual_dispatch,
    bool requires_template_keyword) {

    const std::string* interned_member_name =
        ast_ctx_ ? ast_ctx_->intern_identifier(member_name) : nullptr;
    auto make_member_expr = [&](std::unique_ptr<Expr> member_base)
        -> std::unique_ptr<MemberExpr> {
        if (interned_member_name) {
            return collect_make<MemberExpr>(
                std::move(member_base),
                interned_member_name,
                is_arrow,
                suppress_virtual_dispatch,
                loc);
        }
        return collect_make<MemberExpr>(
            std::move(member_base),
            member_name,
            is_arrow,
            suppress_virtual_dispatch,
            loc);
    };

    if (is_arrow) {
        base = collect_apply_standard_conversions(std::move(base), ExprUseContext::RValue);
        if (lang_opts_.is_cxx_mode() && base) {
            size_t arrow_rewrite_depth = 0;
            bool saw_overloaded_arrow = false;
            while (base) {
                auto semantic_arrow_base =
                    remove_reference_and_desugar(
                        base->get_type(),
                        ast_ctx_.get());
                if (!semantic_arrow_base) {
                    break;
                }
                if (semantic_arrow_base.as_shared<PointerType>()) {
                    break;
                }

                auto arrow_record = semantic_arrow_base.as_shared<ObjectType>();
                if (!arrow_record) {
                    if (saw_overloaded_arrow) {
                        report_error(
                            "result of overloaded operator-> is not a pointer or class type",
                            loc);
                    } else {
                        report_error("arrow operator requires pointer type", loc);
                    }
                    return make_member_expr(std::move(base));
                }

                if (arrow_rewrite_depth >= kOperatorArrowMaxRewriteDepth) {
                    report_error(
                        "overloaded operator-> recursion depth exceeded", loc);
                    return collect_make<ErrorExpr>(
                        "overloaded operator-> recursion depth exceeded", loc);
                }

                bool had_member_match = false;
                bool saw_private_method = false;
                bool saw_protected_method = false;
                std::vector<OverloadCallCandidate> overload_candidates;
                if (auto candidate_error = append_member_overload_candidates(
                        arrow_record.get(),
                        "operator->",
                        base.get(),
                        OverloadImplicitObjectArgKind::None,
                        overload_candidates,
                        had_member_match,
                        saw_private_method,
                        saw_protected_method,
                        loc)) {
                    return candidate_error;
                }

                if (had_member_match && overload_candidates.empty()) {
                    if (auto inaccessible_error = report_inaccessible_member(
                            "operator->",
                            saw_private_method,
                            saw_protected_method,
                            loc)) {
                        return inaccessible_error;
                    }
                }

                if (overload_candidates.empty()) {
                    report_error("arrow operator requires pointer type", loc);
                    return make_member_expr(std::move(base));
                }

                std::vector<std::unique_ptr<Expr>> operator_args;
                std::shared_ptr<Symbol> selected_symbol = nullptr;
                OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
                    OverloadImplicitObjectArgKind::None;
                if (auto overload_error = select_overload_candidate(
                        "operator->",
                        overload_candidates,
                        operator_args,
                        base.get(),
                        loc,
                        selected_symbol,
                        selected_implicit_object_arg_kind)) {
                    return overload_error;
                }

                if (!selected_symbol) {
                    report_error("arrow operator requires pointer type", loc);
                    return make_member_expr(std::move(base));
                }

                auto implicit_object_arg = build_overload_implicit_object_arg(
                    selected_implicit_object_arg_kind,
                    std::move(base),
                    /*object_expr_is_pointer=*/false,
                    loc);

                if (selected_implicit_object_arg_kind !=
                        OverloadImplicitObjectArgKind::None &&
                    implicit_object_arg) {
                    operator_args.insert(
                        operator_args.begin(), std::move(implicit_object_arg));
                }

                auto callee_expr = make_hidden_overload_callee(
                    std::move(selected_symbol), loc);
                base = collect_function_call(
                    std::move(callee_expr), std::move(operator_args), loc);
                if (base && isa<ErrorExpr>(base.get())) {
                    return base;
                }
                saw_overloaded_arrow = true;
                ++arrow_rewrite_depth;
            }
        }
    }
    auto member = make_member_expr(std::move(base));
    if (!member->base) {
        return member;
    }
    auto base_type = member->base->get_type();
    if (!base_type) {
        return member;
    }
    auto semantic_base_type =
        remove_reference_and_desugar(base_type, ast_ctx_.get());
    auto dependent_base_analysis =
        lang_opts_.is_cxx_mode()
            ? analyze_cpp_member_lookup_base(
                  base_type,
                  is_arrow,
                  session_.func_state_.current_function_is_cpp_member
                      ? session_.func_state_.current_function_cpp_this_type
                      : QualType(nullptr),
                  ast_ctx_.get())
            : CppMemberLookupBaseAnalysis{};
    bool dependent_base_expr =
        lang_opts_.is_cxx_mode() &&
        expression_depends_on_template_parameters(member->base.get());
    bool dependent_base_type = dependent_base_analysis.is_dependent;
    auto dependent_record_type = dependent_base_analysis.object_record_type;
    const ObjectDecl* current_record_decl =
        current_access_context_record_decl(
            session_.func_state_.current_function_is_cpp_member,
            session_.func_state_.current_function_cpp_this_type,
            session_.func_state_.current_function_cpp_friend_access_type,
            session_.current_cpp_record_lookup_type_,
            ast_ctx_.get());
    bool is_current_instantiation =
        dependent_base_analysis.is_current_instantiation;
    bool names_dependent_base = false;
    if (is_current_instantiation &&
        record_has_dependent_bases(current_record_decl) &&
        dependent_record_type &&
        !lookup_record_member_name(
             dependent_record_type.get(),
             member_name).has_member_match()) {
        names_dependent_base = true;
    }

    if (lang_opts_.is_cxx_mode() &&
        (dependent_base_expr || dependent_base_type || names_dependent_base)) {
        QualType dependent_declared_member_type;
        QualType dependent_member_type =
            names_dependent_base
                ? QualType(nullptr)
                : try_synthesize_dependent_member_type(
                      base_type,
                      is_arrow,
                      member_name,
                      loc,
                      &dependent_declared_member_type);
        auto unresolved_member = collect_make<UnresolvedMemberExpr>(
            std::move(member->base),
            member_name,
            dependent_member_type,
            std::nullopt,
            is_arrow,
            is_current_instantiation,
            names_dependent_base,
            requires_template_keyword,
            suppress_virtual_dispatch,
            loc);
        unresolved_member->declared_member_type =
            dependent_declared_member_type;
        return unresolved_member;
    }

    std::shared_ptr<ObjectType> record_type = nullptr;
    if (is_arrow) {
        auto ptr_type = semantic_base_type.as_shared<PointerType>();
        if (!ptr_type) {
            report_error("arrow operator requires pointer type", loc);
            return member;
        }
        record_type =
            desugar_type(ptr_type->pointed_type, ast_ctx_.get()).as_shared<ObjectType>();
        if (!record_type) {
            report_error("arrow operator requires pointer to class/struct/union type", loc);
            return member;
        }
    } else {
        record_type = semantic_base_type.as_shared<ObjectType>();
        if (!record_type) {
            report_error("dot operator requires class/struct/union type", loc);
            return member;
        }
    }

    const ObjectDecl* object_record_decl = record_decl_from_record_type(record_type.get());
    const ObjectDecl* access_context_decl =
        lang_opts_.is_cxx_mode()
            ? current_access_context_record_decl(
                  session_.func_state_.current_function_is_cpp_member,
                  session_.func_state_.current_function_cpp_this_type,
                  session_.func_state_.current_function_cpp_friend_access_type,
                  session_.current_cpp_record_lookup_type_,
                  ast_ctx_.get())
            : nullptr;
    auto current_scope_matches_owner =
        [&](const ObjectDecl* owner_decl) {
            auto current_record_scope =
                desugar_type(session_.current_cpp_record_lookup_type_, ast_ctx_.get())
                    .as_shared<ObjectType>();
            const ObjectDecl* scope_decl =
                record_decl_from_record_type(current_record_scope.get());
            if (!owner_decl || !scope_decl) {
                return false;
            }
            owner_decl = canonical_record_decl(owner_decl);
            scope_decl = canonical_record_decl(scope_decl);
            return owner_decl == scope_decl || owner_decl->tag == scope_decl->tag;
        };
    if (record_type->isIncomplete()) {
        report_error("cannot access member of incomplete type", loc);
        return member;
    }
    record_type->getWidth();

    FieldLookupResult lookup;
    std::vector<uint32_t> path;
    find_field_recursive(record_type.get(), member_name, path, 0, lookup);
    if (lookup.matches == 0 || lookup.field == nullptr) {
        auto method_lookup = find_record_method(record_type.get(), member_name);
        auto method_template_matches =
            find_record_method_templates(record_type.get(), member_name);
        size_t total_method_matches =
            static_cast<size_t>(method_lookup.matches) +
            method_template_matches.size();
        if (total_method_matches == 1 &&
            method_lookup.matches == 1 &&
            method_lookup.method &&
            method_template_matches.empty()) {
            if (lang_opts_.is_cxx_mode()) {
                if (method_lookup.method->declared_access ==
                        RecordMemberAccess::Protected &&
                    !can_access_protected_member_in_context(
                        method_lookup.owner_record_decl,
                        access_context_decl,
                        object_record_decl,
                        method_lookup.method->is_static) &&
                    !current_scope_matches_owner(method_lookup.owner_record_decl)) {
                    report_error(
                        "member '" + member_name + "' is protected within this context",
                        loc);
                    return member;
                }
                if (method_lookup.method->declared_access ==
                        RecordMemberAccess::Private &&
                    !can_access_private_member_in_context(
                        method_lookup.owner_record_decl, access_context_decl) &&
                    !current_scope_matches_owner(method_lookup.owner_record_decl)) {
                    report_error(
                        "member '" + member_name + "' is private within this context",
                        loc);
                    return member;
                }
            }
            member->member_type = method_lookup.method->type;
            return member;
        }
        if (total_method_matches > 0) {
            if (lang_opts_.is_cxx_mode() &&
                method_lookup.matches == 0 &&
                method_template_matches.size() == 1 &&
                method_template_matches.front().method_template) {
                const auto* method_template =
                    method_template_matches.front().method_template;
                if (method_template->declared_access ==
                        RecordMemberAccess::Protected &&
                    !can_access_protected_member_in_context(
                        method_template_matches.front().owner_record_decl,
                        access_context_decl,
                        object_record_decl,
                        method_template->is_static) &&
                    !current_scope_matches_owner(
                        method_template_matches.front().owner_record_decl)) {
                    report_error(
                        "member '" + member_name + "' is protected within this context",
                        loc);
                    return member;
                }
                if (method_template->declared_access ==
                        RecordMemberAccess::Private &&
                    !can_access_private_member_in_context(
                        method_template_matches.front().owner_record_decl,
                        access_context_decl) &&
                    !current_scope_matches_owner(
                        method_template_matches.front().owner_record_decl)) {
                    report_error(
                        "member '" + member_name + "' is private within this context",
                        loc);
                    return member;
                }
            }
            if (allow_overloaded_method_set) {
                return member;
            }
            report_error("member '" + member_name + "' is ambiguous", loc);
            return member;
        }
        report_error("type has no member named '" + member_name + "'", loc);
        return member;
    }
    if (lookup.matches > 1) {
        report_error("member '" + member_name + "' is ambiguous", loc);
        return member;
    }
    if (lang_opts_.is_cxx_mode()) {
        if (lookup.field->declared_access == RecordMemberAccess::Protected &&
            !can_access_protected_member_in_context(
                lookup.owner_record_decl,
                access_context_decl,
                object_record_decl,
                false) &&
            !current_scope_matches_owner(lookup.owner_record_decl)) {
            report_error(
                "member '" + member_name + "' is protected within this context",
                loc);
            return member;
        }
        if (lookup.field->declared_access == RecordMemberAccess::Private &&
            !can_access_private_member_in_context(
                lookup.owner_record_decl, access_context_decl) &&
            !current_scope_matches_owner(lookup.owner_record_decl)) {
            report_error(
                "member '" + member_name + "' is private within this context",
                loc);
            return member;
        }
    }

    member->member_type = lookup.field->type;
    member->declared_member_type = lookup.field->type;
    member->virtual_base_record_decl = lookup.virtual_base_record_decl;
    member->field_index = static_cast<uint32_t>(lookup.path.empty() ? 0 : lookup.path.back());
    member->field_path = lookup.path;
    member->byte_offset = static_cast<uint32_t>(
        lookup.virtual_base_record_decl
            ? lookup.relative_byte_offset
            : lookup.byte_offset);
    if (lookup.field->is_bitfield) {
        member->is_bitfield = true;
        ast_ctx_->set_bitfield_info(member->node_id, {
            lookup.field->bit_offset,
            lookup.field->bit_width,
            lookup.field->storage_size
        });
    }

    uint8_t base_quals = QUAL_NONE;
    if (is_arrow) {
        auto ptr_type =
            remove_reference_and_desugar(
                member->base->get_type(),
                ast_ctx_.get())
                .as_shared<PointerType>();
        if (ptr_type) {
            base_quals = ptr_type->pointed_type.get_qualifiers();
        }
    } else {
        base_quals =
            remove_reference(member->base->get_type(), ast_ctx_.get()).get_qualifiers();
    }
    if (base_quals != QUAL_NONE && member->member_type) {
        member->member_type = member->member_type.with_qualifiers(base_quals);
    }
    return member;
}
