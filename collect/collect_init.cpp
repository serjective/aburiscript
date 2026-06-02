#include "collect.h"
#include "collect_internal.h"
#include "../helpers/auto_type_utils.h"

namespace {
bool is_narrow_character_builtin_kind(BuiltinTypes kind) {
    return kind == BuiltinTypes::Char ||
           kind == BuiltinTypes::SChar ||
           kind == BuiltinTypes::UChar;
}

bool record_semantics_describes_aggregate(
    const RecordSemanticState* record_state) {
    if (!record_state) {
        return true;
    }

    if (record_state->definition_data.has_user_declared_constructor ||
        record_state->is_polymorphic) {
        return false;
    }
    for (const auto& base : record_state->bases) {
        if (base.is_virtual ||
            base.declared_access != RecordMemberAccess::Public) {
            return false;
        }
    }
    for (const auto& field : record_state->fields) {
        if (!field.is_base_subobject &&
            field.declared_access != RecordMemberAccess::Public) {
            return false;
        }
    }
    return true;
}

bool string_array_element_types_compatible(const QualType& target_elem,
                                           const QualType& literal_elem,
                                           ASTContext* ast_ctx,
                                           bool cxx_mode) {
    if (!target_elem || !literal_elem) {
        return false;
    }
    QualType target_canonical =
        ast_ctx ? desugar_type(target_elem, ast_ctx) : target_elem;
    QualType literal_canonical =
        ast_ctx ? desugar_type(literal_elem, ast_ctx) : literal_elem;

    if (target_elem.equals_unqualified(literal_elem) ||
        target_canonical.equals_unqualified(literal_canonical)) {
        return true;
    }

    auto target_builtin =
        dyn_cast_shared<BuiltinType>(target_canonical.get_shared());
    auto literal_builtin =
        dyn_cast_shared<BuiltinType>(literal_canonical.get_shared());
    if (!target_builtin || !literal_builtin) {
        return false;
    }

    if (is_narrow_character_builtin_kind(target_builtin->builtin_kind) &&
        is_narrow_character_builtin_kind(literal_builtin->builtin_kind)) {
        return true;
    }

    if (cxx_mode) {
        return target_builtin->builtin_kind == literal_builtin->builtin_kind;
    }

    // Accept typedef-level signedness differences when width matches
    // (for example, wchar_t aliases backed by int/unsigned int).
    return target_builtin->isInteger() && literal_builtin->isInteger() &&
           target_builtin->getWidth() == literal_builtin->getWidth();
}

bool is_same_type_object_prvalue_for_initialization(
    const Collect& collect,
    Expr* expr,
    QualType target_type,
    const ASTContext* ast_ctx) {
    if (!expr || !target_type) {
        return false;
    }

    QualType source_type = expr->get_type();
    if (!source_type) {
        return false;
    }

    QualType canonical_target =
        collect_internal::remove_reference_and_desugar(target_type, ast_ctx);
    QualType canonical_source =
        collect_internal::remove_reference_and_desugar(source_type, ast_ctx);
    if (!canonical_target ||
        !canonical_source ||
        canonical_target->kind != TypeKind::Object ||
        canonical_source->kind != TypeKind::Object) {
        return false;
    }

    bool same_object_type =
        canonical_source.equals_unqualified(canonical_target) ||
        types_equivalent_after_template_argument_canonicalization(
            source_type,
            target_type,
            ast_ctx,
            /*ignore_top_level_qualifiers=*/true);
    return same_object_type &&
           collect.classify_value_category(expr) == Collect::ValueCategory::PRValue;
}

Expr* unwrap_initializer_parens(Expr* expr) {
    while (auto* paren = dyn_cast<ParenExpr>(expr)) {
        expr = paren->subexpr.get();
    }
    return expr;
}
}

void Collect::find_field_recursive(const ObjectType* record, const std::string& name, std::vector<uint32_t>& path, size_t base_offset, FieldLookupResult& result) const {
    collect_internal::RecordFieldLookupResult internal_result{
        result.field,
        result.owner_record_decl,
        result.virtual_base_record_decl,
        result.path,
        result.byte_offset,
        result.relative_byte_offset,
        result.matches};
    collect_internal::lookup_record_field_recursive(
        record,
        name,
        path,
        base_offset,
        internal_result,
        ast_ctx_.get());
    result.field = internal_result.field;
    result.owner_record_decl = internal_result.owner_record_decl;
    result.virtual_base_record_decl = internal_result.virtual_base_record_decl;
    result.path = internal_result.path;
    result.byte_offset = internal_result.byte_offset;
    result.relative_byte_offset = internal_result.relative_byte_offset;
    result.matches = internal_result.matches;
}


int Collect::classify_type(QualType type) const {

    if (!type) return 0;
    auto canonical = desugar_type(type, ast_ctx_.get());
    if (!canonical) return 0;
    if (canonical->isVoid()) return 0;
    if (canonical->isInteger()) return 1;
    if (canonical->kind == TypeKind::Enum) return 3;
    if (canonical->isFloatingPoint()) return 8;
    if (canonical->kind == TypeKind::Pointer) return 5;
    if (canonical->kind == TypeKind::Object) return 12;
    if (canonical->kind == TypeKind::Array) return 14;
    if (canonical->kind == TypeKind::Function) return 10;
    return -1;
}


bool Collect::contains_auto_type(const std::shared_ptr<CType>& type) const {

    if (!type) {
        return false;
    }
    if (isa<AutoType>(type.get())) {
        return true;
    }
    if (auto ptr = dyn_cast_shared<PointerType>(type)) {
        return contains_auto_type(ptr->pointed_type.get_shared());
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(type)) {
        return contains_auto_type(ref->referred_type.get_shared());
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(type)) {
        return contains_auto_type(blk->pointed_type.get_shared());
    }
    if (auto arr = dyn_cast_shared<ArrayType>(type)) {
        return contains_auto_type(arr->element_type.get_shared());
    }
    if (auto func = dyn_cast_shared<FunctionType>(type)) {
        if (contains_auto_type(func->ret_type.get_shared())) {
            return true;
        }
        for (const auto& p : func->parameters) {
            if (contains_auto_type(p.get_shared())) {
                return true;
            }
        }
    }
    return false;
}


std::shared_ptr<CType> Collect::replace_auto_type(const std::shared_ptr<CType>& type, const std::shared_ptr<CType>& deduced) const {

    if (!type) {
        return type;
    }
    if (isa<AutoType>(type.get())) {
        return deduced;
    }
    if (auto ptr = dyn_cast_shared<PointerType>(type)) {
        auto replaced = replace_auto_type(ptr->pointed_type.get_shared(), deduced);
        return std::make_shared<PointerType>(
            QualType(replaced, ptr->pointed_type.get_qualifiers()));
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(type)) {
        auto replaced = replace_auto_type(ref->referred_type.get_shared(), deduced);
        return std::make_shared<ReferenceType>(
            QualType(replaced, ref->referred_type.get_qualifiers()),
            ref->reference_kind);
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(type)) {
        auto replaced = replace_auto_type(blk->pointed_type.get_shared(), deduced);
        return std::make_shared<BlockPointerType>(
            QualType(replaced, blk->pointed_type.get_qualifiers()));
    }
    if (auto arr = dyn_cast_shared<ArrayType>(type)) {
        auto replaced = replace_auto_type(arr->element_type.get_shared(), deduced);
        QualType elem_qt(replaced, arr->element_type.get_qualifiers());
        if (arr->size_kind == ArraySizeKind::Variable) {
            return std::make_shared<ArrayType>(elem_qt, arr->size_expr);
        }
        return std::make_shared<ArrayType>(elem_qt, arr->size);
    }
    if (auto func = dyn_cast_shared<FunctionType>(type)) {
        auto rebuilt = std::make_shared<FunctionType>();
        rebuilt->ret_type = QualType(
            replace_auto_type(func->ret_type.get_shared(), deduced),
            func->ret_type.get_qualifiers());
        rebuilt->parameters.reserve(func->parameters.size());
        for (const auto& param : func->parameters) {
            rebuilt->parameters.push_back(QualType(
                replace_auto_type(param.get_shared(), deduced),
                param.get_qualifiers()));
        }
        rebuilt->parameter_pack_flags = func->parameter_pack_flags;
        rebuilt->normalize_parameter_pack_flags();
        rebuilt->is_variadic = func->is_variadic;
        rebuilt->has_prototype = func->has_prototype;
        rebuilt->member_ref_qualifier = func->member_ref_qualifier;
        return rebuilt;
    }
    return type;
}


bool Collect::contains_typeof_expr_type(const std::shared_ptr<CType>& type) const {

    if (!type) {
        return false;
    }
    if (isa<TypeofExprType>(type.get()) ||
        isa<DecltypeExprType>(type.get())) {
        return true;
    }
    if (auto ptr = dyn_cast_shared<PointerType>(type)) {
        return contains_typeof_expr_type(ptr->pointed_type.get_shared());
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(type)) {
        return contains_typeof_expr_type(blk->pointed_type.get_shared());
    }
    if (auto arr = dyn_cast_shared<ArrayType>(type)) {
        return contains_typeof_expr_type(arr->element_type.get_shared());
    }
    if (auto func = dyn_cast_shared<FunctionType>(type)) {
        if (contains_typeof_expr_type(func->ret_type.get_shared())) {
            return true;
        }
        for (const auto& p : func->parameters) {
            if (contains_typeof_expr_type(p.get_shared())) {
                return true;
            }
        }
    }
    return false;
}


QualType Collect::resolve_typeof_types(QualType type, SrcLoc loc) {
    return finalize_deferred_semantic_type(type, loc);
}


bool Collect::is_aggregate_type(const std::shared_ptr<CType>& type) const {

    if (!type) {
        return false;
    }
    auto canonical_type = desugar_type(type, ast_ctx_.get());
    if (!canonical_type) {
        return false;
    }
    if (canonical_type->kind == TypeKind::Array) {
        return true;
    }
    if (canonical_type->kind != TypeKind::Object) {
        return false;
    }
    if (!lang_opts_.is_cxx_mode()) {
        return true;
    }

    auto record_type = dyn_cast_shared<ObjectType>(canonical_type);
    auto* record_decl =
        record_type ? dyn_cast<ObjectDecl>(record_type->get_decl()) : nullptr;
    const RecordSemanticState* record_state =
        record_decl ? record_semantics_cache_lookup(record_decl) : nullptr;

    return record_semantics_describes_aggregate(record_state);
}


bool Collect::eval_designator_index_expr(Expr* expr, int64_t& out) const {

    if (!expr) {
        return false;
    }
    auto expr_type = expr->get_type();
    if (!expr_type || !expr_type->isInteger()) {
        report_error("designator index must be an integer constant expression", expr->location);
        return false;
    }
    auto val = try_evaluate_with_consteval_compat(expr, ConstEvalMode::c_ice());
    if (!val.has_value()) {
        report_error("designator index must be a constant expression", expr->location);
        return false;
    }
    out = *val;
    return true;
}


std::shared_ptr<CType> Collect::init_get_child_type(std::shared_ptr<CType> parent_type, size_t index, SrcLoc loc) const {

    if (!parent_type) {
        return nullptr;
    }
    auto canonical_parent = desugar_type(parent_type, ast_ctx_.get());
    auto canonical_kind = canonical_parent ? canonical_parent->kind : TypeKind::Other;
    if (canonical_kind == TypeKind::Array) {
        auto arr = dyn_cast_shared<ArrayType>(canonical_parent);
        if (!arr) {
            return nullptr;
        }
        if (arr->size_kind == ArraySizeKind::Constant &&
            arr->size.has_value() &&
            index >= arr->size.value()) {
            report_error("array designator index out of bounds", loc);
            return nullptr;
        }
        return arr->element_type.get_shared();
    }
    if (canonical_kind == TypeKind::Object) {
        auto record = dyn_cast_shared<ObjectType>(canonical_parent);
        if (!record) {
            return nullptr;
        }
        const auto& fields = record->semantic_fields();
        if (index >= fields.size()) {
            report_error("field index out of bounds in designated initializer", loc);
            return nullptr;
        }
        return fields[index].type.get_shared();
    }
    report_error("designator used on non-aggregate type", loc);
    return nullptr;
}


void Collect::init_assign_to_path(InitListExpr* out, std::shared_ptr<CType> cur_type, const std::vector<size_t>& path, size_t depth, std::shared_ptr<Expr> value, SrcLoc loc) const {

    if (!out || depth >= path.size()) {
        report_error("internal error: invalid designated initializer path", loc);
        return;
    }
    size_t idx = path[depth];
    if (depth + 1 == path.size()) {
        auto record_type = dyn_cast_shared<ObjectType>(cur_type);
        if (record_type && record_type->is_union) {
            if (!out->mappings.empty() && !out->mappings.count(idx)) {
                report_warning("overlapping union initializer; last value wins", loc);
            }
            if (out->mappings.count(idx)) {
                report_warning("duplicate designated initializer; last value wins", loc);
            }
            // Union semantics: the last explicit initializer wins.
            out->mappings.clear();
            out->mappings[idx] = value;
            return;
        }
        if (out->mappings.count(idx)) {
            auto* existing_list = dyn_cast<InitListExpr>(out->mappings[idx].get());
            auto* incoming_list = dyn_cast<InitListExpr>(value.get());
            if (existing_list && incoming_list) {
                // Preserve earlier designated values and merge incoming subobject writes.
                for (const auto& [sub_idx, sub_expr] : incoming_list->mappings) {
                    existing_list->mappings[sub_idx] = sub_expr;
                }
                for (const auto& action : incoming_list->actions) {
                    existing_list->actions.push_back(action);
                }
                return;
            }
            report_warning("duplicate designated initializer; last value wins", loc);
        }
        out->mappings[idx] = value;
        return;
    }

    std::shared_ptr<CType> child_type = init_get_child_type(cur_type, idx, loc);
    if (!child_type) {
        return;
    }

    InitListExpr* child_list = nullptr;
    auto it = out->mappings.find(idx);
    if (it != out->mappings.end()) {
        child_list = dyn_cast<InitListExpr>(it->second.get());
        if (!child_list) {
            report_warning("designated initializer overrides previous scalar initializer", loc);
            auto new_list = collect_make<InitListExpr>(loc);
            new_list->type = QualType(child_type);
            auto shared_list = std::shared_ptr<Expr>(std::move(new_list));
            child_list = dyn_cast<InitListExpr>(shared_list.get());
            it->second = std::move(shared_list);
        }
    } else {
        auto new_list = collect_make<InitListExpr>(loc);
        new_list->type = QualType(child_type);
        auto shared_list = std::shared_ptr<Expr>(std::move(new_list));
        child_list = dyn_cast<InitListExpr>(shared_list.get());
        out->mappings[idx] = std::move(shared_list);
    }

    init_assign_to_path(child_list, child_type, path, depth + 1, value, loc);
}


bool Collect::resolve_initializer_designators(const std::vector<Designator>& designators, std::shared_ptr<CType> base_type, std::vector<ResolvedInitPath>& out_paths, size_t& outer_end, bool& has_range) const {

    if (!base_type) {
        report_error("invalid type for designated initializer", SrcLoc());
        return false;
    }
    base_type = desugar_type(base_type, ast_ctx_.get());
    has_range = false;
    bool outer_set = false;

    std::vector<size_t> current;
    std::function<bool(size_t, std::shared_ptr<CType>)> walk =
        [&](size_t idx, std::shared_ptr<CType> cur_type) -> bool {
        cur_type = desugar_type(cur_type, ast_ctx_.get());
        if (idx >= designators.size()) {
            ResolvedInitPath rp;
            rp.path = current;
            rp.target_type = cur_type;
            out_paths.push_back(std::move(rp));
            return true;
        }

        const Designator& d = designators[idx];
        if (d.kind == Designator::Kind::Field) {
            auto record_type = dyn_cast_shared<ObjectType>(cur_type);
            if (!record_type) {
                report_error("field designator used on non-struct/union type", d.loc);
                return false;
            }
            const ObjectType::Field* field = record_type->findField(d.field_name);
            if (field) {
                size_t field_index = 0;
                const auto& fields = record_type->semantic_fields();
                for (size_t i = 0; i < fields.size(); ++i) {
                    if (&fields[i] == field) {
                        field_index = i;
                        break;
                    }
                }
                if (!outer_set && idx == 0) {
                    outer_end = field_index;
                    outer_set = true;
                }
                current.push_back(field_index);
                bool ok = walk(idx + 1, field->type.get_shared());
                current.pop_back();
                return ok;
            }

            FieldLookupResult lookup;
            std::vector<uint32_t> search_path;
            find_field_recursive(record_type.get(), d.field_name, search_path, 0, lookup);
            if (!lookup.field) {
                report_error("unknown field in designated initializer: " + d.field_name, d.loc);
                return false;
            }
            if (!outer_set && idx == 0 && !lookup.path.empty()) {
                outer_end = lookup.path.front();
                outer_set = true;
            }
            for (size_t pi : lookup.path) {
                current.push_back(pi);
            }
            bool ok = walk(idx + 1, lookup.field->type.get_shared());
            for (size_t pi = 0; pi < lookup.path.size(); ++pi) {
                current.pop_back();
            }
            return ok;
        }

        if (d.kind == Designator::Kind::Index || d.kind == Designator::Kind::Range) {
            auto arr_type = dyn_cast_shared<ArrayType>(cur_type);
            if (!arr_type) {
                report_error("array designator used on non-array type", d.loc);
                return false;
            }

            int64_t start_val = 0;
            if (!eval_designator_index_expr(d.index.get(), start_val)) {
                return false;
            }
            int64_t end_val = start_val;
            if (d.kind == Designator::Kind::Range) {
                has_range = true;
                if (!eval_designator_index_expr(d.range_end.get(), end_val)) {
                    return false;
                }
            }
            if (start_val < 0 || end_val < 0) {
                report_error("designator index must be non-negative", d.loc);
                return false;
            }
            if (end_val < start_val) {
                report_error("designator range must have start <= end", d.loc);
                return false;
            }
            if (!outer_set && idx == 0) {
                outer_end = static_cast<size_t>(end_val);
                outer_set = true;
            }
            if (arr_type->size_kind == ArraySizeKind::Constant && arr_type->size.has_value()) {
                size_t limit = arr_type->size.value();
                if (static_cast<size_t>(end_val) >= limit) {
                    report_error("array designator index out of bounds", d.loc);
                    return false;
                }
            }
            for (int64_t i = start_val; i <= end_val; ++i) {
                current.push_back(static_cast<size_t>(i));
                bool ok = walk(idx + 1, arr_type->element_type.get_shared());
                current.pop_back();
                if (!ok) {
                    return false;
                }
            }
            return true;
        }

        report_error("unsupported designator kind", d.loc);
        return false;
    };

    return walk(0, base_type);
}


std::unique_ptr<Expr> Collect::transform_init_value(std::unique_ptr<Expr> expr, std::shared_ptr<CType> type) {

    if (!expr) {
        return nullptr;
    }
    if (auto* inner_list = dyn_cast<InitListExpr>(expr.get())) {
        auto owned = std::unique_ptr<InitListExpr>(static_cast<InitListExpr*>(expr.release()));
        return process_init_list_expression(std::move(owned), type);
    }
    if (lang_opts_.is_cxx_mode() &&
        type &&
        canonical_type_kind(QualType(type), ast_ctx_.get()) ==
            TypeKind::Reference) {
        auto ref_type = desugar_type(QualType(type), ast_ctx_.get())
            .as_shared<ReferenceType>();
        if (!ref_type || !ref_type->referred_type) {
            report_error("invalid reference initializer",
                         expr ? expr->location : SrcLoc());
            return expr;
        }

        Expr* raw_init = strip_implicit_casts(expr.get());
        auto init_category =
            classify_value_category(raw_init ? raw_init : expr.get());
        if (ref_type->isLValueReference()) {
            bool binds_temporary =
                init_category == ValueCategory::PRValue ||
                init_category == ValueCategory::XValue;
            if (binds_temporary && !ref_type->referred_type.is_const()) {
                report_error(
                    "non-const lvalue reference cannot bind to temporary",
                    expr ? expr->location : SrcLoc());
            }
        } else if (ref_type->isRValueReference() &&
                   init_category == ValueCategory::LValue) {
            report_error(
                "rvalue reference cannot bind to lvalue",
                expr ? expr->location : SrcLoc());
        }

        if (expr && expr->get_type() &&
            init_category != ValueCategory::LValue) {
            expr = cast_if_needed(std::move(expr), ref_type->referred_type);
        }
        return expr;
    }
    if (lang_opts_.is_cxx_mode() &&
        type &&
        canonical_type_kind(QualType(type), ast_ctx_.get()) == TypeKind::Object &&
        !is_aggregate_type(type)) {
        if (is_same_type_object_prvalue_for_initialization(
                *this,
                expr.get(),
                QualType(type),
                ast_ctx_.get())) {
            return expr;
        }
        SrcLoc loc = expr->location;
        std::vector<std::unique_ptr<Expr>> init_args;
        init_args.push_back(std::move(expr));
        return collect_member_initializer_expression(
            std::move(init_args),
            QualType(type),
            /*is_list_init=*/false,
            loc,
            /*allow_abstract_object_type_instantiation=*/false,
            /*is_copy_initialization=*/true);
    }
    expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::InitScalar);
    if (type) {
        QualType target_type(type);
        QualType source_type = expr ? expr->get_type() : QualType();
        if (source_type &&
            canonical_type_kind(target_type, ast_ctx_.get()) ==
                TypeKind::MemberPointer) {
            auto source_kind = canonical_type_kind(source_type, ast_ctx_.get());
            if (source_kind == TypeKind::MemberPointer) {
                if (!member_pointer_convertible_to(source_type, target_type)) {
                    report_error("incompatible member pointer conversion in initialization",
                                 expr ? expr->location : SrcLoc());
                }
            } else if (source_type->isInteger()) {
                if (!is_null_pointer_constant_expr(expr.get())) {
                    report_error(
                        "incompatible integer to member pointer conversion in initialization",
                        expr ? expr->location : SrcLoc());
                }
            }
        }
        expr = cast_if_needed(std::move(expr), target_type);
    }
    return expr;
}


std::unique_ptr<Expr> Collect::init_from_single_value(std::unique_ptr<Expr> value, std::shared_ptr<CType> type, SrcLoc loc) {

    if (!type) {
        report_error("invalid type in initializer", loc);
        return nullptr;
    }
    type = desugar_type(type, ast_ctx_.get());
    if (auto* inner_list = dyn_cast<InitListExpr>(value.get())) {
        auto owned = std::unique_ptr<InitListExpr>(static_cast<InitListExpr*>(value.release()));
        return process_init_list_expression(std::move(owned), type);
    }
    if (!is_aggregate_type(type)) {
        return transform_init_value(std::move(value), type);
    }
    if (type->kind == TypeKind::Array) {
        auto arr = dyn_cast_shared<ArrayType>(type);
        if (!arr) {
            return nullptr;
        }
        auto list = collect_make<InitListExpr>(loc);
        list->type = QualType(type);
        auto elem = init_from_single_value(std::move(value), arr->element_type.get_shared(), loc);
        if (elem) {
            std::shared_ptr<Expr> shared_elem = std::move(elem);
            std::vector<size_t> path = {0};
            init_assign_to_path(list.get(), type, path, 0, shared_elem, loc);
            InitAction action;
            action.paths.push_back(path);
            action.value = shared_elem;
            action.loc = loc;
            list->actions.push_back(std::move(action));
        }
        return list;
    }
    if (type->kind == TypeKind::Object) {
        auto record = dyn_cast_shared<ObjectType>(type);
        if (!record) {
            return nullptr;
        }

        // Struct/union copy initialization is valid for non-list values of compatible type.
        auto val_type = desugar_type(value->get_type(), ast_ctx_.get());
        if (val_type->kind == TypeKind::Object &&
            val_type.equals_unqualified(QualType(type))) {
            return cast_if_needed(
                collect_apply_standard_conversions(std::move(value), ExprUseContext::InitScalar),
                QualType(type));
        }

        auto list = collect_make<InitListExpr>(loc);
        list->type = QualType(type);
        const auto& fields = record->semantic_fields();
        if (!fields.empty()) {
            size_t first_field = 0;
            while (first_field < fields.size() &&
                   fields[first_field].is_bitfield &&
                   fields[first_field].name.empty()) {
                ++first_field;
            }
            if (first_field < fields.size()) {
                auto elem = init_from_single_value(
                    std::move(value), fields[first_field].type.get_shared(), loc);
                if (elem) {
                    std::shared_ptr<Expr> shared_elem = std::move(elem);
                    std::vector<size_t> path = {first_field};
                    init_assign_to_path(list.get(), type, path, 0, shared_elem, loc);
                    InitAction action;
                    action.paths.push_back(path);
                    action.value = shared_elem;
                    action.loc = loc;
                    list->actions.push_back(std::move(action));
                }
            }
        }
        return list;
    }
    return transform_init_value(std::move(value), type);
}


std::unique_ptr<Expr> Collect::consume_for_type(std::vector<InitElement>& elements, size_t& index, std::shared_ptr<CType> type, bool ignore_first_designators, size_t array_start_index) {

    if (index >= elements.size()) {
        return nullptr;
    }
    type = desugar_type(type, ast_ctx_.get());
    if (type && type->kind == TypeKind::Array) {
        // Nested flexible-array-member initializers must not mutate the
        // canonical field type on the record declaration. Work on a cloned
        // array type so each aggregate object can materialize its own trailing
        // storage independently.
        type = collect_internal::clone_top_level_incomplete_array(QualType(type)).get_shared();
    }
    InitElement& elem = elements[index];
    if (!ignore_first_designators && !elem.designators.empty()) {
        return nullptr;
    }

    if (auto* inner_list = dyn_cast<InitListExpr>(elem.value.get())) {
        auto owned = std::unique_ptr<InitListExpr>(static_cast<InitListExpr*>(elem.value.release()));
        ++index;
        return process_init_list_expression(std::move(owned), type);
    }

    if (type && type->kind == TypeKind::Array && elem.value && isa<StringLiteral>(elem.value.get())) {
        auto arr_type = dyn_cast_shared<ArrayType>(type);
        auto* str_lit = dyn_cast<StringLiteral>(elem.value.get());
        auto str_lit_type = str_lit ? str_lit->ctype.as_shared<ArrayType>() : nullptr;
        if (arr_type && str_lit_type &&
            string_array_element_types_compatible(arr_type->element_type,
                                                  str_lit_type->element_type,
                                                  ast_ctx_.get(),
                                                  lang_opts_.is_cxx_mode())) {
            auto value = std::move(elem.value);
            if (str_lit_type && arr_type->size_kind == ArraySizeKind::Constant && arr_type->size.has_value()) {
                str_lit_type->size = arr_type->size;
            } else if (str_lit_type && arr_type->size_kind == ArraySizeKind::Incomplete) {
                arr_type->size_kind = ArraySizeKind::Constant;
                arr_type->size = str_lit_type->size;
            }
            ++index;
            return value;
        }
    }

    if (type && type->kind == TypeKind::Array) {
        auto arr_type = dyn_cast_shared<ArrayType>(type);
        if (!arr_type) {
            return nullptr;
        }
        if (arr_type->size_kind == ArraySizeKind::Variable) {
            report_error("initializer lists for VLAs are not supported", elem.loc);
            return nullptr;
        }

        auto new_list = collect_make<InitListExpr>(elem.loc);
        new_list->type = QualType(type);
        size_t limit = std::numeric_limits<size_t>::max();
        if (arr_type->size_kind == ArraySizeKind::Constant && arr_type->size.has_value()) {
            limit = arr_type->size.value();
        }

        size_t i = array_start_index;
        bool first = true;
        while (i < limit) {
            auto sub = consume_for_type(
                elements, index, arr_type->element_type.get_shared(),
                ignore_first_designators && first, 0);
            if (!sub) {
                break;
            }
            std::shared_ptr<Expr> shared_sub = std::move(sub);
            std::vector<size_t> path = {i};
            init_assign_to_path(new_list.get(), type, path, 0, shared_sub, elem.loc);
            InitAction action;
            action.paths.push_back(path);
            action.value = shared_sub;
            action.loc = elem.loc;
            new_list->actions.push_back(std::move(action));
            ++i;
            first = false;
        }
        if (arr_type->size_kind == ArraySizeKind::Incomplete) {
            arr_type->size_kind = ArraySizeKind::Constant;
            arr_type->size = i;
        }
        return new_list;
    }

    if (type && type->kind == TypeKind::Object) {
        auto record_type = dyn_cast_shared<ObjectType>(type);
        if (!record_type) {
            report_error("invalid record type in initializer", elem.loc);
            return nullptr;
        }

        if (!is_aggregate_type(type)) {
            auto value = std::move(elem.value);
            ++index;
            return transform_init_value(std::move(value), type);
        }

        if (elem.value && !isa<InitListExpr>(elem.value.get())) {
            auto original_type =
                desugar_type(elem.value->get_type(), ast_ctx_.get());
            bool is_direct_aggregate_copy =
                original_type &&
                original_type->kind == TypeKind::Object &&
                original_type.equals_unqualified(QualType(type));
            if (is_direct_aggregate_copy) {
                auto transformed = transform_init_value(std::move(elem.value), type);
                if (!transformed) {
                    report_error("invalid aggregate copy initializer", elem.loc);
                    return nullptr;
                }
                ++index;
                return transformed;
            }
        }

        auto new_list = collect_make<InitListExpr>(elem.loc);
        new_list->type = QualType(type);

        const auto& fields = record_type->semantic_fields();
        size_t field_count = fields.size();
        size_t i = 0;
        if (record_type->is_union) {
            while (i < field_count &&
                   fields[i].name.empty() &&
                   fields[i].is_bitfield) {
                ++i;
            }
            field_count = std::min(field_count, i + 1);
        }

        bool first = true;
        while (i < field_count) {
            if (fields[i].name.empty() && fields[i].is_bitfield) {
                ++i;
                continue;
            }
            auto sub = consume_for_type(
                elements, index, fields[i].type.get_shared(),
                ignore_first_designators && first, 0);
            if (!sub) {
                break;
            }
            std::shared_ptr<Expr> shared_sub = std::move(sub);
            std::vector<size_t> path = {i};
            init_assign_to_path(new_list.get(), type, path, 0, shared_sub, elem.loc);
            InitAction action;
            action.paths.push_back(path);
            action.value = shared_sub;
            action.loc = elem.loc;
            new_list->actions.push_back(std::move(action));
            ++i;
            first = false;
        }
        return new_list;
    }

    auto value = std::move(elem.value);
    ++index;
    return transform_init_value(std::move(value), type);
}


std::unique_ptr<Expr> Collect::process_init_list_expression(std::unique_ptr<InitListExpr> init_list, std::shared_ptr<CType> type) {

    if (!init_list) {
        return nullptr;
    }
    if (!type) {
        report_error("invalid type for initializer list", init_list->location);
        return nullptr;
    }
    type = desugar_type(type, ast_ctx_.get());

    if (type->kind == TypeKind::Vector) {
        auto vec_type = dyn_cast_shared<VectorType>(type);
        auto out = collect_make<InitListExpr>(init_list->location);
        out->type = QualType(type);
        size_t i = 0;
        for (auto& elem : init_list->elements) {
            if (i >= vec_type->num_elements) {
                report_error("excess elements in vector initializer", elem.loc);
                break;
            }
            auto val = transform_init_value(
                std::move(elem.value), vec_type->element_type.get_shared());
            if (!val) {
                ++i;
                continue;
            }
            std::shared_ptr<Expr> shared_val = std::move(val);
            out->mappings[i] = shared_val;
            InitAction action;
            action.paths.push_back({i});
            action.value = shared_val;
            action.loc = elem.loc;
            out->actions.push_back(std::move(action));
            ++i;
        }
        return out;
    }

    if (type->kind == TypeKind::Array && init_list->elements.size() == 1) {
        auto* str_lit = dyn_cast<StringLiteral>(init_list->elements[0].value.get());
        if (str_lit) {
            auto arr_type = dyn_cast_shared<ArrayType>(type);
            auto str_lit_type = str_lit->ctype.as_shared<ArrayType>();
            if (arr_type && str_lit_type &&
                string_array_element_types_compatible(arr_type->element_type,
                                                      str_lit_type->element_type,
                                                      ast_ctx_.get(),
                                                      lang_opts_.is_cxx_mode())) {
                auto value = std::move(init_list->elements[0].value);
                auto* moved_lit = dyn_cast<StringLiteral>(value.get());
                auto moved_lit_type = moved_lit ? moved_lit->ctype.as_shared<ArrayType>() : nullptr;
                if (moved_lit_type && arr_type->size_kind == ArraySizeKind::Constant &&
                    arr_type->size.has_value()) {
                    moved_lit_type->size = arr_type->size;
                } else if (moved_lit_type && arr_type->size_kind == ArraySizeKind::Incomplete) {
                    arr_type->size_kind = ArraySizeKind::Constant;
                    arr_type->size = moved_lit_type->size;
                }
                return value;
            }
        }
    }

    ObjectInitializationRecordSemantics object_record_semantics;
    bool has_cxx_object_record_semantics =
        lang_opts_.is_cxx_mode() &&
        canonical_type_kind(QualType(type), ast_ctx_.get()) == TypeKind::Object;
    if (has_cxx_object_record_semantics) {
        object_record_semantics =
            collect_object_initialization_record_semantics(
                QualType(type),
                init_list->location);
    }

    bool aggregate_type = is_aggregate_type(type);
    if (object_record_semantics.record_type && object_record_semantics.state) {
        aggregate_type =
            record_semantics_describes_aggregate(object_record_semantics.state);
    }

    if (!aggregate_type) {
        // Non-aggregate braces are treated like a single scalar/object
        // initializer with optional nested brace elision.
        for (const auto& elem : init_list->elements) {
            if (!elem.designators.empty()) {
                report_error("designated initializer is only valid for aggregates", elem.loc);
                return nullptr;
            }
        }
        if (lang_opts_.is_cxx_mode() &&
            canonical_type_kind(QualType(type), ast_ctx_.get()) == TypeKind::Object) {
            if (init_list->elements.empty()) {
                const RecordSemanticState* object_state =
                    object_record_semantics.state;
                if (!object_state ||
                    (object_state->constructors.empty() &&
                     object_state->method_templates.empty())) {
                    return collect_cpp_value_init_expression(
                        QualType(type),
                        init_list->location);
                }
            }
            std::vector<std::unique_ptr<Expr>> init_args;
            init_args.reserve(init_list->elements.size());
            for (auto& elem : init_list->elements) {
                if (!elem.value) {
                    report_error("missing initializer expression", elem.loc);
                    continue;
                }
                init_args.push_back(std::move(elem.value));
            }
            return collect_member_initializer_expression(
                std::move(init_args),
                QualType(type),
                /*is_list_init=*/true,
                init_list->location,
                /*allow_abstract_object_type_instantiation=*/false,
                /*is_copy_initialization=*/true);
        }
        size_t idx = 0;
        return consume_for_type(init_list->elements, idx, type, false, 0);
    }

    if (type->kind == TypeKind::Object) {
        auto record_type =
            object_record_semantics.record_type
                ? object_record_semantics.record_type
                : dyn_cast_shared<ObjectType>(type);
        const RecordSemanticState* record_state = object_record_semantics.state;
        if (record_type &&
            record_type->isIncomplete() &&
            (!record_state || record_state->is_incomplete)) {
            report_error("cannot initialize variable of incomplete struct type", init_list->location);
            return nullptr;
        }
    }

    auto out = collect_make<InitListExpr>(init_list->location);
    out->type = QualType(type);
    auto elements = std::move(init_list->elements);
    size_t index = 0;
    size_t cursor_index = 0;
    // Tracks continuation point for partially-filled nested arrays so later
    // siblings append instead of restarting at element zero.
    std::unordered_map<size_t, size_t> nested_array_cursor;

    auto get_element_type = [&](size_t idx) -> std::shared_ptr<CType> {
        if (type->kind == TypeKind::Array) {
            auto arr = dyn_cast_shared<ArrayType>(type);
            return arr ? arr->element_type.get_shared() : nullptr;
        }
        auto record = dyn_cast_shared<ObjectType>(type);
        if (!record) {
            return nullptr;
        }
        const auto& fields = record->semantic_fields();
        if (idx >= fields.size()) {
            return nullptr;
        }
        return fields[idx].type.get_shared();
    };

    auto max_index_for_aggregate = [&]() -> std::optional<size_t> {
        if (type->kind == TypeKind::Array) {
            auto arr = dyn_cast_shared<ArrayType>(type);
            if (arr && arr->size_kind == ArraySizeKind::Constant && arr->size.has_value()) {
                return arr->size.value();
            }
            return std::nullopt;
        }
        auto record = dyn_cast_shared<ObjectType>(type);
        if (record) {
            return record->semantic_fields().size();
        }
        return std::nullopt;
    };

    while (index < elements.size()) {
        InitElement& elem = elements[index];
        if (elem.designators.empty()) {
            if (auto record = dyn_cast_shared<ObjectType>(type)) {
                const auto& fields = record->semantic_fields();
                while (cursor_index < fields.size() &&
                       fields[cursor_index].is_bitfield &&
                       fields[cursor_index].name.empty()) {
                    ++cursor_index;
                }
            }

            auto limit = max_index_for_aggregate();
            if (limit.has_value() && cursor_index >= *limit) {
                ++index;
                continue;
            }

            auto target_type = get_element_type(cursor_index);
            auto canon_target_type =
                desugar_type(target_type, ast_ctx_.get());
            if (!target_type) {
                ++index;
                continue;
            }

            SrcLoc elem_loc = elem.loc;
            size_t array_start_index = 0;
            bool has_nested_array_cursor = false;
            if (canon_target_type->kind == TypeKind::Array) {
                auto it = nested_array_cursor.find(cursor_index);
                if (it != nested_array_cursor.end()) {
                    has_nested_array_cursor = true;
                    array_start_index = it->second;
                }
            }
            auto init_val = consume_for_type(
                elements, index, target_type, false, array_start_index);
            if (!init_val) {
                break;
            }
            std::shared_ptr<Expr> shared_init = std::move(init_val);
            std::vector<size_t> path = {cursor_index};
            init_assign_to_path(out.get(), type, path, 0, shared_init, elem_loc);
            bool emitted_leaf_actions = false;
            if (has_nested_array_cursor &&
                canon_target_type->kind == TypeKind::Array) {
                if (auto* consumed_list = dyn_cast<InitListExpr>(shared_init.get())) {
                    emitted_leaf_actions = true;
                    for (const auto& [sub_idx, sub_expr] : consumed_list->mappings) {
                        InitAction action;
                        action.paths.push_back({cursor_index, sub_idx});
                        action.value = sub_expr;
                        action.loc = elem_loc;
                        out->actions.push_back(std::move(action));
                    }
                }
            }
            if (!emitted_leaf_actions) {
                InitAction action;
                action.paths.push_back(path);
                action.value = shared_init;
                action.loc = elem_loc;
                out->actions.push_back(std::move(action));
            }
            if (has_nested_array_cursor &&
                canon_target_type->kind == TypeKind::Array) {
                auto arr_type = dyn_cast_shared<ArrayType>(
                    desugar_type(target_type, ast_ctx_.get()));
                size_t next_array_index = array_start_index;
                if (auto* consumed_list = dyn_cast<InitListExpr>(shared_init.get())) {
                    if (!consumed_list->mappings.empty()) {
                        next_array_index = consumed_list->mappings.rbegin()->first + 1;
                    } else {
                        next_array_index = array_start_index;
                    }
                } else {
                    next_array_index = array_start_index + 1;
                }
                if (arr_type && arr_type->size_kind == ArraySizeKind::Constant &&
                    arr_type->size.has_value() &&
                    next_array_index >= arr_type->size.value()) {
                    nested_array_cursor.erase(cursor_index);
                    ++cursor_index;
                } else {
                    nested_array_cursor[cursor_index] = next_array_index;
                }
            } else {
                nested_array_cursor.erase(cursor_index);
                ++cursor_index;
            }
            continue;
        }

        size_t outer_end = 0;
        bool has_range = false;
        std::vector<ResolvedInitPath> paths;
        if (!resolve_initializer_designators(elem.designators, type, paths, outer_end, has_range)) {
            return nullptr;
        }
        if (paths.empty()) {
            ++index;
            continue;
        }

        if (has_range) {
            auto raw_value = std::move(elem.value);
            SrcLoc elem_loc = elem.loc;
            ++index;
            auto init_val = init_from_single_value(
                std::move(raw_value), paths[0].target_type, elem_loc);
            if (init_val) {
                std::shared_ptr<Expr> shared_init = std::move(init_val);
                InitAction action;
                action.loc = elem_loc;
                action.value = shared_init;
                for (const auto& path : paths) {
                    action.paths.push_back(path.path);
                    init_assign_to_path(out.get(), type, path.path, 0, shared_init, elem_loc);
                }
                out->actions.push_back(std::move(action));
            }
        } else {
            SrcLoc elem_loc = elem.loc;
            const auto& full_path = paths[0].path;
            std::vector<size_t> assign_path = full_path;
            std::shared_ptr<CType> consume_type = paths[0].target_type;

            auto init_val = consume_for_type(elements, index, consume_type, true, 0);
            if (init_val) {
                std::shared_ptr<Expr> shared_init = std::move(init_val);
                // Keep the full designated path for promoted anonymous members
                // inside unions. Collapsing {outer, inner...} to {outer} would
                // reinterpret a nested field designator as "initialize the first
                // field of the outer aggregate", which corrupts constant union
                // initializers.
                init_assign_to_path(out.get(), type, assign_path, 0, shared_init, elem_loc);
                InitAction action;
                action.paths.push_back(assign_path);
                action.value = shared_init;
                action.loc = elem_loc;
                out->actions.push_back(std::move(action));
            } else {
                ++index;
            }
        }

        nested_array_cursor.clear();
        cursor_index = outer_end + 1;
        const auto& cursor_path = paths.back().path;
        if (cursor_path.size() >= 2) {
            size_t outer_idx = cursor_path[0];
            auto outer_type = get_element_type(outer_idx);
            auto outer_arr = dyn_cast_shared<ArrayType>(
                desugar_type(outer_type, ast_ctx_.get()));
            if (outer_arr && outer_arr->size_kind == ArraySizeKind::Constant &&
                outer_arr->size.has_value()) {
                size_t next_inner = cursor_path[1] + 1;
                if (next_inner < outer_arr->size.value()) {
                    cursor_index = outer_idx;
                    nested_array_cursor[outer_idx] = next_inner;
                }
            }
        }
    }

    if (type->kind == TypeKind::Array) {
        auto arr_type = dyn_cast_shared<ArrayType>(type);
        if (arr_type && arr_type->size_kind == ArraySizeKind::Incomplete) {
            arr_type->size_kind = ArraySizeKind::Constant;
            if (!out->mappings.empty()) {
                arr_type->size = out->mappings.rbegin()->first + 1;
            } else {
                arr_type->size = 0;
            }
        }
    }

    return out;
}


std::unique_ptr<Expr> Collect::process_initializer_for_type(std::unique_ptr<Expr> init, QualType declared_type, SrcLoc loc) {

    if (!init) {
        return nullptr;
    }
    auto type = desugar_type(declared_type, ast_ctx_.get());
    if (!type) {
        return init;
    }
    if (lang_opts_.is_cxx_mode() &&
        auto_type_utils::has_cxx_auto_type(declared_type.get_shared())) {
        return init;
    }

    if (type->kind == TypeKind::Reference) {
        auto ref_type = type.as_shared<ReferenceType>();
        if (!ref_type || !ref_type->referred_type) {
            report_error("invalid reference initializer", loc);
            return init;
        }

        Expr* raw_init = strip_implicit_casts(init.get());
        auto init_category = classify_value_category(raw_init ? raw_init : init.get());

        if (ref_type->isLValueReference()) {
            bool binds_temporary =
                init_category == ValueCategory::PRValue ||
                init_category == ValueCategory::XValue;
            if (binds_temporary && !ref_type->referred_type.is_const()) {
                report_error("non-const lvalue reference cannot bind to temporary", loc);
            }
        } else if (ref_type->isRValueReference()) {
            if (init_category == ValueCategory::LValue) {
                report_error("rvalue reference cannot bind to lvalue", loc);
            }
        }

        if (init && init->get_type()) {
            init = cast_if_needed(std::move(init), ref_type->referred_type);
        }
        return init;
    }

    if (auto* init_list = dyn_cast<InitListExpr>(init.get())) {
        if (collect_internal::init_list_has_lowered_semantics_for_type(
                init_list, declared_type, ast_ctx_.get())) {
            return init;
        }
        if (expression_depends_on_template_parameters(init_list) ||
            collect_internal::initializer_target_type_requires_deferred_semantics(
                declared_type,
                ast_ctx_.get())) {
            return init;
        }
        auto owned = std::unique_ptr<InitListExpr>(static_cast<InitListExpr*>(init.release()));
        auto processed = process_init_list_expression(std::move(owned), type.get_shared());
        if (!processed) {
            return collect_make<ErrorExpr>("invalid initializer list", loc);
        }
        return processed;
    }

    Expr* syntactic_init = unwrap_initializer_parens(init.get());

    if (auto* str_lit = dyn_cast<StringLiteral>(syntactic_init)) {
        if (type->kind == TypeKind::Array) {
            auto arr_type = type.as_shared<ArrayType>();
            auto str_lit_type = str_lit->ctype.as_shared<ArrayType>();
            if (!arr_type || !str_lit_type) {
                report_error("incompatible variable for string literal initializer", loc);
                return init;
            }
            auto target_elem = arr_type->element_type;
            auto literal_elem = str_lit_type->element_type;
            bool compatible_elem =
                string_array_element_types_compatible(target_elem,
                                                      literal_elem,
                                                      ast_ctx_.get(),
                                                      lang_opts_.is_cxx_mode());
            if (!compatible_elem) {
                report_error("incompatible variable for string literal initializer", loc);
                return init;
            }
            if (arr_type->size_kind == ArraySizeKind::Incomplete) {
                arr_type->size_kind = ArraySizeKind::Constant;
                if (str_lit_type) {
                    arr_type->size = str_lit_type->size;
                }
            } else if (arr_type->size_kind == ArraySizeKind::Constant &&
                       arr_type->size.has_value() && str_lit_type) {
                str_lit_type->size = arr_type->size;
            } else if (arr_type->size_kind == ArraySizeKind::Variable) {
                report_error("string literal initializer for VLA is not supported", loc);
            }
            return init;
        }
        if (type->kind == TypeKind::Pointer) {
            return cast_if_needed(
                collect_apply_standard_conversions(std::move(init), ExprUseContext::InitScalar),
                declared_type);
        }
        report_error("incompatible variable for string literal initializer", loc);
        return init;
    }

    if (type->kind == TypeKind::Array) {
        if (auto* comp_lit = dyn_cast<CompoundLiteralExpr>(init.get())) {
            auto dst_arr = type.as_shared<ArrayType>();
            auto src_arr =
                desugar_type(comp_lit->get_type(), ast_ctx_.get())
                    .as_shared<ArrayType>();
            if (dst_arr && src_arr &&
                dst_arr->element_type.equals_unqualified(src_arr->element_type)) {
                if (dst_arr->size_kind == ArraySizeKind::Incomplete) {
                    dst_arr->size_kind = src_arr->size_kind;
                    dst_arr->size = src_arr->size;
                    dst_arr->size_expr = src_arr->size_expr;
                }
                if (comp_lit->init) {
                    return process_initializer_for_type(
                        std::move(comp_lit->init), declared_type, loc);
                }
                return init;
            }
        }
        report_error("array initializer must be an initializer list or string literal", loc);
        return init;
    }

    if (lang_opts_.is_cxx_mode() &&
        type->kind != TypeKind::Object &&
        type->kind != TypeKind::Reference) {
        auto init_type = init->get_type();
        bool skip_conversion_check =
            !init_type ||
            expression_depends_on_template_parameters(init.get()) ||
            type_depends_on_template_parameters(declared_type, ast_ctx_.get()) ||
            type_depends_on_template_parameters(init_type, ast_ctx_.get()) ||
            contains_deferred_semantic_type(declared_type.get_shared()) ||
            contains_deferred_semantic_type(init_type.get_shared()) ||
            auto_type_utils::has_cxx_auto_type(declared_type.get_shared()) ||
            auto_type_utils::has_cxx_auto_type(init_type.get_shared());
        if (!skip_conversion_check) {
            auto seq = build_cpp_overload_conversion_sequence(init.get(), declared_type);
            if (!seq.viable) {
                report_error("cannot initialize '" + declared_type.to_string() +
                                 "' with an expression of type '" +
                                 init_type.to_string() + "'",
                             loc);
            } else if (seq.kind == ConversionSequenceKind::UserDefined) {
                init = build_cpp_user_defined_conversion_expr(
                    std::move(init), declared_type, loc);
                return cast_if_needed(std::move(init), declared_type);
            }
        }
    }

    if (type->kind == TypeKind::Object) {
        auto init_type = desugar_type(init->get_type(), ast_ctx_.get());
        auto init_object_type = remove_reference(init_type, ast_ctx_.get());
        if (!init_object_type || !init_object_type.equals_unqualified(type)) {
            report_error("invalid initializer for aggregate type", loc);
        }
        return cast_if_needed(
            collect_apply_standard_conversions(std::move(init), ExprUseContext::InitScalar),
            declared_type);
    }

    init = collect_apply_standard_conversions(std::move(init), ExprUseContext::InitScalar);
    return cast_if_needed(std::move(init), declared_type);
}
