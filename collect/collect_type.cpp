#include "collect.h"
#include "collect_template_state.h"

#include <algorithm>
#include <unordered_set>

namespace aburi::collect {

namespace {

cir::TypeRef remove_top_level_qualifiers(cir::File& file,
                                         cir::TypeRef operand,
                                         uint8_t qualifiers) {
    operand.type = file.resolved_type(operand.type);
    operand.qualifiers = static_cast<uint8_t>(operand.qualifiers & ~qualifiers);
    if (!file.valid(operand.type) ||
        file.type(operand.type).kind != cir::TypeKind::Array) {
        return operand;
    }

    const auto array =
        std::get<cir::ArrayTypePayload>(file.type_payload(operand.type));
    cir::TypeRef element =
        remove_top_level_qualifiers(file, array.element_type, qualifiers);
    operand.type = file.array_type(element,
                                   array.size_kind,
                                   array.size,
                                   array.size_expr,
                                   array.size_expr_is_dependent,
                                   array.extent_param,
                                   array.dependent_size_expr);
    return operand;
}

cir::TypeRef apply_remove_const(cir::File& file, cir::TypeRef operand) {
    return remove_top_level_qualifiers(file, operand, cir::QualConst);
}

cir::TypeRef apply_remove_volatile(cir::File& file, cir::TypeRef operand) {
    return remove_top_level_qualifiers(file, operand, cir::QualVolatile);
}

cir::TypeRef apply_remove_cv(cir::File& file, cir::TypeRef operand) {
    return remove_top_level_qualifiers(
        file, operand, cir::QualConst | cir::QualVolatile);
}

cir::TypeRef apply_remove_reference(cir::File& file,
                                    cir::TypeRef operand) {
    uint8_t qualifiers = operand.qualifiers;
    cir::TypeId type = operand.type;
    while (file.valid(type) &&
           file.type(type).kind == cir::TypeKind::Typedef) {
        const auto& alias =
            std::get<cir::TypedefTypePayload>(file.type_payload(type));
        qualifiers = static_cast<uint8_t>(
            qualifiers | alias.underlying_type.qualifiers);
        type = alias.underlying_type.type;
    }
    operand.type = file.resolved_type(type);
    operand.qualifiers = qualifiers;
    if (std::holds_alternative<cir::ReferenceTypePayload>(
            file.type_payload(operand.type))) {
        return file.reference_referred_ref(operand.type);
    }
    return operand;
}

cir::TypeRef apply_remove_cvref(cir::File& file, cir::TypeRef operand) {
    return apply_remove_cv(file, apply_remove_reference(file, operand));
}

cir::TypeRef apply_underlying_type(cir::File& file, cir::TypeRef operand) {
    cir::TypeId resolved = file.resolved_type(operand.type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Enum) {
        return {};
    }
    const auto* enumeration =
        std::get_if<cir::EnumTypePayload>(&file.type_payload(resolved));
    return enumeration ? enumeration->underlying_type : cir::TypeRef{};
}

cir::TypeRef add_array_cv_qualifiers(cir::File& file,
                                     cir::TypeRef type,
                                     uint8_t qualifiers) {
    constexpr uint8_t cv_mask = cir::QualConst | cir::QualVolatile;
    uint8_t cv_qualifiers = static_cast<uint8_t>(qualifiers & cv_mask);
    type.type = file.resolved_type(type.type);
    if (cv_qualifiers == cir::QualNone || !file.valid(type.type) ||
        file.type(type.type).kind != cir::TypeKind::Array) {
        type.qualifiers = static_cast<uint8_t>(type.qualifiers | qualifiers);
        return type;
    }

    const auto array =
        std::get<cir::ArrayTypePayload>(file.type_payload(type.type));
    cir::TypeRef element =
        add_array_cv_qualifiers(file, array.element_type, cv_qualifiers);
    type.type = file.array_type(element,
                                array.size_kind,
                                array.size,
                                array.size_expr,
                                array.size_expr_is_dependent,
                                array.extent_param,
                                array.dependent_size_expr);
    type.qualifiers = static_cast<uint8_t>(
        (type.qualifiers | qualifiers) & ~cv_mask);
    return type;
}

cir::TypeRef apply_remove_extent(cir::File& file, cir::TypeRef operand) {
    operand.type = file.resolved_type(operand.type);
    if (!file.valid(operand.type) ||
        file.type(operand.type).kind != cir::TypeKind::Array) {
        return operand;
    }
    const auto& array =
        std::get<cir::ArrayTypePayload>(file.type_payload(operand.type));
    cir::TypeRef element =
        add_array_cv_qualifiers(file, array.element_type, operand.qualifiers);
    if (operand.memory_space != cir::MemorySpace::Default) {
        element.memory_space = operand.memory_space;
    }
    return element;
}

cir::TypeRef apply_remove_all_extents(cir::File& file,
                                      cir::TypeRef operand) {
    while (operand.valid()) {
        cir::TypeId resolved = file.resolved_type(operand.type);
        if (!file.valid(resolved) ||
            file.type(resolved).kind != cir::TypeKind::Array) {
            break;
        }
        operand = apply_remove_extent(file, operand);
    }
    return operand;
}

bool is_referenceable_type(const cir::File& file, cir::TypeRef operand) {
    cir::TypeId resolved = file.resolved_type(operand.type);
    if (!file.valid(resolved)) {
        return false;
    }
    if (file.type(resolved).kind == cir::TypeKind::Builtin) {
        const auto* builtin =
            std::get_if<cir::BuiltinTypePayload>(&file.type_payload(resolved));
        return !builtin || builtin->kind != cir::BuiltinTypeKind::Void;
    }
    if (file.type(resolved).kind != cir::TypeKind::Function) {
        return true;
    }
    const auto& function =
        std::get<cir::FunctionTypePayload>(file.type_payload(resolved));
    return !function.member_is_const && !function.member_is_volatile &&
        function.member_ref_qualifier == cir::FunctionRefQualifierKind::None;
}

cir::TypeRef apply_add_reference(cir::File& file,
                                 cir::TypeRef operand,
                                 cir::ReferenceKind kind) {
    if (!is_referenceable_type(file, operand)) {
        return operand;
    }
    return file.type_ref(file.reference_type(operand, kind));
}

bool is_void_type(const cir::File& file, cir::TypeRef operand) {
    cir::TypeId resolved = file.resolved_type(operand.type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Builtin) {
        return false;
    }
    const auto* builtin =
        std::get_if<cir::BuiltinTypePayload>(&file.type_payload(resolved));
    return builtin && builtin->kind == cir::BuiltinTypeKind::Void;
}

cir::TypeRef apply_add_pointer(cir::File& file, cir::TypeRef operand) {
    cir::TypeRef pointee = apply_remove_reference(file, operand);
    if (!is_void_type(file, pointee) &&
        !is_referenceable_type(file, pointee)) {
        return operand;
    }
    return file.type_ref(file.pointer_type(pointee));
}

cir::TypeRef apply_decay(cir::File& file, cir::TypeRef operand) {
    operand = apply_remove_reference(file, operand);
    cir::TypeId resolved = file.resolved_type(operand.type);
    if (!file.valid(resolved)) {
        return operand;
    }
    if (file.type(resolved).kind == cir::TypeKind::Array) {
        return file.type_ref(file.pointer_type(
            apply_remove_extent(file, operand)));
    }
    if (file.type(resolved).kind == cir::TypeKind::Function) {
        return apply_add_pointer(file, operand);
    }
    return apply_remove_cv(file, operand);
}

std::optional<int64_t> integer_attribute_arg(const ParsedAttribute& attr) {
    if (attr.args.empty() ||
        attr.args.front().kind != AttributeArg::Kind::Integer) {
        return std::nullopt;
    }
    return attr.args.front().int_value;
}

bool is_power_of_two(uint64_t value) {
    return value != 0 && (value & (value - 1)) == 0;
}

bool is_glvalue(ValueCategory category) {
    return category == ValueCategory::LValue ||
           category == ValueCategory::XValue;
}

cir::TypeRef expression_object_ref_for_decltype(cir::File& file,
                                                const ExprResult& expr) {
    if (is_glvalue(expr.category) &&
        expr.place.valid() &&
        file.valid(expr.place)) {
        const cir::Inst& place = file.inst(expr.place);
        if (place.place_fact.valid() && file.valid(place.place_fact)) {
            return file.place_fact(place.place_fact).object_type;
        }
        return file.place_object_ref(place.result_type);
    }
    if (expr.type.valid()) {
        return file.type_ref(expr.type);
    }
    if (expr.value.valid() && file.valid(expr.value)) {
        return file.type_ref(file.inst(expr.value).result_type);
    }
    return file.type_ref(file.unknown_type());
}

cir::TypeRef declared_entity_ref_for_decltype(cir::File& file,
                                              const ExprResult& expr) {
    if (expr.entity.valid() && file.valid(expr.entity)) {
        const cir::Entity& entity = file.entity(expr.entity);
        if (entity.type.valid()) {
            return file.type_ref(entity.type,
                                 entity.qualifiers,
                                 entity.memory_space);
        }
    }
    return expression_object_ref_for_decltype(file, expr);
}

cir::DecltypeOperandCategory decltype_operand_category(
    const ExprResult& expr) {
    if (expr.dependent_value_qualifier.type.valid() ||
        expr.dependent_value_name.valid()) {
        return cir::DecltypeOperandCategory::Unknown;
    }
    switch (expr.category) {
        case ValueCategory::Invalid:
            return cir::DecltypeOperandCategory::Unknown;
        case ValueCategory::PrValue:
            return cir::DecltypeOperandCategory::PrValue;
        case ValueCategory::LValue:
        case ValueCategory::QualifiedMember:
            return cir::DecltypeOperandCategory::LValue;
        case ValueCategory::XValue:
            return cir::DecltypeOperandCategory::XValue;
        case ValueCategory::FunctionDesignator:
            return cir::DecltypeOperandCategory::FunctionDesignator;
        case ValueCategory::OverloadDesignator:
            return cir::DecltypeOperandCategory::Unknown;
        case ValueCategory::MemberPointerDesignator:
            return cir::DecltypeOperandCategory::MemberPointerDesignator;
        case ValueCategory::MemberFunctionPointerCallee:
            return cir::DecltypeOperandCategory::PrValue;
        case ValueCategory::Dependent:
        case ValueCategory::InitList:
        case ValueCategory::Type:
            return cir::DecltypeOperandCategory::Unknown;
    }
    return cir::DecltypeOperandCategory::Unknown;
}

cir::InstId decltype_operand_inst(const ExprResult& expr) {
    if (expr.value.valid()) {
        return expr.value;
    }
    if (expr.place.valid()) {
        return expr.place;
    }
    return {};
}

enum class QualificationLayerKind : uint8_t {
    Pointer,
    MemberPointer,
    Array,
};

struct QualificationLayer {
    QualificationLayerKind kind = QualificationLayerKind::Pointer;
    cir::TypeRef member_class;
    cir::ArraySizeKind array_size_kind = cir::ArraySizeKind::Incomplete;
    std::optional<size_t> array_size;
};

struct QualificationDecomposition {
    bool valid = false;
    std::vector<cir::TypeRef> levels;
    std::vector<QualificationLayer> layers;
    cir::TypeId terminal;
    bool terminal_is_type_parameter = false;
};

cir::TypeRef resolve_qualification_ref(const cir::File& file,
                                       cir::TypeRef ref) {
    while (file.valid(ref.type) &&
           file.type(ref.type).kind == cir::TypeKind::Typedef) {
        const auto* alias = std::get_if<cir::TypedefTypePayload>(
            &file.type_payload(ref.type));
        if (!alias) {
            return {};
        }
        ref.qualifiers = static_cast<uint8_t>(
            ref.qualifiers | alias->underlying_type.qualifiers);
        if (ref.memory_space == cir::MemorySpace::Default) {
            ref.memory_space = alias->underlying_type.memory_space;
        }
        ref.type = alias->underlying_type.type;
    }
    ref.type = file.resolved_type(ref.type);
    return ref;
}

QualificationDecomposition decompose_qualification(
    const cir::File& file,
    cir::TypeRef root) {
    QualificationDecomposition result;
    root = resolve_qualification_ref(file, root);
    for (size_t depth = 0; depth < 256; ++depth) {
        if (!root.valid() || !file.valid(root.type)) {
            return result;
        }
        result.levels.push_back(root);
        const cir::TypeKind kind = file.type(root.type).kind;
        QualificationLayer layer;
        if (kind == cir::TypeKind::Pointer) {
            layer.kind = QualificationLayerKind::Pointer;
            result.layers.push_back(layer);
            root = resolve_qualification_ref(
                file, file.pointer_pointee_ref(root.type));
            continue;
        }
        if (kind == cir::TypeKind::MemberPointer) {
            const auto* member =
                std::get_if<cir::MemberPointerTypePayload>(
                    &file.type_payload(root.type));
            if (!member) {
                return result;
            }
            layer.kind = QualificationLayerKind::MemberPointer;
            layer.member_class =
                resolve_qualification_ref(file, member->class_type);
            result.layers.push_back(layer);
            root = resolve_qualification_ref(file, member->member_type);
            continue;
        }
        if (kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file.type_payload(root.type));
            if (!array) {
                return result;
            }
            layer.kind = QualificationLayerKind::Array;
            layer.array_size_kind = array->size_kind;
            layer.array_size = array->size;
            result.layers.push_back(layer);
            root = resolve_qualification_ref(file, array->element_type);
            continue;
        }
        result.terminal = root.type;
        result.terminal_is_type_parameter =
            kind == cir::TypeKind::TypeParam;
        result.valid = true;
        break;
    }
    if (!result.valid ||
        result.levels.size() != result.layers.size() + 1) {
        result.valid = false;
        return result;
    }
    constexpr uint8_t cv_mask = cir::QualConst | cir::QualVolatile;

    for (size_t i = result.layers.size(); i > 0; --i) {
        size_t layer_index = i - 1;
        if (result.layers[layer_index].kind ==
            QualificationLayerKind::Array) {
            uint8_t array_cv = static_cast<uint8_t>(
                (result.levels[layer_index].qualifiers |
                 result.levels[layer_index + 1].qualifiers) & cv_mask);
            result.levels[layer_index].qualifiers = static_cast<uint8_t>(
                result.levels[layer_index].qualifiers | array_cv);
            result.levels[layer_index + 1].qualifiers = static_cast<uint8_t>(
                result.levels[layer_index + 1].qualifiers | array_cv);
        }
    }
    return result;
}

bool same_member_class(const cir::File& file,
                       cir::TypeRef lhs,
                       cir::TypeRef rhs) {
    lhs = resolve_qualification_ref(file, lhs);
    rhs = resolve_qualification_ref(file, rhs);
    return lhs.type == rhs.type && lhs.qualifiers == rhs.qualifiers &&
           lhs.memory_space == rhs.memory_space;
}

} // namespace

cir::TypeRef Session::collect_builtin_type_transform(BuiltinKind kind,
                                                     cir::TypeRef operand,
                                                     SrcLoc loc) {
    if (!operand.valid()) {
        report_error("invalid builtin type transform invocation", loc);
        return type_ref(file_.unknown_type());
    }
    if (is_dependent_type(operand.type)) {
        cir::BuiltinTypeTransformKind transform_kind;
        switch (kind) {
            case BuiltinKind::REMOVE_CONST:
                transform_kind = cir::BuiltinTypeTransformKind::RemoveConst;
                break;
            case BuiltinKind::REMOVE_VOLATILE:
                transform_kind =
                    cir::BuiltinTypeTransformKind::RemoveVolatile;
                break;
            case BuiltinKind::REMOVE_CV:
                transform_kind = cir::BuiltinTypeTransformKind::RemoveCV;
                break;
            case BuiltinKind::REMOVE_CVREF:
                transform_kind = cir::BuiltinTypeTransformKind::RemoveCVRef;
                break;
            case BuiltinKind::REMOVE_REFERENCE:
                transform_kind =
                    cir::BuiltinTypeTransformKind::RemoveReference;
                break;
            case BuiltinKind::UNDERLYING_TYPE:
                transform_kind = cir::BuiltinTypeTransformKind::UnderlyingType;
                break;
            case BuiltinKind::REMOVE_EXTENT:
                transform_kind = cir::BuiltinTypeTransformKind::RemoveExtent;
                break;
            case BuiltinKind::REMOVE_ALL_EXTENTS:
                transform_kind =
                    cir::BuiltinTypeTransformKind::RemoveAllExtents;
                break;
            case BuiltinKind::ADD_LVALUE_REFERENCE:
                transform_kind =
                    cir::BuiltinTypeTransformKind::AddLValueReference;
                break;
            case BuiltinKind::ADD_RVALUE_REFERENCE:
                transform_kind =
                    cir::BuiltinTypeTransformKind::AddRValueReference;
                break;
            case BuiltinKind::ADD_POINTER:
                transform_kind = cir::BuiltinTypeTransformKind::AddPointer;
                break;
            case BuiltinKind::DECAY:
                transform_kind = cir::BuiltinTypeTransformKind::Decay;
                break;
            default:
                report_error("invalid builtin type transform invocation", loc);
                return type_ref(file_.unknown_type());
        }
        return type_ref(file_.builtin_type_transform_type(
            transform_kind, operand));
    }
    switch (kind) {
        case BuiltinKind::REMOVE_CONST:
            return apply_remove_const(file_, operand);
        case BuiltinKind::REMOVE_VOLATILE:
            return apply_remove_volatile(file_, operand);
        case BuiltinKind::REMOVE_CV:
            return apply_remove_cv(file_, operand);
        case BuiltinKind::REMOVE_CVREF:
            return apply_remove_cvref(file_, operand);
        case BuiltinKind::REMOVE_REFERENCE:
            return apply_remove_reference(file_, operand);
        case BuiltinKind::UNDERLYING_TYPE: {
            cir::TypeRef result = apply_underlying_type(file_, operand);
            if (!result.valid()) {
                report_error("__underlying_type requires an enumeration type",
                             loc);
                return type_ref(file_.unknown_type());
            }
            return result;
        }
        case BuiltinKind::REMOVE_EXTENT:
            return apply_remove_extent(file_, operand);
        case BuiltinKind::REMOVE_ALL_EXTENTS:
            return apply_remove_all_extents(file_, operand);
        case BuiltinKind::ADD_LVALUE_REFERENCE:
            return apply_add_reference(
                file_, operand, cir::ReferenceKind::LValue);
        case BuiltinKind::ADD_RVALUE_REFERENCE:
            return apply_add_reference(
                file_, operand, cir::ReferenceKind::RValue);
        case BuiltinKind::ADD_POINTER:
            return apply_add_pointer(file_, operand);
        case BuiltinKind::DECAY:
            return apply_decay(file_, operand);
        default:
            report_error("invalid builtin type transform invocation", loc);
            return type_ref(file_.unknown_type());
    }
}

Session::QualificationConversionAnalysis
Session::analyze_qualification_conversion(
    cir::TypeRef source,
    cir::TypeRef target,
    QualificationTargetKind target_kind) const {
    QualificationConversionAnalysis analysis;
    QualificationDecomposition from =
        decompose_qualification(file_, source);
    QualificationDecomposition to =
        decompose_qualification(file_, target);
    if (!from.valid || !to.valid ||
        from.layers.size() != to.layers.size()) {
        return analysis;
    }
    analysis.has_indirection = !from.layers.empty();
    if (target_kind != QualificationTargetKind::TypePattern &&
        from.terminal != to.terminal) {
        return analysis;
    }

    std::vector<bool> layer_differs(from.layers.size(), false);
    for (size_t i = 0; i < from.layers.size(); ++i) {
        const QualificationLayer& source_layer = from.layers[i];
        const QualificationLayer& target_layer = to.layers[i];
        if (source_layer.kind != target_layer.kind) {
            return analysis;
        }
        if (source_layer.kind == QualificationLayerKind::MemberPointer &&
            !same_member_class(file_,
                               source_layer.member_class,
                               target_layer.member_class)) {
            return analysis;
        }
        if (source_layer.kind != QualificationLayerKind::Array) {
            continue;
        }
        bool same_bound =
            source_layer.array_size_kind == target_layer.array_size_kind &&
            source_layer.array_size == target_layer.array_size;
        bool source_unknown =
            source_layer.array_size_kind == cir::ArraySizeKind::Incomplete;
        bool target_unknown =
            target_layer.array_size_kind == cir::ArraySizeKind::Incomplete;
        bool known_unknown_pair =
            source_layer.array_size_kind == cir::ArraySizeKind::Constant &&
            target_unknown;
        bool unknown_known_pair =
            source_unknown &&
            target_layer.array_size_kind == cir::ArraySizeKind::Constant;
        if (!same_bound && !known_unknown_pair && !unknown_known_pair) {
            return analysis;
        }
        layer_differs[i] = !same_bound;
        if (unknown_known_pair) {
            analysis.similar = true;
            analysis.allowed = false;
            return analysis;
        }
    }
    analysis.similar = true;

    constexpr uint8_t cv_mask = cir::QualConst | cir::QualVolatile;
    constexpr uint8_t non_cv_mask = static_cast<uint8_t>(~cv_mask);
    std::vector<uint8_t> target_cv(to.levels.size(), cir::QualNone);
    for (size_t i = 0; i < from.levels.size(); ++i) {
        if ((from.levels[i].qualifiers & non_cv_mask) !=
                (to.levels[i].qualifiers & non_cv_mask) ||
            from.levels[i].memory_space != to.levels[i].memory_space) {
            return analysis;
        }
        target_cv[i] = to.levels[i].qualifiers & cv_mask;
    }
    if (target_kind == QualificationTargetKind::TypePattern &&
        to.terminal_is_type_parameter && !target_cv.empty()) {
        target_cv.back() = static_cast<uint8_t>(
            target_cv.back() |
            (from.levels.back().qualifiers & cv_mask));
    }
    auto prior_levels_are_const = [&](size_t changed_index) {
        for (size_t k = 1; k < changed_index; ++k) {
            if ((target_cv[k] & cir::QualConst) == 0) {
                return false;
            }
        }
        return true;
    };
    if (target_kind == QualificationTargetKind::ReferenceCompatible &&
        !from.levels.empty()) {

        uint8_t source_cv = from.levels[0].qualifiers & cv_mask;
        if ((source_cv & static_cast<uint8_t>(~target_cv[0])) != 0) {
            return analysis;
        }
    }
    for (size_t i = 1; i < from.levels.size(); ++i) {
        uint8_t source_cv = from.levels[i].qualifiers & cv_mask;
        if ((source_cv & static_cast<uint8_t>(~target_cv[i])) != 0) {
            return analysis;
        }
        if (source_cv != target_cv[i] &&
            !prior_levels_are_const(i)) {
            return analysis;
        }
    }
    for (size_t i = 0; i < layer_differs.size(); ++i) {
        if (layer_differs[i] && !prior_levels_are_const(i)) {
            return analysis;
        }
    }
    analysis.allowed = true;
    return analysis;
}

cir::TypeRef Session::lookup_active_template_header_type_parameter(
    std::string_view name) const {
    if (!active_template_header_info_) {
        return {};
    }
    for (auto it = active_template_header_info_->parameters.rbegin();
         it != active_template_header_info_->parameters.rend();
         ++it) {
        if (it->kind == TemplateParameterKind::Type &&
            it->name == name && it->type_param_type.valid()) {
            return file_.type_ref(it->type_param_type);
        }
    }
    return {};
}

cir::TypeRef
Session::lookup_record_scope_type_before_outer_template_parameters(
    std::string_view name,
    bool* found_name) const {
    if (found_name) {
        *found_name = false;
    }
    for (cir::DeclContextId context = current_decl_context();
         context.valid() && file_.valid(context);
         context = file_.decl_context(context).parent) {
        cir::DeclContextKind kind = file_.decl_context(context).kind;
        if (kind == cir::DeclContextKind::Namespace ||
            kind == cir::DeclContextKind::TranslationUnit) {
            break;
        }
        if (kind == cir::DeclContextKind::Record) {
            cir::EntityId owner = file_.decl_context(context).owner;
            if (owner.valid() && file_.valid(owner)) {
                MemberLookupResult lookup =
                    lookup_member_name(file_.entity(owner).type, name);
                if (lookup.found_name) {
                    if (found_name) {
                        *found_name = true;
                    }
                    if (lookup.ambiguous || lookup.declarations.empty()) {
                        return {};
                    }
                    cir::TypeRef designated{};
                    for (const MemberLookupDeclaration& declaration :
                         lookup.declarations) {
                        if (!declaration.designated_type.valid()) {
                            return {};
                        }
                        cir::TypeRef candidate =
                            declaration.designated_type;
                        candidate.type = file_.resolved_type(candidate.type);
                        if (designated.valid() && designated != candidate) {
                            return {};
                        }
                        designated = candidate;
                    }
                    return designated;
                }
                cir::TypeRef provisional =
                    lookup_qualified_type_name_ref(context, name);
                if (provisional.valid()) {
                    if (found_name) {
                        *found_name = true;
                    }
                    return provisional;
                }
            }
        }
        const cir::Binding* ordinary = file_.lookup_ordinary_binding(
            context, name, /*include_parents=*/false);
        if (ordinary) {

            bool designates_namespace =
                !ordinary->entities.empty() &&
                (file_.entity(ordinary->entities.back()).kind ==
                     cir::EntityKind::Namespace ||
                 file_.entity(ordinary->entities.back()).kind ==
                     cir::EntityKind::NamespaceAlias);
            if (!designates_namespace) {
                if (found_name) {
                    *found_name = true;
                }
                return ordinary->is_type_name && ordinary->type.valid()
                    ? ordinary->type
                    : cir::TypeRef{};
            }
        }
        const cir::Binding* tag = file_.lookup_tag_binding(
            context, name, /*include_parents=*/false);
        if (tag && tag->type.valid()) {
            if (found_name) {
                *found_name = true;
            }
            return tag->type;
        }
    }
    return {};
}

bool Session::is_type_name(std::string_view name) const {
    static const std::unordered_set<std::string_view> builtins = {
        "void", "char", "short", "int", "long", "float", "double", "bool", "_Bool"
    };
    if (builtins.contains(name)) {
        return true;
    }
    if (parameter_pack_replay_element(ParameterPackKind::Type, name)) {
        return true;
    }
    if (lookup_active_template_header_type_parameter(name).valid() ||
        (active_template_header_info_ &&
         lookup_record_scope_type_before_outer_template_parameters(name)
             .valid())) {
        return true;
    }
    bool found_member = false;
    cir::TypeRef member =
        lookup_record_scope_type_before_outer_template_parameters(
            name, &found_member);
    if (found_member) {
        return member.valid();
    }
    const cir::Binding* binding = lookup_type_name_binding(name);
    if (binding && binding->is_type_name &&
        binding->dependent_member_using && collecting_pattern_) {

        const_cast<Session*>(this)->mark_pattern_unusable();
    }
    if (binding && binding->is_type_name) {
        return true;
    }

    if (!objc_.initialized) {
        return false;
    }
    if (is_objc_class_name(name)) {
        return true;
    }
    for (const std::vector<std::string>& frame : objc_.type_param_stack) {
        for (const std::string& parameter : frame) {
            if (parameter == name) {
                return true;
            }
        }
    }
    return false;
}

bool Session::is_typedef_name(std::string_view name) const {
    if (parameter_pack_replay_element(ParameterPackKind::Type, name)) {
        return true;
    }
    if (lookup_active_template_header_type_parameter(name).valid() ||
        (active_template_header_info_ &&
         lookup_record_scope_type_before_outer_template_parameters(name)
             .valid())) {
        return true;
    }
    bool found_member = false;
    cir::TypeRef member =
        lookup_record_scope_type_before_outer_template_parameters(
            name, &found_member);
    if (found_member) {
        return member.valid();
    }
    const cir::Binding* binding = lookup_type_name_binding(name);
    return binding && binding->is_type_name && !binding->entities.empty();
}

cir::TypeId Session::lookup_type_name(std::string_view name) const {
    if (const ParameterPackElement* replay = parameter_pack_replay_element(
            ParameterPackKind::Type, name)) {
        if (const cir::TypeRef* type = std::get_if<cir::TypeRef>(replay)) {
            return type->type;
        }
    }
    if (cir::TypeRef active =
            lookup_active_template_header_type_parameter(name);
        active.valid()) {
        return active.type;
    }
    if (active_template_header_info_) {
        if (cir::TypeRef member =
                lookup_record_scope_type_before_outer_template_parameters(
                    name);
            member.valid()) {
            return member.type;
        }
    }
    bool found_member = false;
    cir::TypeRef member =
        lookup_record_scope_type_before_outer_template_parameters(
            name, &found_member);
    if (found_member) {
        return member.type;
    }
    const cir::Binding* binding = lookup_type_name_binding(name);
    if (binding && binding->is_type_name) {
        if (binding->dependent_member_using && collecting_pattern_) {
            const_cast<Session*>(this)->bump_pattern_taint();
        }
        return binding->type.type;
    }
    if (objc_.initialized) {
        cir::TypeId object_type = objc_class_object_type(name);
        if (object_type.valid()) {
            return object_type;
        }
        for (const std::vector<std::string>& frame : objc_.type_param_stack) {
            for (const std::string& parameter : frame) {
                if (parameter == name) {

                    return objc_.id_type;
                }
            }
        }
    }
    return {};
}

cir::TypeRef Session::lookup_type_name_ref(std::string_view name) const {
    if (const ParameterPackElement* replay = parameter_pack_replay_element(
            ParameterPackKind::Type, name)) {
        if (const cir::TypeRef* type = std::get_if<cir::TypeRef>(replay)) {
            return *type;
        }
    }
    if (cir::TypeRef active =
            lookup_active_template_header_type_parameter(name);
        active.valid()) {
        return active;
    }
    if (active_template_header_info_) {
        if (cir::TypeRef member =
                lookup_record_scope_type_before_outer_template_parameters(
                    name);
            member.valid()) {
            return member;
        }
    }
    bool found_member = false;
    cir::TypeRef member =
        lookup_record_scope_type_before_outer_template_parameters(
            name, &found_member);
    if (found_member) {
        return member;
    }
    const cir::Binding* binding = lookup_type_name_binding(name);
    if (binding && binding->is_type_name) {
        if (binding->dependent_member_using && collecting_pattern_) {
            const_cast<Session*>(this)->bump_pattern_taint();
        }
        return binding->type;
    }
    if (objc_.initialized) {
        cir::TypeId object_type = objc_class_object_type(name);
        if (object_type.valid()) {
            cir::TypeRef ref;
            ref.type = object_type;
            return ref;
        }
        for (const std::vector<std::string>& frame : objc_.type_param_stack) {
            for (const std::string& parameter : frame) {
                if (parameter == name) {
                    cir::TypeRef ref;
                    ref.type = objc_.id_type;
                    return ref;
                }
            }
        }
    }
    return {};
}

cir::TypeRef Session::lookup_type_name_ref_checked(std::string_view name,
                                                   SrcLoc loc) {
    cir::TypeRef type = lookup_type_name_ref(name);
    if (!type.valid()) {
        return type;
    }
    cir::TypeId resolved = file_.resolved_type(type.type);
    for (cir::DeclContextId context = current_decl_context();
         context.valid() && file_.valid(context);
         context = file_.decl_context(context).parent) {
        cir::DeclContextKind kind = file_.decl_context(context).kind;
        if (kind == cir::DeclContextKind::Namespace ||
            kind == cir::DeclContextKind::TranslationUnit) {
            break;
        }
        if (kind != cir::DeclContextKind::Record) {
            const cir::Binding* ordinary = file_.lookup_ordinary_binding(
                context, name, /*include_parents=*/false);
            if (ordinary) {
                break;
            }
            continue;
        }
        cir::EntityId owner = file_.decl_context(context).owner;
        if (!owner.valid() || !file_.valid(owner)) {
            continue;
        }
        MemberLookupResult lookup =
            lookup_member_name(file_.entity(owner).type, name);
        if (!lookup.found_name) {
            continue;
        }
        for (const MemberLookupDeclaration& declaration :
             lookup.declarations) {
            if (!declaration.designated_type.valid() ||
                file_.resolved_type(declaration.designated_type.type) !=
                    resolved) {
                continue;
            }
            (void)check_member_lookup_access(declaration, loc);
            (void)check_member_lookup_base_access(
                declaration, file_.entity(owner).type, loc);
            return type;
        }
        break;
    }
    return type;
}

cir::TypeRef Session::type_ref(cir::TypeId type,
                               uint8_t qualifiers,
                               cir::MemorySpace memory_space) const {
    return file_.type_ref(type, qualifiers, memory_space);
}

cir::TypeId Session::pointer_type(cir::TypeId pointee) {
    return builder_.pointer_type(pointee);
}

cir::TypeId Session::pointer_type(cir::TypeRef pointee) {
    return builder_.pointer_type(pointee);
}

cir::TypeId Session::block_pointer_type(cir::TypeRef pointee) {
    return file_.block_pointer_type(pointee);
}

cir::TypeId Session::reference_type(cir::TypeRef referred,
                                    cir::ReferenceKind reference_kind) {
    return file_.reference_type(referred, reference_kind);
}

cir::TypeId Session::member_pointer_type(cir::TypeRef class_type,
                                         cir::TypeRef member_type) {
    return file_.member_pointer_type(class_type, member_type);
}

cir::TypeId Session::auto_type(cir::AutoTypeFlavor flavor) {
    return file_.auto_type(flavor);
}

cir::TypeId Session::dependent_type(std::string_view name) {
    return file_.dependent_type(std::string(name));
}

cir::TypeId Session::complex_type(cir::TypeRef element_type) {
    return file_.complex_type(element_type);
}

cir::TypeId Session::vector_type(cir::TypeRef element_type,
                                 uint32_t element_count,
                                 uint64_t size_bytes) {
    return file_.vector_type(element_type, element_count, size_bytes);
}

cir::TypeRef Session::apply_type_attributes(cir::TypeRef type,
                                            const AttributeList& attrs,
                                            SrcLoc loc) {
    if (!type.valid() || attrs.empty()) {
        return type;
    }

    for (const ParsedAttribute& attr : attrs.attrs) {
        if (attr.kind == AttributeKind::Mode) {
            SrcLoc attr_loc = attr.loc.isInvalid() ? loc : attr.loc;
            if (attr.args.size() != 1 ||
                attr.args[0].kind != AttributeArg::Kind::Identifier) {
                report_error("mode attribute requires a mode name", attr_loc);
                continue;
            }
            std::string name = attr.args[0].value;
            if (name.size() > 4 && name.compare(0, 2, "__") == 0 &&
                name.compare(name.size() - 2, 2, "__") == 0) {
                name = name.substr(2, name.size() - 4);
            }
            if (name == "SF" || name == "DF") {
                type.type = file_.builtin_type(name == "SF"
                                                   ? cir::BuiltinTypeKind::Float
                                                   : cir::BuiltinTypeKind::Double);
                continue;
            }
            if (name == "TC") {

                type.type = complex_type(type_ref(
                    file_.builtin_type(cir::BuiltinTypeKind::LongDouble)));
                continue;
            }
            size_t bytes = 0;
            if (name == "QI" || name == "byte") {
                bytes = 1;
            } else if (name == "HI") {
                bytes = 2;
            } else if (name == "SI") {
                bytes = 4;
            } else if (name == "DI" || name == "word" || name == "pointer") {
                bytes = 8;
            } else if (name == "TI") {
                bytes = 16;
            } else {
                report_error("unsupported machine mode '" + attr.args[0].value + "'",
                             attr_loc);
                continue;
            }
            if (!is_integer_type(type.type)) {
                report_error("mode attribute applies to integer types", attr_loc);
                continue;
            }
            bool is_unsigned = file_.operator_value_domain(type) ==
                               cir::OperatorValueDomain::UnsignedInteger;
            cir::BuiltinTypeKind kind = cir::BuiltinTypeKind::Int;
            switch (bytes) {
                case 1: kind = is_unsigned ? cir::BuiltinTypeKind::UChar
                                           : cir::BuiltinTypeKind::SChar; break;
                case 2: kind = is_unsigned ? cir::BuiltinTypeKind::UShort
                                           : cir::BuiltinTypeKind::Short; break;
                case 4: kind = is_unsigned ? cir::BuiltinTypeKind::UInt
                                           : cir::BuiltinTypeKind::Int; break;
                case 8: kind = is_unsigned ? cir::BuiltinTypeKind::ULong
                                           : cir::BuiltinTypeKind::Long; break;
                case 16: kind = is_unsigned ? cir::BuiltinTypeKind::UInt128
                                            : cir::BuiltinTypeKind::Int128; break;
            }
            type.type = file_.builtin_type(kind);
            continue;
        }
        if (attr.kind != AttributeKind::VectorSize &&
            attr.kind != AttributeKind::ExtVectorType &&
            attr.kind != AttributeKind::NeonVectorType) {
            continue;
        }

        SrcLoc attr_loc = attr.loc.isInvalid() ? loc : attr.loc;
        if (is_vector_type(type.type)) {
            continue;
        }
        std::optional<int64_t> raw_value = integer_attribute_arg(attr);
        if (!raw_value.has_value()) {
            report_error(attr.kind == AttributeKind::VectorSize
                             ? "vector_size requires an integer constant expression"
                             : "ext_vector_type requires an integer constant expression",
                         attr_loc);
            continue;
        }
        if (*raw_value <= 0) {
            report_error(attr.kind == AttributeKind::VectorSize
                             ? "vector_size must be a positive integer"
                             : "ext_vector_type element count must be positive",
                         attr_loc);
            continue;
        }

        cir::TypeId element_type_id = file_.resolved_type(type.type);
        if (!file_.valid(element_type_id)) {
            report_error("vector attribute requires a valid base type", attr_loc);
            continue;
        }

        cir::OperatorValueDomain domain = file_.operator_value_domain(type);
        bool is_boolean_ext_vector =
            domain == cir::OperatorValueDomain::Bool &&
            attr.kind == AttributeKind::ExtVectorType;
        bool valid_element_domain =
            domain == cir::OperatorValueDomain::SignedInteger ||
            domain == cir::OperatorValueDomain::UnsignedInteger ||
            domain == cir::OperatorValueDomain::Floating ||
            is_boolean_ext_vector;
        if (!valid_element_domain || is_void_type(element_type_id)) {
            report_error("vector attribute requires an integer or floating-point base type",
                         attr_loc);
            continue;
        }

        std::optional<std::pair<size_t, size_t>> element_layout =
            size_align_of_type(element_type_id, attr_loc);
        if (!element_layout.has_value() || element_layout->first == 0) {
            report_error("vector attribute requires a complete base type", attr_loc);
            continue;
        }

        uint64_t element_count = 0;
        uint64_t size_bytes = 0;
        if (attr.kind == AttributeKind::VectorSize) {
            size_bytes = static_cast<uint64_t>(*raw_value);
            if (!is_power_of_two(size_bytes)) {
                report_error("vector_size must be a power of 2", attr_loc);
                continue;
            }
            if (size_bytes % element_layout->first != 0) {
                report_error("vector_size must be a multiple of the base type size",
                             attr_loc);
                continue;
            }
            element_count = size_bytes / element_layout->first;
        } else {
            element_count = static_cast<uint64_t>(*raw_value);
            if (element_count > UINT32_MAX) {
                report_error("vector element count is too large", attr_loc);
                continue;
            }
            if (is_boolean_ext_vector) {

                uint64_t packed_bytes = (element_count + 7) / 8;
                size_bytes = 1;
                while (size_bytes < packed_bytes) {
                    size_bytes <<= 1;
                }
            } else {
                size_bytes = element_count * element_layout->first;
            }
        }

        if (element_count == 0 || element_count > UINT32_MAX) {
            report_error("vector element count is too large", attr_loc);
            continue;
        }

        cir::TypeRef element_ref = type;
        element_ref.type = element_type_id;
        element_ref.qualifiers = cir::QualNone;
        cir::TypeId vector = vector_type(element_ref,
                                         static_cast<uint32_t>(element_count),
                                         size_bytes);
        type = type_ref(vector, type.qualifiers, type.memory_space);
    }

    return type;
}

bool Session::variably_modified_type(cir::TypeId type) const {
    type = file_.resolved_type(type);
    while (file_.valid(type) && file_.type(type).kind == cir::TypeKind::Array) {
        const auto* array =
            std::get_if<cir::ArrayTypePayload>(&file_.type_payload(type));
        if (!array) {
            return false;
        }
        if (array->size_kind == cir::ArraySizeKind::Variable &&
            !array->size_expr_is_dependent) {
            return true;
        }
        type = file_.resolved_type(array->element_type.type);
    }
    return false;
}

cir::TypeId Session::typeof_expr_type(cir::InstId expr) {
    return file_.typeof_expr_type(expr);
}

cir::TypeId Session::decltype_expr_type(
    cir::InstId expr,
    bool use_declared_type_rule,
    cir::DecltypeOperandCategory operand_category,
    cir::TypeRef operand_type,
    cir::TypeRef dependent_value_qualifier,
    cir::NameId dependent_value_name,
    cir::TemplateValueExpression operand_expression) {
    return file_.decltype_expr_type(expr,
                                    use_declared_type_rule,
                                    operand_category,
                                    operand_type,
                                    dependent_value_qualifier,
                                    dependent_value_name,
                                    std::move(operand_expression));
}

cir::TypeRef Session::resolve_typeof_expr_type(const ExprResult& expr, SrcLoc loc) {
    (void)loc;

    if (is_glvalue(expr.category)) {
        cir::TypeRef object_ref = expression_object_ref_for_decltype(file_, expr);
        if (object_ref.type.valid()) {
            return object_ref;
        }
    }
    if (expr.type.valid()) {
        return type_ref(expr.type);
    }
    if (expr.value.valid()) {
        return type_ref(typeof_expr_type(expr.value));
    }
    return type_ref(file_.unknown_type());
}

cir::TypeRef Session::resolve_decltype_expr_type(const ExprResult& expr,
                                                 bool use_declared_type_rule,
                                                 SrcLoc loc) {
    if (expr.has_error) {
        return type_ref(file_.unknown_type());
    }
    if (expr.category == ValueCategory::InitList || expr.init_list) {
        report_error("decltype operand cannot be an initializer list", loc);
        return type_ref(file_.unknown_type());
    }
    if (expr.category == ValueCategory::Type) {
        report_error("decltype operand must name an expression", loc);
        return type_ref(file_.unknown_type());
    }
    if (use_declared_type_rule && expr.entity.valid()) {
        return declared_entity_ref_for_decltype(file_, expr);
    }
    if (expr.category == ValueCategory::Dependent ||
        (expr.type.valid() && is_dependent_type(expr.type)) ||
        (expr_is_value_dependent(expr) &&
         expr.template_value_expr.valid())) {
        return type_ref(decltype_expr_type(
            decltype_operand_inst(expr),
            use_declared_type_rule,
            decltype_operand_category(expr),
            expression_object_ref_for_decltype(file_, expr),
            expr.dependent_value_qualifier,
            expr.dependent_value_name,
            expr.template_value_expr));
    }

    if (expr.category == ValueCategory::FunctionDesignator) {
        cir::TypeRef function_ref = declared_entity_ref_for_decltype(file_, expr);
        return type_ref(reference_type(function_ref, cir::ReferenceKind::LValue));
    }
    if (expr.category == ValueCategory::OverloadDesignator) {
        report_error("decltype operand names an unresolved overload set", loc);
        return type_ref(file_.unknown_type());
    }
    if (expr.category == ValueCategory::MemberPointerDesignator) {
        return expression_object_ref_for_decltype(file_, expr);
    }
    if (expr.category == ValueCategory::MemberFunctionPointerCallee) {
        return expression_object_ref_for_decltype(file_, expr);
    }

    cir::TypeRef object_ref = expression_object_ref_for_decltype(file_, expr);
    switch (expr.category) {
        case ValueCategory::LValue:
        case ValueCategory::QualifiedMember:
            return type_ref(reference_type(object_ref, cir::ReferenceKind::LValue));
        case ValueCategory::XValue:
            return type_ref(reference_type(object_ref, cir::ReferenceKind::RValue));
        case ValueCategory::PrValue:
            return object_ref;
        default:
            if (!object_ref.type.valid()) {
                return type_ref(file_.unknown_type());
            }
            return object_ref;
    }
}

bool Session::contains_auto_type(cir::TypeId type_id,
                                 std::optional<cir::AutoTypeFlavor> flavor) const {
    if (!file_.valid(type_id)) {
        return false;
    }
    type_id = file_.resolved_type(type_id);
    if (!file_.valid(type_id)) {
        return false;
    }
    const cir::Type& type = file_.type(type_id);
    const cir::TypePayload& payload = file_.type_payload(type_id);
    switch (type.kind) {
        case cir::TypeKind::Auto:
            return !flavor.has_value() ||
                   std::get<cir::AutoTypePayload>(payload).flavor == *flavor;
        case cir::TypeKind::Pointer:
            return contains_auto_type(std::get<cir::PointerTypePayload>(payload).pointee.type,
                                      flavor);
        case cir::TypeKind::BlockPointer:
            return contains_auto_type(std::get<cir::BlockPointerTypePayload>(payload).pointee.type,
                                      flavor);
        case cir::TypeKind::MemberPointer: {
            const auto& member = std::get<cir::MemberPointerTypePayload>(payload);
            return contains_auto_type(member.class_type.type, flavor) ||
                   contains_auto_type(member.member_type.type, flavor);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return contains_auto_type(std::get<cir::ReferenceTypePayload>(payload).referred_type.type,
                                      flavor);
        case cir::TypeKind::Array:
            return contains_auto_type(std::get<cir::ArrayTypePayload>(payload).element_type.type,
                                      flavor);
        case cir::TypeKind::Function: {
            const auto& function = std::get<cir::FunctionTypePayload>(payload);
            if (contains_auto_type(function.return_type.type, flavor)) {
                return true;
            }
            for (cir::TypeRef param : function.parameters) {
                if (contains_auto_type(param.type, flavor)) {
                    return true;
                }
            }
            return false;
        }
        case cir::TypeKind::Complex:
            return contains_auto_type(std::get<cir::ComplexTypePayload>(payload).element_type.type,
                                      flavor);
        default:
            return false;
    }
}

bool Session::function_has_placeholder_return(cir::TypeId function_type,
                                              cir::TypeRef* pattern) const {
    if (!file_.valid(function_type)) {
        return false;
    }
    cir::TypeId resolved = file_.resolved_type(function_type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Function) {
        return false;
    }
    const auto* function = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(resolved));
    if (!function || !contains_auto_type(function->return_type.type)) {
        return false;
    }
    if (pattern) {
        *pattern = function->return_type;
    }
    return true;
}

cir::TypeId Session::deduce_auto_type(cir::TypeId pattern,
                                      const ExprResult& initializer,
                                      SrcLoc loc) {
    if (!file_.valid(pattern)) {
        return {};
    }

    if (std::shared_ptr<const OverloadDesignator> designator =
            canonical_overload_designator(initializer);
        designator &&
        (initializer.category == ValueCategory::OverloadDesignator ||
         initializer.category == ValueCategory::FunctionDesignator ||
         initializer.category == ValueCategory::MemberPointerDesignator)) {
        cir::TypeId invented = file_.type_param_type(
            {}, "__aburi_auto_overload_target", 0, 0, false);
        cir::TypeId invented_pattern =
            replace_auto_type(pattern, file_.type_ref(invented), loc);
        PatternBindings bindings;
        bindings.types.resize(1);
        bindings.values.resize(1);
        bindings.templates.resize(1);
        bindings.explicit_types.resize(1, false);
        bindings.explicit_values.resize(1, false);
        bindings.explicit_templates.resize(1, false);
        if (!deduce_call_argument(invented_pattern, initializer, bindings) ||
            bindings.types.empty() || !bindings.types.front().type.valid()) {
            return {};
        }
        return replace_auto_type(pattern, bindings.types.front(), loc);
    }

    if (!initializer.type.valid()) {
        return {};
    }

    cir::TypeRef initializer_ref = type_ref(initializer.type);
    if (is_glvalue(initializer.category) && initializer.place.valid()) {
        const cir::Inst& place = file_.inst(initializer.place);
        if (place.place_fact.valid()) {
            initializer_ref =
                file_.place_fact(place.place_fact).object_type;
        }
    } else {

        cir::TypeId resolved = file_.resolved_type(initializer_ref.type);
        if (file_.valid(resolved) &&
            (file_.type(resolved).kind ==
                 cir::TypeKind::LValueReference ||
             file_.type(resolved).kind ==
                 cir::TypeKind::RValueReference)) {
            initializer_ref = file_.reference_referred_ref(resolved);
        }
    }

    std::optional<cir::TypeRef> deduced;
    bool saw_auto = false;
    auto remember = [&](cir::TypeRef candidate) -> bool {
        if (!file_.valid(candidate.type)) {
            return false;
        }
        candidate.type = file_.resolved_type(candidate.type);
        if (!file_.valid(candidate.type)) {
            return false;
        }
        if (deduced.has_value()) {
            cir::TypeRef prior = *deduced;
            prior.type = file_.resolved_type(prior.type);
            return prior == candidate;
        }
        deduced = candidate;
        return true;
    };

    auto deduce_ref = [&](auto& self,
                          cir::TypeRef pattern_ref,
                          cir::TypeRef argument_ref) -> bool {
        if (!file_.valid(pattern_ref.type) ||
            !file_.valid(argument_ref.type)) {
            return false;
        }
        pattern_ref.type = file_.resolved_type(pattern_ref.type);
        argument_ref.type = file_.resolved_type(argument_ref.type);
        if (!file_.valid(pattern_ref.type) ||
            !file_.valid(argument_ref.type)) {
            return false;
        }

        const cir::Type& pattern_type = file_.type(pattern_ref.type);
        if (pattern_type.kind == cir::TypeKind::Auto) {
            const auto* auto_payload =
                std::get_if<cir::AutoTypePayload>(
                    &file_.type_payload(pattern_ref.type));
            if (!auto_payload ||
                auto_payload->flavor != cir::AutoTypeFlavor::Cxx) {
                return false;
            }
            saw_auto = true;
            cir::TypeRef candidate = argument_ref;
            candidate.qualifiers = static_cast<uint8_t>(
                candidate.qualifiers &
                static_cast<uint8_t>(~pattern_ref.qualifiers));
            return remember(candidate);
        }

        const cir::Type& argument_type = file_.type(argument_ref.type);
        switch (pattern_type.kind) {
            case cir::TypeKind::Pointer:
                if (argument_type.kind != cir::TypeKind::Pointer) {
                    return false;
                }
                return self(self,
                            file_.pointer_pointee_ref(pattern_ref.type),
                            file_.pointer_pointee_ref(argument_ref.type));
            case cir::TypeKind::BlockPointer:
                if (argument_type.kind != cir::TypeKind::BlockPointer) {
                    return false;
                }
                return self(self,
                            std::get<cir::BlockPointerTypePayload>(
                                file_.type_payload(pattern_ref.type)).pointee,
                            std::get<cir::BlockPointerTypePayload>(
                                file_.type_payload(argument_ref.type)).pointee);
            case cir::TypeKind::MemberPointer: {
                if (argument_type.kind != cir::TypeKind::MemberPointer) {
                    return false;
                }
                const auto& pattern_member =
                    std::get<cir::MemberPointerTypePayload>(
                        file_.type_payload(pattern_ref.type));
                const auto& argument_member =
                    std::get<cir::MemberPointerTypePayload>(
                        file_.type_payload(argument_ref.type));
                if (file_.resolved_type(pattern_member.class_type.type) !=
                    file_.resolved_type(argument_member.class_type.type)) {
                    return false;
                }
                return self(self,
                            pattern_member.member_type,
                            argument_member.member_type);
            }
            case cir::TypeKind::LValueReference:

                return self(self,
                            file_.reference_referred_ref(pattern_ref.type),
                            argument_ref);
            case cir::TypeKind::RValueReference:

                if (initializer.category == ValueCategory::LValue ||
                    initializer.category == ValueCategory::QualifiedMember) {
                    argument_ref.type = reference_type(
                        argument_ref, cir::ReferenceKind::LValue);
                } else if (initializer.category != ValueCategory::XValue &&
                           initializer.category != ValueCategory::PrValue) {
                    return false;
                }
                return self(self,
                            file_.reference_referred_ref(pattern_ref.type),
                            argument_ref);
            case cir::TypeKind::Array: {
                if (argument_type.kind != cir::TypeKind::Array) {
                    return false;
                }
                const auto& pattern_array =
                    std::get<cir::ArrayTypePayload>(
                        file_.type_payload(pattern_ref.type));
                const auto& argument_array =
                    std::get<cir::ArrayTypePayload>(
                        file_.type_payload(argument_ref.type));
                if (pattern_array.size.has_value() &&
                    argument_array.size.has_value() &&
                    pattern_array.size != argument_array.size) {
                    return false;
                }
                return self(self,
                            pattern_array.element_type,
                            argument_array.element_type);
            }
            default:
                return pattern_ref == argument_ref;
        }
    };

    if (!deduce_ref(deduce_ref, type_ref(pattern), initializer_ref) ||
        !saw_auto || !deduced.has_value()) {
        return {};
    }
    return replace_auto_type(pattern, *deduced, loc);
}

cir::TypeId Session::replace_auto_type(cir::TypeId pattern,
                                       cir::TypeRef replacement,
                                       SrcLoc loc) {
    auto replace_ref = [&](auto& self, cir::TypeRef ref) -> cir::TypeRef {
        if (!file_.valid(ref.type)) {
            return ref;
        }
        cir::TypeId resolved = file_.resolved_type(ref.type);
        const cir::Type& type = file_.type(resolved);
        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (type.kind) {
            case cir::TypeKind::Auto: {
                cir::TypeRef out = replacement;
                out.qualifiers = static_cast<uint8_t>(out.qualifiers | ref.qualifiers);
                if (out.memory_space == cir::MemorySpace::Default) {
                    out.memory_space = ref.memory_space;
                }
                return out;
            }
            case cir::TypeKind::Pointer: {
                const auto& pointer = std::get<cir::PointerTypePayload>(payload);
                return type_ref(pointer_type(self(self, pointer.pointee)), ref.qualifiers, ref.memory_space);
            }
            case cir::TypeKind::BlockPointer: {
                const auto& pointer = std::get<cir::BlockPointerTypePayload>(payload);
                return type_ref(block_pointer_type(self(self, pointer.pointee)), ref.qualifiers, ref.memory_space);
            }
            case cir::TypeKind::MemberPointer: {
                const auto& member = std::get<cir::MemberPointerTypePayload>(payload);
                return type_ref(member_pointer_type(self(self, member.class_type),
                                                    self(self, member.member_type)),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference: {
                const auto& reference = std::get<cir::ReferenceTypePayload>(payload);
                return type_ref(reference_type(self(self, reference.referred_type),
                                               reference.reference_kind),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::Array: {
                const auto& array = std::get<cir::ArrayTypePayload>(payload);
                return type_ref(file_.array_type(
                                    self(self, array.element_type),
                                    array.size_kind,
                                    array.size,
                                    array.size_expr,
                                    array.size_expr_is_dependent,
                                    array.extent_param,
                                    array.dependent_size_expr),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::Function: {
                const auto& function = std::get<cir::FunctionTypePayload>(payload);
                std::vector<cir::TypeRef> params;
                params.reserve(function.parameters.size());
                for (cir::TypeRef param : function.parameters) {
                    params.push_back(self(self, param));
                }
                return type_ref(function_type(self(self, function.return_type),
                                              params,
                                              function.is_variadic,
                                              function.has_prototype,
                                              function.member_is_const,
                                              function.exception_spec,
                                              function.parameter_pack_flags,
                                              function.member_ref_qualifier,
                                              function.member_is_volatile),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::Complex: {
                const auto& complex = std::get<cir::ComplexTypePayload>(payload);
                return type_ref(complex_type(self(self, complex.element_type)),
                                ref.qualifiers,
                                ref.memory_space);
            }
            default:
                return ref;
        }
    };

    cir::TypeRef replaced = replace_ref(replace_ref, type_ref(pattern));
    if (!replaced.type.valid()) {
        report_error("cannot deduce placeholder type", loc);
        return file_.unknown_type();
    }
    return replaced.type;
}

size_t Session::count_auto_type_occurrences(
    cir::TypeId type,
    cir::AutoTypeFlavor flavor) const {
    auto count_ref = [&](auto& self, cir::TypeRef ref) -> size_t {
        if (!file_.valid(ref.type)) {
            return 0;
        }
        cir::TypeId resolved = file_.resolved_type(ref.type);
        const cir::Type& current = file_.type(resolved);
        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (current.kind) {
            case cir::TypeKind::Auto: {
                const auto& placeholder =
                    std::get<cir::AutoTypePayload>(payload);
                return placeholder.flavor == flavor ? 1 : 0;
            }
            case cir::TypeKind::Pointer:
                return self(self,
                            std::get<cir::PointerTypePayload>(payload).pointee);
            case cir::TypeKind::BlockPointer:
                return self(
                    self,
                    std::get<cir::BlockPointerTypePayload>(payload).pointee);
            case cir::TypeKind::MemberPointer: {
                const auto& member =
                    std::get<cir::MemberPointerTypePayload>(payload);
                return self(self, member.class_type) +
                    self(self, member.member_type);
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference:
                return self(
                    self,
                    std::get<cir::ReferenceTypePayload>(payload).referred_type);
            case cir::TypeKind::Array:
                return self(
                    self,
                    std::get<cir::ArrayTypePayload>(payload).element_type);
            case cir::TypeKind::Function: {
                const auto& function =
                    std::get<cir::FunctionTypePayload>(payload);
                size_t count = self(self, function.return_type);
                for (cir::TypeRef parameter : function.parameters) {
                    count += self(self, parameter);
                }
                return count;
            }
            case cir::TypeKind::Complex:
                return self(
                    self,
                    std::get<cir::ComplexTypePayload>(payload).element_type);
            default:
                return 0;
        }
    };
    return count_ref(count_ref, type_ref(type));
}

cir::TypeId Session::replace_auto_type_occurrences(
    cir::TypeId pattern,
    const std::vector<cir::TypeRef>& replacements,
    cir::AutoTypeFlavor flavor,
    SrcLoc loc) {
    size_t replacement_index = 0;
    auto replace_ref = [&](auto& self, cir::TypeRef ref) -> cir::TypeRef {
        if (!file_.valid(ref.type)) {
            return ref;
        }
        cir::TypeId resolved = file_.resolved_type(ref.type);
        const cir::Type& type = file_.type(resolved);
        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (type.kind) {
            case cir::TypeKind::Auto: {
                const auto& placeholder =
                    std::get<cir::AutoTypePayload>(payload);
                if (placeholder.flavor != flavor) {
                    return ref;
                }
                if (replacement_index >= replacements.size()) {
                    report_error("missing invented function parameter type",
                                 loc);
                    return type_ref(file_.unknown_type());
                }
                cir::TypeRef out = replacements[replacement_index++];
                out.qualifiers = static_cast<uint8_t>(out.qualifiers |
                                                       ref.qualifiers);
                if (out.memory_space == cir::MemorySpace::Default) {
                    out.memory_space = ref.memory_space;
                }
                return out;
            }
            case cir::TypeKind::Pointer: {
                const auto& pointer =
                    std::get<cir::PointerTypePayload>(payload);
                return type_ref(pointer_type(self(self, pointer.pointee)),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::BlockPointer: {
                const auto& pointer =
                    std::get<cir::BlockPointerTypePayload>(payload);
                return type_ref(block_pointer_type(self(self, pointer.pointee)),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::MemberPointer: {
                const auto& member =
                    std::get<cir::MemberPointerTypePayload>(payload);
                return type_ref(member_pointer_type(
                                    self(self, member.class_type),
                                    self(self, member.member_type)),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference: {
                const auto& reference =
                    std::get<cir::ReferenceTypePayload>(payload);
                return type_ref(reference_type(
                                    self(self, reference.referred_type),
                                    reference.reference_kind),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::Array: {
                const auto& array =
                    std::get<cir::ArrayTypePayload>(payload);
                return type_ref(file_.array_type(
                                    self(self, array.element_type),
                                    array.size_kind,
                                    array.size,
                                    array.size_expr,
                                    array.size_expr_is_dependent,
                                    array.extent_param,
                                    array.dependent_size_expr),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::Function: {
                const auto& function =
                    std::get<cir::FunctionTypePayload>(payload);
                cir::TypeRef result = self(self, function.return_type);
                std::vector<cir::TypeRef> parameters;
                parameters.reserve(function.parameters.size());
                for (cir::TypeRef parameter : function.parameters) {
                    parameters.push_back(self(self, parameter));
                }
                return type_ref(function_type(result,
                                              parameters,
                                              function.is_variadic,
                                              function.has_prototype,
                                              function.member_is_const,
                                              function.exception_spec,
                                              function.parameter_pack_flags,
                                              function.member_ref_qualifier,
                                              function.member_is_volatile),
                                ref.qualifiers,
                                ref.memory_space);
            }
            case cir::TypeKind::Complex: {
                const auto& complex =
                    std::get<cir::ComplexTypePayload>(payload);
                return type_ref(complex_type(self(self, complex.element_type)),
                                ref.qualifiers,
                                ref.memory_space);
            }
            default:
                return ref;
        }
    };

    cir::TypeRef replaced = replace_ref(replace_ref, type_ref(pattern));
    if (!replaced.type.valid() || replacement_index != replacements.size()) {
        report_error("cannot form invented function parameter type", loc);
        return file_.unknown_type();
    }
    return replaced.type;
}

cir::TypeId Session::array_type(cir::TypeId element, std::optional<size_t> size) {
    return file_.array_type(element, size);
}

cir::TypeId Session::array_type(cir::TypeRef element, std::optional<size_t> size) {
    return file_.array_type(element,
                            size.has_value() ? cir::ArraySizeKind::Constant
                                             : cir::ArraySizeKind::Incomplete,
                            size);
}

cir::TypeId Session::array_type_with_extent_param(cir::TypeRef element,
                                                  std::optional<size_t> size,
                                                  uint32_t extent_param) {
    return file_.array_type(
        element,
        cir::ArraySizeKind::Constant,
        size,
        {},
        false,
        extent_param);
}

cir::TypeId Session::array_type(cir::TypeRef element,
                                cir::ArraySizeKind size_kind,
                                std::optional<size_t> size,
                                cir::InstId size_expr,
                                bool size_expr_is_dependent,
                                cir::TemplateValueExpression dependent_size_expr) {
    return file_.array_type(element,
                            size_kind,
                            size,
                            size_expr,
                            size_expr_is_dependent,
                            cir::ArrayTypePayload::no_extent_param,
                            std::move(dependent_size_expr));
}

cir::TypeId Session::function_type(cir::TypeRef result,
                                   const std::vector<cir::TypeRef>& params,
                                   bool is_variadic,
                                   bool has_prototype,
                                   bool member_is_const,
                                   cir::FunctionExceptionSpec exception_spec,
                                   const std::vector<uint8_t>& parameter_pack_flags,
                                   cir::FunctionRefQualifierKind member_ref_qualifier,
                                   bool member_is_volatile) {
    return file_.function_type(result, params, is_variadic, has_prototype,
                               member_is_const, std::move(exception_spec),
                               parameter_pack_flags,
                               member_ref_qualifier, member_is_volatile);
}

} // namespace aburi::collect
