#include "collect.h"
#include "collect_template_state.h"

#include <cstring>

#include "../numeric/floating_cir.h"
#include "../constexpr/constant_state.h"
#include "../constexpr/consteval_engine.h"
#include "../cir/layout.h"
#include "../numeric_utils.h"

#include <algorithm>
#include <optional>
#include <limits>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::collect {

namespace {

void append_fragment_blocks(cir::Fragment& target, const cir::Fragment& source) {
    target.blocks.insert(target.blocks.end(), source.blocks.begin(), source.blocks.end());
}

bool is_compound_assignment(syntax::BinaryOperator op) {
    switch (op) {
        case syntax::BinaryOperator::AssignAdd:
        case syntax::BinaryOperator::AssignSub:
        case syntax::BinaryOperator::AssignMul:
        case syntax::BinaryOperator::AssignDiv:
        case syntax::BinaryOperator::AssignMod:
        case syntax::BinaryOperator::AssignShl:
        case syntax::BinaryOperator::AssignShr:
        case syntax::BinaryOperator::AssignAnd:
        case syntax::BinaryOperator::AssignXor:
        case syntax::BinaryOperator::AssignOr:
            return true;
        default:
            return false;
    }
}

std::optional<cir::TemplateValueExprOp>
template_value_expr_op(syntax::BinaryOperator op) {
    switch (op) {
        case syntax::BinaryOperator::Add: return cir::TemplateValueExprOp::Add;
        case syntax::BinaryOperator::Sub: return cir::TemplateValueExprOp::Sub;
        case syntax::BinaryOperator::Mul: return cir::TemplateValueExprOp::Mul;
        case syntax::BinaryOperator::Div: return cir::TemplateValueExprOp::Div;
        case syntax::BinaryOperator::Mod: return cir::TemplateValueExprOp::Mod;
        case syntax::BinaryOperator::Shl: return cir::TemplateValueExprOp::Shl;
        case syntax::BinaryOperator::Shr: return cir::TemplateValueExprOp::Shr;
        case syntax::BinaryOperator::BitAnd:
            return cir::TemplateValueExprOp::BitAnd;
        case syntax::BinaryOperator::BitOr:
            return cir::TemplateValueExprOp::BitOr;
        case syntax::BinaryOperator::BitXor:
            return cir::TemplateValueExprOp::BitXor;
        case syntax::BinaryOperator::Less: return cir::TemplateValueExprOp::Less;
        case syntax::BinaryOperator::LessEqual:
            return cir::TemplateValueExprOp::LessEqual;
        case syntax::BinaryOperator::Greater:
            return cir::TemplateValueExprOp::Greater;
        case syntax::BinaryOperator::GreaterEqual:
            return cir::TemplateValueExprOp::GreaterEqual;
        case syntax::BinaryOperator::Equal: return cir::TemplateValueExprOp::Equal;
        case syntax::BinaryOperator::NotEqual:
            return cir::TemplateValueExprOp::NotEqual;
        case syntax::BinaryOperator::ThreeWay:
            return cir::TemplateValueExprOp::ThreeWay;
        case syntax::BinaryOperator::LogicalAnd:
            return cir::TemplateValueExprOp::LogicalAnd;
        case syntax::BinaryOperator::LogicalOr:
            return cir::TemplateValueExprOp::LogicalOr;
        case syntax::BinaryOperator::Comma: return cir::TemplateValueExprOp::Comma;
        case syntax::BinaryOperator::PtrMemDot:
            return cir::TemplateValueExprOp::MemberPointerDot;
        case syntax::BinaryOperator::PtrMemArrow:
            return cir::TemplateValueExprOp::MemberPointerArrow;
        default: return std::nullopt;
    }
}

std::optional<cir::TemplateValueExprOp>
template_value_unary_expr_op(syntax::UnaryOperator op) {
    switch (op) {
        case syntax::UnaryOperator::Plus:
            return cir::TemplateValueExprOp::UnaryPlus;
        case syntax::UnaryOperator::Minus:
            return cir::TemplateValueExprOp::UnaryMinus;
        case syntax::UnaryOperator::LogicalNot:
            return cir::TemplateValueExprOp::LogicalNot;
        case syntax::UnaryOperator::BitwiseNot:
            return cir::TemplateValueExprOp::BitwiseNot;
        case syntax::UnaryOperator::Dereference:
            return cir::TemplateValueExprOp::Dereference;
        case syntax::UnaryOperator::AddressOf:
            return cir::TemplateValueExprOp::AddressOf;
        default: return std::nullopt;
    }
}

cir::TemplateValueExpression template_value_integer_expr(
    const cir::File& file,
    cir::IntegerValue value,
    cir::TypeRef type) {
    cir::TemplateValueExpression expr;
    expr.nodes.push_back(
        file.template_integer_expression_node(value, type));
    expr.root = 0;
    return expr;
}

cir::TemplateValueExpression template_value_parameter_expr(uint32_t index,
                                                           cir::TypeRef type,
                                                           cir::EntityId entity) {
    cir::TemplateValueExpression expr;
    cir::TemplateValueExprNode node;
    node.kind = cir::TemplateValueExprKind::Parameter;
    node.parameter_index = index;
    node.result_type = type;
    node.entity = entity;
    expr.nodes.push_back(node);
    expr.root = 0;
    return expr;
}

cir::TemplateValueExpression template_value_pack_size_expr(uint32_t index,
                                                          cir::TypeRef type) {
    cir::TemplateValueExpression expr;
    cir::TemplateValueExprNode node;
    node.kind = cir::TemplateValueExprKind::PackSize;
    node.parameter_index = index;
    node.result_type = type;
    expr.nodes.push_back(node);
    expr.root = 0;
    return expr;
}

cir::TemplateValueExpression template_value_sizeof_expr(cir::TypeId type,
                                                        bool is_alignof,
                                                        cir::TypeRef result_type) {
    cir::TemplateValueExpression expr;
    cir::TemplateValueExprNode node;
    node.kind = is_alignof ? cir::TemplateValueExprKind::AlignofType
                           : cir::TemplateValueExprKind::SizeofType;
    node.type = type;
    node.result_type = result_type;
    expr.nodes.push_back(node);
    expr.root = 0;
    return expr;
}

bool type_is_trivially_destructible(const cir::File& file,
                                    cir::TypeId type_id,
                                    std::vector<cir::TypeId>& record_stack);

bool record_is_trivially_destructible(const cir::File& file,
                                      cir::TypeId type_id,
                                      std::vector<cir::TypeId>& record_stack) {
    const cir::RecordFacts* facts = file.record_facts_for_type(type_id);
    if (!facts || facts->is_incomplete) {
        return false;
    }
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (method.special_member_kind !=
                cir::SpecialMemberKind::Destructor ||
            !method.is_selected_destructor) {
            continue;
        }
        return method.declared_access == cir::RecordMemberAccess::Public &&
            method.is_trivial && !method.is_deleted;
    }
    (void)record_stack;
    return false;
}

bool type_is_trivially_destructible(const cir::File& file,
                                    cir::TypeId type_id,
                                    std::vector<cir::TypeId>& record_stack) {
    cir::TypeId type = file.resolved_type(type_id);
    if (!file.valid(type)) {
        return false;
    }

    switch (file.type(type).kind) {
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return true;
        case cir::TypeKind::Builtin: {
            const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
                &file.type_payload(type));
            return builtin && builtin->kind != cir::BuiltinTypeKind::Void;
        }
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
        case cir::TypeKind::MemberPointer:
        case cir::TypeKind::Enum:
        case cir::TypeKind::Vector:
        case cir::TypeKind::Complex:
        case cir::TypeKind::BitInt:
            return true;
        case cir::TypeKind::Array: {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file.type_payload(type));
            return array &&
                array->size_kind == cir::ArraySizeKind::Constant &&
                array->size.has_value() &&
                type_is_trivially_destructible(file, array->element_type.type,
                                                record_stack);
        }
        case cir::TypeKind::Record:
            return record_is_trivially_destructible(file, type, record_stack);
        case cir::TypeKind::Typedef: {
            const auto* alias = std::get_if<cir::TypedefTypePayload>(
                &file.type_payload(type));
            return alias && type_is_trivially_destructible(
                file, alias->underlying_type.type, record_stack);
        }
        case cir::TypeKind::Invalid:
        case cir::TypeKind::Error:
        case cir::TypeKind::Unknown:
        case cir::TypeKind::Function:
        case cir::TypeKind::TypeParam:
        case cir::TypeKind::TemplateSpecialization:
        case cir::TypeKind::AliasSpecialization:
        case cir::TypeKind::DependentName:
        case cir::TypeKind::Dependent:
        case cir::TypeKind::Placeholder:
        case cir::TypeKind::Auto:
        case cir::TypeKind::TypeofExpr:
        case cir::TypeKind::DecltypeExpr:
        case cir::TypeKind::BuiltinTransform:
        case cir::TypeKind::BuiltinPackElement:
        case cir::TypeKind::PackIndex:
        case cir::TypeKind::Place:
            return false;
    }
    return false;
}

void append_template_value_expr_nodes(cir::TemplateValueExpression& target,
                                      const cir::TemplateValueExpression& source,
                                      uint32_t offset) {
    for (cir::TemplateValueExprNode node : source.nodes) {
        if (node.lhs != cir::TemplateValueExprNoNode) {
            node.lhs += offset;
        }
        if (node.rhs != cir::TemplateValueExprNoNode) {
            node.rhs += offset;
        }
        if (node.third != cir::TemplateValueExprNoNode) {
            node.third += offset;
        }
        for (uint32_t& operand : node.operands) {
            if (operand != cir::TemplateValueExprNoNode) {
                operand += offset;
            }
        }
        target.nodes.push_back(node);
    }
}

cir::TemplateValueExpression template_value_pack_index_expr(
    uint32_t pack_index,
    const cir::TemplateValueExpression& index,
    cir::TypeRef result_type,
    std::optional<uint32_t> function_parameter_index = std::nullopt) {
    cir::TemplateValueExpression expr;
    if (!index.valid()) {
        return expr;
    }
    append_template_value_expr_nodes(expr, index, 0);
    cir::TemplateValueExprNode node;
    node.kind = cir::TemplateValueExprKind::PackIndex;
    node.parameter_index = pack_index;
    node.lhs = index.root;
    node.result_type = result_type;
    node.semantic_key = function_parameter_index.has_value()
        ? "function-parameter-pack"
        : "template-parameter-pack";
    if (function_parameter_index.has_value()) {
        node.value = static_cast<int64_t>(*function_parameter_index);
    }
    expr.nodes.push_back(node);
    expr.root = static_cast<uint32_t>(expr.nodes.size() - 1);
    return expr;
}

cir::TemplateValueExpression
template_value_binary_expr(cir::TemplateValueExprOp op,
                           const cir::TemplateValueExpression& lhs,
                           const cir::TemplateValueExpression& rhs,
                           cir::TypeRef result_type,
                           ValueCategory result_category =
                               ValueCategory::Invalid) {
    cir::TemplateValueExpression expr;
    if (!lhs.valid() || !rhs.valid()) {
        return expr;
    }
    append_template_value_expr_nodes(expr, lhs, 0);
    uint32_t rhs_offset = static_cast<uint32_t>(expr.nodes.size());
    append_template_value_expr_nodes(expr, rhs, rhs_offset);

    cir::TemplateValueExprNode node;
    node.kind = cir::TemplateValueExprKind::Binary;
    node.op = op;
    node.lhs = lhs.root;
    node.rhs = rhs.root + rhs_offset;
    node.result_type = result_type;
    node.value = static_cast<int64_t>(result_category);
    expr.nodes.push_back(node);
    expr.root = static_cast<uint32_t>(expr.nodes.size() - 1);
    return expr;
}

cir::TemplateValueExpression template_value_unary_expr(
    cir::TemplateValueExprOp op,
    cir::TemplateValueExpression operand,
    cir::TypeRef result_type,
    ValueCategory result_category = ValueCategory::Invalid) {
    if (!operand.valid()) {
        return {};
    }
    operand.canonical_id = {};
    cir::TemplateValueExprNode node;
    node.kind = cir::TemplateValueExprKind::Unary;
    node.op = op;
    node.lhs = operand.root;
    node.result_type = result_type;
    node.value = static_cast<int64_t>(result_category);
    operand.nodes.push_back(node);
    operand.root = static_cast<uint32_t>(operand.nodes.size() - 1);
    return operand;
}

cir::TemplateValueExpression template_value_conditional_expr(
    const cir::TemplateValueExpression& condition,
    const cir::TemplateValueExpression& true_expr,
    const cir::TemplateValueExpression& false_expr,
    cir::TypeRef result_type,
    ValueCategory result_category = ValueCategory::PrValue) {
    cir::TemplateValueExpression expr;
    if (!condition.valid() || !true_expr.valid() || !false_expr.valid()) {
        return expr;
    }
    append_template_value_expr_nodes(expr, condition, 0);
    uint32_t true_offset = static_cast<uint32_t>(expr.nodes.size());
    append_template_value_expr_nodes(expr, true_expr, true_offset);
    uint32_t false_offset = static_cast<uint32_t>(expr.nodes.size());
    append_template_value_expr_nodes(expr, false_expr, false_offset);
    cir::TemplateValueExprNode node;
    node.kind = cir::TemplateValueExprKind::Conditional;
    node.lhs = condition.root;
    node.rhs = true_expr.root + true_offset;
    node.third = false_expr.root + false_offset;
    node.result_type = result_type;
    node.value = static_cast<int64_t>(result_category);
    expr.nodes.push_back(node);
    expr.root = static_cast<uint32_t>(expr.nodes.size() - 1);
    return expr;
}

std::string template_recipe_type_key(const cir::File& file,
                                     cir::TypeRef ref) {
    cir::TypeId type = file.resolved_type(ref.type);
    std::string key;
    if (!file.valid(type)) {
        key = "<invalid-type>";
    } else {
        switch (file.type(type).kind) {
            case cir::TypeKind::TypeParam: {
                const auto* parameter =
                    std::get_if<cir::TypeParamTypePayload>(
                        &file.type_payload(type));
                key = parameter
                    ? "$" + std::to_string(parameter->depth) + "." +
                          std::to_string(parameter->index) +
                          (parameter->is_parameter_pack ? "..." : "")
                    : "<type-parameter>";
                break;
            }
            case cir::TypeKind::Pointer: {
                const auto* pointer =
                    std::get_if<cir::PointerTypePayload>(
                        &file.type_payload(type));
                key = pointer
                    ? "*" + template_recipe_type_key(file, pointer->pointee)
                    : "*<invalid-type>";
                break;
            }
            case cir::TypeKind::LValueReference:
                key = "&" + template_recipe_type_key(
                    file, file.reference_referred_ref(type));
                break;
            case cir::TypeKind::RValueReference:
                key = "&&" + template_recipe_type_key(
                    file, file.reference_referred_ref(type));
                break;
            default:
                key = file.format_type(ref);
                break;
        }
    }
    if (ref.qualifiers != cir::QualNone) {
        key += ":q" + std::to_string(ref.qualifiers);
    }
    if (ref.memory_space != cir::MemorySpace::Default) {
        key += ":m" +
            std::to_string(static_cast<unsigned>(ref.memory_space));
    }
    return key;
}

cir::TemplateValueExpression template_value_type_trait_expr(
    const cir::File& file,
    cir::BuiltinTypeTraitKind trait_kind,
    const std::vector<cir::TypeRef>& operands,
    const std::vector<uint32_t>& pack_indices,
    cir::TypeRef result_type) {
    cir::TemplateValueExpression expr;
    auto append_type_operand = [&](cir::TypeRef operand,
                                   uint32_t pack_index) {
        cir::TemplateValueExprNode node;
        node.kind = cir::TemplateValueExprKind::TypeOperand;
        node.type = operand.type;
        node.result_type = operand;
        node.semantic_key = template_recipe_type_key(file, operand);
        node.expands_parameter_pack =
            pack_index != cir::TemplateValueExprNoParameter;
        node.parameter_index = pack_index;
        expr.nodes.push_back(std::move(node));
        return static_cast<uint32_t>(expr.nodes.size() - 1);
    };

    cir::TemplateValueExprNode trait;
    trait.kind = cir::TemplateValueExprKind::TypeTrait;
    trait.trait_kind = trait_kind;
    trait.operands.reserve(operands.size());
    for (size_t i = 0; i < operands.size(); ++i) {
        trait.operands.push_back(
            append_type_operand(operands[i], pack_indices[i]));
    }
    trait.result_type = result_type;
    trait.semantic_key = "type-trait." +
        std::to_string(static_cast<unsigned>(trait_kind));
    expr.nodes.push_back(std::move(trait));
    expr.root = static_cast<uint32_t>(expr.nodes.size() - 1);
    return expr;
}

cir::TypeRef resolve_trait_type_ref(const cir::File& file,
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

uint8_t trait_top_level_qualifiers(const cir::File& file,
                                   cir::TypeRef ref) {
    ref = resolve_trait_type_ref(file, ref);
    uint8_t qualifiers = ref.qualifiers;
    while (ref.valid() && file.valid(ref.type) &&
           file.type(ref.type).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file.type_payload(ref.type));
        if (!array) {
            break;
        }
        ref = resolve_trait_type_ref(file, array->element_type);
        qualifiers = static_cast<uint8_t>(qualifiers | ref.qualifiers);
    }
    return qualifiers;
}

bool trait_is_integral(const cir::File& file, cir::TypeRef ref) {
    ref = resolve_trait_type_ref(file, ref);
    if (!ref.valid() || !file.valid(ref.type)) {
        return false;
    }
    if (file.type(ref.type).kind == cir::TypeKind::BitInt) {
        return true;
    }
    if (file.type(ref.type).kind != cir::TypeKind::Builtin) {
        return false;
    }
    const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
        &file.type_payload(ref.type));
    if (!builtin) {
        return false;
    }
    switch (builtin->kind) {
        case cir::BuiltinTypeKind::Bool:
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
        case cir::BuiltinTypeKind::UChar:
        case cir::BuiltinTypeKind::Char8:
        case cir::BuiltinTypeKind::WChar:
        case cir::BuiltinTypeKind::Char16:
        case cir::BuiltinTypeKind::Char32:
        case cir::BuiltinTypeKind::Short:
        case cir::BuiltinTypeKind::UShort:
        case cir::BuiltinTypeKind::Int:
        case cir::BuiltinTypeKind::UInt:
        case cir::BuiltinTypeKind::Long:
        case cir::BuiltinTypeKind::ULong:
        case cir::BuiltinTypeKind::LongLong:
        case cir::BuiltinTypeKind::ULongLong:
        case cir::BuiltinTypeKind::Int128:
        case cir::BuiltinTypeKind::UInt128:
        case cir::BuiltinTypeKind::USize:
            return true;
        case cir::BuiltinTypeKind::Void:
        case cir::BuiltinTypeKind::NullPtr:
        case cir::BuiltinTypeKind::Float16:
        case cir::BuiltinTypeKind::Float:
        case cir::BuiltinTypeKind::Double:
        case cir::BuiltinTypeKind::LongDouble:
        case cir::BuiltinTypeKind::MetaInfo:
        case cir::BuiltinTypeKind::Other:
            return false;
    }
    return false;
}

bool trait_is_floating(const cir::File& file, cir::TypeRef ref) {
    ref = resolve_trait_type_ref(file, ref);
    if (!ref.valid() || !file.valid(ref.type) ||
        file.type(ref.type).kind != cir::TypeKind::Builtin) {
        return false;
    }
    const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
        &file.type_payload(ref.type));
    return builtin &&
        (builtin->kind == cir::BuiltinTypeKind::Float16 ||
         builtin->kind == cir::BuiltinTypeKind::Float ||
         builtin->kind == cir::BuiltinTypeKind::Double ||
         builtin->kind == cir::BuiltinTypeKind::LongDouble);
}

bool trait_has_unique_object_representations(
    const cir::File& file,
    cir::TypeRef ref,
    std::vector<cir::TypeId>& record_stack) {
    ref = resolve_trait_type_ref(file, ref);
    if (!ref.valid() || !file.valid(ref.type)) {
        return false;
    }
    const cir::TypeKind kind = file.type(ref.type).kind;
    if (trait_is_integral(file, ref)) {
        std::optional<size_t> size = cir::size_of_type(file, ref.type);
        if (!size.has_value()) {
            return false;
        }
        cir::IntegerTypeShape shape =
            cir::integer_shape_for_type(file, ref.type);
        return *size * 8 == shape.bit_width;
    }
    switch (kind) {
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
            return true;
        case cir::TypeKind::Enum: {
            const auto* enumeration = std::get_if<cir::EnumTypePayload>(
                &file.type_payload(ref.type));
            return enumeration && enumeration->underlying_type.valid() &&
                trait_has_unique_object_representations(
                    file, enumeration->underlying_type, record_stack);
        }
        case cir::TypeKind::Array: {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file.type_payload(ref.type));
            return array &&
                trait_has_unique_object_representations(
                    file, array->element_type, record_stack);
        }
        case cir::TypeKind::Record:
            break;
        case cir::TypeKind::Invalid:
        case cir::TypeKind::Error:
        case cir::TypeKind::Unknown:
        case cir::TypeKind::Builtin:
        case cir::TypeKind::MemberPointer:
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
        case cir::TypeKind::Function:
        case cir::TypeKind::Vector:
        case cir::TypeKind::Complex:
        case cir::TypeKind::BitInt:
        case cir::TypeKind::Typedef:
        case cir::TypeKind::TypeParam:
        case cir::TypeKind::TemplateSpecialization:
        case cir::TypeKind::AliasSpecialization:
        case cir::TypeKind::DependentName:
        case cir::TypeKind::Dependent:
        case cir::TypeKind::Placeholder:
        case cir::TypeKind::Auto:
        case cir::TypeKind::TypeofExpr:
        case cir::TypeKind::DecltypeExpr:
        case cir::TypeKind::BuiltinTransform:
        case cir::TypeKind::BuiltinPackElement:
        case cir::TypeKind::PackIndex:
        case cir::TypeKind::Place:
            return false;
    }

    const cir::RecordFacts* facts = file.record_facts_for_type(ref.type);
    if (!facts || facts->is_incomplete ||
        facts->is_trivially_copyable != cir::ClassPropertyState::True ||
        std::find(record_stack.begin(), record_stack.end(), ref.type) !=
            record_stack.end()) {
        return false;
    }
    std::optional<size_t> record_size = cir::size_of_type(file, ref.type);
    if (!record_size.has_value()) {
        return false;
    }

    struct OccupiedBits {
        size_t begin = 0;
        size_t end = 0;
    };
    std::vector<OccupiedBits> occupied;
    record_stack.push_back(ref.type);
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.is_flexible_array_member ||
            field.subobject_size != cir::SubobjectSizeKind::NonZero ||
            field.is_potentially_overlapping) {
            record_stack.pop_back();
            return false;
        }
        if (field.is_bitfield) {
            if (field.bit_width == 0) {
                continue;
            }
            if (cir::bitfield_value_width(file, field) != field.bit_width) {
                record_stack.pop_back();
                return false;
            }
            size_t begin = field.offset * 8 + field.bit_offset;
            occupied.push_back({begin, begin + field.bit_width});
            continue;
        }
        if (!trait_has_unique_object_representations(
                file, field.type, record_stack)) {
            record_stack.pop_back();
            return false;
        }
        std::optional<size_t> field_size =
            cir::size_of_type(file, field.type.type);
        if (!field_size.has_value()) {
            record_stack.pop_back();
            return false;
        }
        size_t begin = field.offset * 8;
        occupied.push_back({begin, begin + *field_size * 8});
    }
    record_stack.pop_back();

    if (facts->kind == cir::RecordKind::Union && occupied.size() > 1) {
        return false;
    }
    std::sort(occupied.begin(), occupied.end(),
              [](const OccupiedBits& lhs, const OccupiedBits& rhs) {
                  return lhs.begin < rhs.begin ||
                      (lhs.begin == rhs.begin && lhs.end < rhs.end);
              });
    size_t cursor = 0;
    for (const OccupiedBits& bits : occupied) {
        if (bits.begin != cursor || bits.end < bits.begin) {
            return false;
        }
        cursor = bits.end;
    }
    return cursor == *record_size * 8;
}

std::string template_recipe_value_expr_key(
    const cir::File& file,
    const cir::TemplateValueExpression& expression) {
    std::string key = "r" + std::to_string(expression.root);
    for (const cir::TemplateValueExprNode& node : expression.nodes) {
        key += ":n" + std::to_string(static_cast<unsigned>(node.kind));
        key += ":o" + std::to_string(static_cast<unsigned>(node.op));
        key += ":f" +
            std::to_string(static_cast<unsigned>(node.fold_kind));
        key += ":v" + std::to_string(node.value);
        key += ":p" + std::to_string(node.parameter_index);
        key += ":l" + std::to_string(node.lhs);
        key += ":r" + std::to_string(node.rhs);
        key += ":x" + std::to_string(node.third);
        if (node.result_type.type.valid()) {
            key += ":t" + template_recipe_type_key(file, node.result_type);
        }
        key += ":s" + std::to_string(node.semantic_key.size()) + ":" +
            node.semantic_key;
    }
    return key;
}

std::string template_recipe_argument_key(
    const cir::File& file,
    const cir::TemplateArgument& argument) {
    std::string key = "k" +
        std::to_string(static_cast<unsigned>(argument.kind));
    if (argument.type.type.valid()) {
        key += ":t" + template_recipe_type_key(file, argument.type);
    }
    if (argument.value_type.type.valid()) {
        key += ":vt" + template_recipe_type_key(file, argument.value_type);
    }
    key += ":vk" +
        std::to_string(static_cast<unsigned>(argument.value_kind));
    key += ":nk" +
        std::to_string(static_cast<unsigned>(argument.null_kind));
    key += ":v" + argument.integer_value.decimal();
    key += argument.integer_value.is_unsigned ? ":u" : ":s";
    key += std::to_string(argument.integer_value.bit_width);
    key += ":o" + std::to_string(argument.value_byte_offset);
    key += ":m" +
        std::to_string(static_cast<unsigned>(argument.meta_kind));
    key += ":vp" + std::to_string(argument.value_param_index);
    key += ":tp" + std::to_string(argument.template_param_index);
    key += argument.is_dependent ? ":d1" : ":d0";
    key += argument.expands_parameter_pack ? ":p1" : ":p0";
    key += argument.expands_pack_pattern ? ":x1" : ":x0";
    key += ":g" + std::to_string(
        static_cast<unsigned>(argument.generated_pack_kind));
    if (argument.generated_pack_count_type.type.valid()) {
        key += ":gt" + template_recipe_type_key(
            file, argument.generated_pack_count_type);
    }
    key += ":ge" + template_recipe_value_expr_key(
        file, argument.generated_pack_count_expr);
    for (const cir::TemplateArgument& element : argument.value_elements) {
        std::string element_key =
            template_recipe_argument_key(file, element);
        key += ":e" + std::to_string(element_key.size()) + ":" +
            element_key;
    }
    return key;
}

cir::EntityId stable_template_recipe_entity(const cir::File& file,
                                             cir::EntityId entity) {
    if (!entity.valid() || !file.valid(entity)) {
        return {};
    }
    if (const cir::TemplateSpecializationFact* specialization =
            file.template_specialization(entity);
        specialization && specialization->template_entity.valid() &&
        file.valid(specialization->template_entity)) {
        return specialization->template_entity;
    }
    return entity;
}

std::string template_recipe_entity_key(const cir::File& file,
                                       cir::EntityId entity) {
    entity = stable_template_recipe_entity(file, entity);
    if (!entity.valid()) {
        return "<invalid-entity>";
    }

    std::vector<std::string> components;
    cir::EntityId current = entity;
    for (size_t depth = 0;
         current.valid() && file.valid(current) && depth != 64;
         ++depth) {
        const cir::Entity& declaration = file.entity(current);
        std::string component =
            std::to_string(static_cast<unsigned>(declaration.kind)) + ":";
        component += declaration.name.valid()
            ? std::string(file.name(declaration.name))
            : std::string("<anonymous>");
        components.push_back(std::move(component));
        current = declaration.parent;
    }
    std::reverse(components.begin(), components.end());

    std::string key;
    for (const std::string& component : components) {
        key += std::to_string(component.size()) + ":" + component;
    }
    const cir::Entity& declaration = file.entity(entity);
    if (declaration.type.valid() && file.valid(declaration.type)) {
        key += ":type:" +
            template_recipe_type_key(file, file.type_ref(declaration.type));
    }
    return key;
}

cir::TypeRef template_recipe_expression_type(const cir::File& file,
                                             const ExprResult& expression) {
    cir::TypeRef result = file.type_ref(expression.type);
    bool glvalue = expression.category == ValueCategory::LValue ||
        expression.category == ValueCategory::XValue ||
        expression.category == ValueCategory::QualifiedMember;
    if (!glvalue) {
        return result;
    }
    if (expression.semantic_object_qualifiers.has_value()) {
        result.qualifiers = static_cast<uint8_t>(
            result.qualifiers | *expression.semantic_object_qualifiers);
    }
    if (!expression.place.valid() || !file.valid(expression.place)) {
        return result;
    }
    const cir::Inst& place = file.inst(expression.place);
    cir::TypeRef object;
    if (place.place_fact.valid() && file.valid(place.place_fact)) {
        object = file.place_fact(place.place_fact).object_type;
    } else {
        object = file.place_object_ref(place.result_type);
    }
    return object.valid() ? object : result;
}

cir::TemplateValueExpression template_value_operand_expr(
    cir::File& file,
    const ExprResult& operand) {
    if (operand.template_value_expr.valid()) {
        cir::TemplateValueExpression expression = operand.template_value_expr;
        expression.canonical_id = {};
        return expression;
    }

    cir::TemplateValueExpression expression;
    cir::TemplateValueExprNode descriptor;
    if (operand.entity.valid() && file.valid(operand.entity)) {
        const cir::Entity& entity = file.entity(operand.entity);
        if (entity.has_constant_value &&
            (entity.constant_value_kind ==
                 cir::TemplateValueKind::Integer ||
             entity.constant_value_kind ==
                 cir::TemplateValueKind::Boolean)) {
            cir::TypeRef result_type =
                operand.type.valid() && file.valid(operand.type)
                    ? file.type_ref(operand.type)
                    : cir::TypeRef{};
            descriptor = file.template_integer_expression_node(
                entity.constant_integer_value, result_type);
            expression.nodes.push_back(std::move(descriptor));
            expression.root = 0;
            return expression;
        }
    }
    descriptor.kind = cir::TemplateValueExprKind::TypeOperand;
    descriptor.value = static_cast<int64_t>(operand.category);
    cir::TypeId resolved_operand_type =
        file.resolved_type(operand.type);
    bool opaque_dependent_type =
        file.valid(resolved_operand_type) &&
        file.type(resolved_operand_type).kind == cir::TypeKind::Dependent;
    if (operand.type.valid() && file.valid(operand.type) &&
        !opaque_dependent_type) {
        cir::TypeRef expression_type =
            template_recipe_expression_type(file, operand);
        descriptor.type = operand.type;
        descriptor.result_type = expression_type;
    }
    descriptor.entity = stable_template_recipe_entity(file, operand.entity);
    descriptor.name = !operand.name.empty()
        ? file.intern_name(operand.name)
        : operand.dependent_value_name;
    if (operand.dependent_value_qualifier.type.valid() &&
        file.valid(operand.dependent_value_qualifier.type)) {
        descriptor.qualifier_type = operand.dependent_value_qualifier;
    }
    if (descriptor.entity.valid()) {
        descriptor.semantic_key =
            template_recipe_entity_key(file, descriptor.entity);
    } else if (!operand.name.empty()) {
        descriptor.semantic_key = operand.name;
    } else if (operand.type.valid() && file.valid(operand.type)) {
        descriptor.semantic_key =
            template_recipe_type_key(
                file, template_recipe_expression_type(file, operand));
    } else {
        descriptor.semantic_key = "<dependent-operand>";
    }
    expression.nodes.push_back(std::move(descriptor));
    expression.root = 0;
    return expression;
}

cir::TemplateValueExpression template_value_member_access_expr(
    cir::File& file,
    const ExprResult& base,
    std::string_view member_name,
    bool is_arrow) {
    cir::TemplateValueExpression expression =
        template_value_operand_expr(file, base);
    if (!expression.valid()) {
        return {};
    }
    expression.canonical_id = {};
    cir::TemplateValueExprNode member;
    member.kind = cir::TemplateValueExprKind::TypeOperand;
    member.lhs = expression.root;
    member.name = file.intern_name(std::string(member_name));
    cir::TemplateCalleeFlag flags =
        cir::TemplateCalleeFlag::MemberAccess;
    if (is_arrow) {
        flags |= cir::TemplateCalleeFlag::MemberArrow;
    }
    member.value = static_cast<int64_t>(flags);
    member.semantic_key =
        std::string(is_arrow ? "member-arrow:" : "member-dot:") +
        std::string(member_name);
    expression.nodes.push_back(std::move(member));
    expression.root = static_cast<uint32_t>(expression.nodes.size() - 1);
    file.canonicalize_template_value_expression(expression);
    return expression;
}

cir::TemplateValueExpression template_value_call_expr(
    Session& session,
    cir::File& file,
    const ExprResult& callee,
    const std::vector<ExprResult>& arguments,
    cir::TypeRef result_type,
    cir::DeclContextId definition_context,
    uint64_t definition_lookup_generation,
    SrcLoc loc) {
    cir::TemplateValueExpression expr;

    auto append_expression = [&](const cir::TemplateValueExpression& source)
        -> uint32_t {
        if (!source.valid()) {
            return cir::TemplateValueExprNoNode;
        }
        uint32_t offset = static_cast<uint32_t>(expr.nodes.size());
        append_template_value_expr_nodes(expr, source, offset);
        return source.root + offset;
    };

    uint32_t argument_head = cir::TemplateValueExprNoNode;
    uint32_t argument_tail = cir::TemplateValueExprNoNode;
    for (const ExprResult& argument : arguments) {
        cir::TemplateValueExpression value_expression =
            argument.template_value_expr;
        if (!value_expression.valid() &&
            argument.dependent_value_qualifier.type.valid() &&
            argument.dependent_value_name.valid()) {

            value_expression =
                session.template_value_operand_expression(argument);
        }
        uint32_t value_root = append_expression(value_expression);
        cir::TemplateValueExprNode node;
        node.kind = cir::TemplateValueExprKind::TypeOperand;
        node.value = static_cast<int64_t>(argument.category);
        node.lhs = value_root;
        node.type = argument.type;
        node.result_type =
            template_recipe_expression_type(file, argument);
        node.pack_references = argument.pack_expansion_references;
        if (!node.pack_references.empty()) {
            node.expands_parameter_pack = true;
            auto first_type = std::find_if(
                node.pack_references.begin(),
                node.pack_references.end(),
                [](const cir::TemplateValuePackReference& reference) {
                    return reference.kind ==
                        cir::TemplateValuePackKind::Type;
                });
            if (first_type != node.pack_references.end()) {
                node.parameter_index = first_type->index;
            }
        }
        node.semantic_key = template_recipe_type_key(
            file, node.result_type);
        expr.nodes.push_back(node);
        uint32_t index = static_cast<uint32_t>(expr.nodes.size() - 1);
        if (argument_tail == cir::TemplateValueExprNoNode) {
            argument_head = index;
        } else {
            expr.nodes[argument_tail].rhs = index;
        }
        argument_tail = index;
    }

    auto append_explicit_argument_chain =
        [&](const std::vector<cir::TemplateArgument>& arguments) {
        uint32_t head = cir::TemplateValueExprNoNode;
        uint32_t tail = cir::TemplateValueExprNoNode;
        for (const cir::TemplateArgument& argument : arguments) {
            uint32_t value_root =
                append_expression(argument.dependent_value_expr);
            cir::TemplateValueExprNode node;
            node.kind = cir::TemplateValueExprKind::TypeOperand;
            node.template_arguments =
                cir::TemplateArgumentList({argument});
            node.value = static_cast<int64_t>(argument.kind);
            node.lhs = value_root;
            node.type = argument.type.type;
            node.result_type = argument.value_type;
            node.entity =
                argument.kind == cir::TemplateArgumentKind::Template
                ? argument.template_entity
                : argument.value_entity;
            node.name =
                argument.kind == cir::TemplateArgumentKind::Template
                ? argument.template_name
                : argument.dependent_value_name;
            node.qualifier_type =
                argument.kind == cir::TemplateArgumentKind::Template
                ? argument.dependent_template_qualifier
                : argument.dependent_value_qualifier;
            if (argument.kind == cir::TemplateArgumentKind::Template) {
                node.parameter_index = argument.template_param_index;
            }
            if (argument.expands_parameter_pack) {
                cir::TemplateValuePackReference reference;
                std::optional<uint32_t> pack_index;
                switch (argument.kind) {
                    case cir::TemplateArgumentKind::Type:
                        reference.kind =
                            cir::TemplateValuePackKind::Type;
                        reference.parameter_type = argument.type.type;
                        pack_index = session.type_parameter_pack_index(
                            argument.type.type);
                        break;
                    case cir::TemplateArgumentKind::Value:
                        reference.kind =
                            cir::TemplateValuePackKind::Value;
                        if (argument.value_param_index !=
                            cir::ArrayTypePayload::no_extent_param) {
                            pack_index = argument.value_param_index;
                        }
                        break;
                    case cir::TemplateArgumentKind::Template:
                        reference.kind =
                            cir::TemplateValuePackKind::Template;
                        reference.declaration =
                            argument.template_entity;
                        if (argument.template_param_index !=
                            cir::ArrayTypePayload::no_extent_param) {
                            pack_index =
                                argument.template_param_index;
                        }
                        reference.name = argument.template_name;
                        break;
                }
                if (pack_index.has_value()) {
                    reference.index = *pack_index;
                    node.pack_references.push_back(reference);
                    node.parameter_index = *pack_index;
                }
                node.expands_parameter_pack = true;
            }
            node.semantic_key =
                template_recipe_argument_key(file, argument);
            expr.nodes.push_back(node);
            uint32_t index =
                static_cast<uint32_t>(expr.nodes.size() - 1);
            if (tail == cir::TemplateValueExprNoNode) {
                head = index;
            } else {
                expr.nodes[tail].rhs = index;
            }
            tail = index;
        }
        return head;
    };
    uint32_t explicit_head = append_explicit_argument_chain(
        callee.explicit_template_arguments);

    uint32_t member_base = cir::TemplateValueExprNoNode;
    bool member_is_arrow = false;
    if (callee.dependent_member_access.has_value() &&
        callee.dependent_member_access->base) {
        const ExprResult& base = *callee.dependent_member_access->base;
        cir::TemplateValueExprNode node;
        node.kind = cir::TemplateValueExprKind::TypeOperand;
        node.value = static_cast<int64_t>(base.category);
        node.lhs = append_expression(base.template_value_expr);
        node.type = base.type;
        node.result_type = template_recipe_expression_type(file, base);
        node.semantic_key = template_recipe_type_key(
            file, node.result_type);
        expr.nodes.push_back(node);
        member_base = static_cast<uint32_t>(expr.nodes.size() - 1);
        member_is_arrow = callee.dependent_member_access->is_arrow;
    }

    cir::TemplateValueExprNode target;
    target.kind = cir::TemplateValueExprKind::Callee;
    bool has_named_target = callee.dependent_member_access.has_value() ||
        callee.entity.valid() || !callee.name.empty() ||
        callee.dependent_value_name.valid();
    bool named_object_target =
        callee.entity.valid() && file.valid(callee.entity) &&
        file.entity(callee.entity).kind != cir::EntityKind::Function &&
        file.entity(callee.entity).kind != cir::EntityKind::Method;
    if (!callee.dependent_member_access.has_value() &&
        (callee.template_value_expr.valid() || !has_named_target ||
         named_object_target)) {

        target.lhs = append_expression(
            session.template_value_operand_expression(callee));
    } else {
        target.entity = stable_template_recipe_entity(file, callee.entity);
        target.name = !callee.name.empty()
            ? file.intern_name(callee.name)
            : callee.dependent_value_name;
        target.qualifier_type = callee.dependent_value_qualifier;
        target.rhs = member_base;
        if (target.entity.valid()) {
            target.semantic_key =
                template_recipe_entity_key(file, target.entity);
        } else if (!callee.name.empty()) {
            target.semantic_key = callee.name;
        } else if (target.name.valid() && file.valid(target.name)) {
            target.semantic_key = std::string(file.name(target.name));
        }

        struct CandidateIdentity {
            cir::EntityId entity{};
            std::string key;
        };
        std::vector<CandidateIdentity> lookup_candidates;
        lookup_candidates.reserve(callee.candidates.size());
        for (cir::EntityId candidate : callee.candidates) {
            candidate = stable_template_recipe_entity(file, candidate);
            if (!candidate.valid()) {
                continue;
            }
            lookup_candidates.push_back(
                {candidate, template_recipe_entity_key(file, candidate)});
        }
        std::sort(lookup_candidates.begin(), lookup_candidates.end(),
                  [](const CandidateIdentity& lhs,
                     const CandidateIdentity& rhs) {
                      if (lhs.key != rhs.key) {
                          return lhs.key < rhs.key;
                      }
                      if (lhs.entity.index != rhs.entity.index) {
                          return lhs.entity.index < rhs.entity.index;
                      }
                      return lhs.entity.generation < rhs.entity.generation;
                  });
        lookup_candidates.erase(
            std::unique(
                lookup_candidates.begin(), lookup_candidates.end(),
                [](const CandidateIdentity& lhs,
                   const CandidateIdentity& rhs) {
                    return lhs.entity == rhs.entity;
                }),
            lookup_candidates.end());
        for (CandidateIdentity& identity : lookup_candidates) {
            cir::TemplateValueExprNode candidate;
            candidate.kind = cir::TemplateValueExprKind::TypeOperand;
            candidate.entity = identity.entity;
            candidate.semantic_key = std::move(identity.key);
            auto candidate_arguments = std::find_if(
                callee.candidate_explicit_template_arguments.begin(),
                callee.candidate_explicit_template_arguments.end(),
                [&](const CandidateExplicitTemplateArguments& entry) {
                    return stable_template_recipe_entity(
                               file, entry.template_entity) ==
                        candidate.entity;
                });
            if (candidate_arguments !=
                callee.candidate_explicit_template_arguments.end()) {
                if (!candidate_arguments->viable) {
                    continue;
                }
                candidate.lhs =
                    append_explicit_argument_chain(
                        candidate_arguments->arguments);
            }
            expr.nodes.push_back(std::move(candidate));
            target.operands.push_back(
                static_cast<uint32_t>(expr.nodes.size() - 1));
        }
    }
    // A Callee node describes lookup, not an expression value. In particular,
    // an overload-set designator's transient type can name any one candidate;
    // retaining it would make substitution instantiate that candidate before
    // overload resolution has had a chance to discard it. The Call node owns
    // the expression's result type, while expression callees retain their type
    // on the graph rooted at target.lhs.
    target.result_type = {};
    cir::TemplateCalleeFlag flags = cir::TemplateCalleeFlag::None;
    if (callee.qualified_name) {
        flags |= cir::TemplateCalleeFlag::QualifiedName;
    }
    if (callee.suppress_argument_dependent_lookup) {
        flags |= cir::TemplateCalleeFlag::SuppressArgumentDependentLookup;
    }
    if (callee.unresolved_unqualified_name) {
        flags |= cir::TemplateCalleeFlag::UnresolvedUnqualifiedName;
    }
    if (callee.has_explicit_template_arguments) {
        flags |= cir::TemplateCalleeFlag::HasExplicitTemplateArguments;
    }
    if (callee.builtin_call_designator) {
        flags |= cir::TemplateCalleeFlag::BuiltinCallDesignator;
    }
    if (member_is_arrow) {
        flags |= cir::TemplateCalleeFlag::MemberArrow;
    }
    target.value = static_cast<int64_t>(flags);
    expr.nodes.push_back(std::move(target));
    uint32_t target_index = static_cast<uint32_t>(expr.nodes.size() - 1);

    cir::TemplateValueExprNode call;
    call.kind = cir::TemplateValueExprKind::Call;
    call.lhs = argument_head;
    call.rhs = explicit_head;
    call.third = target_index;
    call.result_type = result_type;
    expr.nodes.push_back(call);
    expr.root = static_cast<uint32_t>(expr.nodes.size() - 1);
    expr.loc = loc;
    expr.definition_context = definition_context;
    expr.definition_lookup_generation = definition_lookup_generation;
    return expr;
}

const cir::LiteralPayload* literal_payload(const cir::File& file, cir::InstId inst) {
    if (!file.valid(inst)) {
        return nullptr;
    }
    const cir::Inst& record = file.inst(inst);
    if (record.payload_index == 0) {
        return nullptr;
    }
    return std::get_if<cir::LiteralPayload>(&file.payload(record.payload_index));
}

std::optional<std::string> string_literal_text(const cir::File& file,
                                               const ExprResult& expr) {
    cir::InstId inst = expr.place.valid() ? expr.place : expr.value;
    if (!file.valid(inst) ||
        file.inst(inst).kind != cir::InstKind::StringLiteral) {
        return std::nullopt;
    }
    const cir::LiteralPayload* literal = literal_payload(file, inst);
    const auto* bytes = literal
        ? std::get_if<cir::LiteralByteArray>(&literal->value)
        : nullptr;
    return bytes
        ? std::optional<std::string>(
              std::string(bytes->begin(), bytes->end()))
        : std::nullopt;
}

bool is_integer_zero_literal(const cir::File& file, const ExprResult& expr) {
    if (!file.valid(expr.value) || !file.valid(expr.type) ||
        !cir::is_integer_like_type(file, expr.type)) {
        return false;
    }
    if (file.inst(expr.value).kind != cir::InstKind::IntegerLiteral) {
        return false;
    }
    const cir::LiteralPayload* literal = literal_payload(file, expr.value);
    const auto* value = literal
        ? std::get_if<cir::IntegerValue>(&literal->value)
        : nullptr;
    return value && value->is_zero();
}

bool is_cir_pointer_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    return file.valid(type) &&
           (file.type(type).kind == cir::TypeKind::Pointer ||
            file.type(type).kind == cir::TypeKind::BlockPointer);
}

bool pointee_is_void(const cir::File& file, cir::TypeId pointer_type);

bool is_null_pointer_constant_expr(const cir::File& file, const ExprResult& expr) {
    if (is_integer_zero_literal(file, expr)) {
        return true;
    }
    cir::TypeId type = file.resolved_type(expr.type);
    if (!is_cir_pointer_type(file, type) || !pointee_is_void(file, type)) {
        return false;
    }

    cir::InstId inst = expr.value;
    while (file.valid(inst)) {
        const cir::Inst& current = file.inst(inst);
        if (current.kind == cir::InstKind::IntegerLiteral) {
            const cir::LiteralPayload* literal = literal_payload(file, inst);
            const auto* value = literal
                ? std::get_if<cir::IntegerValue>(&literal->value)
                : nullptr;
            return value && value->is_zero();
        }
        if (current.kind != cir::InstKind::Cast) {
            break;
        }
        std::vector<cir::ValueRef> operands = file.value_operands(current.operands);
        if (operands.empty()) {
            return false;
        }
        cir::InstId operand = operands[0].inst;
        if (file.valid(operand) &&
            cir::is_integer_like_type(
                file, file.resolved_type(file.inst(operand).result_type))) {
            LangOptions options;
            options.enable_consteval_engine = true;
            ConstEvalEngine engine(file, options);
            ConstEvalRequest request;
            request.mode = ConstEvalMode::c_ice();
            request.required = false;
            ConstEvalResult result = engine.evaluate_inst(operand, request);
            return result.status == ConstEvalStatus::Constant &&
                   result.value.has_value() &&
                   result.value->kind == ConstValueKind::Integer &&
                   result.value->int_value.is_zero();
        }
        inst = operand;
    }
    return false;
}

bool template_info_is_function_template(const Session::TemplateInfo& info) {
    return !info.is_class_template && !info.is_alias_template &&
           !info.is_variable_template && !info.is_concept;
}

cir::TypeRef pointer_pointee_ref(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    return is_cir_pointer_type(file, type) ? file.pointer_pointee_ref(type) : cir::TypeRef{};
}

bool is_void_ref(const cir::File& file, cir::TypeRef ref) {
    cir::TypeId type = file.resolved_type(ref.type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Builtin) {
        return false;
    }
    const auto* builtin =
        std::get_if<cir::BuiltinTypePayload>(&file.type_payload(type));
    return builtin && builtin->kind == cir::BuiltinTypeKind::Void;
}

bool pointee_is_void(const cir::File& file, cir::TypeId pointer_type) {
    cir::TypeId resolved = file.resolved_type(pointer_type);
    if (!is_cir_pointer_type(file, resolved)) {
        return false;
    }
    return is_void_ref(file, file.pointer_pointee_ref(resolved));
}

std::optional<cir::BuiltinTypeKind> builtin_kind(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Builtin) {
        return std::nullopt;
    }
    const auto* builtin =
        std::get_if<cir::BuiltinTypePayload>(&file.type_payload(type));
    if (!builtin) {
        return std::nullopt;
    }
    return builtin->kind;
}

bool is_char_family_ref(const cir::File& file, cir::TypeRef ref) {
    std::optional<cir::BuiltinTypeKind> kind = builtin_kind(file, ref.type);
    return kind == cir::BuiltinTypeKind::Char ||
           kind == cir::BuiltinTypeKind::SChar ||
           kind == cir::BuiltinTypeKind::UChar;
}

bool is_unknown_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    return file.valid(type) && file.type(type).kind == cir::TypeKind::Unknown;
}

ExprResult prepare_dependent_member_access(ExprResult base,
                                           std::string_view member_name_view,
                                           bool is_arrow,
                                           cir::File& file) {
    std::string member_name(member_name_view);
    DependentMemberAccessIdentity identity;
    identity.base = std::make_shared<ExprResult>(base);
    identity.member_name = member_name;
    identity.is_arrow = is_arrow;

    base.template_value_expr = template_value_member_access_expr(
        file, base, member_name, is_arrow);

    base.entity = {};
    base.candidates.clear();
    base.overload_designator.reset();
    base.has_explicit_template_arguments = false;
    base.explicit_template_arguments.clear();
    base.candidate_explicit_template_arguments.clear();
    base.dependent_value_qualifier = {};
    base.dependent_value_name = {};
    base.qualified_name = false;
    base.unresolved_unqualified_name = false;

    base.suppress_argument_dependent_lookup = true;
    base.name = std::move(member_name);
    base.type = file.dependent_type("dependent member access");
    base.category = ValueCategory::Dependent;
    base.dependent_member_access = std::move(identity);
    return base;
}

bool same_unqualified_type(const cir::File& file, cir::TypeId lhs, cir::TypeId rhs) {
    lhs = file.resolved_type(lhs);
    rhs = file.resolved_type(rhs);
    return file.valid(lhs) && file.valid(rhs) && lhs == rhs;
}

const cir::PointerTypePayload* pointer_payload(const cir::File& file,
                                               cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Pointer) {
        return nullptr;
    }
    return std::get_if<cir::PointerTypePayload>(&file.type_payload(type));
}

const cir::BlockPointerTypePayload* block_pointer_payload(
    const cir::File& file,
    cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) ||
        file.type(type).kind != cir::TypeKind::BlockPointer) {
        return nullptr;
    }
    return std::get_if<cir::BlockPointerTypePayload>(&file.type_payload(type));
}

const cir::MemberPointerTypePayload* member_pointer_payload(
    const cir::File& file,
    cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) ||
        file.type(type).kind != cir::TypeKind::MemberPointer) {
        return nullptr;
    }
    return std::get_if<cir::MemberPointerTypePayload>(&file.type_payload(type));
}

bool is_function_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    return file.valid(type) && file.type(type).kind == cir::TypeKind::Function;
}

bool is_record_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    return file.valid(type) && file.type(type).kind == cir::TypeKind::Record;
}

bool is_complete_record_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    const cir::RecordFacts* facts = file.record_facts_for_type(type);
    return facts && !facts->is_incomplete;
}

bool is_void_type_for_cast(const cir::File& file, cir::TypeId type) {
    std::optional<cir::BuiltinTypeKind> kind = builtin_kind(file, type);
    return kind == cir::BuiltinTypeKind::Void;
}

bool pointer_points_to_function(const cir::File& file, cir::TypeId type) {
    if (const auto* pointer = pointer_payload(file, type)) {
        return is_function_type(file, pointer->pointee.type);
    }
    if (const auto* pointer = block_pointer_payload(file, type)) {
        return is_function_type(file, pointer->pointee.type);
    }
    return false;
}

bool member_pointer_points_to_function(const cir::File& file, cir::TypeId type) {
    const auto* member = member_pointer_payload(file, type);
    return member && is_function_type(file, member->member_type.type);
}

bool similar_types_ignoring_cv(const cir::File& file,
                               cir::TypeRef lhs,
                               cir::TypeRef rhs) {
    lhs.type = file.resolved_type(lhs.type);
    rhs.type = file.resolved_type(rhs.type);
    if (!file.valid(lhs.type) || !file.valid(rhs.type)) {
        return false;
    }
    if (lhs.type == rhs.type) {
        return true;
    }
    const cir::TypeKind lhs_kind = file.type(lhs.type).kind;
    const cir::TypeKind rhs_kind = file.type(rhs.type).kind;
    if (lhs_kind != rhs_kind) {
        return false;
    }
    switch (lhs_kind) {
        case cir::TypeKind::Pointer:
            return similar_types_ignoring_cv(file,
                                             file.pointer_pointee_ref(lhs.type),
                                             file.pointer_pointee_ref(rhs.type));
        case cir::TypeKind::BlockPointer: {
            const auto* lhs_block =
                std::get_if<cir::BlockPointerTypePayload>(&file.type_payload(lhs.type));
            const auto* rhs_block =
                std::get_if<cir::BlockPointerTypePayload>(&file.type_payload(rhs.type));
            return lhs_block && rhs_block &&
                   similar_types_ignoring_cv(file,
                                             lhs_block->pointee,
                                             rhs_block->pointee);
        }
        case cir::TypeKind::MemberPointer: {
            const auto* lhs_member = member_pointer_payload(file, lhs.type);
            const auto* rhs_member = member_pointer_payload(file, rhs.type);
            return lhs_member && rhs_member &&
                   same_unqualified_type(file,
                                         lhs_member->class_type.type,
                                         rhs_member->class_type.type) &&
                   similar_types_ignoring_cv(file,
                                             lhs_member->member_type,
                                             rhs_member->member_type);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return similar_types_ignoring_cv(file,
                                             file.reference_referred_ref(lhs.type),
                                             file.reference_referred_ref(rhs.type));
        case cir::TypeKind::Array: {
            const auto* lhs_array =
                std::get_if<cir::ArrayTypePayload>(&file.type_payload(lhs.type));
            const auto* rhs_array =
                std::get_if<cir::ArrayTypePayload>(&file.type_payload(rhs.type));
            return lhs_array && rhs_array &&
                   lhs_array->size_kind == rhs_array->size_kind &&
                   lhs_array->size == rhs_array->size &&
                   similar_types_ignoring_cv(file,
                                             lhs_array->element_type,
                                             rhs_array->element_type);
        }
        default:
            return false;
    }
}

bool qualifiers_preserved_in_similar_type(const cir::File& file,
                                          cir::TypeRef source,
                                          cir::TypeRef target) {
    if ((source.qualifiers & static_cast<uint8_t>(~target.qualifiers)) != 0) {
        return false;
    }
    source.type = file.resolved_type(source.type);
    target.type = file.resolved_type(target.type);
    if (!file.valid(source.type) || !file.valid(target.type)) {
        return true;
    }
    if (source.type == target.type) {
        return true;
    }
    if (file.type(source.type).kind != file.type(target.type).kind) {
        return true;
    }
    switch (file.type(source.type).kind) {
        case cir::TypeKind::Pointer:
            return qualifiers_preserved_in_similar_type(
                file,
                file.pointer_pointee_ref(source.type),
                file.pointer_pointee_ref(target.type));
        case cir::TypeKind::BlockPointer: {
            const auto* source_block =
                std::get_if<cir::BlockPointerTypePayload>(&file.type_payload(source.type));
            const auto* target_block =
                std::get_if<cir::BlockPointerTypePayload>(&file.type_payload(target.type));
            return !source_block || !target_block ||
                   qualifiers_preserved_in_similar_type(file,
                                                        source_block->pointee,
                                                        target_block->pointee);
        }
        case cir::TypeKind::MemberPointer: {
            const auto* source_member = member_pointer_payload(file, source.type);
            const auto* target_member = member_pointer_payload(file, target.type);
            return !source_member || !target_member ||
                   qualifiers_preserved_in_similar_type(file,
                                                        source_member->member_type,
                                                        target_member->member_type);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return qualifiers_preserved_in_similar_type(
                file,
                file.reference_referred_ref(source.type),
                file.reference_referred_ref(target.type));
        case cir::TypeKind::Array: {
            const auto* source_array =
                std::get_if<cir::ArrayTypePayload>(&file.type_payload(source.type));
            const auto* target_array =
                std::get_if<cir::ArrayTypePayload>(&file.type_payload(target.type));
            return !source_array || !target_array ||
                   qualifiers_preserved_in_similar_type(file,
                                                        source_array->element_type,
                                                        target_array->element_type);
        }
        default:
            return true;
    }
}

const char* named_cast_payload_kind(CppNamedCastKind kind) {
    switch (kind) {
        case CppNamedCastKind::Static: return "static_cast";
        case CppNamedCastKind::Const: return "const_cast";
        case CppNamedCastKind::Reinterpret: return "reinterpret_cast";
        case CppNamedCastKind::Dynamic: return "dynamic_cast";
    }
    return "named_cast";
}

enum class PointerPointeeMode : uint8_t {
    Compatible,
    Composite,
};

std::optional<cir::TypeRef> common_pointer_pointee(const Session& session,
                                                   const cir::File& file,
                                                   cir::TypeId lhs,
                                                   cir::TypeId rhs,
                                                   PointerPointeeMode mode) {
    cir::TypeRef lhs_ref = pointer_pointee_ref(file, lhs);
    cir::TypeRef rhs_ref = pointer_pointee_ref(file, rhs);
    if (!lhs_ref.valid() || !rhs_ref.valid()) {
        return std::nullopt;
    }

    if (same_unqualified_type(file, lhs_ref.type, rhs_ref.type)) {
        lhs_ref.qualifiers = static_cast<uint8_t>(lhs_ref.qualifiers | rhs_ref.qualifiers);
        return lhs_ref;
    }
    if (is_void_ref(file, lhs_ref)) {
        lhs_ref.qualifiers = static_cast<uint8_t>(lhs_ref.qualifiers | rhs_ref.qualifiers);
        return lhs_ref;
    }
    if (is_void_ref(file, rhs_ref)) {
        rhs_ref.qualifiers = static_cast<uint8_t>(rhs_ref.qualifiers | lhs_ref.qualifiers);
        return rhs_ref;
    }
    if (is_char_family_ref(file, lhs_ref) && is_char_family_ref(file, rhs_ref)) {
        lhs_ref.qualifiers = static_cast<uint8_t>(lhs_ref.qualifiers | rhs_ref.qualifiers);
        return lhs_ref;
    }
    cir::TypeId lhs_type = file.resolved_type(lhs_ref.type);
    cir::TypeId rhs_type = file.resolved_type(rhs_ref.type);
    if (mode == PointerPointeeMode::Composite &&
        is_record_type(file, lhs_type) &&
        is_record_type(file, rhs_type)) {
        Session::DerivedToBasePathResult lhs_to_rhs =
            session.analyze_derived_to_base_path(lhs_type, rhs_type);
        if (lhs_to_rhs.kind != Session::DerivedToBasePathKind::NotFound) {
            rhs_ref.qualifiers = static_cast<uint8_t>(
                lhs_ref.qualifiers | rhs_ref.qualifiers);
            return rhs_ref;
        }
        Session::DerivedToBasePathResult rhs_to_lhs =
            session.analyze_derived_to_base_path(rhs_type, lhs_type);
        if (rhs_to_lhs.kind != Session::DerivedToBasePathKind::NotFound) {
            lhs_ref.qualifiers = static_cast<uint8_t>(
                lhs_ref.qualifiers | rhs_ref.qualifiers);
            return lhs_ref;
        }
    }
    return std::nullopt;
}

bool is_comparison_operator(syntax::BinaryOperator op) {
    switch (op) {
        case syntax::BinaryOperator::Less:
        case syntax::BinaryOperator::LessEqual:
        case syntax::BinaryOperator::Greater:
        case syntax::BinaryOperator::GreaterEqual:
        case syntax::BinaryOperator::Equal:
        case syntax::BinaryOperator::NotEqual:
        case syntax::BinaryOperator::ThreeWay:
            return true;
        default:
            return false;
    }
}

syntax::BinaryOperator compound_base_operator(syntax::BinaryOperator op) {
    switch (op) {
        case syntax::BinaryOperator::AssignAdd: return syntax::BinaryOperator::Add;
        case syntax::BinaryOperator::AssignSub: return syntax::BinaryOperator::Sub;
        case syntax::BinaryOperator::AssignMul: return syntax::BinaryOperator::Mul;
        case syntax::BinaryOperator::AssignDiv: return syntax::BinaryOperator::Div;
        case syntax::BinaryOperator::AssignMod: return syntax::BinaryOperator::Mod;
        case syntax::BinaryOperator::AssignShl: return syntax::BinaryOperator::Shl;
        case syntax::BinaryOperator::AssignShr: return syntax::BinaryOperator::Shr;
        case syntax::BinaryOperator::AssignAnd: return syntax::BinaryOperator::BitAnd;
        case syntax::BinaryOperator::AssignXor: return syntax::BinaryOperator::BitXor;
        case syntax::BinaryOperator::AssignOr: return syntax::BinaryOperator::BitOr;
        default: return syntax::BinaryOperator::Invalid;
    }
}

bool is_postfix_increment_or_decrement(syntax::UnaryOperator op) {
    return op == syntax::UnaryOperator::PostfixIncrement ||
           op == syntax::UnaryOperator::PostfixDecrement;
}

bool is_vector_integer_operator(syntax::BinaryOperator op) {
    switch (op) {
        case syntax::BinaryOperator::Mod:
        case syntax::BinaryOperator::BitAnd:
        case syntax::BinaryOperator::BitOr:
        case syntax::BinaryOperator::BitXor:
        case syntax::BinaryOperator::Shl:
        case syntax::BinaryOperator::Shr:
            return true;
        default:
            return false;
    }
}

bool is_vector_numeric_operator(syntax::BinaryOperator op) {
    switch (op) {
        case syntax::BinaryOperator::Add:
        case syntax::BinaryOperator::Sub:
        case syntax::BinaryOperator::Mul:
        case syntax::BinaryOperator::Div:
            return true;
        default:
            return false;
    }
}

cir::TypeId function_return_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Function) {
        return {};
    }
    const auto* function = std::get_if<cir::FunctionTypePayload>(&file.type_payload(type));
    return function ? function->return_type.type : cir::TypeId{};
}

bool has_reserved_builtin_prefix(std::string_view name) {
    return name.rfind("__builtin_", 0) == 0;
}

bool is_builtin_call_syntax(const BuiltinInfo& info) {
    return info.supported && info.syntax == BuiltinSyntaxKind::Call;
}

} // namespace

bool Session::is_null_pointer_constant(const ExprResult& expr) const {
    if (is_nullptr_type(expr.type)) {
        return true;
    }

    if (lang_opts_.is_cxx_mode()) {
        return is_integer_zero_literal(file_, expr);
    }
    return is_null_pointer_constant_expr(file_, expr);
}

cir::TemplateValueExpression Session::template_value_operand_expression(
    const ExprResult& operand) {
    if (!operand.template_value_expr.valid() &&
        !expr_is_value_dependent(operand)) {
        cir::IntegerValue value;
        if (try_evaluate_integer_constant_value(operand, value)) {
            cir::TemplateValueExpression expression =
                template_value_integer_expr(file_, value,
                                            type_ref(operand.type));
            expression.definition_context = current_decl_context();
            expression.definition_lookup_generation = lookup_generation_;
            return expression;
        }
    }
    return template_value_operand_expr(file_, operand);
}

ExprResult Session::make_dependent_binary_operator_expr(
    syntax::BinaryOperator op,
    ExprResult lhs,
    ExprResult rhs,
    SrcLoc loc) {
    cir::TemplateValueExpression lhs_expression =
        template_value_operand_expression(lhs);
    cir::TemplateValueExpression rhs_expression =
        template_value_operand_expression(rhs);

    ExprResult combined;
    combined.fragment =
        chain(std::move(lhs.fragment), std::move(rhs.fragment), loc);
    combined.type = file_.dependent_type("dependent-binary-operator");
    cir::TypeId lhs_type = file_.resolved_type(lhs.type);
    cir::TypeId rhs_type = file_.resolved_type(rhs.type);
    bool builtin_operands = file_.valid(lhs_type) &&
        file_.valid(rhs_type) && !is_dependent_type(lhs_type) &&
        !is_dependent_type(rhs_type) && is_scalar_type(lhs_type) &&
        is_scalar_type(rhs_type);
    if (builtin_operands) {
        switch (op) {
            case syntax::BinaryOperator::Less:
            case syntax::BinaryOperator::LessEqual:
            case syntax::BinaryOperator::Greater:
            case syntax::BinaryOperator::GreaterEqual:
            case syntax::BinaryOperator::Equal:
            case syntax::BinaryOperator::NotEqual:
            case syntax::BinaryOperator::LogicalAnd:
            case syntax::BinaryOperator::LogicalOr:
                combined.type = file_.builtin_type(
                    cir::BuiltinTypeKind::Bool);
                break;
            case syntax::BinaryOperator::Comma:
                combined.type = rhs_type;
                break;
            case syntax::BinaryOperator::Shl:
            case syntax::BinaryOperator::Shr: {
                cir::TypeId promoted = integer_promotion_type(lhs_type);
                if (promoted.valid()) {
                    combined.type = promoted;
                }
                break;
            }
            case syntax::BinaryOperator::Add:
            case syntax::BinaryOperator::Sub:
            case syntax::BinaryOperator::Mul:
            case syntax::BinaryOperator::Div:
            case syntax::BinaryOperator::Mod:
            case syntax::BinaryOperator::BitAnd:
            case syntax::BinaryOperator::BitOr:
            case syntax::BinaryOperator::BitXor: {
                cir::TypeId common = usual_arithmetic_conversion_type(
                    lhs_type, rhs_type);
                if (common.valid()) {
                    combined.type = common;
                }
                break;
            }
            default:
                break;
        }
    }
    combined.category = ValueCategory::Dependent;
    combined.references_template_value_parameter =
        lhs.references_template_value_parameter ||
        rhs.references_template_value_parameter;
    combined.value_dependent = true;
    combined.has_error = lhs.has_error || rhs.has_error;
    if (std::optional<cir::TemplateValueExprOp> graph_op =
            template_value_expr_op(op)) {
        combined.template_value_expr = template_value_binary_expr(
            *graph_op,
            lhs_expression,
            rhs_expression,
            type_ref(combined.type),
            ValueCategory::Dependent);
        combined.template_value_expr.loc = loc;
        combined.template_value_expr.definition_context =
            current_decl_context();
        combined.template_value_expr.definition_lookup_generation =
            lookup_generation_;
    }
    return make_dependent_expr(std::move(combined), loc);
}

ExprResult Session::make_dependent_fold_expression(
    cir::TemplateValueFoldKind fold_kind,
    syntax::BinaryOperator op,
    ExprResult pattern,
    std::optional<ExprResult> initializer,
    std::vector<cir::TemplateValuePackReference> pack_references,
    SrcLoc loc) {
    std::optional<cir::TemplateValueExprOp> graph_op =
        template_value_expr_op(op);
    cir::TemplateValueExpression pattern_expression =
        template_value_operand_expression(pattern);
    cir::TemplateValueExpression init_expression;
    if (initializer.has_value()) {
        init_expression = template_value_operand_expression(*initializer);
    }

    ExprResult result;
    result.fragment = std::move(pattern.fragment);
    result.references_template_value_parameter =
        pattern.references_template_value_parameter;
    result.has_error = pattern.has_error;
    if (initializer.has_value()) {
        result.fragment = chain(std::move(result.fragment),
                                std::move(initializer->fragment), loc);
        result.references_template_value_parameter =
            result.references_template_value_parameter ||
            initializer->references_template_value_parameter;
        result.has_error = result.has_error || initializer->has_error;
    }
    result.value_dependent = true;

    if (graph_op.has_value() && pattern_expression.valid() &&
        (!initializer.has_value() || init_expression.valid()) &&
        !pack_references.empty()) {
        append_template_value_expr_nodes(result.template_value_expr,
                                         pattern_expression, 0);
        uint32_t initializer_offset = static_cast<uint32_t>(
            result.template_value_expr.nodes.size());
        if (initializer.has_value()) {
            append_template_value_expr_nodes(result.template_value_expr,
                                             init_expression,
                                             initializer_offset);
        }
        cir::TemplateValueExprNode fold;
        fold.kind = cir::TemplateValueExprKind::Fold;
        fold.op = *graph_op;
        fold.fold_kind = fold_kind;
        fold.lhs = pattern_expression.root;
        fold.rhs = initializer.has_value()
            ? init_expression.root + initializer_offset
            : cir::TemplateValueExprNoNode;
        fold.result_type = type_ref(file_.dependent_type("fold expression"));
        fold.pack_references = std::move(pack_references);
        result.template_value_expr.nodes.push_back(std::move(fold));
        result.template_value_expr.root = static_cast<uint32_t>(
            result.template_value_expr.nodes.size() - 1);
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context = current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
    }
    return make_dependent_expr(std::move(result), loc);
}

ExprResult Session::make_integer_literal(int64_t value,
                                         std::string spelling,
                                         cir::TypeId type,
                                         SrcLoc loc) {
    cir::TypeId result_type = type.valid() ? type : builder_.int_type();
    cir::IntegerTypeShape shape =
        cir::integer_shape_for_type(file_, result_type);
    cir::IntegerValue exact = cir::IntegerValue::from_signed(value, 64).cast(
        shape.bit_width, shape.is_unsigned);
    return make_integer_literal(exact, std::move(spelling), result_type, loc);
}

ExprResult Session::make_integer_literal(cir::IntegerValue value,
                                         std::string spelling,
                                         cir::TypeId type,
                                         SrcLoc loc) {
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.int");
    cir::InstId inst = builder_.integer_literal(value,
                                                type.valid() ? type : builder_.int_type(),
                                                std::move(spelling),
                                                loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    result.template_value_expr =
        template_value_integer_expr(file_, value, type_ref(result.type));
    result.template_value_expr.loc = loc;
    result.template_value_expr.definition_context = current_decl_context();
    result.template_value_expr.definition_lookup_generation =
        lookup_generation_;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::make_integer_literal(int64_t value,
                                         std::string spelling,
                                         TokenType token_type,
                                         SrcLoc loc) {
    uint64_t unsigned_value = static_cast<uint64_t>(value);
    if (auto parsed = parse_integer_literal_info(spelling)) {
        unsigned_value = parsed->value;
    }
    cir::TypeId type = integer_literal_type(token_type, spelling, unsigned_value);
    return make_integer_literal(value,
                                std::move(spelling),
                                type,
                                loc);
}

ExprResult Session::make_integer_literal(int64_t value, std::string spelling, SrcLoc loc) {
    return make_integer_literal(value, std::move(spelling), builder_.int_type(), loc);
}

ExprResult Session::make_nullptr_literal(SrcLoc loc) {
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.nullptr");
    cir::InstId inst = builder_.nullptr_literal("nullptr", loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.builtin_type(cir::BuiltinTypeKind::NullPtr);
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::make_void_prvalue() {
    ExprResult result;
    result.type = builder_.void_type();
    result.category = ValueCategory::PrValue;
    return result;
}

cir::TypeId Session::complex_element_type(cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Complex) {
        return {};
    }
    const auto* payload =
        std::get_if<cir::ComplexTypePayload>(&file_.type_payload(resolved));
    return payload ? payload->element_type.type : cir::TypeId{};
}

ExprResult Session::make_imaginary_literal(syntax::FloatingLiteralKind kind,
                                           std::string spelling,
                                           SrcLoc loc) {
    cir::TypeId element = floating_literal_type(kind);
    cir::TypeId complex = complex_type(file_.type_ref(element));
    cir::FloatingSemantics semantics = floating::semantics_for_type(file_, element);
    floating::FloatParseResult parsed = floating::parse(spelling, semantics);
    if (!parsed || parsed.status.has(floating::FloatStatusFlag::Overflow)) {
        report_error("invalid or out-of-range imaginary literal", loc);
        parsed.value = floating::zero(semantics);
        parsed.error = numeric::ParseError::None;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.imaginary");
    cir::InstId zero = builder_.floating_literal(
        floating::zero(semantics), element, "0.0", loc);
    cir::InstId imag = builder_.floating_literal(
        parsed.value, element, std::move(spelling), loc);
    cir::InstId inst = builder_.complex_make(complex, zero, imag, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = complex;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::collect_complex_part_expr(ExprResult operand,
                                              bool imaginary,
                                              SrcLoc loc) {

    if (operand.category == ValueCategory::LValue && operand.place.valid() &&
        complex_element_type(object_type_from_place(operand.place)).valid()) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.complex.place");
        cir::InstId place = imaginary
            ? builder_.complex_imag_place(operand.place, loc)
            : builder_.complex_real_place(operand.place, loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        operand.fragment = chain(std::move(operand.fragment), std::move(fragment), loc);
        operand.place = place;
        operand.type = file_.place_object_type(file_.inst(place).result_type);
        operand.entity = {};
        return operand;
    }

    ExprResult value = require_value(std::move(operand), UseContext::RValue, loc);
    cir::TypeId element = complex_element_type(value.type);
    if (!element.valid()) {

        if (!imaginary) {
            return value;
        }
        cir::TypeId zero_type =
            is_floating_type(value.type) ? value.type : builder_.double_type();
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.imag.zero");
        cir::InstId zero = builder_.floating_literal(
            floating::zero(floating::semantics_for_type(file_, zero_type)),
            zero_type,
            "0.0",
            loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        ExprResult result;
        result.fragment = chain(std::move(value.fragment), std::move(fragment), loc);
        result.value = zero;
        result.type = zero_type;
        result.category = ValueCategory::PrValue;
        result.has_error = value.has_error;
        return result;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.complex.part");
    cir::InstId part = imaginary ? builder_.complex_imag(value.value, loc)
                                 : builder_.complex_real(value.value, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);
    ExprResult result;
    result.fragment = chain(std::move(value.fragment), std::move(fragment), loc);
    result.value = part;
    result.type = element;
    result.category = ValueCategory::PrValue;
    result.has_error = value.has_error;
    return result;
}

ExprResult Session::make_boolean_literal(bool value, std::string spelling, SrcLoc loc) {
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.bool");
    cir::InstId inst = builder_.boolean_literal(value, std::move(spelling), loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    cir::IntegerTypeShape shape =
        cir::integer_shape_for_type(file_, result.type);
    result.template_value_expr = template_value_integer_expr(
        file_,
        cir::IntegerValue::from_unsigned(value ? 1 : 0, shape.bit_width),
        type_ref(result.type));
    result.template_value_expr.loc = loc;
    result.template_value_expr.definition_context = current_decl_context();
    result.template_value_expr.definition_lookup_generation =
        lookup_generation_;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::make_dependent_boolean_expr(SrcLoc loc) {
    bump_pattern_taint();
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.dependent.bool");
    cir::InstId inst =
        builder_.name_ref("<dependent-bool>", builder_.bool_type(), loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = builder_.bool_type();
    result.category = ValueCategory::PrValue;
    result.references_template_value_parameter = true;
    return result;
}

ExprResult Session::make_floating_literal(syntax::FloatingLiteralKind kind,
                                          std::string spelling,
                                          SrcLoc loc) {
    cir::TypeId type = floating_literal_type(kind);
    cir::FloatingSemantics semantics = floating::semantics_for_type(file_, type);
    floating::FloatParseResult parsed = floating::parse(spelling, semantics);
    if (!parsed || parsed.status.has(floating::FloatStatusFlag::Overflow)) {
        report_error("invalid or out-of-range floating literal", loc);
        parsed.value = floating::zero(semantics);
        parsed.error = numeric::ParseError::None;
    }
    return make_floating_value(parsed.value, type, std::move(spelling), loc);
}

ExprResult Session::make_floating_value(cir::FloatingValue value,
                                        cir::TypeId type,
                                        std::string spelling,
                                        SrcLoc loc) {
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.float");
    cir::InstId inst = builder_.floating_literal(
        value, type, std::move(spelling), loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::make_character_literal(std::string decoded,
                                           LiteralPrefix prefix,
                                           std::string spelling,
                                           SrcLoc loc) {

    if (!lang_opts_.is_cxx_mode() && prefix == LiteralPrefix::None &&
        decoded.size() == 1 && !file_.target_info().char_is_unsigned &&
        (static_cast<unsigned char>(decoded[0]) & 0x80u) != 0) {
        uint32_t value = static_cast<uint32_t>(
            static_cast<int32_t>(static_cast<signed char>(decoded[0])));
        decoded.assign({static_cast<char>((value >> 24) & 0xff),
                        static_cast<char>((value >> 16) & 0xff),
                        static_cast<char>((value >> 8) & 0xff),
                        static_cast<char>(value & 0xff)});
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.char");
    cir::InstId inst = builder_.character_literal(
        character_literal_type(prefix), std::move(decoded), std::move(spelling), loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::make_string_literal(std::string value, std::string spelling, SrcLoc loc,
                                        LiteralPrefix prefix) {

    cir::TypeRef element_type;
    size_t char_width = 1;
    switch (prefix) {
        case LiteralPrefix::L:
            element_type.type = file_.builtin_type(cir::BuiltinTypeKind::WChar);
            char_width = std::max<size_t>(1, file_.target_info().wchar_width / 8);
            break;
        case LiteralPrefix::u:
            element_type.type = file_.builtin_type(cir::BuiltinTypeKind::Char16);
            char_width = 2;
            break;
        case LiteralPrefix::U:
            element_type.type = file_.builtin_type(cir::BuiltinTypeKind::Char32);
            char_width = 4;
            break;
        case LiteralPrefix::U8:
            element_type.type = lang_opts_.is_cxx20_or_later()
                ? file_.builtin_type(cir::BuiltinTypeKind::Char8)
                : cir::TypeId{};
            char_width = 1;
            break;
        case LiteralPrefix::None:
        default:
            element_type = {};
            char_width = 1;
            break;
    }
    if (lang_opts_.is_cxx_mode()) {
        element_type.qualifiers |= cir::QualConst;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.string");
    cir::InstId inst = builder_.string_literal(std::move(value), std::move(spelling),
                                               loc, element_type, char_width);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.place = inst;
    cir::TypeId place_type = file_.inst(inst).result_type;
    result.type = file_.resolved_type(file_.place_object_ref(place_type).type);
    result.category = ValueCategory::LValue;
    return result;
}

ExprResult Session::collect_user_defined_literal(
    ExprResult literal,
    UserDefinedLiteralKind kind,
    std::string suffix,
    std::string base_spelling,
    SrcLoc loc) {
    UserDefinedLiteralInfo info;
    info.kind = kind;
    info.suffix = file_.intern_name(suffix);
    info.base_spelling = std::move(base_spelling);
    info.loc = loc;

    const std::string operator_name = "operator\"\"" + suffix;
    ExprResult callee = lookup_name(operator_name, loc,
                                    /*allow_unresolved=*/true);
    std::vector<cir::EntityId> declarations = callee.candidates;
    if (declarations.empty() && callee.entity.valid()) {
        declarations.push_back(callee.entity);
    }
    declarations.erase(
        std::remove_if(
            declarations.begin(),
            declarations.end(),
            [&](cir::EntityId declaration) {
                if (!declaration.valid() || !file_.valid(declaration)) {
                    return true;
                }
                const cir::OperatorFunctionIdentity& identity =
                    file_.entity(declaration).operator_function;
                return identity.kind !=
                           cir::OperatorFunctionKind::Literal ||
                    identity.literal_suffix != info.suffix;
            }),
        declarations.end());

    auto fail = [&](std::string message) {
        report_error(std::move(message), loc);
        literal.user_defined_literal = info;
        literal.has_error = true;
        return std::move(literal);
    };
    if (declarations.empty()) {
        return fail("no literal operator found for suffix '" + suffix + "'");
    }

    auto without_top_level_cv = [](cir::TypeRef type) {
        type.qualifiers = static_cast<uint8_t>(
            type.qualifiers &
            ~(cir::QualConst | cir::QualVolatile));
        return type;
    };
    auto function_parameters =
        [&](cir::EntityId declaration)
            -> const std::vector<cir::TypeRef>* {
            if (template_info(declaration)) {
                return nullptr;
            }
            cir::TypeId type =
                file_.resolved_type(file_.entity(declaration).type);
            if (!file_.valid(type) ||
                file_.type(type).kind != cir::TypeKind::Function) {
                return nullptr;
            }
            const auto* function =
                std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(type));
            return function ? &function->parameters : nullptr;
        };
    auto matches_builtin = [&](cir::TypeRef type,
                               cir::BuiltinTypeKind kind) {
        return same_type_identity(
            without_top_level_cv(type),
            file_.type_ref(file_.builtin_type(kind)));
    };
    auto matches_const_char_pointer = [&](cir::TypeRef type) {
        cir::TypeId pointer_type = file_.resolved_type(type.type);
        if (!file_.valid(pointer_type) ||
            file_.type(pointer_type).kind != cir::TypeKind::Pointer) {
            return false;
        }
        cir::TypeRef expected =
            file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::Char));
        expected.qualifiers = cir::QualConst;
        return same_type_identity(file_.pointer_pointee_ref(pointer_type),
                                  expected);
    };
    auto dispatch_call =
        [&](std::vector<cir::EntityId> selected,
            std::vector<ExprResult> arguments) {
            callee.entity = selected.back();
            callee.type = file_.entity(callee.entity).type;
            callee.category = ValueCategory::FunctionDesignator;
            callee.candidates =
                selected.size() > 1
                    ? std::move(selected)
                    : std::vector<cir::EntityId>{};
            callee.has_error = false;
            callee.unresolved_unqualified_name = false;

            callee.suppress_argument_dependent_lookup = true;
            ExprResult result = collect_call_expr(
                std::move(callee), std::move(arguments), loc);
            result.user_defined_literal = std::move(info);
            return result;
        };

    std::vector<cir::EntityId> cooked;
    bool numeric_fallback = false;
    switch (kind) {
        case UserDefinedLiteralKind::Integer:
            for (cir::EntityId declaration : declarations) {
                const std::vector<cir::TypeRef>* parameters =
                    function_parameters(declaration);
                if (parameters && parameters->size() == 1 &&
                    matches_builtin((*parameters)[0],
                                    cir::BuiltinTypeKind::ULongLong)) {
                    cooked.push_back(declaration);
                }
            }
            if (cooked.empty()) {
                numeric_fallback = true;
            }
            break;
        case UserDefinedLiteralKind::Floating:
            for (cir::EntityId declaration : declarations) {
                const std::vector<cir::TypeRef>* parameters =
                    function_parameters(declaration);
                if (parameters && parameters->size() == 1 &&
                    matches_builtin((*parameters)[0],
                                    cir::BuiltinTypeKind::LongDouble)) {
                    cooked.push_back(declaration);
                }
            }
            if (cooked.empty()) {
                numeric_fallback = true;
            }
            break;
        case UserDefinedLiteralKind::Character:
            for (cir::EntityId declaration : declarations) {
                const std::vector<cir::TypeRef>* parameters =
                    function_parameters(declaration);
                if (parameters && parameters->size() == 1 &&
                    same_type_identity(
                        without_top_level_cv((*parameters)[0]),
                        file_.type_ref(literal.type))) {
                    cooked.push_back(declaration);
                }
            }
            if (cooked.empty()) {
                return fail("no applicable character literal operator for "
                            "suffix '" +
                            suffix + "'");
            }
            break;
        case UserDefinedLiteralKind::String: {
            std::vector<cir::EntityId> string_template_specializations;
            for (cir::EntityId declaration : declarations) {
                const TemplateInfo* candidate = template_info(declaration);
                if (!candidate || candidate->parameters.size() != 1) {
                    continue;
                }
                const TemplateParameter& parameter =
                    candidate->parameters.front();
                cir::TypeId parameter_type =
                    file_.resolved_type(parameter.non_type_type);
                bool is_class_template_placeholder =
                    class_template_placeholder_info(
                        parameter.non_type_type) != nullptr;
                if (parameter.kind == TemplateParameterKind::NonType &&
                    !parameter.is_parameter_pack &&
                    (is_class_template_placeholder ||
                     (file_.valid(parameter_type) &&
                      file_.type(parameter_type).kind ==
                          cir::TypeKind::Record))) {

                    SpeculativeParseGuard transaction = speculative_parse();
                    TemplateArgument argument;
                    std::string error;
                    if (!form_class_template_value_argument(
                            parameter.non_type_type,
                            literal,
                            argument,
                            loc,
                            "string literal is not a constant template argument",
                            &error,
                            /*diagnose_deduction=*/false)) {
                        continue;
                    }
                    TemplateArgumentBindings bindings;
                    if (!bind_template_arguments_to_parameters(
                            candidate->parameters,
                            {argument},
                            bindings)) {
                        continue;
                    }
                    canonicalize_template_argument_bindings(bindings);
                    cir::EntityId specialization =
                        form_function_template_specialization_candidate(
                            *candidate, bindings, loc);
                    if (!specialization.valid()) {
                        continue;
                    }
                    transaction.commit();
                    if (std::find(
                            string_template_specializations.begin(),
                            string_template_specializations.end(),
                            specialization) ==
                        string_template_specializations.end()) {
                        string_template_specializations.push_back(
                            specialization);
                    }
                }
            }
            if (!string_template_specializations.empty()) {
                return dispatch_call(
                    std::move(string_template_specializations), {});
            }

            cir::TypeId array_type = file_.resolved_type(literal.type);
            cir::TypeRef element_type =
                file_.valid(array_type) &&
                        file_.type(array_type).kind ==
                            cir::TypeKind::Array
                    ? file_.array_element_ref(array_type)
                    : cir::TypeRef{};
            for (cir::EntityId declaration : declarations) {
                const std::vector<cir::TypeRef>* parameters =
                    function_parameters(declaration);
                if (!parameters || parameters->size() != 2) {
                    continue;
                }
                cir::TypeId pointer_type =
                    file_.resolved_type((*parameters)[0].type);
                cir::TypeRef pointee =
                    file_.valid(pointer_type) &&
                            file_.type(pointer_type).kind ==
                                cir::TypeKind::Pointer
                        ? file_.pointer_pointee_ref(pointer_type)
                        : cir::TypeRef{};
                if (pointee.valid() && element_type.valid() &&
                    same_type_identity(pointee, element_type)) {
                    cooked.push_back(declaration);
                }
            }
            if (cooked.empty()) {
                return fail("no applicable string literal operator for "
                            "suffix '" +
                            suffix + "'");
            }
            break;
        }
    }

    if (numeric_fallback) {
        std::vector<cir::EntityId> raw;
        std::vector<const TemplateInfo*> templates;
        for (cir::EntityId declaration : declarations) {
            if (const std::vector<cir::TypeRef>* parameters =
                    function_parameters(declaration);
                parameters && parameters->size() == 1 &&
                matches_const_char_pointer((*parameters)[0])) {
                raw.push_back(declaration);
                continue;
            }
            const TemplateInfo* candidate = template_info(declaration);
            if (!candidate || candidate->parameters.size() != 1) {
                continue;
            }
            const TemplateParameter& parameter =
                candidate->parameters.front();
            if (parameter.kind == TemplateParameterKind::NonType &&
                parameter.is_parameter_pack &&
                matches_builtin(type_ref(parameter.non_type_type),
                                cir::BuiltinTypeKind::Char)) {
                templates.push_back(candidate);
            }
        }
        if (!raw.empty() && !templates.empty()) {
            return fail("literal suffix '" + suffix +
                        "' has both a raw literal operator and a numeric "
                        "literal operator template");
        }
        if (!raw.empty()) {
            std::string spelling = "\"" + info.base_spelling + "\"";
            std::vector<ExprResult> arguments;
            arguments.push_back(make_string_literal(
                info.base_spelling, std::move(spelling), loc));
            return dispatch_call(std::move(raw), std::move(arguments));
        }
        if (templates.empty()) {
            return fail("no applicable numeric literal operator for suffix '" +
                        suffix + "'");
        }

        cir::TypeId char_type =
            file_.builtin_type(cir::BuiltinTypeKind::Char);
        std::vector<TemplateArgument> arguments;
        arguments.reserve(info.base_spelling.size());
        for (unsigned char source_character : info.base_spelling) {
            TemplateValueConstant constant;
            constant.kind = cir::TemplateValueKind::Integer;
            constant.integer_value = cir::IntegerValue::from_unsigned(
                source_character, 8);
            TemplateArgument argument;
            std::string error;
            if (!build_template_value_argument(
                    char_type, constant, argument, &error)) {
                return fail(
                    error.empty()
                        ? "numeric literal template argument is not "
                          "representable as char"
                        : std::move(error));
            }
            argument.value_spelling =
                std::to_string(source_character);
            arguments.push_back(std::move(argument));
        }

        std::vector<cir::EntityId> specializations;
        for (const TemplateInfo* candidate : templates) {
            TemplateArgumentBindings bindings;
            if (!bind_template_arguments_to_parameters(
                    candidate->parameters, arguments, bindings)) {
                continue;
            }
            canonicalize_template_argument_bindings(bindings);
            cir::EntityId specialization =
                form_function_template_specialization_candidate(
                    *candidate, bindings, loc);
            if (specialization.valid() &&
                std::find(specializations.begin(),
                          specializations.end(),
                          specialization) == specializations.end()) {
                specializations.push_back(specialization);
            }
        }
        if (specializations.empty()) {
            return fail("no applicable numeric literal operator for suffix '" +
                        suffix + "'");
        }
        return dispatch_call(std::move(specializations), {});
    }

    std::vector<ExprResult> arguments;
    switch (kind) {
        case UserDefinedLiteralKind::Integer: {
            uint64_t value = 0;
            if (auto parsed =
                    parse_integer_literal_info(info.base_spelling)) {
                value = parsed->value;
            }
            arguments.push_back(make_integer_literal(
                static_cast<int64_t>(value),
                info.base_spelling + "ULL",
                file_.builtin_type(cir::BuiltinTypeKind::ULongLong),
                loc));
            break;
        }
        case UserDefinedLiteralKind::Floating:
            arguments.push_back(make_floating_literal(
                syntax::FloatingLiteralKind::LongDouble,
                info.base_spelling + "L",
                loc));
            break;
        case UserDefinedLiteralKind::Character:
            arguments.push_back(std::move(literal));
            break;
        case UserDefinedLiteralKind::String: {
            size_t length = 0;
            cir::TypeId array_type = file_.resolved_type(literal.type);
            if (file_.valid(array_type)) {
                const auto* array =
                    std::get_if<cir::ArrayTypePayload>(
                        &file_.type_payload(array_type));
                if (array && array->size.has_value() &&
                    *array->size != 0) {
                    length = *array->size - 1;
                }
            }
            arguments.push_back(std::move(literal));
            arguments.push_back(make_integer_literal(
                static_cast<int64_t>(length),
                std::to_string(length),
                builder_.usize_type(),
                loc));
            break;
        }
    }
    return dispatch_call(std::move(cooked), std::move(arguments));
}

ExprResult Session::lookup_name(std::string_view name,
                                SrcLoc loc,
                                bool allow_unresolved) {
    std::string key(name);
    if (in_pack_pattern_capture() &&
        template_value_pack_param_index_for_name(name).has_value() &&
        capture_parameter_pack(ParameterPackKind::Value, name)) {
        ExprResult result;
        result.name = std::move(key);
        result.type =
            file_.dependent_type("template value parameter pack expansion");
        result.category = ValueCategory::Dependent;

        uint32_t parameter_index =
            *template_value_pack_param_index_for_name(name);
        cir::TemplateValueExprNode node;
        node.kind = cir::TemplateValueExprKind::Parameter;
        node.parameter_index = parameter_index;
        node.name = file_.intern_name(name);
        if (const cir::Binding* binding = lookup_ordinary_binding(name)) {
            for (cir::EntityId entity : binding->entities) {
                if (template_value_param_is_pack(entity)) {
                    node.entity = entity;
                    node.result_type =
                        file_.type_ref(file_.entity(entity).type);
                    break;
                }
            }
        }
        cir::TemplateValuePackReference reference;
        reference.kind = cir::TemplateValuePackKind::Value;
        reference.index = parameter_index;
        reference.declaration = node.entity;
        reference.name = node.name;
        node.pack_references.push_back(std::move(reference));
        cir::TemplateValueExpression recipe;
        recipe.nodes.push_back(std::move(node));
        recipe.root = 0;
        result.template_value_expr = std::move(recipe);
        return result;
    }
    if (in_pack_pattern_capture() && function_parameter_pack_name(name) &&
        capture_parameter_pack(ParameterPackKind::Function, name)) {
        ExprResult result;
        result.name = std::move(key);
        result.type =
            file_.dependent_type("function parameter pack expansion");
        result.category = ValueCategory::Dependent;
        return result;
    }
    if (const ParameterPackElement* replay = parameter_pack_replay_element(
            ParameterPackKind::Value, name)) {
        const TemplateArgument* argument =
            std::get_if<TemplateArgument>(replay);
        if (!argument) {
            return lookup_name_fallback(name, loc, allow_unresolved);
        }
        return value_parameter_pack_element_expr_result(
            name,
            *argument,
            loc);
    }
    if (const ParameterPackElement* replay = parameter_pack_replay_element(
            ParameterPackKind::Function, name)) {
        const FunctionParameterPackElement* element =
            std::get_if<FunctionParameterPackElement>(replay);
        if (!element) {
            return lookup_name_fallback(name, loc, allow_unresolved);
        }

        if (closure_field_pack_element(*element)) {
            return closure_field_pack_element_expr_result(name,
                                                          *element,
                                                          loc);
        }
        ExprResult element_result = function_parameter_pack_element_expr_result(
            name,
            *element,
            loc);
        return element_result;
    }
    if (function_parameter_pack_name(name)) {
        report_error("unexpanded function parameter pack '" +
                         std::string(name) +
                         "' is not supported yet",
                     loc);
        ExprResult result;
        result.name = std::move(key);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    if (const cir::Binding* binding = lookup_ordinary_binding(name)) {
        return expr_result_for_binding(*binding, name, loc);
    }
    return lookup_name_fallback(name, loc, allow_unresolved);
}

ExprResult Session::make_entity_reference(cir::EntityId entity,
                                          std::string_view name,
                                          SrcLoc loc,
                                          bool qualified_name) {
    ExprResult result;
    if (!entity.valid() || !file_.valid(entity)) {
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }

    const cir::Entity& record = file_.entity(entity);
    cir::Binding binding;
    binding.name = file_.intern_name(name);
    binding.context = current_decl_context();
    binding.lookup_namespace = cir::LookupNamespace::Ordinary;
    binding.entities.push_back(entity);
    binding.type = record.type.valid() ? file_.type_ref(record.type)
                                       : cir::TypeRef{};
    binding.is_definition = record.is_definition;
    binding.loc = loc;

    cir::Fragment local_place_fragment;
    if ((record.storage_duration == cir::StorageDuration::Automatic ||
         record.storage_duration == cir::StorageDuration::Temporary) &&
        !is_cross_function_local(entity) &&
        !is_default_argument_local(entity)) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.entity_place");
        binding.place = builder_.local_place(entity, record.type, loc);
        local_place_fragment = finish_fragment_block(block, previous);
    }

    result = expr_result_for_binding(binding, name, loc);
    result.fragment = chain(std::move(local_place_fragment),
                            std::move(result.fragment), loc);
    result.qualified_name = qualified_name;
    return result;
}

bool Session::in_pack_pattern_capture() const {
    return !tstate().parameter_pack_pattern_captures_.empty();
}

bool Session::function_parameter_pack_name(std::string_view name) const {
    std::string key(name);
    bool has_active_projection =
        tstate().function_parameter_pack_names_.count(key) != 0;
    if (const cir::Binding* binding = lookup_ordinary_binding(name)) {
        for (cir::EntityId entity : binding->entities) {
            if (entity.valid() &&
                tstate().function_parameter_pack_params_.count(
                    static_cast<uint64_t>(entity.index)) != 0) {
                return true;
            }
        }
        if (has_active_projection && binding->context.valid() &&
            file_.decl_context(binding->context).kind ==
                cir::DeclContextKind::Prototype) {
            return true;
        }
        return false;
    }
    return has_active_projection;
}

Session::ParameterPackPatternCaptureScope
Session::begin_parameter_pack_pattern_capture() {
    ParameterPackPatternCaptureScope scope;
    scope.active = true;
    scope.depth = tstate().parameter_pack_pattern_captures_.size();
    tstate().parameter_pack_pattern_captures_.push_back({});
    return scope;
}

std::vector<Session::ParameterPackIdentity>
Session::finish_parameter_pack_pattern_capture(
    ParameterPackPatternCaptureScope scope) {
    if (!scope.active ||
        scope.depth >= tstate().parameter_pack_pattern_captures_.size()) {
        return {};
    }
    std::vector<ParameterPackIdentity> packs =
        std::move(tstate().parameter_pack_pattern_captures_[scope.depth]);
    tstate().parameter_pack_pattern_captures_.resize(scope.depth);
    return packs;
}

Session::ParameterPackPatternCaptureCheckpoint
Session::checkpoint_parameter_pack_pattern_capture() const {
    ParameterPackPatternCaptureCheckpoint checkpoint;
    if (tstate().parameter_pack_pattern_captures_.empty()) {
        return checkpoint;
    }
    checkpoint.active = true;
    checkpoint.depth =
        tstate().parameter_pack_pattern_captures_.size() - 1;
    checkpoint.size =
        tstate().parameter_pack_pattern_captures_.back().size();
    return checkpoint;
}

void Session::restore_parameter_pack_pattern_capture(
    ParameterPackPatternCaptureCheckpoint checkpoint) {
    if (!checkpoint.active ||
        checkpoint.depth >=
            tstate().parameter_pack_pattern_captures_.size()) {
        return;
    }
    std::vector<ParameterPackIdentity>& capture =
        tstate().parameter_pack_pattern_captures_[checkpoint.depth];
    if (capture.size() > checkpoint.size) {
        capture.resize(checkpoint.size);
    }
}

bool Session::closure_field_pack_element(
    const FunctionParameterPackElement& element) const {
    return element.entity.valid() && file_.valid(element.entity) &&
           file_.entity(element.entity).kind == cir::EntityKind::Field &&
           current_this_place_.valid();
}

ExprResult Session::closure_field_pack_element_expr_result(
    std::string_view name,
    const FunctionParameterPackElement& element,
    SrcLoc loc) {
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.pack.capture.field");
    cir::InstId this_value =
        builder_.lvalue_to_rvalue(current_this_place_, loc);
    cir::InstId object_place = builder_.deref(this_value, loc);
    cir::InstId field_place = builder_.field_addr(
        object_place, element.entity, element.type, loc);
    ExprResult result;
    result.fragment = finish_fragment_block(block, previous);
    result.place = field_place;
    result.type = element.type;
    result.entity = element.entity;
    result.name = std::string(name);
    result.category = ValueCategory::LValue;
    if (is_reference_type(result.type)) {
        result = deref_reference_lvalue(std::move(result), loc);
    }
    return result;
}

ExprResult Session::function_parameter_pack_element_expr_result(
    std::string_view name,
    const FunctionParameterPackElement& element,
    SrcLoc loc) {
    if (element.entity.valid() && file_.valid(element.entity) &&
        file_.entity(element.entity).kind ==
            cir::EntityKind::StructuredBinding) {
        return structured_binding_expr_result(element.entity, name, loc);
    }
    ExprResult result;
    result.type = element.type;
    result.entity = element.entity;
    result.name = file_.valid(element.entity) &&
                          file_.entity(element.entity).name.valid()
                      ? std::string(file_.name(
                            file_.entity(element.entity).name))
                      : std::string(name);
    result.place = element.place;
    result.category = ValueCategory::LValue;
    if (result.entity.valid()) {
        result.potential_results.push_back(result.entity);
    }
    if (!result.place.valid() && result.entity.valid() &&
        file_.valid(result.entity) &&
        file_.entity(result.entity).kind == cir::EntityKind::Parameter) {

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block =
            begin_fragment_block("expr.pack.prototype_parameter");
        result.place = builder_.local_place(result.entity, element.type, loc);
        result.fragment = finish_fragment_block(block, previous);
    }
    if (is_cross_function_local(result.entity) ||
        is_default_argument_local(result.entity)) {
        result.place = {};
        result.deferred_entity_place = true;
        if (!note_potential_lambda_capture(result.entity, loc)) {
            result.has_error = true;
        }
    }

    if (result.category == ValueCategory::LValue &&
        is_reference_type(result.type)) {
        result = deref_reference_lvalue(std::move(result), loc);
    }
    return result;
}

ExprResult Session::value_parameter_pack_element_expr_result(
    std::string_view name,
    const TemplateArgument& argument,
    SrcLoc loc) {
    if (argument.value_kind == cir::TemplateValueKind::Boolean) {
        return make_boolean_literal(!argument.integer_value.is_zero(),
                                    !argument.integer_value.is_zero()
                                        ? "true"
                                        : "false",
                                    loc);
    }
    if (argument.value_kind == cir::TemplateValueKind::Integer ||
        argument.value_kind == cir::TemplateValueKind::None) {
        std::string spelling = argument.value_spelling.empty()
            ? argument.integer_value.decimal()
            : argument.value_spelling;
        return make_integer_literal(argument.integer_value,
                                    std::move(spelling),
                                    argument.value_type.type,
                                    loc);
    }
    if (argument.value_kind == cir::TemplateValueKind::Floating) {
        if (!argument.floating_value.valid()) {
            ExprResult result;
            result.type = argument.value_type.type.valid()
                ? argument.value_type.type
                : builder_.double_type();
            result.name = std::string(name);
            result.category = ValueCategory::Dependent;
            result.value_dependent = true;
            result.references_template_value_parameter = true;
            return result;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.template_value_float");
        cir::TypeId type = argument.value_type.type.valid()
            ? argument.value_type.type
            : builder_.double_type();
        cir::InstId value = builder_.floating_literal(
            argument.floating_value,
            type,
            argument.value_spelling,
            loc);
        ExprResult result;
        result.value = value;
        result.fragment = finish_fragment_block(block, previous);
        result.type = type;
        result.category = ValueCategory::PrValue;
        return result;
    }
    if (argument.value_kind == cir::TemplateValueKind::Null) {
        if (argument.null_kind == cir::TemplateNullKind::Nullptr) {
            return make_nullptr_literal(loc);
        }
        cir::TypeId type = argument.value_type.type.valid()
            ? argument.value_type.type
            : pointer_type(type_ref(builder_.void_type()));
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.template_value_null");
        cir::InstId zero = builder_.integer_literal(0,
                                                    builder_.int_type(),
                                                    "0",
                                                    loc);
        ExprResult result;
        result.value = builder_.cast(type, zero, "conversion", loc);
        result.fragment = finish_fragment_block(block, previous);
        result.type = file_.inst(result.value).result_type;
        result.category = ValueCategory::PrValue;
        return result;
    }
    if (argument.value_kind == cir::TemplateValueKind::Address &&
        argument.value_entity.valid() &&
        file_.valid(argument.value_entity)) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.template_value_addr");
        auto materialize_address = [&](cir::TypeId target_pointer_type) {
            cir::InstId place =
                builder_.global_place(argument.value_entity, loc);
            cir::InstId address = builder_.addr_of(place, loc);
            if (argument.value_byte_offset != 0) {
                cir::TypeId byte_pointer =
                    pointer_type(type_ref(builder_.char_type()));
                if (file_.inst(address).result_type != byte_pointer) {
                    address = builder_.cast(byte_pointer,
                                            address,
                                            "conversion",
                                            loc);
                }
                cir::InstId offset = builder_.integer_literal(
                    argument.value_byte_offset,
                    builder_.usize_type(),
                    std::to_string(argument.value_byte_offset),
                    loc);
                address = builder_.binary(cir::BinaryOpKind::Add,
                                          byte_pointer,
                                          address,
                                          offset,
                                          loc);
            }
            if (file_.valid(target_pointer_type) &&
                file_.inst(address).result_type != target_pointer_type) {
                address = builder_.cast(target_pointer_type,
                                        address,
                                        "conversion",
                                        loc);
            }
            return address;
        };

        cir::TypeId resolved_value_type =
            file_.resolved_type(argument.value_type.type);
        cir::EntityKind address_entity_kind =
            file_.entity(argument.value_entity).kind;
        bool function_address =
            address_entity_kind == cir::EntityKind::Function ||
            (address_entity_kind == cir::EntityKind::Method &&
             file_.method_fact(argument.value_entity) &&
             file_.method_fact(argument.value_entity)->is_static);
        bool reference_param = file_.valid(resolved_value_type) &&
            (file_.type(resolved_value_type).kind ==
                 cir::TypeKind::LValueReference ||
             file_.type(resolved_value_type).kind ==
                 cir::TypeKind::RValueReference);
        if (reference_param) {
            cir::TypeRef referred =
                file_.reference_referred_ref(resolved_value_type);
            cir::TypeId referred_type = file_.resolved_type(referred.type);
            if (file_.valid(referred_type) &&
                file_.type(referred_type).kind == cir::TypeKind::Function &&
                function_address) {
                ExprResult result;
                result.entity = argument.value_entity;
                result.type = referred.type;
                result.fragment = finish_fragment_block(block, previous);
                result.category = ValueCategory::FunctionDesignator;
                return result;
            }
            cir::TypeId pointer_to_referred = pointer_type(referred);
            cir::InstId address = materialize_address(pointer_to_referred);
            ExprResult result;
            result.place = builder_.deref(address, loc);
            result.type = referred.type.valid()
                ? referred.type
                : file_.entity(argument.value_entity).type;
            result.fragment = finish_fragment_block(block, previous);
            result.category = ValueCategory::LValue;
            return result;
        }

        ExprResult result;
        if (function_address &&
            argument.value_byte_offset == 0) {
            result.value =
                builder_.function_to_pointer(argument.value_entity, loc);
        } else {
            result.value = materialize_address(argument.value_type.type);
        }
        if (argument.value_type.type.valid() &&
            file_.inst(result.value).result_type != argument.value_type.type) {
            result.value = builder_.cast(argument.value_type.type,
                                         result.value,
                                         "conversion",
                                         loc);
        }
        result.fragment = finish_fragment_block(block, previous);
        result.type = file_.inst(result.value).result_type;
        result.category = ValueCategory::PrValue;
        return result;
    }
    if (argument.value_kind == cir::TemplateValueKind::MemberPointer &&
        argument.value_entity.valid() &&
        file_.valid(argument.value_entity)) {
        ExprResult result;
        result.entity = argument.value_entity;
        result.type = argument.value_type.type;
        result.category = ValueCategory::MemberPointerDesignator;
        return result;
    }
    if (argument.value_kind == cir::TemplateValueKind::MemberPointer &&
        !argument.value_entity.valid()) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block =
            begin_fragment_block("expr.template_value_member_null");
        cir::InstId zero = builder_.integer_literal(0,
                                                    builder_.int_type(),
                                                    "0",
                                                    loc);
        ExprResult result;
        result.value = builder_.cast(argument.value_type.type,
                                     zero,
                                     "conversion",
                                     loc);
        result.fragment = finish_fragment_block(block, previous);
        result.type = file_.inst(result.value).result_type;
        result.category = ValueCategory::PrValue;
        return result;
    }
    report_error("value pack element '" + std::string(name) +
                     "' is not supported in expression replay yet",
                 loc);
    ExprResult result;
    result.has_error = true;
    result.type = builder_.unknown_type();
    result.category = ValueCategory::PrValue;
    return result;
}

std::optional<std::vector<ExprResult>>
Session::function_parameter_pack_arguments(std::string_view name,
                                           SrcLoc loc) {
    auto found = tstate().function_parameter_pack_elements_.find(std::string(name));
    if (found == tstate().function_parameter_pack_elements_.end()) {
        return std::nullopt;
    }

    std::vector<FunctionParameterPackElement> elements = found->second;
    std::vector<ExprResult> arguments;
    arguments.reserve(elements.size());
    for (const FunctionParameterPackElement& element : elements) {

        if (closure_field_pack_element(element)) {
            arguments.push_back(
                closure_field_pack_element_expr_result(name, element, loc));
            continue;
        }
        ExprResult element_result =
            function_parameter_pack_element_expr_result(name, element, loc);
        arguments.push_back(std::move(element_result));
    }
    return arguments;
}

cir::TypeRef Session::collect_pack_index_type(cir::TypeRef pack_type,
                                              ExprResult index,
                                              SrcLoc loc) {
    cir::TypeId resolved_pack = file_.resolved_type(pack_type.type);
    const auto* pack = file_.valid(resolved_pack)
        ? std::get_if<cir::TypeParamTypePayload>(
              &file_.type_payload(resolved_pack))
        : nullptr;
    if (!pack || !pack->is_parameter_pack) {
        report_error("pack index specifier does not name a type parameter pack",
                     loc);
        return type_ref(builder_.unknown_type());
    }

    index = require_value(std::move(index), UseContext::RValue, loc);
    bool dependent = expr_is_dependent(index) || index.value_dependent;
    int64_t index_value = 0;
    if (!dependent &&
        !evaluate_integer_constant(
            index,
            index_value,
            loc,
            "pack index is not a converted constant expression of type size_t")) {
        return type_ref(builder_.unknown_type());
    }
    if (!dependent && index_value < 0) {
        report_error("pack index is negative", loc);
        return type_ref(builder_.unknown_type());
    }
    std::optional<std::vector<TemplateArgument>> arguments =
        template_type_pack_arguments(resolved_pack);
    if (arguments.has_value() && !dependent) {
        size_t selected = static_cast<size_t>(index_value);
        if (selected >= arguments->size()) {
            report_error("pack index " + std::to_string(selected) +
                             " is out of bounds for pack of length " +
                             std::to_string(arguments->size()),
                         loc);
            return type_ref(builder_.unknown_type());
        }
        const TemplateArgument& argument = (*arguments)[selected];
        if (argument.kind != cir::TemplateArgumentKind::Type ||
            !argument.type.valid()) {
            report_error("selected pack element is not a type", loc);
            return type_ref(builder_.unknown_type());
        }
        cir::TypeRef selected_type = argument.type;
        selected_type.qualifiers |= pack_type.qualifiers;
        if (pack_type.memory_space != cir::MemorySpace::Default) {
            selected_type.memory_space = pack_type.memory_space;
        }
        return selected_type;
    }

    if (!index.template_value_expr.valid() && index.entity.valid()) {
        uint32_t parameter_index = template_value_param_index(index.entity);
        if (parameter_index != cir::ArrayTypePayload::no_extent_param) {
            index.template_value_expr = template_value_parameter_expr(
                parameter_index, type_ref(index.type), index.entity);
            index.template_value_expr.loc = loc;
            index.template_value_expr.definition_context =
                current_decl_context();
            index.template_value_expr.definition_lookup_generation =
                lookup_generation_;
        }
    }
    if (!index.template_value_expr.valid()) {
        report_error("pack index could not be retained as a constant expression",
                     loc);
        return type_ref(builder_.unknown_type());
    }

    std::vector<cir::TypeRef> expansions;
    if (arguments.has_value()) {
        expansions.reserve(arguments->size());
        for (const TemplateArgument& argument : *arguments) {
            if (argument.kind != cir::TemplateArgumentKind::Type ||
                !argument.type.valid()) {
                report_error("type parameter pack contains a non-type element",
                             loc);
                return type_ref(builder_.unknown_type());
            }
            expansions.push_back(argument.type);
        }
    }
    cir::TypeId selected = file_.pack_index_type(
        type_ref(resolved_pack),
        std::move(index.template_value_expr),
        std::move(expansions),
        arguments.has_value());
    return file_.type_ref(selected,
                          pack_type.qualifiers,
                          pack_type.memory_space);
}

ExprResult Session::collect_pack_index_expr(std::string_view name,
                                            ExprResult index,
                                            SrcLoc loc) {
    index = require_value(std::move(index), UseContext::RValue, loc);
    bool dependent_index = expr_is_dependent(index) || index.value_dependent;
    int64_t index_value = 0;
    if (!dependent_index &&
        !evaluate_integer_constant(
            index,
            index_value,
            loc,
            "pack index is not a converted constant expression of type size_t")) {
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        return result;
    }
    if (!dependent_index && index_value < 0) {
        report_error("pack index is negative", loc);
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        return result;
    }

    std::optional<ParameterPackIdentity> identity =
        parameter_pack_identity(ParameterPackKind::Function, name);
    std::optional<std::vector<ExprResult>> function_arguments;
    if (identity.has_value()) {
        function_arguments = function_parameter_pack_arguments(name, loc);
        if (function_arguments.has_value() && !dependent_index) {
            size_t selected = static_cast<size_t>(index_value);
            if (selected >= function_arguments->size()) {
                report_error("pack index " + std::to_string(selected) +
                                 " is out of bounds for pack of length " +
                                 std::to_string(function_arguments->size()),
                             loc);
                ExprResult result;
                result.has_error = true;
                result.type = builder_.unknown_type();
                return result;
            }
            return std::move((*function_arguments)[selected]);
        }
    }

    std::optional<uint32_t> value_pack_index =
        template_value_pack_param_index_for_name(name);
    std::optional<std::vector<TemplateArgument>> value_arguments;
    if (!identity.has_value() && value_pack_index.has_value()) {
        ParameterPackIdentity value_identity;
        if (auto found = parameter_pack_identity(ParameterPackKind::Value,
                                                 name)) {
            value_identity = *found;
        } else {
            value_identity.kind = ParameterPackKind::Value;
            value_identity.name = std::string(name);
            value_identity.index = *value_pack_index;
        }
        identity = std::move(value_identity);
        TemplateArgument marker;
        marker.kind = cir::TemplateArgumentKind::Value;
        marker.value_param_index = *value_pack_index;
        value_arguments = template_argument_pack_arguments(marker);
        if (value_arguments.has_value() && !dependent_index) {
            size_t selected = static_cast<size_t>(index_value);
            if (selected >= value_arguments->size()) {
                report_error("pack index " + std::to_string(selected) +
                                 " is out of bounds for pack of length " +
                                 std::to_string(value_arguments->size()),
                             loc);
                ExprResult result;
                result.has_error = true;
                result.type = builder_.unknown_type();
                return result;
            }
            return value_parameter_pack_element_expr_result(
                name, (*value_arguments)[selected], loc);
        }
    }

    if (!identity.has_value()) {
        report_error("pack index expression does not name a parameter pack",
                     loc);
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        return result;
    }
    if (!index.template_value_expr.valid() && index.entity.valid()) {
        uint32_t parameter_index = template_value_param_index(index.entity);
        if (parameter_index != cir::ArrayTypePayload::no_extent_param) {
            index.template_value_expr = template_value_parameter_expr(
                parameter_index, type_ref(index.type), index.entity);
            index.template_value_expr.loc = loc;
            index.template_value_expr.definition_context =
                current_decl_context();
            index.template_value_expr.definition_lookup_generation =
                lookup_generation_;
        }
    }
    if (!index.template_value_expr.valid() ||
        identity->index == cir::ArrayTypePayload::no_extent_param) {
        report_error("dependent pack index could not be retained", loc);
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        return result;
    }

    bump_pattern_taint();
    ExprResult result;
    result.name = std::string(name) + "...[...]";
    result.type = identity->declaration.valid() &&
                          file_.valid(identity->declaration)
        ? file_.entity(identity->declaration).type
        : cir::TypeId{};
    if (identity->kind == ParameterPackKind::Function &&
        result.type.valid() &&
        file_.type(file_.resolved_type(result.type)).kind ==
            cir::TypeKind::TypeParam) {
        const auto* parameter = std::get_if<cir::TypeParamTypePayload>(
            &file_.type_payload(file_.resolved_type(result.type)));
        if (parameter && parameter->is_parameter_pack) {
            result.type = file_.pack_index_type(
                type_ref(result.type), index.template_value_expr);
        }
    }
    if (!result.type.valid() || contains_auto_type(result.type)) {
        result.type = file_.dependent_type("pack index expression");
    }
    result.category = ValueCategory::Dependent;
    result.value_dependent = true;
    result.references_template_value_parameter = true;
    std::optional<uint32_t> function_parameter_index;
    if (identity->kind == ParameterPackKind::Function &&
        identity->declaration.valid() &&
        builder_.current_function().valid() &&
        file_.valid(builder_.current_function())) {
        const cir::Function& function =
            file_.function(builder_.current_function());
        for (size_t parameter = 0;
             parameter < function.parameters.size(); ++parameter) {
            if (function.parameters[parameter].entity ==
                identity->declaration) {
                function_parameter_index =
                    static_cast<uint32_t>(parameter);
                break;
            }
        }
    }
    result.template_value_expr = template_value_pack_index_expr(
        identity->index,
        index.template_value_expr,
        type_ref(result.type),
        function_parameter_index);
    result.template_value_expr.loc = loc;
    result.template_value_expr.definition_context = current_decl_context();
    result.template_value_expr.definition_lookup_generation =
        lookup_generation_;
    return result;
}

ExprResult Session::expr_result_for_binding(const cir::Binding& binding_record,
                                            std::string_view name,
                                            SrcLoc loc) {
    const cir::Binding* binding = &binding_record;
    {
        ExprResult result;
        result.type = binding->type.type;
        result.entity = binding->entities.empty() ? cir::EntityId{} : binding->entities.back();
        if (result.entity.valid()) {
            result.potential_results.push_back(result.entity);
        }
        result.name = std::string(name);
        if (result.entity.valid() && file_.valid(result.entity) &&
            file_.entity(result.entity).kind ==
                cir::EntityKind::StructuredBinding) {
            return structured_binding_expr_result(result.entity, name, loc);
        }
        bool block_scope_binding =
            binding->context.valid() &&
            file_.decl_context(binding->context).kind ==
                cir::DeclContextKind::Block;

        result.suppress_argument_dependent_lookup =
            block_scope_binding &&
            (!file_.binding_is_callable(*binding) ||
             binding->has_block_scope_function_declaration);
        result.type_originates_from_template_parameter =
            result.entity.valid() &&
            tstate().template_type_origin_parameter_entities_.count(
                static_cast<uint64_t>(result.entity.index)) != 0;
        if (result.entity.valid() &&
            tstate().function_parameter_pack_params_.count(
                static_cast<uint64_t>(result.entity.index)) != 0) {
            report_error("unexpanded function parameter pack '" +
                             std::string(name) +
                             "' is not supported yet",
                         loc);
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        result.references_template_value_parameter =
            result.entity.valid() &&
            template_value_param_index(result.entity) !=
                cir::ArrayTypePayload::no_extent_param;

        result.value_dependent =
            result.references_template_value_parameter;
        if (result.entity.valid() && file_.valid(result.entity) &&
            file_.entity(result.entity).kind == cir::EntityKind::TemplateParam) {
            if (const TemplateArgument* dependent =
                    dependent_instantiation_value_argument(result.entity)) {
                result.type = dependent->value_type.type.valid()
                    ? dependent->value_type.type
                    : result.type;
                result.category = ValueCategory::Dependent;
                result.value_dependent = true;
                result.references_template_value_parameter = true;
                result.template_value_expr = dependent->dependent_value_expr;
                result.dependent_value_qualifier =
                    dependent->dependent_value_qualifier;
                result.dependent_value_name = dependent->dependent_value_name;
                if (!result.template_value_expr.valid() &&
                    dependent->value_param_index !=
                        cir::ArrayTypePayload::no_extent_param) {
                    result.template_value_expr = template_value_parameter_expr(
                        dependent->value_param_index,
                        dependent->value_type,
                        dependent->value_entity);
                }
                return result;
            }
        }
        if (result.references_template_value_parameter &&
            template_value_param_is_pack(result.entity)) {
            report_error("unexpanded template parameter pack '" +
                             std::string(name) +
                             "' is not supported yet",
                         loc);
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        if (result.references_template_value_parameter) {
            result.template_value_expr = template_value_parameter_expr(
                template_value_param_index(result.entity),
                type_ref(result.type),
                result.entity);
            result.template_value_expr.loc = loc;
            result.template_value_expr.definition_context =
                current_decl_context();
            result.template_value_expr.definition_lookup_generation =
                lookup_generation_;
        }
        if (collecting_pattern_ && result.entity.valid()) {

            if (template_value_param_index(result.entity) !=
                    cir::ArrayTypePayload::no_extent_param ||
                tstate().pattern_holed_locals_.count(
                    static_cast<uint64_t>(result.entity.index)) != 0) {
                bump_pattern_taint();
            }
        }
        if (result.entity.valid() && file_.valid(result.entity)) {
            const cir::Entity& entity = file_.entity(result.entity);
            bool dependent_constant_candidate =
                (entity.qualifiers & cir::QualConst) != 0 &&
                (is_dependent_type(entity.type) ||
                 type_contains_dependent_alias_specialization(entity.type));
            bool potentially_constant =
                entity.decl_flags.is_constexpr ||
                is_reference_type(entity.type) ||
                ((entity.qualifiers & cir::QualConst) != 0 &&
                 cir::is_integer_like_type(file_, entity.type)) ||
                dependent_constant_candidate;
            bool member_of_current_instantiation = false;
            if (entity.parent.valid()) {
                for (auto frame =
                         tstate().current_instantiation_frames_.rbegin();
                     frame != tstate().current_instantiation_frames_.rend();
                     ++frame) {
                    if (frame->record.valid() &&
                        frame->record == entity.parent) {
                        member_of_current_instantiation = true;
                        break;
                    }
                }
            }
            bool uninitialized_current_static_member =
                member_of_current_instantiation &&
                entity.kind == cir::EntityKind::Variable &&
                (entity.storage_duration == cir::StorageDuration::Static ||
                 entity.storage_duration == cir::StorageDuration::Thread) &&
                !entity.has_initializer;
            const cir::RecordStaticDataMemberFact* static_member =
                static_data_member_fact(result.entity);
            bool type_dependent_static_constant =
                in_template_definition() &&
                entity.kind == cir::EntityKind::Variable &&
                (entity.storage_duration == cir::StorageDuration::Static ||
                 entity.storage_duration == cir::StorageDuration::Thread) &&
                static_member &&
                (static_member->is_constexpr ||
                 (static_member->type.qualifiers & cir::QualConst) != 0) &&
                (is_dependent_type(entity.type) ||
                 type_contains_dependent_alias_specialization(entity.type));
            if ((potentially_constant &&
                 entity.initializer_is_value_dependent) ||
                uninitialized_current_static_member ||
                type_dependent_static_constant) {
                result.value_dependent = true;
                if (type_dependent_static_constant &&
                    entity.parent.valid() && file_.valid(entity.parent) &&
                    entity.name.valid()) {

                    result.dependent_value_qualifier =
                        type_ref(file_.entity(entity.parent).type);
                    result.dependent_value_name = entity.name;
                } else if (potentially_constant &&
                    entity.initializer_is_value_dependent &&
                    !result.template_value_expr.valid()) {
                    cir::TemplateValueExprNode node;
                    node.kind = cir::TemplateValueExprKind::Entity;
                    node.entity = result.entity;
                    node.name = entity.name;
                    node.result_type = type_ref(result.type);
                    if (entity.parent.valid() &&
                        file_.valid(entity.parent)) {
                        node.qualifier_type =
                            type_ref(file_.entity(entity.parent).type);
                    }
                    result.template_value_expr.nodes.push_back(node);
                    result.template_value_expr.root = 0;
                    result.template_value_expr.loc = loc;
                    result.template_value_expr.definition_context =
                        current_decl_context();
                    result.template_value_expr
                        .definition_lookup_generation = lookup_generation_;
                }
                if (collecting_pattern_) {
                    bump_pattern_taint();
                }
            }

            if (entity.kind == cir::EntityKind::Variable &&
                entity.initializer_is_value_dependent &&
                contains_auto_type(entity.type) &&
                in_template_definition()) {
                result.category = ValueCategory::Dependent;
                return make_dependent_expr(std::move(result), loc);
            }
        }
        if (result.entity.valid() &&
            file_.entity(result.entity).attr_facts.is_deprecated) {
            const std::string& note =
                file_.entity(result.entity).attr_facts.deprecated_message;
            report_warning(WarningId::DeprecatedDeclarations,
                           "'" + std::string(name) + "' is deprecated" +
                               (note.empty() ? "" : ": " + note),
                           loc);
        }
        if (binding->dependent_member_using &&
            !binding->is_type_name &&
            binding->entities.empty()) {

            result.category = ValueCategory::Dependent;
            result.value_dependent = true;
            return make_dependent_expr(std::move(result), loc);
        }
        if (binding->is_type_name) {
            result.category = ValueCategory::Type;
        } else if (result.entity.valid() &&
                   (file_.entity(result.entity).kind ==
                        cir::EntityKind::Enumerator ||
                    file_.entity(result.entity).kind ==
                        cir::EntityKind::TemplateParam)) {
            const cir::Entity& entity = file_.entity(result.entity);
            if (!entity.has_constant_value) {
                report_error("constant entity has no constant value", loc);
                result.has_error = true;
            }
            if (entity.constant_value_kind ==
                    cir::TemplateValueKind::Address &&
                !entity.constant_entity.valid() &&
                in_template_definition()) {
                result.category = ValueCategory::Dependent;
                return make_dependent_expr(std::move(result), loc);
            }
            if (entity.constant_value_kind ==
                    cir::TemplateValueKind::MemberPointer &&
                !entity.constant_entity.valid() &&
                in_template_definition()) {
                result.category = ValueCategory::Dependent;
                return make_dependent_expr(std::move(result), loc);
            }
            if (entity.constant_value_kind ==
                    cir::TemplateValueKind::MetaInfo &&
                entity.constant_meta_kind == cir::MetaInfoKind::Null &&
                !entity.constant_entity.valid() &&
                !entity.constant_meta_type.type.valid() &&
                (in_template_definition() ||
                 result.references_template_value_parameter)) {

                result.category = ValueCategory::Dependent;
                return make_dependent_expr(std::move(result), loc);
            }
            if (entity.constant_value_kind ==
                    cir::TemplateValueKind::Floating &&
                !entity.constant_floating_value.valid()) {
                result.category = ValueCategory::Dependent;
                return make_dependent_expr(std::move(result), loc);
            }
            if (entity.kind == cir::EntityKind::TemplateParam &&
                contains_auto_type(entity.type) &&
                in_template_definition()) {
                result.category = ValueCategory::Dependent;
                return make_dependent_expr(std::move(result), loc);
            }
            if (entity.kind == cir::EntityKind::TemplateParam &&
                (entity.constant_value_kind ==
                     cir::TemplateValueKind::StructuralObject ||
                 entity.constant_value_kind ==
                     cir::TemplateValueKind::Closure)) {
                if (entity.template_parameter_object.valid() &&
                    file_.valid(entity.template_parameter_object)) {
                    cir::BlockId previous = builder_.current_block();
                    cir::BlockId block =
                        begin_fragment_block("expr.template_parameter_object");
                    result.place = builder_.global_place(
                        entity.template_parameter_object,
                        loc);
                    result.fragment = finish_fragment_block(block, previous);
                    result.type =
                        file_.entity(entity.template_parameter_object).type;
                    result.category = ValueCategory::LValue;
                    return result;
                }
                if (in_template_definition() ||
                    template_value_param_index(result.entity) !=
                        cir::ArrayTypePayload::no_extent_param) {
                    result.category = ValueCategory::Dependent;
                    return make_dependent_expr(std::move(result), loc);
                }
                report_error(
                    "class template parameter object cannot be materialized",
                    loc);
                result.has_error = true;
                result.type = builder_.unknown_type();
                result.category = ValueCategory::PrValue;
                return result;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.enumerator");
            if (entity.constant_value_kind ==
                cir::TemplateValueKind::Boolean) {
                result.value = builder_.boolean_literal(
                    !entity.constant_integer_value.is_zero(),
                    std::string(name),
                    loc);
            } else if (entity.constant_value_kind ==
                       cir::TemplateValueKind::Floating) {
                result.value = builder_.floating_literal(
                    entity.constant_floating_value,
                    file_.valid(entity.type)
                        ? entity.type
                        : builder_.double_type(),
                    std::string(name),
                    loc);
            } else if (entity.constant_value_kind ==
                       cir::TemplateValueKind::Null) {
                if (entity.constant_null_kind ==
                    cir::TemplateNullKind::Nullptr) {
                    result.value = builder_.nullptr_literal(
                        std::string(name).empty()
                            ? "nullptr"
                            : std::string(name),
                        loc);
                } else {
                    cir::TypeId type = file_.valid(entity.type)
                        ? entity.type
                        : pointer_type(type_ref(builder_.void_type()));
                    cir::InstId zero = builder_.integer_literal(
                        0, builder_.int_type(), "0", loc);
                    result.value = builder_.cast(type, zero, "conversion", loc);
                }
            } else if (entity.constant_value_kind ==
                       cir::TemplateValueKind::Address &&
                       entity.constant_entity.valid() &&
                       file_.valid(entity.constant_entity)) {
                auto materialize_address = [&](cir::TypeId target_pointer_type) {
                    cir::InstId place =
                        builder_.global_place(entity.constant_entity, loc);
                    cir::InstId address = builder_.addr_of(place, loc);
                    if (entity.constant_byte_offset != 0) {
                        cir::TypeId byte_pointer =
                            pointer_type(type_ref(builder_.char_type()));
                        if (file_.inst(address).result_type != byte_pointer) {
                            address = builder_.cast(byte_pointer, address,
                                                    "conversion", loc);
                        }
                        cir::InstId offset = builder_.integer_literal(
                            entity.constant_byte_offset,
                            builder_.usize_type(),
                            std::to_string(entity.constant_byte_offset),
                            loc);
                        address = builder_.binary(cir::BinaryOpKind::Add,
                                                  byte_pointer,
                                                  address,
                                                  offset,
                                                  loc);
                    }
                    if (file_.valid(target_pointer_type) &&
                        file_.inst(address).result_type != target_pointer_type) {
                        address = builder_.cast(target_pointer_type, address,
                                                "conversion", loc);
                    }
                    return address;
                };
                cir::TypeId resolved_entity_type =
                    file_.resolved_type(entity.type);
                cir::EntityKind constant_entity_kind =
                    file_.entity(entity.constant_entity).kind;
                bool function_address =
                    constant_entity_kind == cir::EntityKind::Function ||
                    (constant_entity_kind == cir::EntityKind::Method &&
                     file_.method_fact(entity.constant_entity) &&
                     file_.method_fact(entity.constant_entity)->is_static);
                bool reference_param = file_.valid(resolved_entity_type) &&
                    (file_.type(resolved_entity_type).kind ==
                         cir::TypeKind::LValueReference ||
                     file_.type(resolved_entity_type).kind ==
                         cir::TypeKind::RValueReference);
                if (reference_param) {
                    cir::TypeRef referred =
                        file_.reference_referred_ref(resolved_entity_type);
                    cir::TypeId referred_type =
                        file_.resolved_type(referred.type);
                    if (file_.valid(referred_type) &&
                        file_.type(referred_type).kind ==
                            cir::TypeKind::Function &&
                        function_address) {
                        result.entity = entity.constant_entity;
                        result.type = referred.type;
                        result.fragment =
                            finish_fragment_block(block, previous);
                        result.category = ValueCategory::FunctionDesignator;
                        return result;
                    }
                    cir::TypeId pointer_to_referred = pointer_type(referred);
                    cir::InstId address =
                        materialize_address(pointer_to_referred);
                    result.place = builder_.deref(address, loc);
                    result.type = referred.type.valid()
                        ? referred.type
                        : file_.entity(entity.constant_entity).type;
                    result.fragment = finish_fragment_block(block, previous);
                    result.category = ValueCategory::LValue;
                    return result;
                }
                if (function_address &&
                    entity.constant_byte_offset == 0) {
                    result.value =
                        builder_.function_to_pointer(entity.constant_entity, loc);
                } else {
                    result.value = materialize_address(entity.type);
                }
                if (file_.valid(entity.type) &&
                    file_.inst(result.value).result_type != entity.type) {
                    result.value =
                        builder_.cast(entity.type, result.value, "conversion", loc);
                }
            } else if (entity.constant_value_kind ==
                       cir::TemplateValueKind::MetaInfo) {
                if (entity.constant_meta_kind == cir::MetaInfoKind::Type &&
                    entity.constant_meta_type.type.valid()) {
                    result.value =
                        builder_.reflect_type(entity.constant_meta_type, loc);
                } else if (entity.constant_entity.valid()) {
                    result.value =
                        builder_.reflect_entity(entity.constant_meta_kind,
                                                entity.constant_entity,
                                                loc);
                } else {
                    report_error(
                        "null reflection template arguments are not "
                        "supported yet",
                        loc);
                    result.value = builder_.integer_literal(
                        0, builder_.int_type(), "0", loc);
                    result.has_error = true;
                }
            } else if (entity.constant_value_kind ==
                           cir::TemplateValueKind::MemberPointer &&
                       !entity.constant_entity.valid()) {
                cir::InstId zero = builder_.integer_literal(
                    0, builder_.int_type(), "0", loc);
                result.value = builder_.cast(entity.type, zero, "conversion", loc);
            } else if (entity.constant_value_kind ==
                           cir::TemplateValueKind::MemberPointer &&
                       entity.constant_entity.valid() &&
                       file_.valid(entity.constant_entity)) {
                result.fragment = finish_fragment_block(block, previous);
                result.entity = entity.constant_entity;
                result.type = entity.type;
                result.category = ValueCategory::MemberPointerDesignator;
                return result;
            } else {
                result.value = builder_.integer_literal(
                    entity.constant_integer_value,
                    file_.valid(entity.type) ? entity.type : builder_.int_type(),
                    std::string(name),
                    loc);
            }
            result.fragment = finish_fragment_block(block, previous);
            result.type = file_.inst(result.value).result_type;
            result.category = ValueCategory::PrValue;
        } else if (result.entity.valid() &&
                   file_.entity(result.entity).kind == cir::EntityKind::Function) {
            result.category = ValueCategory::FunctionDesignator;
            std::vector<cir::EntityId> visible = binding->entities;
            if (lookup_generation_ceiling_ != 0) {

                std::vector<cir::EntityId> filtered;
                for (size_t i = 0; i < binding->entities.size(); ++i) {
                    if (binding_entity_visible_at_generation(
                            *binding, i, lookup_generation_ceiling_)) {
                        filtered.push_back(binding->entities[i]);
                    }
                }
                if (!filtered.empty()) {
                    visible = std::move(filtered);
                    result.entity = visible.back();
                    result.type = file_.entity(result.entity).type;
                } else {
                    result.entity = {};
                    result.type = builder_.unknown_type();
                    result.category = ValueCategory::Dependent;
                    result.unresolved_unqualified_name = true;
                    return result;
                }
            }
            if (file_.has_module_units()) {

                std::vector<cir::EntityId> module_visible;
                for (cir::EntityId candidate : visible) {
                    if (file_.entity_lookup_visible(candidate)) {
                        module_visible.push_back(candidate);
                    }
                }
                if (!module_visible.empty() &&
                    module_visible.size() != visible.size()) {
                    visible = std::move(module_visible);
                    result.entity = visible.back();
                    result.type = file_.entity(result.entity).type;
                }
            }
            if (visible.size() > 1) {
                result.candidates = std::move(visible);
            }
        } else if (result.entity.valid() &&
                   file_.entity(result.entity).kind ==
                       cir::EntityKind::Concept) {
            report_error("concept name requires a template argument list", loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.concept.error");
            result.value = builder_.error("bare concept name", loc);
            result.fragment = finish_fragment_block(block, previous);
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            result.has_error = true;
            return result;
        }

        if (binding->is_type_name ||
            (result.entity.valid() &&
             (file_.entity(result.entity).kind ==
                  cir::EntityKind::Enumerator ||
              file_.entity(result.entity).kind ==
                  cir::EntityKind::TemplateParam ||
              file_.entity(result.entity).kind ==
                  cir::EntityKind::Function))) {
            return result;
        }
        if (result.entity.valid() &&
            file_.entity(result.entity).kind == cir::EntityKind::Field) {
            const cir::Entity& member = file_.entity(result.entity);
            cir::EntityId anonymous_owner =
                member.declaring_record.valid()
                    ? member.declaring_record
                    : member.parent;
            const cir::RecordFacts* anonymous =
                file_.record_facts(anonymous_owner);
            bool promoted_variable = anonymous &&
                (anonymous->anonymous_union_object_kind ==
                     cir::AnonymousUnionObjectKind::BlockVariable ||
                 anonymous->anonymous_union_object_kind ==
                     cir::AnonymousUnionObjectKind::NamespaceVariable);
            if (promoted_variable) {
                cir::EntityId object = anonymous->anonymous_union_object;
                if (!object.valid() || !file_.valid(object)) {
                    report_error("anonymous union member has no object",
                                 loc);
                    result.has_error = true;
                    result.type = builder_.unknown_type();
                    result.category = ValueCategory::PrValue;
                    return result;
                }
                if (is_cross_function_local(object) ||
                    is_default_argument_local(object)) {
                    report_error("a member of an anonymous union cannot be captured by a lambda",
                                 loc);
                    result.has_error = true;
                    result.type = builder_.unknown_type();
                    result.category = ValueCategory::PrValue;
                    return result;
                }
                cir::Fragment ensure;
                if (file_.entity(object).storage_duration ==
                    cir::StorageDuration::Thread) {
                    ensure = ensure_thread_initialized(object, loc);
                }
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("expr.anonymous_union.member");
                cir::InstId place = binding->place;
                if (!place.valid()) {
                    place = builder_.global_place(object, loc);
                }
                const cir::AnonymousUnionPromotionFact* promotion = nullptr;
                for (const cir::AnonymousUnionPromotionFact& candidate :
                     anonymous->anonymous_union_promotions) {
                    if (candidate.member == result.entity) {
                        promotion = &candidate;
                        break;
                    }
                }
                if (!promotion) {
                    result.has_error = true;
                    result.type = builder_.unknown_type();
                } else {
                    place = emit_subobject_path(place,
                                                promotion->path,
                                                loc);
                    result.type = file_.entity(result.entity).type;
                }
                cir::Fragment member_fragment =
                    finish_fragment_block(block, previous);
                result.fragment = chain(std::move(result.fragment),
                                        std::move(ensure), loc);
                result.fragment = chain(std::move(result.fragment),
                                        std::move(member_fragment), loc);
                result.place = place;
                result.category = ValueCategory::LValue;
                if (const cir::RecordFieldFact* field =
                        file_.field_fact(result.entity)) {
                    result.designates_bitfield = field->is_bitfield;
                }
                return result;
            }

            if (binding->place.valid()) {
                result.place = binding->place;
                result.category = ValueCategory::LValue;
                return result;
            }
        }
        if (binding->place.valid()) {
            if (result.entity.valid() &&
                file_.entity(result.entity).is_block_byref &&
                make_block_byref_access(result.entity, result, loc)) {
                return result;
            }
            bool default_argument_local =
                is_default_argument_local(result.entity);
            if (is_cross_function_local(result.entity) ||
                default_argument_local) {
                result.deferred_entity_place = true;
                result.category = ValueCategory::LValue;
                if (!note_potential_lambda_capture(result.entity, loc)) {
                    result.has_error = true;
                }
            } else {
                result.place = binding->place;
                result.category = ValueCategory::LValue;
            }
        } else if (result.entity.valid() &&
                   file_.entity(result.entity).kind ==
                       cir::EntityKind::Constructor) {

            cir::EntityId record_entity = file_.entity(result.entity).parent;
            result.type = record_entity.valid()
                ? file_.entity(record_entity).type
                : builder_.unknown_type();
            result.category = ValueCategory::Type;
        } else if (result.entity.valid() &&
                   (file_.entity(result.entity).kind == cir::EntityKind::Method ||
                    file_.entity(result.entity).kind == cir::EntityKind::Destructor)) {
            const cir::Entity& member = file_.entity(result.entity);
            const cir::RecordMethodFact* method_fact =
                file_.method_fact(result.entity);
            bool is_static_member_function =
                member.is_static_member_function ||
                (method_fact && method_fact->is_static);
            result.category = ValueCategory::FunctionDesignator;
            result.type = member.type;
            if (binding->entities.size() > 1) {
                result.candidates = binding->entities;
            }
            if (is_static_member_function) {

                if (in_template_definition() &&
                    member.parent.valid() &&
                    member.parent == current_validation_record()) {
                    result.value_dependent = true;
                }
                return result;
            }

            if (!lambda_stack_.empty() &&
                member.parent !=
                    lambda_stack_.back().closure_record) {
                ExprResult enclosing_this = lambda_enclosing_this_value(loc);
                if (enclosing_this.has_error) {
                    result.has_error = true;
                    result.type = builder_.unknown_type();
                    result.category = ValueCategory::PrValue;
                    return result;
                }
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("expr.lambda.this.method");
                cir::InstId object_place =
                    builder_.deref(enclosing_this.value, loc);
                cir::Fragment fragment = finish_fragment_block(block, previous);
                result.fragment = chain(std::move(result.fragment),
                                        std::move(enclosing_this.fragment),
                                        loc);
                result.fragment =
                    chain(std::move(result.fragment), std::move(fragment), loc);
                result.place = object_place;
                return result;
            }
            if (current_complete_class_object_place_.valid()) {
                result.place = current_complete_class_object_place_;
            } else {
                cir::Fragment fragment;
                cir::InstId object_place = materialize_implicit_object_place(
                    "expr.this.method", &fragment, loc);
                result.fragment =
                    chain(std::move(result.fragment), std::move(fragment), loc);
                result.place = object_place;
            }
        } else if (result.entity.valid() &&
                   file_.entity(result.entity).kind == cir::EntityKind::Field) {

            if (!lambda_stack_.empty() &&
                lambda_capture_source_usable(result.entity)) {
                return lambda_capture_access(std::move(result), name, loc);
            }

            if (!lambda_stack_.empty() &&
                file_.entity(result.entity).parent !=
                    lambda_stack_.back().closure_record) {
                ExprResult enclosing_this = lambda_enclosing_this_value(loc);
                if (enclosing_this.has_error) {
                    result.has_error = true;
                    result.type = builder_.unknown_type();
                    result.category = ValueCategory::PrValue;
                    return result;
                }
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("expr.lambda.this.field");
                cir::InstId object_place =
                    builder_.deref(enclosing_this.value, loc);
                cir::InstId field_place = builder_.field_addr(
                    object_place, result.entity, binding->type.type, loc);
                cir::Fragment fragment = finish_fragment_block(block, previous);
                result.fragment = chain(std::move(result.fragment),
                                        std::move(enclosing_this.fragment),
                                        loc);
                result.fragment =
                    chain(std::move(result.fragment), std::move(fragment), loc);
                result.place = field_place;
                result.type = binding->type.type;
                result.category = ValueCategory::LValue;
                if (const cir::RecordFieldFact* field =
                        file_.field_fact(result.entity)) {
                    result.designates_bitfield = field->is_bitfield;
                }
                if (is_reference_type(result.type)) {
                    result = deref_reference_lvalue(std::move(result), loc);
                }
                return result;
            }
            cir::Fragment object_fragment;
            cir::InstId object_place = materialize_implicit_object_place(
                "expr.this.field", &object_fragment, loc);
            if (!object_place.valid()) {
                report_error("member '" + std::string(name) +
                                 "' cannot be used outside a member function",
                             loc);
                result.has_error = true;
                result.type = builder_.unknown_type();
                result.category = ValueCategory::PrValue;
                return result;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.field");
            cir::InstId field_place = builder_.field_addr(
                object_place, result.entity, binding->type.type, loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            result.fragment =
                chain(std::move(result.fragment),
                      std::move(object_fragment), loc);
            result.fragment =
                chain(std::move(result.fragment), std::move(fragment), loc);
            result.place = field_place;
            result.type = binding->type.type;
            result.category = ValueCategory::LValue;
            if (const cir::RecordFieldFact* field =
                    file_.field_fact(result.entity)) {
                result.designates_bitfield = field->is_bitfield;
            }
            if (is_reference_type(result.type)) {
                result = deref_reference_lvalue(std::move(result), loc);
            }
        } else if (result.entity.valid() &&
                   file_.entity(result.entity).kind ==
                       cir::EntityKind::Parameter) {

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.param_place");
            cir::InstId place = builder_.local_place(
                result.entity, file_.entity(result.entity).type, loc);
            result.fragment = finish_fragment_block(block, previous);
            result.place = place;
            result.category = ValueCategory::LValue;
        } else if (result.entity.valid()) {
            cir::Fragment ensure;
            if (file_.entity(result.entity).storage_duration ==
                cir::StorageDuration::Thread) {
                ensure = ensure_thread_initialized(result.entity, loc);
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.global_place");
            cir::InstId place = builder_.global_place(result.entity, loc);
            cir::Fragment place_fragment =
                finish_fragment_block(block, previous);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(ensure), loc);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(place_fragment), loc);
            result.place = place;
            result.category = ValueCategory::LValue;
        }

        if (result.category == ValueCategory::LValue &&
            is_reference_type(result.type)) {
            result = deref_reference_lvalue(std::move(result), loc);
        }
        return result;
    }
}

cir::InstId Session::materialize_implicit_object_place(
    const char* label,
    cir::Fragment* fragment_out,
    SrcLoc loc) {
    if (current_complete_class_object_place_.valid()) {
        return current_complete_class_object_place_;
    }
    if (!current_this_place_.valid() &&
        !member_declarator_this_type_.valid()) {
        return {};
    }

    cir::InstId this_value;
    cir::Fragment this_fragment;
    if (current_this_place_.valid()) {
        cir::BlockId this_previous = builder_.current_block();
        cir::BlockId this_block =
            begin_fragment_block("expr.this.implicit");
        this_value = builder_.lvalue_to_rvalue(current_this_place_, loc);
        this_fragment = finish_fragment_block(this_block, this_previous);
    } else {
        ExprResult declarator_this = collect_this_expr(loc);
        if (declarator_this.has_error || !declarator_this.value.valid()) {
            return {};
        }
        this_value = declarator_this.value;
        this_fragment = std::move(declarator_this.fragment);
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block(label);
    cir::InstId place = builder_.deref(this_value, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);
    *fragment_out = chain(std::move(this_fragment),
                          std::move(fragment), loc);
    return place;
}

ExprResult Session::lookup_name_fallback(std::string_view name,
                                         SrcLoc loc,
                                         bool allow_unresolved) {

    cir::EntityId member_record = current_member_record_;
    bool through_lambda = false;
    if (!lambda_stack_.empty()) {
        member_record = lambda_stack_.front().enclosing_member_record;
        through_lambda = true;
    }
    if (lang_opts_.is_cxx_mode() && member_record.valid()) {
        cir::TypeId record_type = file_.entity(member_record).type;

        auto emit_this_object_place =
            [&](const char* label,
                cir::Fragment* fragment_out) -> cir::InstId {
            if (through_lambda) {
                ExprResult enclosing_this = lambda_enclosing_this_value(loc);
                if (enclosing_this.has_error) {
                    return {};
                }
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block(label);
                cir::InstId place = builder_.deref(enclosing_this.value, loc);
                cir::Fragment fragment = finish_fragment_block(block, previous);
                *fragment_out = chain(std::move(enclosing_this.fragment),
                                      std::move(fragment), loc);
                return place;
            }
            return materialize_implicit_object_place(
                label, fragment_out, loc);
        };
        MemberLookupResult member_lookup =
            lookup_member_name(record_type, name);

        if (const cir::TemplateSpecializationFact* specialization =
                file_.template_specialization(member_record)) {
            const TemplateInfo* info =
                template_info(specialization->template_entity);
            if (info && info->pattern_record.valid() &&
                file_.valid(info->pattern_record) &&
                info->pattern_record != member_record) {
                MemberLookupResult definition_lookup = lookup_member_name(
                    file_.entity(info->pattern_record).type, name);
                if (definition_lookup.found_name &&
                    !definition_lookup.ambiguous &&
                    !definition_lookup.declarations.empty()) {
                    std::vector<MemberLookupDeclaration> fixed;
                    for (const MemberLookupDeclaration& concrete :
                         member_lookup.declarations) {
                        bool selected_at_definition = std::any_of(
                            definition_lookup.declarations.begin(),
                            definition_lookup.declarations.end(),
                            [&](const MemberLookupDeclaration& pattern) {
                                return pattern.entity == concrete.entity;
                            });
                        if (selected_at_definition) {
                            fixed.push_back(concrete);
                        }
                    }
                    if (!fixed.empty()) {
                        member_lookup.declarations = std::move(fixed);
                        member_lookup.ambiguous = false;
                        member_lookup.found_name = true;
                    }
                }
            }
        }
        if (member_lookup.ambiguous) {
            report_error("member '" + std::string(name) +
                             "' is ambiguous through base classes",
                         loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.member.error");
            cir::InstId value = builder_.name_ref(
                "<invalid-member>", builder_.unknown_type(), loc);
            ExprResult error;
            error.fragment = finish_fragment_block(block, previous);
            error.value = value;
            error.type = builder_.unknown_type();
            error.name = std::string(name);
            error.category = ValueCategory::PrValue;
            error.has_error = true;
            return error;
        }

        const MemberLookupDeclaration* type_declaration = nullptr;
        cir::TypeRef designated_type{};
        for (const MemberLookupDeclaration& declaration :
             member_lookup.declarations) {
            if (!declaration.designated_type.valid()) {
                continue;
            }
            cir::TypeRef candidate = declaration.designated_type;
            candidate.type = file_.resolved_type(candidate.type);
            if (designated_type.valid() && designated_type != candidate) {
                designated_type = {};
                type_declaration = nullptr;
                break;
            }
            designated_type = candidate;
            type_declaration = &declaration;
        }
        if (designated_type.valid()) {
            if (type_declaration) {
                (void)check_member_lookup_access(*type_declaration, loc,
                                                 record_type);
                (void)check_member_lookup_base_access(
                    *type_declaration, record_type, loc);
            }
            ExprResult result;
            result.type = designated_type.type;
            result.name = std::string(name);
            result.category = ValueCategory::Type;
            return result;
        }

        const cir::RecordStaticDataMemberFact* static_member = nullptr;
        const MemberLookupDeclaration* static_declaration = nullptr;
        cir::EntityId enumerator{};
        const MemberLookupDeclaration* enumerator_declaration = nullptr;
        const MemberLookupDeclaration* field_declaration = nullptr;
        std::vector<cir::EntityId> callable_declarations;
        for (const MemberLookupDeclaration& declaration :
             member_lookup.declarations) {
            if (!declaration.entity.valid() ||
                !file_.valid(declaration.entity)) {
                continue;
            }
            if (const cir::RecordStaticDataMemberFact* candidate =
                    static_data_member_fact(declaration.entity)) {
                static_member = candidate;
                static_declaration = &declaration;
                break;
            }
            cir::EntityKind kind = file_.entity(declaration.entity).kind;
            if (kind == cir::EntityKind::Enumerator) {
                enumerator = declaration.entity;
                enumerator_declaration = &declaration;
            } else if (kind == cir::EntityKind::Field) {
                field_declaration = &declaration;
            } else if (kind == cir::EntityKind::Method ||
                       kind == cir::EntityKind::Destructor ||
                       (template_info(declaration.entity) &&
                        template_info_is_function_template(
                            *template_info(declaration.entity)))) {
                callable_declarations.push_back(declaration.entity);
            }
        }
        if (static_member) {
            if (static_declaration) {
                (void)check_member_lookup_access(*static_declaration, loc,
                                                 record_type);
                (void)check_member_lookup_base_access(
                    *static_declaration, record_type, loc);
            } else {
                check_member_access(static_member->entity,
                                    static_member->declared_access, loc);
            }
            return make_entity_reference(static_member->entity, name, loc);
        }
        if (enumerator.valid()) {
            if (enumerator_declaration) {
                (void)check_member_lookup_access(
                    *enumerator_declaration, loc, record_type);
                (void)check_member_lookup_base_access(
                    *enumerator_declaration, record_type, loc);
            }
            return make_entity_reference(enumerator, name, loc);
        }

        FieldPathLookupResult field_path;
        if (field_declaration) {
            field_path.found = true;
            field_path.type = file_.entity(field_declaration->entity).type;
            field_path.ambiguous =
                field_declaration->object_paths.size() != 1;
            if (!field_path.ambiguous) {
                field_path.entities =
                    field_declaration->object_paths.front();
                field_path.entities.insert(
                    field_path.entities.end(),
                    field_declaration->member_path.begin(),
                    field_declaration->member_path.end());
            }
        }
        if (field_path.found && !field_path.ambiguous) {
            cir::Fragment fragment;
            cir::InstId place =
                emit_this_object_place("expr.this.base.field", &fragment);
            if (place.valid()) {
                std::vector<cir::EntityId> base_prefix;
                for (cir::EntityId step : field_path.entities) {
                    const cir::RecordFieldFact* field =
                        file_.field_fact(step);
                    if (!field || !field->is_base_subobject) {
                        break;
                    }
                    base_prefix.push_back(step);
                }
                if (!base_prefix.empty()) {
                    const cir::RecordFieldFact* naming =
                        file_.field_fact(base_prefix.back());
                    if (naming) {
                        check_base_path_access(
                            base_prefix, record_type,
                            file_.resolved_type(naming->type.type), loc);
                    }
                }
                (void)check_member_lookup_access(*field_declaration, loc,
                                                 record_type);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("expr.this.base.field.path");
                place = emit_subobject_path(place, field_path.entities, loc);
                fragment = chain(std::move(fragment),
                                 finish_fragment_block(block, previous), loc);
                ExprResult result;
                result.fragment = std::move(fragment);
                result.place = place;
                result.type = field_path.type;
                result.entity = field_path.entities.empty()
                    ? cir::EntityId{}
                    : field_path.entities.back();
                result.name = std::string(name);
                result.category = ValueCategory::LValue;
                if (const cir::RecordFieldFact* field =
                        file_.field_fact(result.entity)) {
                    result.designates_bitfield = field->is_bitfield;
                }
                if (is_reference_type(result.type)) {
                    result = deref_reference_lvalue(std::move(result), loc);
                }
                return result;
            }
        }
        if (field_path.ambiguous) {
            report_error("member '" + std::string(name) +
                             "' is ambiguous through base classes",
                         loc);
            ExprResult error;
            error.type = builder_.unknown_type();
            error.name = std::string(name);
            error.category = ValueCategory::PrValue;
            error.has_error = true;
            return error;
        }
        if (!callable_declarations.empty()) {
            if (!through_lambda && !current_this_place_.valid() &&
                !current_complete_class_object_place_.valid() &&
                !member_declarator_this_type_.valid()) {
                std::vector<cir::EntityId> static_callables;
                for (cir::EntityId candidate : callable_declarations) {
                    const cir::RecordMethodFact* method =
                        file_.method_fact(candidate);
                    if (method && method->is_static) {
                        static_callables.push_back(candidate);
                    }
                }
                if (!static_callables.empty()) {
                    MemberAccessBase access;
                    access.base_place.type = record_type;
                    access.base_place.category = ValueCategory::PrValue;
                    access.record_type = record_type;
                    return collect_bound_member_function_access_expr(
                        std::move(access),
                        std::move(static_callables),
                        name,
                        loc,
                        &member_lookup);
                }
            }
            cir::Fragment fragment;
            cir::InstId place =
                emit_this_object_place("expr.this.base.method", &fragment);
            if (place.valid()) {
                MemberAccessBase access;
                access.base_place.fragment = std::move(fragment);
                access.base_place.place = place;
                access.base_place.type = record_type;
                access.base_place.category = ValueCategory::LValue;
                access.record_type = record_type;
                return collect_bound_member_function_access_expr(
                    std::move(access), std::move(callable_declarations), name,
                    loc, &member_lookup);
            }
        }
    }

    if ((name == "__func__" || name == "__FUNCTION__" ||
         name == "__PRETTY_FUNCTION__") &&
        current_function_.valid()) {
        const cir::Function& function = file_.function(current_function_);
        std::string function_name;
        if (function.entity.valid()) {
            const cir::Entity& entity = file_.entity(function.entity);
            if (entity.name.valid()) {
                function_name = file_.name(entity.name);
            }
        }
        if (name == "__PRETTY_FUNCTION__") {

            std::string pretty;
            const auto* fn_payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(function.type)));
            if (fn_payload) {
                pretty = file_.format_type(fn_payload->return_type) + " " +
                         function_name + "(";
                if (fn_payload->parameters.empty()) {
                    pretty += fn_payload->has_prototype ? "void" : "";
                } else {
                    for (size_t i = 0; i < fn_payload->parameters.size(); ++i) {
                        if (i > 0) {
                            pretty += ", ";
                        }
                        pretty += file_.format_type(fn_payload->parameters[i]);
                    }
                    if (fn_payload->is_variadic) {
                        pretty += ", ...";
                    }
                }
                pretty += ")";
            } else {
                pretty = function_name;
            }
            function_name = std::move(pretty);
        }
        std::string spelling = "\"" + function_name + "\"";
        ExprResult predefined =
            make_string_literal(std::move(function_name),
                                std::move(spelling),
                                loc);
        if (in_template_definition()) {

            return make_dependent_expr(std::move(predefined), loc);
        }
        return predefined;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.name");
    cir::InstId inst = builder_.name_ref(name, builder_.unknown_type(), loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    result.name = std::string(name);
    result.category = ValueCategory::Dependent;
    result.unresolved_unqualified_name = true;
    if (!allow_unresolved) {
        report_error("use of undeclared identifier '" + std::string(name) + "'",
                     loc);
        note_module_hidden_name(name, loc);
        result.has_error = true;
    }
    return result;
}

ExprResult Session::collect_sizeof_type(cir::TypeId type,
                                        SrcLoc loc,
                                        cir::Fragment vla_bounds) {
    cir::TypeId resolved = file_.resolved_type(type);
    if (file_.valid(resolved) &&
        (file_.type(resolved).kind == cir::TypeKind::LValueReference ||
         file_.type(resolved).kind == cir::TypeKind::RValueReference)) {

        type = file_.reference_referred_ref(resolved).type;
    }

    bool dependent = is_dependent_type(type);
    if (dependent) {

        bump_pattern_taint();
    }
    if (!dependent) {
        (void)require_complete_class_type(
            type, loc, cir::InstantiationDemandKind::CompleteClass);
    }
    if (variably_modified_type(type)) {

        cir::TypeId cursor = file_.resolved_type(type);
        ExprResult total = make_integer_literal(1, "1", builder_.usize_type(), loc);
        bool saw_runtime = false;
        while (file_.valid(cursor) &&
               file_.type(cursor).kind == cir::TypeKind::Array) {
            const auto* array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(cursor));
            if (!array) {
                break;
            }
            if (array->size_kind == cir::ArraySizeKind::Variable) {
                ExprResult extent;
                extent.value = array->size_expr;
                extent.type = file_.valid(array->size_expr)
                    ? file_.inst(array->size_expr).result_type
                    : builder_.int_type();
                extent.category = ValueCategory::PrValue;
                total = collect_binary_expr(syntax::BinaryOperator::Mul,
                                            std::move(total),
                                            std::move(extent),
                                            loc);
                saw_runtime = true;
            } else if (array->size_kind == cir::ArraySizeKind::Constant &&
                       array->size.has_value()) {
                total = collect_binary_expr(
                    syntax::BinaryOperator::Mul,
                    std::move(total),
                    make_integer_literal(static_cast<int64_t>(*array->size),
                                         std::to_string(*array->size),
                                         builder_.usize_type(),
                                         loc),
                    loc);
            } else {
                report_error("sizeof applied to an incomplete array type", loc);
                break;
            }
            cursor = file_.resolved_type(array->element_type.type);
        }
        std::optional<size_t> element_size = size_of_type(cursor, loc);
        if (!element_size.has_value()) {
            report_error("sizeof element type is incomplete", loc);
            element_size = 1;
        }
        total = collect_binary_expr(
            syntax::BinaryOperator::Mul,
            std::move(total),
            make_integer_literal(static_cast<int64_t>(*element_size),
                                 std::to_string(*element_size),
                                 builder_.usize_type(),
                                 loc),
            loc);
        total = convert_to_arithmetic_type(std::move(total), builder_.usize_type(), loc);
        (void)saw_runtime;
        total.fragment = chain(std::move(vla_bounds), std::move(total.fragment), loc);
        return total;
    }
    if (!dependent && !cir::size_align_of_type(file_, type).has_value()) {
        if (!is_unknown_type(file_, type)) {
            report_error("sizeof applied to an incomplete or unsupported type",
                         loc);
        }
        ExprResult result =
            make_integer_literal(1, "1", builder_.usize_type(), loc);
        result.fragment =
            chain(std::move(vla_bounds), std::move(result.fragment), loc);
        result.has_error = true;
        return result;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.sizeof");
    cir::InstId inst = builder_.sizeof_type(type, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(vla_bounds), std::move(fragment), loc);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    result.category = ValueCategory::PrValue;
    result.value_dependent = dependent;
    if (dependent) {

        result.references_template_value_parameter = true;
        result.template_value_expr = template_value_sizeof_expr(
            type, false, type_ref(result.type));
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context = current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
    } else if (std::optional<cir::TypeSizeAlign> size_align =
                   cir::size_align_of_type(file_, type)) {

        result.template_value_expr = template_value_integer_expr(
            file_,
            cir::IntegerValue::from_unsigned(
                size_align->size_bytes,
                cir::integer_shape_for_type(file_, result.type).bit_width),
            type_ref(result.type));
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context = current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
    }
    return result;
}

ExprResult Session::collect_sizeof_pack(std::string_view name, SrcLoc loc) {
    auto make_count = [&](size_t count) {
        return make_integer_literal(static_cast<int64_t>(count),
                                    std::to_string(count),
                                    builder_.usize_type(),
                                    loc);
    };
    auto make_dependent_count = [&](uint32_t parameter_index) {
        bump_pattern_taint();
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.sizeof_pack");
        std::string spelling = "sizeof...(" + std::string(name) + ")";
        cir::InstId value =
            builder_.name_ref(spelling, builder_.usize_type(), loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = value;
        result.type = file_.inst(value).result_type;
        result.name = std::move(spelling);
        result.category = ValueCategory::PrValue;
        result.references_template_value_parameter = true;
        result.value_dependent = true;
        result.template_value_expr =
            template_value_pack_size_expr(parameter_index,
                                          type_ref(result.type));
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context = current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
        return result;
    };
    auto make_dependent_function_count = [&]() {
        bump_pattern_taint();
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.sizeof_pack");
        std::string spelling = "sizeof...(" + std::string(name) + ")";
        cir::InstId value =
            builder_.name_ref(spelling, builder_.usize_type(), loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = value;
        result.type = file_.inst(value).result_type;
        result.name = std::move(spelling);
        result.category = ValueCategory::PrValue;
        return result;
    };

    if (std::optional<cir::TypeId> pack_type =
            type_parameter_pack_type(name)) {
        if (std::optional<std::vector<TemplateArgument>> arguments =
                template_type_pack_arguments(*pack_type)) {
            return make_count(arguments->size());
        }
        cir::TypeId resolved = file_.resolved_type(*pack_type);
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::TypeParam) {
            const auto& payload =
                std::get<cir::TypeParamTypePayload>(
                    file_.type_payload(resolved));
            if (payload.is_parameter_pack) {
                return make_dependent_count(payload.index);
            }
        }
    }

    if (std::optional<uint32_t> value_pack_index =
            template_value_pack_param_index_for_name(name)) {
        TemplateArgument marker;
        marker.kind = cir::TemplateArgumentKind::Value;
        marker.value_param_index = *value_pack_index;
        if (std::optional<std::vector<TemplateArgument>> arguments =
                template_argument_pack_arguments(marker)) {
            return make_count(arguments->size());
        }
        return make_dependent_count(*value_pack_index);
    }

    if (std::optional<uint32_t> template_pack_index =
            template_template_pack_param_index_for_name(name)) {
        TemplateArgument marker;
        marker.kind = cir::TemplateArgumentKind::Template;
        marker.template_param_index = *template_pack_index;
        if (std::optional<std::vector<TemplateArgument>> arguments =
                template_argument_pack_arguments(marker)) {
            return make_count(arguments->size());
        }
        return make_dependent_count(*template_pack_index);
    }

    if (function_parameter_pack_name(name)) {
        auto index =
            tstate().function_parameter_pack_template_indices_.find(std::string(name));
        if (collecting_pattern_) {
            if (index != tstate().function_parameter_pack_template_indices_.end()) {
                return make_dependent_count(index->second);
            }
            return make_dependent_function_count();
        }
        if (std::optional<std::vector<ExprResult>> arguments =
                function_parameter_pack_arguments(name, loc)) {
            return make_count(arguments->size());
        }
        if (index != tstate().function_parameter_pack_template_indices_.end()) {
            return make_dependent_count(index->second);
        }
        return make_dependent_function_count();
    }

    report_error("sizeof... operand '" + std::string(name) +
                     "' does not name a parameter pack",
                 loc);
    ExprResult result =
        make_integer_literal(0, "0", builder_.usize_type(), loc);
    result.has_error = true;
    return result;
}

ExprResult Session::collect_alignof_type(cir::TypeId type, SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(type);
    if (file_.valid(resolved) &&
        (file_.type(resolved).kind == cir::TypeKind::LValueReference ||
         file_.type(resolved).kind == cir::TypeKind::RValueReference)) {

        type = file_.reference_referred_ref(resolved).type;
    }
    bool dependent = is_dependent_type(type);
    if (dependent) {
        bump_pattern_taint();
    } else {
        (void)require_complete_class_type(
            type, loc, cir::InstantiationDemandKind::CompleteClass);
    }
    if (!dependent && !cir::align_of_type(file_, type).has_value()) {

        if (!is_unknown_type(file_, type)) {
            report_error("alignof applied to an incomplete or unsupported type",
                         loc);
        }
        ExprResult result =
            make_integer_literal(1, "1", builder_.usize_type(), loc);
        result.has_error = true;
        return result;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.alignof");
    cir::InstId inst = builder_.alignof_type(type, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    result.category = ValueCategory::PrValue;
    result.value_dependent = dependent;
    if (dependent) {
        result.references_template_value_parameter = true;
        result.template_value_expr = template_value_sizeof_expr(
            type, true, type_ref(result.type));
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context = current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
    }
    return result;
}

cir::TypeId Session::resolve_std_type_info_type(SrcLoc loc) {
    cir::DeclContextId root = resolve_qualifier_root().context;
    const cir::Binding* std_binding = file_.lookup_namespace_name_binding(
        root, "std", /*include_parents=*/false);
    if (!std_binding || std_binding->entities.empty()) {
        report_error("typeid requires a preceding declaration of 'std::type_info'; include <typeinfo>",
                     loc);
        return {};
    }
    cir::EntityId std_namespace = std_binding->entities.back();
    if (!std_namespace.valid() || !file_.valid(std_namespace)) {
        report_error("typeid requires a preceding declaration of 'std::type_info'; include <typeinfo>",
                     loc);
        return {};
    }
    cir::DeclContextId std_context =
        file_.entity(std_namespace).semantic_context;
    const cir::Binding* binding = file_.lookup_type_name_binding(
        std_context, "type_info", /*include_parents=*/false);
    if (!binding) {
        binding = file_.lookup_tag_binding(
            std_context, "type_info", /*include_parents=*/false);
    }
    if (!binding || binding->entities.empty()) {
        report_error("typeid requires a preceding declaration of 'std::type_info'; include <typeinfo>",
                     loc);
        return {};
    }
    cir::EntityId entity = binding->entities.back();
    if (!entity.valid() || !file_.valid(entity) ||
        file_.entity(entity).kind != cir::EntityKind::Record) {
        report_error("'std::type_info' must name a class type", loc);
        return {};
    }
    return file_.resolved_type(file_.entity(entity).type);
}

bool Session::typeid_operand_is_potentially_evaluated(
    const ExprResult& operand) const {
    if (expr_is_dependent(operand) ||
        (operand.category != ValueCategory::LValue &&
         operand.category != ValueCategory::XValue)) {
        return false;
    }
    cir::TypeId object_type = file_.resolved_type(operand.type);
    if (operand.place.valid() && file_.valid(operand.place)) {
        object_type = file_.resolved_type(
            file_.place_object_ref(file_.inst(operand.place).result_type).type);
    }
    if (!file_.valid(object_type) ||
        file_.type(object_type).kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file_.record_facts_for_type(object_type);
    return facts && !facts->is_incomplete && facts->is_polymorphic;
}

ExprResult Session::collect_typeid_type(cir::TypeId type, SrcLoc loc) {
    ExprResult result;
    cir::TypeId type_info = resolve_std_type_info_type(loc);
    result.type = type_info.valid() ? type_info : builder_.unknown_type();
    result.category = ValueCategory::LValue;
    if (!type_info.valid()) {
        result.has_error = true;
        return result;
    }
    if (file_.abi_policy().cxx_abi != CxxAbiKind::Itanium) {
        report_error("typeid lowering is not implemented for the Microsoft C++ ABI",
                     loc);
        result.has_error = true;
        return result;
    }

    cir::TypeRef represented = file_.type_ref(file_.resolved_type(type));
    if (file_.valid(represented.type) &&
        (file_.type(represented.type).kind == cir::TypeKind::LValueReference ||
         file_.type(represented.type).kind == cir::TypeKind::RValueReference)) {
        represented = file_.reference_referred_ref(represented.type);
        represented.type = file_.resolved_type(represented.type);
    }
    represented.qualifiers = cir::QualNone;
    if (is_dependent_type(represented.type)) {
        bump_pattern_taint();
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.typeid.dependent");
        cir::TypeId pointer = builder_.pointer_type(
            cir::TypeRef{type_info, cir::QualConst, cir::MemorySpace::Default});
        cir::InstId address =
            builder_.name_ref("<dependent-typeinfo-address>", pointer, loc);
        result.place = builder_.deref(address, loc);
        result.fragment = finish_fragment_block(block, previous);
        result.value_dependent = true;
        return result;
    }
    if (file_.valid(represented.type) &&
        file_.type(represented.type).kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(represented.type);
        if (!facts || facts->is_incomplete) {
            report_error("typeid cannot be applied to an incomplete class type",
                         loc);
            result.has_error = true;
            return result;
        }
    }
    cir::EntityId typeinfo = typeinfo_entity_for_type(represented, loc);
    if (!typeinfo.valid()) {
        report_error("typeid cannot emit RTTI for type '" +
                         file_.format_type(represented.type) + "'",
                     loc);
        result.has_error = true;
        return result;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.typeid.static");
    cir::InstId raw_place = builder_.global_place(typeinfo, loc);
    cir::InstId raw_address = builder_.addr_of(raw_place, loc);
    cir::TypeId typeinfo_pointer = builder_.pointer_type(
        cir::TypeRef{type_info, cir::QualConst, cir::MemorySpace::Default});
    cir::InstId typed_address =
        builder_.cast(typeinfo_pointer, raw_address, "value", loc);
    result.place = builder_.deref(typed_address, loc);
    result.fragment = finish_fragment_block(block, previous);
    return result;
}

ExprResult Session::collect_typeid_expr(ExprResult operand, SrcLoc loc) {
    cir::TypeId type_info = resolve_std_type_info_type(loc);
    ExprResult result;
    result.type = type_info.valid() ? type_info : builder_.unknown_type();
    result.category = ValueCategory::LValue;
    result.has_error = operand.has_error || !type_info.valid();
    if (!type_info.valid()) {
        return result;
    }
    if (file_.abi_policy().cxx_abi != CxxAbiKind::Itanium) {
        report_error("typeid lowering is not implemented for the Microsoft C++ ABI",
                     loc);
        result.has_error = true;
        return result;
    }

    if (expr_is_dependent(operand)) {
        bump_pattern_taint();
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.typeid.dependent");
        cir::TypeId pointer = builder_.pointer_type(
            cir::TypeRef{type_info, cir::QualConst, cir::MemorySpace::Default});
        cir::InstId address =
            builder_.name_ref("<dependent-typeinfo-address>", pointer, loc);
        result.place = builder_.deref(address, loc);
        result.fragment = finish_fragment_block(block, previous);
        result.value_dependent = true;
        result.references_template_value_parameter =
            operand.references_template_value_parameter;
        return result;
    }

    cir::TypeRef represented = file_.type_ref(file_.resolved_type(operand.type));
    if (operand.place.valid() && file_.valid(operand.place)) {
        represented = file_.place_object_ref(
            file_.inst(operand.place).result_type);
        represented.type = file_.resolved_type(represented.type);
    } else if (file_.valid(represented.type) &&
               (file_.type(represented.type).kind ==
                    cir::TypeKind::LValueReference ||
                file_.type(represented.type).kind ==
                    cir::TypeKind::RValueReference)) {
        represented = file_.reference_referred_ref(represented.type);
        represented.type = file_.resolved_type(represented.type);
    }
    represented.qualifiers = cir::QualNone;
    if (file_.valid(represented.type) &&
        file_.type(represented.type).kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(represented.type);
        if (!facts || facts->is_incomplete) {
            report_error("typeid cannot be applied to an incomplete class type",
                         loc);
            result.has_error = true;
            return result;
        }
    }

    bool dynamic = typeid_operand_is_potentially_evaluated(operand);
    if (!dynamic) {

        ExprResult static_result =
            collect_typeid_type(represented.type, loc);
        static_result.has_error = static_result.has_error || operand.has_error;
        return static_result;
    }

    std::vector<cir::EntityId> vptr_path;
    if (!vptr_field_path(represented.type, &vptr_path)) {
        report_error("typeid requires a valid polymorphic object layout", loc);
        result.has_error = true;
        return result;
    }

    cir::TypeId typeinfo_pointer = builder_.pointer_type(
        cir::TypeRef{type_info, cir::QualConst, cir::MemorySpace::Default});
    const size_t pointer_bytes = std::max<size_t>(
        1, (file_.target_info().pointer_width + 7) / 8);

    auto emit_dynamic_place = [&]() {
        cir::InstId vptr_place = operand.place;
        for (cir::EntityId step : vptr_path) {
            vptr_place = builder_.field_addr(
                vptr_place, step, file_.entity(step).type, loc);
        }
        cir::InstId vptr = builder_.lvalue_to_rvalue(vptr_place, loc);
        cir::TypeId usize = builder_.usize_type();
        cir::InstId raw_vptr = builder_.cast(usize, vptr, "value", loc);
        cir::InstId slot_address = builder_.binary(
            cir::BinaryOpKind::Sub,
            usize,
            raw_vptr,
            builder_.integer_literal(static_cast<int64_t>(pointer_bytes),
                                     usize,
                                     std::to_string(pointer_bytes),
                                     loc),
            loc);
        cir::TypeId void_pointer = builder_.pointer_type(builder_.void_type());
        cir::TypeId slot_pointer =
            builder_.pointer_type(file_.type_ref(void_pointer));
        cir::InstId typed_slot =
            builder_.cast(slot_pointer, slot_address, "value", loc);
        cir::InstId slot_place = builder_.deref(typed_slot, loc);
        cir::InstId raw_typeinfo =
            builder_.lvalue_to_rvalue(slot_place, loc);
        cir::InstId typed_typeinfo =
            builder_.cast(typeinfo_pointer, raw_typeinfo, "value", loc);
        return builder_.deref(typed_typeinfo, loc);
    };

    cir::BlockId previous = builder_.current_block();
    cir::BlockId entry = begin_fragment_block("expr.typeid.dynamic");
    cir::Fragment dynamic_fragment;
    if (operand.direct_dereference_pointer.valid() &&
        operand.direct_dereference_pointer_type.valid()) {
        cir::InstId null_value = builder_.cast(
            operand.direct_dereference_pointer_type,
            builder_.nullptr_literal("nullptr", loc),
            "nullptr",
            loc);
        cir::InstId is_null = builder_.binary(
            cir::BinaryOpKind::Equal,
            builder_.bool_type(),
            operand.direct_dereference_pointer,
            null_value,
            loc);
        dynamic_fragment = finish_fragment_block(entry, previous);
        cir::BlockId bad =
            builder_.create_detached_block("expr.typeid.dynamic.bad");
        cir::BlockId success =
            builder_.create_detached_block("expr.typeid.dynamic.ok");
        builder_.cond_branch_from(dynamic_fragment.exit,
                                  is_null,
                                  bad,
                                  success,
                                  {},
                                  loc);

        builder_.switch_to_block(bad);
        cir::EntityId bad_typeid = runtime_function(
            file_.abi_policy().eh_runtime_hooks.bad_typeid,
            function_type(file_.type_ref(builder_.void_type()),
                          {},
                          false,
                          true),
            loc);
        file_.entity_mut(bad_typeid).attr_facts.is_noreturn = true;
        builder_.call(bad_typeid, builder_.void_type(), {}, loc);
        builder_.unreachable(loc);

        builder_.switch_to_block(success);
        result.place = emit_dynamic_place();

        builder_.switch_to_block(previous);
        append_fragment_blocks(dynamic_fragment,
                               builder_.block_fragment(bad));
        append_fragment_blocks(dynamic_fragment,
                               builder_.block_fragment(success));
        dynamic_fragment.exit = success;
    } else {
        result.place = emit_dynamic_place();
        dynamic_fragment = finish_fragment_block(entry, previous);
    }
    result.fragment = chain(std::move(operand.fragment),
                            std::move(dynamic_fragment),
                            loc);
    result.has_error = operand.has_error;
    return result;
}

ExprResult Session::collect_unary_expr(syntax::UnaryOperator op, ExprResult operand, SrcLoc loc) {

    switch (op) {
        case syntax::UnaryOperator::SizeofExpr:
        case syntax::UnaryOperator::SizeofType:
            return collect_sizeof_type(
                operand.type.valid() ? operand.type : builder_.unknown_type(),
                loc);
        case syntax::UnaryOperator::AlignofExpr:
        case syntax::UnaryOperator::AlignofType:
            return collect_alignof_type(
                operand.type.valid() ? operand.type : builder_.unknown_type(),
                loc);
        default:
            break;
    }
    bool operand_value_dependent = expr_is_value_dependent(operand);
    if (expr_is_dependent(operand)) {
        if (std::optional<cir::TemplateValueExprOp> graph_op =
                template_value_unary_expr_op(op)) {
            cir::TemplateValueExpression source =
                template_value_operand_expression(operand);
            cir::TypeId result_type =
                file_.dependent_type("dependent-unary-operator");
            ValueCategory result_category =
                op == syntax::UnaryOperator::Dereference
                    ? ValueCategory::LValue
                    : ValueCategory::PrValue;
            operand.template_value_expr = template_value_unary_expr(
                *graph_op,
                std::move(source),
                type_ref(result_type),
                result_category);
            operand.template_value_expr.loc = loc;
            operand.template_value_expr.definition_context =
                current_decl_context();
            operand.template_value_expr.definition_lookup_generation =
                lookup_generation_;

            operand.entity = {};
            operand.name.clear();
            operand.candidates.clear();
            operand.overload_designator.reset();
            operand.explicit_template_arguments.clear();
            operand.candidate_explicit_template_arguments.clear();
            operand.dependent_value_qualifier = {};
            operand.dependent_value_name = {};
            operand.dependent_member_access.reset();
            operand.qualified_name = false;
            operand.unresolved_unqualified_name = false;
            operand.suppress_argument_dependent_lookup = false;
        }
        return make_dependent_expr(std::move(operand), loc);
    }

    if (lang_opts_.is_cxx_mode()) {
        bool unary_handled = false;
        ExprResult overloaded =
            try_overloaded_unary(op, operand, &unary_handled, loc);
        if (unary_handled) {
            return overloaded;
        }

        if (op == syntax::UnaryOperator::Plus &&
            is_record_type(file_, operand.type)) {
            if (operand.category == ValueCategory::PrValue &&
                operand.value.valid()) {
                MemberAccessBase materialized = collect_member_access_base(
                    std::move(operand), /*is_arrow=*/false, loc);
                operand = std::move(materialized.base_place);
            }
            cir::TypeId conversion_target;
            UserConversionSequence sequence =
                resolve_permitted_implicit_conversion(
                    operand,
                    PermittedImplicitTarget::UnaryPlus,
                    &conversion_target,
                    loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_error(
                    "built-in unary operator '+' has ambiguous conversions",
                    loc);
                ExprResult result = make_integer_literal(0, "0", loc);
                result.fragment = chain(std::move(operand.fragment),
                                        std::move(result.fragment), loc);
                result.has_error = true;
                return result;
            }
            if (sequence.kind ==
                UserConversionSequence::Kind::ConversionFunction) {
                operand = apply_user_conversion_sequence(
                    std::move(operand), conversion_target, sequence, loc);
            }
        }
    }

    switch (op) {
        case syntax::UnaryOperator::PrefixIncrement:
        case syntax::UnaryOperator::PrefixDecrement:
        case syntax::UnaryOperator::PostfixIncrement:
        case syntax::UnaryOperator::PostfixDecrement: {

            ExprResult place = require_place(std::move(operand), UseContext::Assignment, loc);
            cir::TypeId object_type = place.type.valid()
                ? place.type
                : object_type_from_place(place.place);
            if (!object_type.valid()) {
                object_type = builder_.int_type();
            }

            cir::TypeRef incdec_object_ref =
                file_.place_object_ref(file_.inst(place.place).result_type);
            if ((incdec_object_ref.qualifiers & cir::QualAtomic) &&
                is_integer_type(object_type)) {
                bool increment = op == syntax::UnaryOperator::PrefixIncrement ||
                                 op == syntax::UnaryOperator::PostfixIncrement;
                cir::BlockId atomic_previous = builder_.current_block();
                cir::BlockId atomic_block = begin_fragment_block("expr.incdec.atomic");
                cir::InstId one_literal = builder_.integer_literal(1, "1", loc);
                cir::InstId one_typed = builder_.cast(object_type, one_literal, "arith", loc);
                cir::InstId atomic_old = builder_.atomic_rmw(
                    place.place,
                    one_typed,
                    increment ? cir::AtomicRmwOp::Add : cir::AtomicRmwOp::Sub,
                    cir::MemoryOrder::SeqCst,
                    loc);
                cir::InstId atomic_new = builder_.binary(
                    increment ? cir::BinaryOpKind::Add : cir::BinaryOpKind::Sub,
                    object_type,
                    atomic_old,
                    one_typed,
                    loc);
                cir::Fragment atomic_fragment =
                    finish_fragment_block(atomic_block, atomic_previous);

                ExprResult result;
                result.fragment =
                    chain(std::move(place.fragment), std::move(atomic_fragment), loc);
                result.value = is_postfix_increment_or_decrement(op) ? atomic_old
                                                                     : atomic_new;
                bool cxx_prefix_lvalue =
                    lang_opts_.is_cxx_mode() &&
                    !is_postfix_increment_or_decrement(op);
                result.place =
                    cxx_prefix_lvalue ? place.place : cir::InstId{};
                result.type = object_type;
                result.category = cxx_prefix_lvalue
                    ? ValueCategory::LValue
                    : ValueCategory::PrValue;
                result.has_error = place.has_error;
                return result;
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId load_block = begin_fragment_block("expr.incdec.load");
            cir::InstId old_value = builder_.lvalue_to_rvalue(place.place, loc);
            cir::Fragment load_fragment = finish_fragment_block(load_block, previous);

            previous = builder_.current_block();
            cir::BlockId one_block = begin_fragment_block("expr.incdec.one");
            cir::InstId one = builder_.integer_literal(1, "1", loc);
            cir::Fragment one_fragment = finish_fragment_block(one_block, previous);

            previous = builder_.current_block();
            cir::BlockId op_block = begin_fragment_block("expr.incdec.op");
            syntax::BinaryOperator binary_op =
                op == syntax::UnaryOperator::PrefixIncrement ||
                op == syntax::UnaryOperator::PostfixIncrement
                    ? syntax::BinaryOperator::Add
                    : syntax::BinaryOperator::Sub;
            cir::InstId new_value =
                builder_.binary(binary_op_kind(binary_op), object_type, old_value, one, loc);
            cir::Fragment op_fragment = finish_fragment_block(op_block, previous);

            previous = builder_.current_block();
            cir::BlockId store_block = begin_fragment_block("expr.incdec.store");
            builder_.store(place.place, new_value, loc);
            cir::Fragment store_fragment = finish_fragment_block(store_block, previous);

            cir::Fragment fragment = chain(std::move(place.fragment), std::move(load_fragment), loc);
            fragment = chain(std::move(fragment), std::move(one_fragment), loc);
            fragment = chain(std::move(fragment), std::move(op_fragment), loc);
            fragment = chain(std::move(fragment), std::move(store_fragment), loc);

            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = is_postfix_increment_or_decrement(op) ? old_value : new_value;
            bool cxx_prefix_lvalue =
                lang_opts_.is_cxx_mode() &&
                !is_postfix_increment_or_decrement(op);
            result.place = cxx_prefix_lvalue ? place.place : cir::InstId{};
            result.type = object_type;
            result.category = cxx_prefix_lvalue
                ? ValueCategory::LValue
                : ValueCategory::PrValue;
            result.has_error = place.has_error;
            return result;
        }
        case syntax::UnaryOperator::AddressOf: {
            if (operand.destructor_designator) {
                report_error("cannot take the address of a destructor", loc);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("expr.addr_of.error");
                cir::InstId value =
                    builder_.error("address of destructor", loc);
                cir::Fragment error_fragment =
                    finish_fragment_block(block, previous);
                operand.fragment = chain(std::move(operand.fragment),
                                         std::move(error_fragment), loc);
                operand.value = value;
                operand.type = builder_.unknown_type();
                operand.category = ValueCategory::PrValue;
                operand.has_error = true;
                return operand;
            }
            if (operand.category == ValueCategory::Type) {
                bool constructor_name = false;
                cir::TypeId type = file_.resolved_type(operand.type);
                if (operand.qualified_name && file_.valid(type) &&
                    file_.type(type).kind == cir::TypeKind::Record) {
                    cir::EntityId record = file_.record_entity(type);
                    constructor_name = record.valid() && file_.valid(record) &&
                        file_.entity(record).name.valid() &&
                        file_.name(file_.entity(record).name) == operand.name;
                }
                report_error(constructor_name
                                 ? "cannot take the address of a constructor"
                                 : "cannot take the address of a type",
                             loc);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("expr.addr_of.error");
                cir::InstId value =
                    builder_.error("address of type", loc);
                cir::Fragment error_fragment =
                    finish_fragment_block(block, previous);
                operand.fragment = chain(std::move(operand.fragment),
                                         std::move(error_fragment), loc);
                operand.value = value;
                operand.type = builder_.unknown_type();
                operand.category = ValueCategory::PrValue;
                operand.has_error = true;
                return operand;
            }
            if (operand.category == ValueCategory::QualifiedMember &&
                operand.entity.valid() &&
                file_.valid(operand.entity) &&
                file_.entity(operand.entity).kind == cir::EntityKind::Field) {
                const cir::RecordFieldFact* field_fact =
                    file_.field_fact(operand.entity);
                if (field_fact && field_fact->is_bitfield) {
                    report_error("cannot form pointer to bit-field", loc);
                    operand.has_error = true;
                }
                cir::EntityId record_entity =
                    file_.entity(operand.entity).declaring_record.valid()
                        ? file_.entity(operand.entity).declaring_record
                        : file_.entity(operand.entity).parent;
                if (field_fact &&
                    field_fact->declared_access ==
                        cir::RecordMemberAccess::Protected &&
                    operand.qualified_member_owner.valid() &&
                    !protected_member_object_access_allowed(
                        record_entity,
                        operand.qualified_member_owner)) {
                    report_error(
                        "a protected member pointer must be formed through "
                        "the granting class or one derived from it",
                        loc);
                    operand.has_error = true;
                }
                ExprResult result;
                result.fragment = std::move(operand.fragment);
                result.entity = operand.entity;
                result.name = operand.name;
                cir::TypeId designating_class =
                    operand.qualified_member_owner.valid()
                        ? operand.qualified_member_owner
                        : (file_.valid(record_entity)
                               ? file_.entity(record_entity).type
                               : builder_.unknown_type());
                result.type = member_pointer_type(
                    type_ref(designating_class),
                    type_ref(file_.entity(operand.entity).type));
                result.category = ValueCategory::MemberPointerDesignator;
                result.qualified_member_owner =
                    operand.qualified_member_owner;
                result.value_dependent = operand_value_dependent;
                result.has_error = operand.has_error;
                return result;
            }
            if (operand.category == ValueCategory::FunctionDesignator &&
                (!operand.candidates.empty() ||
                 (operand.entity.valid() &&
                  template_info(operand.entity) != nullptr))) {

                operand.overload_designator =
                    canonical_overload_designator(operand,
                                                  /*address_of_written=*/true);
                operand.type = {};
                operand.category = ValueCategory::OverloadDesignator;
                operand.value_dependent = operand_value_dependent;
                return operand;
            }
            if (operand.category == ValueCategory::FunctionDesignator &&
                operand.qualified_name &&
                operand.entity.valid() &&
                file_.valid(operand.entity) &&
                file_.entity(operand.entity).kind == cir::EntityKind::Method) {
                const cir::RecordMethodFact* method_fact =
                    file_.method_fact(operand.entity);
                if (method_fact && !method_fact->is_static) {
                    cir::EntityId record_entity =
                        file_.entity(operand.entity).parent;
                    ExprResult result;
                    result.fragment = std::move(operand.fragment);
                    result.entity = operand.entity;
                    result.name = operand.name;
                    result.explicit_template_arguments =
                        std::move(operand.explicit_template_arguments);
                    result.candidate_explicit_template_arguments =
                        std::move(
                            operand.candidate_explicit_template_arguments);
                    result.qualified_member_owner =
                        operand.qualified_member_owner;
                    result.type = member_pointer_type(
                        type_ref(file_.valid(record_entity)
                                     ? file_.entity(record_entity).type
                                     : builder_.unknown_type()),
                        method_fact->type);
                    result.category = ValueCategory::MemberPointerDesignator;
                    result.value_dependent = operand_value_dependent;
                    result.has_error = operand.has_error;
                    return result;
                }
            }
            if (operand.category == ValueCategory::FunctionDesignator) {

                bool unresolved_set =
                    !operand.candidates.empty() ||
                    !operand.explicit_template_arguments.empty() ||
                    !operand.candidate_explicit_template_arguments.empty();
                if (unresolved_set) {
                    return operand;
                }

                return require_value(std::move(operand), UseContext::RValue,
                                     loc);
            }
            bool operand_was_clean = !operand.has_error;
            ExprResult place = require_place(std::move(operand),
                                             UseContext::LValue, loc);

            bool place_is_error_fallback = operand_was_clean &&
                place.has_error && place.place.valid() &&
                file_.valid(place.place) &&
                file_.inst(place.place).kind == cir::InstKind::Error;
            if (place.category != ValueCategory::LValue ||
                !place.place.valid() || place_is_error_fallback) {
                report_error("cannot take the address of a non-lvalue expression",
                             loc);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("expr.addr_of.error");
                cir::InstId value =
                    builder_.error("address of non-lvalue", loc);
                cir::Fragment error_fragment =
                    finish_fragment_block(block, previous);
                place.fragment = chain(std::move(place.fragment),
                                         std::move(error_fragment), loc);
                place.value = value;
                place.type = builder_.unknown_type();
                place.category = ValueCategory::PrValue;
                place.has_error = true;
                return place;
            }
            if (const cir::RecordFieldFact* field = file_.field_fact(place.entity);
                field && field->is_bitfield) {
                report_error("cannot take address of bit-field", loc);
                place.has_error = true;
            }
            if (file_.valid(place.place)) {
                const cir::Inst& place_inst = file_.inst(place.place);
                if (place_inst.place_fact.valid() &&
                    file_.valid(place_inst.place_fact) &&
                    !file_.place_fact(place_inst.place_fact).addressable) {
                    report_error("cannot take address of non-addressable vector element",
                                 loc);
                    place.has_error = true;
                }
                if (place_inst.place_fact.valid() && file_.valid(place_inst.place_fact)) {
                    cir::EntityId place_entity =
                        file_.place_fact(place_inst.place_fact).entity;
                    if (place_entity.valid() &&
                        file_.entity(place_entity).decl_flags.is_register) {
                        report_error("cannot take the address of a register variable",
                                     loc);
                        place.has_error = true;
                    }
                }
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.addr_of");
            cir::InstId inst = builder_.addr_of(place.place, loc);
            cir::Fragment op_fragment = finish_fragment_block(block, previous);

            ExprResult result;
            result.fragment = chain(std::move(place.fragment), std::move(op_fragment), loc);
            result.value = inst;
            result.type = file_.inst(inst).result_type;
            result.category = ValueCategory::PrValue;
            result.value_dependent = operand_value_dependent;
            result.has_error = place.has_error;
            return result;
        }
        case syntax::UnaryOperator::Dereference: {
            ExprResult value = require_value(std::move(operand), UseContext::RValue, loc);

            cir::TypeId indirect_type = file_.resolved_type(value.type);
            bool valid_indirection = file_.valid(indirect_type) &&
                (file_.type(indirect_type).kind == cir::TypeKind::Pointer ||
                 file_.type(indirect_type).kind ==
                     cir::TypeKind::LValueReference ||
                 file_.type(indirect_type).kind ==
                     cir::TypeKind::RValueReference);
            if (!valid_indirection) {
                if (!value.has_error) {
                    report_error("indirection requires a pointer operand", loc);
                }
                ExprResult result;
                result.fragment = std::move(value.fragment);
                result.type = builder_.unknown_type();
                result.category = ValueCategory::PrValue;
                result.has_error = true;
                return result;
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.deref");
            cir::InstId place = builder_.deref(value.value, loc);
            cir::Fragment op_fragment = finish_fragment_block(block, previous);

            ExprResult result;
            result.fragment = chain(std::move(value.fragment), std::move(op_fragment), loc);
            result.place = place;
            result.type = object_type_from_place(place);
            result.category = ValueCategory::LValue;
            result.direct_dereference_pointer = value.value;
            result.direct_dereference_pointer_type = value.type;
            result.value_dependent = operand_value_dependent;
            result.type_originates_from_template_parameter =
                value.type_originates_from_template_parameter;
            if (operand_value_dependent) {
                result.template_value_expr = template_value_unary_expr(
                    cir::TemplateValueExprOp::Dereference,
                    template_value_operand_expression(value),
                    type_ref(result.type),
                    result.category);
                result.template_value_expr.loc = loc;
                result.template_value_expr.definition_context =
                    current_decl_context();
                result.template_value_expr.definition_lookup_generation =
                    lookup_generation_;
            }
            result.has_error = value.has_error;
            return result;
        }
        case syntax::UnaryOperator::SizeofExpr:
        case syntax::UnaryOperator::SizeofType:
        case syntax::UnaryOperator::AlignofExpr:
        case syntax::UnaryOperator::AlignofType:
        case syntax::UnaryOperator::TypeidExpr:
        case syntax::UnaryOperator::TypeidType:
            break;
        case syntax::UnaryOperator::LabelAddress:
            break;
        case syntax::UnaryOperator::Plus:
        case syntax::UnaryOperator::Minus:
        case syntax::UnaryOperator::LogicalNot:
        case syntax::UnaryOperator::BitwiseNot: {

            ExprResult value = require_value(
                std::move(operand),
                op == syntax::UnaryOperator::LogicalNot
                    ? UseContext::Condition
                    : UseContext::RValue,
                loc);
            cir::TypeId result_type;
            if (op == syntax::UnaryOperator::LogicalNot) {
                result_type = lang_opts_.is_cxx_mode() ? builder_.bool_type()
                                                       : builder_.int_type();
            } else if (is_vector_type(value.type)) {
                cir::TypeId element_type = file_.vector_element_type(value.type);
                if (op == syntax::UnaryOperator::BitwiseNot) {
                    if (!is_integer_type(element_type)) {
                        report_error("bitwise not requires integer vector elements", loc);
                        value.has_error = true;
                    }
                } else if (!is_arithmetic_type(element_type)) {
                    report_error("unary expression requires integer or floating-point vector elements",
                                 loc);
                    value.has_error = true;
                }
                result_type = value.type;
            } else if (op == syntax::UnaryOperator::BitwiseNot) {
                if (is_complex_type(value.type)) {

                    result_type = value.type;
                } else {
                    diagnose_if_not_integer(value.type, loc, "bitwise not");
                    result_type = integer_promotion_type(value.type);
                    value = convert_to_arithmetic_type(std::move(value), result_type, loc);
                }
            } else if (op == syntax::UnaryOperator::Plus &&
                       is_pointer_type(value.type)) {

                value.category = ValueCategory::PrValue;
                value.value_dependent = operand_value_dependent;
                if (value.template_value_expr.valid()) {
                    value.template_value_expr = template_value_unary_expr(
                        cir::TemplateValueExprOp::UnaryPlus,
                        std::move(value.template_value_expr),
                        type_ref(value.type));
                    value.template_value_expr.loc = loc;
                    value.template_value_expr.definition_context =
                        current_decl_context();
                    value.template_value_expr
                        .definition_lookup_generation = lookup_generation_;
                }
                return value;
            } else {
                diagnose_if_not_arithmetic(value.type, loc, "unary expression");
                result_type = is_integer_type(value.type)
                    ? integer_promotion_type(value.type)
                    : value.type;
                value = convert_to_arithmetic_type(std::move(value), result_type, loc);
            }
            if (!result_type.valid()) {
                result_type = builder_.int_type();
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.unary");
            cir::InstId inst = builder_.unary(unary_op_kind(op), result_type, value.value, loc);
            cir::Fragment op_fragment = finish_fragment_block(block, previous);

            ExprResult result;
            result.fragment = chain(std::move(value.fragment), std::move(op_fragment), loc);
            result.value = inst;
            result.type = result_type;
            result.category = ValueCategory::PrValue;
            result.value_dependent = operand_value_dependent;
            if (auto graph_op = template_value_unary_expr_op(op);
                graph_op.has_value() && value.template_value_expr.valid()) {
                result.template_value_expr = template_value_unary_expr(
                    *graph_op,
                    std::move(value.template_value_expr),
                    type_ref(result.type));
                result.template_value_expr.loc = loc;
                result.template_value_expr.definition_context =
                    current_decl_context();
                result.template_value_expr.definition_lookup_generation =
                    lookup_generation_;
            }
            result.has_error = value.has_error;
            return result;
        }
        case syntax::UnaryOperator::Invalid:
            break;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.error");
    cir::InstId inst = builder_.error("invalid unary operator", loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult error;
    error.fragment = std::move(fragment);
    error.value = inst;
    error.type = builder_.unknown_type();
    error.category = ValueCategory::PrValue;
    error.has_error = true;
    return error;
}

ExprResult Session::collect_cast_to_union(cir::TypeId target_type,
                                          cir::TypeId union_type,
                                          ExprResult operand,
                                          SrcLoc loc) {
    ExprResult value = require_value(std::move(operand), UseContext::RValue, loc);

    if (value.type.valid() &&
        types_compatible(file_.type_ref(value.type), file_.type_ref(union_type))) {
        value.type = target_type;
        value.category = ValueCategory::PrValue;
        return value;
    }
    const cir::RecordFacts* facts = file_.record_facts_for_type(union_type);
    if (!facts) {
        report_error("cast to an incomplete union type", loc);
        value.has_error = true;
        value.type = target_type;
        value.category = ValueCategory::PrValue;
        return value;
    }

    cir::TypeRef value_ref = file_.type_ref(value.type);
    std::string member_name;
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.is_flexible_array_member || field.is_base_subobject ||
            field.is_virtual_base_storage || !field.name.valid()) {
            continue;
        }
        if (types_compatible(field.type, value_ref)) {
            member_name = std::string(file_.name(field.name));
            break;
        }
    }
    if (member_name.empty()) {
        report_error("cast to union type from a type not present in the union",
                     loc);
        value.has_error = true;
        value.type = target_type;
        value.category = ValueCategory::PrValue;
        return value;
    }

    InitDesignator designator;
    designator.kind = InitDesignatorKind::Field;
    designator.field_name = member_name;
    designator.loc = loc;

    InitElementInput element;
    element.designators.push_back(std::move(designator));
    element.value = std::move(value);
    element.loc = loc;

    auto init_list = std::make_shared<InitListValue>();
    init_list->elements.push_back(std::move(element));
    init_list->loc = loc;
    init_list->syntax = InitListSyntax::Braced;

    ExprResult init;
    init.category = ValueCategory::InitList;
    init.init_list = std::move(init_list);
    init.type = target_type;
    return collect_compound_literal_expr(target_type, std::move(init), loc);
}

ExprResult Session::collect_cast_expr(cir::TypeId target_type, ExprResult operand, SrcLoc loc) {
    if (in_template_definition() && target_type.valid() &&
        is_dependent_type(target_type)) {

        return make_dependent_expr(std::move(operand), loc);
    }
    if (expr_is_value_dependent(operand)) {

        return make_deferred_conversion_expr(std::move(operand), target_type,
                                             loc);
    }
    if (arc_enabled() && target_type.valid() && operand.type.valid() &&
        arc_check_plain_cast(target_type, operand.type, loc)) {
        operand.has_error = true;
    }
    cir::TypeId resolved_target =
        target_type.valid() ? file_.resolved_type(target_type) : cir::TypeId{};
    if (file_.valid(resolved_target) &&
        (file_.type(resolved_target).kind == cir::TypeKind::LValueReference ||
         file_.type(resolved_target).kind == cir::TypeKind::RValueReference)) {
        cir::ReferenceKind reference_kind =
            file_.type(resolved_target).kind == cir::TypeKind::RValueReference
                ? cir::ReferenceKind::RValue
                : cir::ReferenceKind::LValue;
        cir::TypeRef referred = file_.reference_referred_ref(resolved_target);
        cir::TypeId resolved_referred =
            file_.resolved_type(referred.type);
        bool refers_to_function =
            file_.valid(resolved_referred) &&
            file_.type(resolved_referred).kind == cir::TypeKind::Function;
        ValueCategory result_category =
            reference_kind == cir::ReferenceKind::RValue &&
                    !refers_to_function
                ? ValueCategory::XValue
                : ValueCategory::LValue;
        bool glvalue_with_place =
            (operand.category == ValueCategory::LValue ||
             operand.category == ValueCategory::XValue) &&
            operand.place.valid();
        if (glvalue_with_place) {
            cir::TypeRef object_ref = file_.type_ref(operand.type);
            const cir::Inst& place_inst = file_.inst(operand.place);
            if (place_inst.place_fact.valid()) {
                object_ref = file_.place_fact(place_inst.place_fact).object_type;
            }
            bool same = types_compatible(
                cir::TypeRef{file_.resolved_type(referred.type), cir::QualNone,
                             referred.memory_space},
                cir::TypeRef{file_.resolved_type(object_ref.type), cir::QualNone,
                             object_ref.memory_space});
            std::vector<cir::EntityId> base_path;
            bool base_cast =
                !same && derived_to_base_path(object_ref.type, referred.type, &base_path);
            if (same || base_cast) {
                ExprResult result = std::move(operand);
                if (base_cast) {
                    cir::BlockId previous = builder_.current_block();
                    cir::BlockId block = begin_fragment_block("expr.cast.ref.base");
                    cir::InstId place =
                        emit_subobject_path(result.place, base_path, loc);
                    cir::Fragment fragment = finish_fragment_block(block, previous);
                    result.fragment =
                        chain(std::move(result.fragment), std::move(fragment), loc);
                    result.place = place;
                }
                result.value = {};
                result.type = referred.type.valid() ? referred.type
                                                    : builder_.unknown_type();
                result.entity = {};
                result.name.clear();
                result.candidates.clear();
                result.qualified_name = false;
                result.unparenthesized_id_or_member = false;
                result.category = result_category;
                return result;
            }

            // If neither an identity/base reference conversion nor ordinary
            // reference binding applies, cast notation can still select the
            // reinterpret_cast family ([expr.cast], [expr.reinterpret.cast]).
            // It designates the same object through a pointer to the referred
            // type; no temporary or copy is involved. Keep object and
            // function domains separate here rather than accepting the
            // implementation-defined function/object pointer bridge.
            cir::TypeId resolved_object =
                file_.resolved_type(object_ref.type);
            bool object_is_function =
                file_.valid(resolved_object) &&
                file_.type(resolved_object).kind ==
                    cir::TypeKind::Function;
            bool object_is_record =
                file_.valid(resolved_object) &&
                file_.type(resolved_object).kind ==
                    cir::TypeKind::Record;
            bool target_is_record =
                file_.valid(resolved_referred) &&
                file_.type(resolved_referred).kind ==
                    cir::TypeKind::Record;
            if (!is_void_type(resolved_object) &&
                !is_void_type(resolved_referred) &&
                !object_is_record && !target_is_record &&
                object_is_function == refers_to_function) {
                cir::TypeId target_pointer =
                    builder_.pointer_type(referred);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("expr.cast.ref.reinterpret");
                cir::InstId address =
                    builder_.addr_of(operand.place, loc);
                cir::InstId pointer = builder_.cast(
                    target_pointer, address, "reinterpret_cast", loc);
                cir::InstId place = builder_.deref(pointer, loc);
                cir::Fragment fragment =
                    finish_fragment_block(block, previous);
                operand.fragment = chain(std::move(operand.fragment),
                                         std::move(fragment), loc);
                operand.place = place;
                operand.value = {};
                operand.type = referred.type.valid()
                    ? referred.type
                    : builder_.unknown_type();
                operand.entity = {};
                operand.name.clear();
                operand.candidates.clear();
                operand.qualified_name = false;
                operand.unparenthesized_id_or_member = false;
                operand.category = result_category;
                return operand;
            }
        }

        ExprResult bound = bind_to_reference(std::move(operand), target_type, loc);
        if (!bound.value.valid()) {
            return bound;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.cast.ref");
        cir::InstId place = builder_.deref(bound.value, loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        bound.fragment = chain(std::move(bound.fragment), std::move(fragment), loc);
        bound.place = place;
        bound.value = {};
        bound.type = referred.type.valid() ? referred.type : builder_.unknown_type();
        bound.entity = {};
        bound.name.clear();
        bound.candidates.clear();
        bound.qualified_name = false;
        bound.unparenthesized_id_or_member = false;
        bound.category = result_category;
        return bound;
    }
    if (operand.category == ValueCategory::OverloadDesignator &&
        target_type.valid()) {
        ExprResult converted =
            convert_overload_designator_to_target(std::move(operand),
                                                  target_type,
                                                  loc);
        if (converted.has_error ||
            converted.category != ValueCategory::OverloadDesignator) {
            return cast_if_needed(std::move(converted),
                                  target_type,
                                  "explicit",
                                  loc);
        }
        operand = std::move(converted);
    } else if (operand.category == ValueCategory::FunctionDesignator &&
               target_type.valid()) {
        ExprResult converted =
            convert_function_designator_to_target(std::move(operand),
                                                  target_type,
                                                  loc);
        if (converted.has_error ||
            converted.category != ValueCategory::FunctionDesignator) {
            return cast_if_needed(std::move(converted),
                                  target_type,
                                  "explicit",
                                  loc);
        }
        operand = std::move(converted);
    }
    if (operand.category == ValueCategory::MemberPointerDesignator &&
        target_type.valid()) {
        ExprResult converted =
            convert_member_pointer_designator_to_target(std::move(operand),
                                                        target_type,
                                                        loc);
        if (converted.has_error ||
            converted.category != ValueCategory::MemberPointerDesignator) {
            return cast_if_needed(std::move(converted),
                                  target_type,
                                  "explicit",
                                  loc);
        }
        operand = std::move(converted);
    }

    if (lang_opts_.is_cxx_mode() && target_type.valid() &&
        !operand.has_error && !expr_is_dependent(operand)) {
        cir::TypeId source_resolved = file_.resolved_type(operand.type);
        cir::TypeId cast_target_resolved = file_.resolved_type(target_type);
        bool source_is_record = file_.valid(source_resolved) &&
            file_.type(source_resolved).kind == cir::TypeKind::Record;
        bool cast_target_is_record = file_.valid(cast_target_resolved) &&
            file_.type(cast_target_resolved).kind == cir::TypeKind::Record;
        if (cast_target_is_record &&
            !type_equal(operand.type, target_type)) {
            std::vector<ExprResult> cast_arguments;
            cast_arguments.push_back(std::move(operand));
            return collect_functional_cast(target_type,
                                           std::move(cast_arguments),
                                           loc,
                                           InitListSyntax::Parenthesized,
                                           /*allow_explicit=*/true);
        }
        if (source_is_record && !cast_target_is_record &&
            !is_void_type(cast_target_resolved) &&
            !type_equal(operand.type, target_type)) {
            if (operand.category == ValueCategory::PrValue &&
                operand.value.valid()) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(operand),
                                               /*is_arrow=*/false,
                                               loc);
                operand = std::move(materialized.base_place);
            }
            UserConversionSequence sequence =
                resolve_initialization_user_conversion(
                    operand, target_type,
                    UserConversionContext::DirectInitialization, loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_error("conversion from '" +
                                 file_.format_type(operand.type) + "' to '" +
                                 file_.format_type(target_type) +
                                 "' is ambiguous",
                             loc);
                report_overload_ambiguity_notes(sequence.ambiguity, loc);
            } else if (sequence.kind ==
                       UserConversionSequence::Kind::ConversionFunction) {
                return apply_user_conversion_sequence(
                    std::move(operand), target_type, sequence, loc);
            } else {
                report_error("cannot convert expression of type '" +
                                 file_.format_type(operand.type) + "' to '" +
                                 file_.format_type(target_type) + "'",
                             loc);
            }
            ExprResult error_result;
            error_result.has_error = true;
            error_result.type = target_type;
            error_result.category = ValueCategory::PrValue;
            error_result.fragment = std::move(operand.fragment);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.cast.error");
            error_result.value = builder_.error("class operand cast", loc);
            cir::Fragment error_fragment =
                finish_fragment_block(block, previous);
            error_result.fragment = chain(std::move(error_result.fragment),
                                          std::move(error_fragment),
                                          loc);
            return error_result;
        }
    }

    if (!lang_opts_.is_cxx_mode() && !expr_is_dependent(operand) &&
        file_.valid(resolved_target) &&
        file_.type(resolved_target).kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(resolved_target);
        if (facts && facts->kind == cir::RecordKind::Union &&
            !facts->is_incomplete) {
            return collect_cast_to_union(target_type, resolved_target,
                                         std::move(operand), loc);
        }
    }

    UseContext operand_context =
        (target_type.valid() && is_void_type(target_type))
            ? UseContext::Discard
            : UseContext::RValue;
    ExprResult value = require_value(std::move(operand), operand_context, loc);
    if (!target_type.valid()) {
        target_type = builder_.unknown_type();
    }
    if (is_void_type(target_type) && !value.value.valid()) {

        value.value = {};
        value.place = {};
        value.entity = {};
        value.type = target_type;
        value.category = ValueCategory::PrValue;
        return value;
    }

    const char* cast_kind = "explicit";
    if (target_type.valid() && value.type.valid() &&
        !type_equal(value.type, target_type)) {
        bool from_vec = is_vector_type(value.type);
        bool to_vec = is_vector_type(target_type);
        bool from_ok = from_vec || is_integer_type(value.type) ||
                       is_floating_type(value.type);
        bool to_ok = to_vec || is_integer_type(target_type) ||
                     is_floating_type(target_type);
        if ((from_vec || to_vec) && from_ok && to_ok) {
            auto from_size = size_of_type(value.type, loc);
            auto to_size = size_of_type(target_type, loc);
            if (from_size && to_size && *from_size == *to_size) {
                cast_kind = "vector_reinterpret";
            }
        }
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.cast");
    cir::InstId cast = builder_.cast(target_type, value.value, cast_kind, loc);
    cir::Fragment cast_fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(value.fragment), std::move(cast_fragment), loc);
    result.value = cast;
    result.type = target_type;
    result.category = ValueCategory::PrValue;
    result.has_error = value.has_error;
    return result;
}

ExprResult Session::collect_cpp_named_cast(CppNamedCastKind kind,
                                           cir::TypeId target_type,
                                           ExprResult operand,
                                           SrcLoc loc) {
    if (in_template_definition() && target_type.valid() &&
        is_dependent_type(target_type)) {

        return make_deferred_conversion_expr(std::move(operand), target_type,
                                             loc);
    }
    if (expr_is_value_dependent(operand)) {
        return make_deferred_conversion_expr(std::move(operand), target_type,
                                             loc);
    }

    auto make_error = [&](ExprResult base, std::string message) {
        report_error(message, loc);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.named_cast.error");
        cir::InstId error = builder_.error(message, loc);
        if (target_type.valid()) {
            error = builder_.cast(target_type, error, "error", loc);
        }
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        ExprResult result;
        result.fragment = chain(std::move(base.fragment),
                                std::move(error_fragment), loc);
        result.value = error;
        result.type = target_type.valid() ? target_type : builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    };

    if (operand.has_error) {
        return make_error(std::move(operand), "named cast operand is invalid");
    }
    if (!target_type.valid()) {
        return make_error(std::move(operand),
                          "named cast requires a valid target type");
    }

    cir::TypeId resolved_target = file_.resolved_type(target_type);
    if (!file_.valid(resolved_target)) {
        return make_error(std::move(operand),
                          "named cast requires a valid target type");
    }
    cir::TypeKind target_kind = file_.type(resolved_target).kind;

    auto place_object_ref = [&](const ExprResult& expr) {
        cir::TypeRef object_ref = file_.type_ref(expr.type);
        if (expr.place.valid()) {
            const cir::Inst& place_inst = file_.inst(expr.place);
            if (place_inst.place_fact.valid()) {
                object_ref = file_.place_fact(place_inst.place_fact).object_type;
            }
        }
        object_ref.type = file_.resolved_type(object_ref.type);
        return object_ref;
    };

    auto reference_category = [&](cir::TypeId reference_type) {
        cir::TypeId resolved = file_.resolved_type(reference_type);
        cir::TypeRef referred = file_.reference_referred_ref(resolved);
        if (file_.type(resolved).kind == cir::TypeKind::LValueReference ||
            is_function_type(file_, referred.type)) {
            return ValueCategory::LValue;
        }
        return ValueCategory::XValue;
    };

    auto finish_reference_result = [&](ExprResult base,
                                       cir::InstId place,
                                       cir::TypeId reference_type) {
        cir::TypeId resolved = file_.resolved_type(reference_type);
        cir::TypeRef referred = file_.reference_referred_ref(resolved);
        base.place = place;
        base.value = {};
        base.type = referred.type.valid() ? referred.type
                                          : builder_.unknown_type();
        base.entity = {};
        base.name.clear();
        base.candidates.clear();
        base.qualified_name = false;
        base.unparenthesized_id_or_member = false;
        base.category = reference_category(reference_type);
        return base;
    };

    auto static_path_offset = [&](const std::vector<cir::EntityId>& path,
                                  int64_t* offset_out) {
        int64_t offset = 0;
        for (cir::EntityId step : path) {
            const cir::RecordFieldFact* fact = file_.field_fact(step);
            if (!fact) {
                return false;
            }
            if (fact->is_virtual_base_storage) {
                return false;
            }

            if (!member_access_allowed(file_.entity(step).parent,
                                       fact->declared_access)) {
                return false;
            }
            offset += static_cast<int64_t>(fact->offset);
        }
        if (offset_out) {
            *offset_out = offset;
        }
        return true;
    };

    auto null_pointer_value = [&](cir::TypeId pointer_type) {
        cir::InstId null = builder_.nullptr_literal("nullptr", loc);
        return builder_.cast(pointer_type, null, "nullptr", loc);
    };

    auto adjust_pointer_by_offset = [&](ExprResult value,
                                        cir::TypeId result_type,
                                        int64_t offset,
                                        std::string_view cast_payload) {
        if (offset == 0) {
            return cast_if_needed(std::move(value), result_type, cast_payload, loc);
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId entry = begin_fragment_block("expr.named_cast.ptr.check");
        cir::InstId source_null = null_pointer_value(value.type);
        cir::InstId is_null = builder_.binary(cir::BinaryOpKind::Equal,
                                              builder_.bool_type(),
                                              value.value,
                                              source_null,
                                              loc);
        cir::Fragment fragment = finish_fragment_block(entry, previous);

        cir::BlockId null_block =
            builder_.create_detached_block("expr.named_cast.ptr.null");
        cir::BlockId adjust_block =
            builder_.create_detached_block("expr.named_cast.ptr.adjust");
        cir::BlockId merge_block =
            builder_.create_detached_block("expr.named_cast.ptr.merge");
        cir::InstId merge_value =
            builder_.add_block_parameter(merge_block,
                                         result_type,
                                         ".named.cast.ptr",
                                         loc);
        builder_.cond_branch_from(fragment.exit,
                                  is_null,
                                  null_block,
                                  adjust_block,
                                  {},
                                  loc);

        builder_.switch_to_block(null_block);
        cir::InstId result_null = null_pointer_value(result_type);
        builder_.branch(merge_block, {result_null}, loc);

        builder_.switch_to_block(adjust_block);
        cir::TypeId usize = builder_.usize_type();
        cir::InstId raw = builder_.cast(usize, value.value, "value", loc);
        int64_t magnitude = offset < 0 ? -offset : offset;
        cir::InstId delta = builder_.integer_literal(
            magnitude, usize, std::to_string(magnitude), loc);
        cir::InstId adjusted_raw = builder_.binary(
            offset < 0 ? cir::BinaryOpKind::Sub : cir::BinaryOpKind::Add,
            usize,
            raw,
            delta,
            loc);
        cir::InstId adjusted =
            builder_.cast(result_type, adjusted_raw, cast_payload, loc);
        builder_.branch(merge_block, {adjusted}, loc);

        builder_.switch_to_block(previous);
        append_fragment_blocks(fragment, builder_.block_fragment(null_block));
        append_fragment_blocks(fragment, builder_.block_fragment(adjust_block));
        append_fragment_blocks(fragment, builder_.block_fragment(merge_block));
        fragment.exit = merge_block;

        value.fragment = chain(std::move(value.fragment), std::move(fragment), loc);
        value.value = merge_value;
        value.type = result_type;
        value.category = ValueCategory::PrValue;
        return value;
    };

    auto adjust_reference_by_offset = [&](ExprResult base,
                                          cir::TypeId reference_type,
                                          int64_t offset,
                                          std::string_view cast_payload) {
        cir::TypeRef referred =
            file_.reference_referred_ref(file_.resolved_type(reference_type));
        cir::TypeId result_pointer =
            builder_.pointer_type(file_.type_ref(referred.type));
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.named_cast.ref.adjust");
        cir::InstId address = builder_.addr_of(base.place, loc);
        cir::InstId raw = builder_.cast(builder_.usize_type(), address,
                                        "value", loc);
        int64_t magnitude = offset < 0 ? -offset : offset;
        cir::InstId delta = builder_.integer_literal(
            magnitude, builder_.usize_type(), std::to_string(magnitude), loc);
        cir::InstId adjusted_raw = builder_.binary(
            offset < 0 ? cir::BinaryOpKind::Sub : cir::BinaryOpKind::Add,
            builder_.usize_type(),
            raw,
            delta,
            loc);
        cir::InstId pointer =
            builder_.cast(result_pointer, adjusted_raw, cast_payload, loc);
        cir::InstId place = builder_.deref(pointer, loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        base.fragment = chain(std::move(base.fragment), std::move(fragment), loc);
        return finish_reference_result(std::move(base), place, reference_type);
    };

    auto typeinfo_pointer = [&](cir::EntityId typeinfo) {
        cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
        cir::InstId place = builder_.global_place(typeinfo, loc);
        cir::InstId address = builder_.addr_of(place, loc);
        return builder_.cast(void_ptr, address, "value", loc);
    };

    auto dynamic_cast_runtime = [&]() {
        cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
        cir::TypeId usize = builder_.usize_type();
        return runtime_function(
            "__dynamic_cast",
            function_type(file_.type_ref(void_ptr),
                          {file_.type_ref(void_ptr),
                           file_.type_ref(void_ptr),
                           file_.type_ref(void_ptr),
                           file_.type_ref(usize)},
                          false,
                          true),
            loc);
    };

    auto bad_cast_runtime = [&]() {
        cir::TypeId void_type = builder_.void_type();
        cir::EntityId bad_cast = runtime_function(
            "__cxa_bad_cast",
            function_type(file_.type_ref(void_type), {}, false, true),
            loc);
        file_.entity_mut(bad_cast).attr_facts.is_noreturn = true;
        return bad_cast;
    };

    auto call_dynamic_cast = [&](cir::InstId source_address,
                                 cir::TypeId source_object,
                                 cir::TypeId target_object) {
        cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
        cir::EntityId source_typeinfo =
            typeinfo_entity_for_type(file_.type_ref(source_object), loc);
        cir::EntityId target_typeinfo =
            typeinfo_entity_for_type(file_.type_ref(target_object), loc);
        if (!source_typeinfo.valid() || !target_typeinfo.valid()) {
            return cir::InstId{};
        }
        cir::InstId source_void =
            builder_.cast(void_ptr, source_address, "value", loc);
        cir::InstId src = typeinfo_pointer(source_typeinfo);
        cir::InstId dst = typeinfo_pointer(target_typeinfo);
        cir::InstId hint =
            builder_.integer_literal(-1, builder_.usize_type(), "-1", loc);
        return builder_.call(dynamic_cast_runtime(),
                             void_ptr,
                             {source_void, src, dst, hint},
                             loc);
    };

    auto recover_complete_object_pointer = [&](ExprResult value) {
        const auto* source_pointer = pointer_payload(file_, value.type);
        if (!source_pointer) {
            return make_error(std::move(value),
                              "dynamic_cast<void*> requires a pointer operand");
        }
        cir::TypeId source_object =
            file_.resolved_type(source_pointer->pointee.type);
        std::vector<cir::EntityId> vptr_path;
        if (!vptr_field_path(source_object, &vptr_path)) {
            return make_error(std::move(value),
                              "dynamic_cast<void*> requires a polymorphic source type");
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId entry = begin_fragment_block("expr.dynamic_cast.void.check");
        cir::InstId source_null = null_pointer_value(value.type);
        cir::InstId is_null = builder_.binary(cir::BinaryOpKind::Equal,
                                              builder_.bool_type(),
                                              value.value,
                                              source_null,
                                              loc);
        cir::Fragment fragment = finish_fragment_block(entry, previous);

        cir::BlockId null_block =
            builder_.create_detached_block("expr.dynamic_cast.void.null");
        cir::BlockId recover_block =
            builder_.create_detached_block("expr.dynamic_cast.void.recover");
        cir::BlockId merge_block =
            builder_.create_detached_block("expr.dynamic_cast.void.merge");
        cir::InstId merge_value =
            builder_.add_block_parameter(merge_block,
                                         target_type,
                                         ".dynamic.cast.void",
                                         loc);
        builder_.cond_branch_from(fragment.exit,
                                  is_null,
                                  null_block,
                                  recover_block,
                                  {},
                                  loc);

        builder_.switch_to_block(null_block);
        builder_.branch(merge_block, {null_pointer_value(target_type)}, loc);

        builder_.switch_to_block(recover_block);
        cir::TypeId usize = builder_.usize_type();
        cir::InstId object_place = builder_.deref(value.value, loc);
        cir::InstId vptr_place = object_place;
        for (cir::EntityId step : vptr_path) {
            vptr_place = builder_.field_addr(vptr_place, step,
                                             file_.entity(step).type, loc);
        }
        cir::InstId vptr = builder_.lvalue_to_rvalue(vptr_place, loc);
        cir::InstId vptr_raw = builder_.cast(usize, vptr, "value", loc);
        cir::InstId offset_to_top_slot = builder_.binary(
            cir::BinaryOpKind::Sub,
            usize,
            vptr_raw,
            builder_.integer_literal(16, usize, "16", loc),
            loc);
        cir::InstId offset_pointer =
            builder_.cast(builder_.pointer_type(usize),
                          offset_to_top_slot,
                          "value",
                          loc);
        cir::InstId offset_place = builder_.deref(offset_pointer, loc);
        cir::InstId offset_to_top = builder_.lvalue_to_rvalue(offset_place, loc);
        cir::InstId object_raw = builder_.cast(usize, value.value, "value", loc);
        cir::InstId top_raw = builder_.binary(cir::BinaryOpKind::Add,
                                              usize,
                                              object_raw,
                                              offset_to_top,
                                              loc);
        cir::InstId top_pointer =
            builder_.cast(target_type, top_raw, "dynamic_cast", loc);
        builder_.branch(merge_block, {top_pointer}, loc);

        builder_.switch_to_block(previous);
        append_fragment_blocks(fragment, builder_.block_fragment(null_block));
        append_fragment_blocks(fragment, builder_.block_fragment(recover_block));
        append_fragment_blocks(fragment, builder_.block_fragment(merge_block));
        fragment.exit = merge_block;

        value.fragment = chain(std::move(value.fragment), std::move(fragment), loc);
        value.value = merge_value;
        value.type = target_type;
        value.category = ValueCategory::PrValue;
        return value;
    };

    auto perform_static_reference_cast = [&](ExprResult source) -> ExprResult {
        if (target_kind != cir::TypeKind::LValueReference &&
            target_kind != cir::TypeKind::RValueReference) {
            return make_error(std::move(source),
                              "static_cast target is not a reference type");
        }
        cir::TypeRef target_referred =
            file_.reference_referred_ref(resolved_target);
        bool glvalue_with_place =
            (source.category == ValueCategory::LValue ||
             source.category == ValueCategory::XValue) &&
            source.place.valid();
        if (glvalue_with_place) {
            cir::TypeRef source_ref = place_object_ref(source);
            if (!qualifiers_preserved_in_similar_type(file_,
                                                      source_ref,
                                                      target_referred) &&
                same_unqualified_type(file_, source_ref.type,
                                      target_referred.type)) {
                return make_error(std::move(source),
                                  "static_cast cannot cast away qualifiers");
            }
            if (same_unqualified_type(file_, source_ref.type,
                                      target_referred.type)) {
                return finish_reference_result(std::move(source),
                                               source.place,
                                               target_type);
            }
            DerivedToBasePathResult up_result =
                analyze_derived_to_base_path(source_ref.type,
                                             target_referred.type);
            if (up_result.kind == DerivedToBasePathKind::Ambiguous) {
                return make_error(
                    std::move(source),
                    "ambiguous conversion from derived class '" +
                        file_.format_type(source_ref.type) +
                        "' to base class '" +
                        file_.format_type(target_referred.type) + "'");
            }
            if (up_result.kind == DerivedToBasePathKind::Unique) {

                if (!check_base_path_access(up_result.path, source_ref.type,
                                            target_referred.type, loc)) {
                    source.has_error = true;
                }
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("expr.static_cast.ref.up");
                cir::InstId place =
                    emit_subobject_path(source.place, up_result.path, loc);
                cir::Fragment fragment = finish_fragment_block(block, previous);
                source.fragment =
                    chain(std::move(source.fragment), std::move(fragment), loc);
                return finish_reference_result(std::move(source), place, target_type);
            }
            DerivedToBasePathResult down_result =
                analyze_derived_to_base_path(target_referred.type,
                                             source_ref.type);
            if (down_result.kind == DerivedToBasePathKind::Ambiguous) {
                return make_error(
                    std::move(source),
                    "invalid static_cast through an ambiguous base class");
            }
            if (down_result.kind == DerivedToBasePathKind::Unique) {
                int64_t offset = 0;
                if (!static_path_offset(down_result.path, &offset)) {
                    return make_error(
                        std::move(source),
                        "invalid static_cast between reference types across virtual or inaccessible base class");
                }
                return adjust_reference_by_offset(std::move(source),
                                                  target_type,
                                                  -offset,
                                                  "static_cast");
            }
        }
        return collect_cast_expr(target_type, std::move(source), loc);
    };

    if (kind == CppNamedCastKind::Const) {
        if (target_kind == cir::TypeKind::LValueReference ||
            target_kind == cir::TypeKind::RValueReference) {
            cir::TypeRef target_referred =
                file_.reference_referred_ref(resolved_target);
            bool glvalue_with_place =
                (operand.category == ValueCategory::LValue ||
                 operand.category == ValueCategory::XValue) &&
                operand.place.valid();
            if (!glvalue_with_place) {
                return make_error(std::move(operand),
                                  "const_cast reference target requires a glvalue operand");
            }
            cir::TypeRef source_ref = place_object_ref(operand);
            if (is_function_type(file_, source_ref.type) ||
                is_function_type(file_, target_referred.type)) {
                return make_error(std::move(operand),
                                  "const_cast cannot be used with function types");
            }
            if (!similar_types_ignoring_cv(file_, source_ref, target_referred)) {
                return make_error(std::move(operand),
                                  "const_cast target type is not similar to source type");
            }

            cir::TypeId target_pointer =
                builder_.pointer_type(target_referred);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("expr.const_cast.ref");
            cir::InstId address = builder_.addr_of(operand.place, loc);
            cir::InstId pointer =
                builder_.cast(target_pointer, address, "const_cast", loc);
            cir::InstId place = builder_.deref(pointer, loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            operand.fragment =
                chain(std::move(operand.fragment), std::move(fragment), loc);
            return finish_reference_result(std::move(operand),
                                           place,
                                           target_type);
        }

        ExprResult value = require_value(std::move(operand), UseContext::RValue, loc);
        bool pointer_target = pointer_payload(file_, resolved_target) != nullptr;
        bool member_pointer_target =
            member_pointer_payload(file_, resolved_target) != nullptr;
        if (!pointer_target && !member_pointer_target) {
            return make_error(std::move(value),
                              "const_cast requires pointer, reference, or pointer-to-member target type");
        }
        cir::TypeId source_resolved = file_.resolved_type(value.type);
        if (pointer_target) {
            if (!pointer_payload(file_, source_resolved)) {
                return make_error(std::move(value),
                                  "const_cast requires pointer operand types");
            }
            if (pointer_points_to_function(file_, source_resolved) ||
                pointer_points_to_function(file_, resolved_target)) {
                return make_error(std::move(value),
                                  "const_cast cannot be used with function pointer types");
            }
            if (!similar_types_ignoring_cv(file_,
                                           file_.type_ref(source_resolved),
                                           file_.type_ref(resolved_target))) {
                return make_error(std::move(value),
                                  "const_cast target type is not similar to source type");
            }
        } else {
            if (!member_pointer_payload(file_, source_resolved)) {
                return make_error(std::move(value),
                                  "const_cast requires pointer-to-member operand types");
            }
            if (member_pointer_points_to_function(file_, source_resolved) ||
                member_pointer_points_to_function(file_, resolved_target)) {
                return make_error(std::move(value),
                                  "const_cast cannot be used with member function pointer types");
            }
            if (!similar_types_ignoring_cv(file_,
                                           file_.type_ref(source_resolved),
                                           file_.type_ref(resolved_target))) {
                return make_error(std::move(value),
                                  "const_cast target type is not similar to source type");
            }
        }
        return cast_if_needed(std::move(value), target_type, "const_cast", loc);
    }

    if (kind == CppNamedCastKind::Reinterpret) {
        if (target_kind == cir::TypeKind::LValueReference ||
            target_kind == cir::TypeKind::RValueReference) {
            cir::TypeRef target_referred =
                file_.reference_referred_ref(resolved_target);
            bool glvalue_with_place =
                (operand.category == ValueCategory::LValue ||
                 operand.category == ValueCategory::XValue) &&
                operand.place.valid();
            if (!glvalue_with_place) {
                return make_error(std::move(operand),
                                  "reinterpret_cast reference target requires a glvalue operand");
            }
            cir::TypeRef source_ref = place_object_ref(operand);
            if (!qualifiers_preserved_in_similar_type(file_,
                                                      source_ref,
                                                      target_referred) &&
                similar_types_ignoring_cv(file_, source_ref, target_referred)) {
                return make_error(std::move(operand),
                                  "reinterpret_cast cannot cast away qualifiers");
            }
            if (is_void_type_for_cast(file_, source_ref.type) ||
                is_void_type_for_cast(file_, target_referred.type)) {
                return make_error(std::move(operand),
                                  "reinterpret_cast reference target cannot be void");
            }
            cir::TypeId target_pointer =
                builder_.pointer_type(file_.type_ref(target_referred.type));
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.reinterpret_cast.ref");
            cir::InstId address = builder_.addr_of(operand.place, loc);
            cir::InstId pointer =
                builder_.cast(target_pointer, address, "reinterpret_cast", loc);
            cir::InstId place = builder_.deref(pointer, loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            operand.fragment =
                chain(std::move(operand.fragment), std::move(fragment), loc);
            return finish_reference_result(std::move(operand),
                                           place,
                                           target_type);
        }

        ExprResult value = require_value(std::move(operand), UseContext::RValue, loc);
        cir::TypeId source = file_.resolved_type(value.type);
        bool source_pointer = pointer_payload(file_, source) != nullptr ||
                              block_pointer_payload(file_, source) != nullptr;
        bool target_pointer = pointer_payload(file_, resolved_target) != nullptr ||
                              block_pointer_payload(file_, resolved_target) != nullptr;
        bool source_member = member_pointer_payload(file_, source) != nullptr;
        bool target_member = member_pointer_payload(file_, resolved_target) != nullptr;
        bool source_nullptr = is_nullptr_type(source);
        bool target_nullptr = is_nullptr_type(resolved_target);
        bool source_integer = is_integer_type(source);
        bool target_integer = is_integer_type(resolved_target);
        bool allowed = false;
        if (target_nullptr) {
            return make_error(
                std::move(value),
                "reinterpret_cast cannot convert to std::nullptr_t");
        }
        if (type_equal(source, resolved_target)) {
            allowed = true;
        } else if (source_pointer && target_pointer) {
            if (similar_types_ignoring_cv(file_,
                                          file_.type_ref(source),
                                          file_.type_ref(resolved_target)) &&
                !qualifiers_preserved_in_similar_type(
                    file_, file_.type_ref(source),
                    file_.type_ref(resolved_target))) {
                return make_error(std::move(value),
                                  "reinterpret_cast cannot cast away qualifiers");
            }
            allowed = true;
        } else if (source_pointer && target_integer) {
            uint16_t pointer_bits =
                static_cast<uint16_t>(file_.target_info().pointer_width);
            cir::IntegerTypeShape target_shape =
                cir::integer_shape_for_type(file_, resolved_target);
            if (target_shape.bit_width != 0 &&
                target_shape.bit_width < pointer_bits) {
                return make_error(
                    std::move(value),
                    "reinterpret_cast from pointer to smaller integer type loses information");
            }
            allowed = true;
        } else if (source_nullptr && target_integer) {
            uint16_t pointer_bits =
                static_cast<uint16_t>(file_.target_info().pointer_width);
            cir::IntegerTypeShape target_shape =
                cir::integer_shape_for_type(file_, resolved_target);
            if (target_shape.bit_width != 0 &&
                target_shape.bit_width < pointer_bits) {
                return make_error(
                    std::move(value),
                    "reinterpret_cast from nullptr_t to smaller integer type loses information");
            }
            allowed = true;
        } else if (source_integer && target_pointer) {
            allowed = true;
        } else if (source_member && target_member) {
            const auto* source_member_payload = member_pointer_payload(file_, source);
            const auto* target_member_payload =
                member_pointer_payload(file_, resolved_target);
            bool source_function = source_member_payload &&
                is_function_type(file_, source_member_payload->member_type.type);
            bool target_function = target_member_payload &&
                is_function_type(file_, target_member_payload->member_type.type);
            allowed = source_function == target_function;
        }
        if (!allowed) {
            return make_error(std::move(value),
                              "invalid operands to reinterpret_cast");
        }
        return cast_if_needed(std::move(value),
                              target_type,
                              "reinterpret_cast",
                              loc);
    }

    if (kind == CppNamedCastKind::Static) {
        if (target_kind == cir::TypeKind::LValueReference ||
            target_kind == cir::TypeKind::RValueReference) {
            cir::TypeId source_type = file_.resolved_type(operand.type);
            if (file_.valid(source_type) &&
                file_.type(source_type).kind == cir::TypeKind::Record) {
                if (operand.category == ValueCategory::PrValue &&
                    operand.value.valid()) {
                    MemberAccessBase materialized =
                        collect_member_access_base(std::move(operand),
                                                   /*is_arrow=*/false, loc);
                    operand = std::move(materialized.base_place);
                }
                UserConversionSequence sequence =
                    resolve_initialization_user_conversion(
                        operand, target_type,
                        UserConversionContext::DirectReferenceBinding, loc);
                if (sequence.kind ==
                    UserConversionSequence::Kind::Ambiguous) {
                    report_overload_ambiguity_notes(sequence.ambiguity, loc);
                    return make_error(std::move(operand),
                                      "static_cast conversion is ambiguous");
                }
                if (sequence.kind ==
                    UserConversionSequence::Kind::ConversionFunction) {
                    ExprResult converted = apply_user_conversion_sequence(
                        std::move(operand), target_type, sequence, loc);
                    if (converted.value.valid()) {
                        cir::BlockId previous = builder_.current_block();
                        cir::BlockId block =
                            begin_fragment_block("expr.static_cast.ref.user");
                        cir::InstId place = builder_.deref(converted.value, loc);
                        cir::Fragment fragment =
                            finish_fragment_block(block, previous);
                        converted.fragment = chain(
                            std::move(converted.fragment),
                            std::move(fragment), loc);
                        return finish_reference_result(
                            std::move(converted), place, target_type);
                    }
                    return converted;
                }
            }
            return perform_static_reference_cast(std::move(operand));
        }
        if (is_void_type(target_type)) {
            ExprResult value =
                require_value(std::move(operand), UseContext::Discard, loc);
            value.value = {};
            value.type = target_type;
            value.category = ValueCategory::PrValue;
            return value;
        }
        if (is_record_type(file_, resolved_target)) {
            std::vector<ExprResult> args;
            args.push_back(std::move(operand));
            return collect_functional_cast(target_type, std::move(args), loc);
        }
        cir::TypeId operand_type = file_.resolved_type(operand.type);
        if (file_.valid(operand_type) &&
            file_.type(operand_type).kind == cir::TypeKind::Record) {
            std::string source_name = file_.format_type(operand.type);
            std::string target_name = file_.format_type(target_type);
            if (operand.category == ValueCategory::PrValue &&
                operand.value.valid()) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(operand),
                                               /*is_arrow=*/false, loc);
                operand = std::move(materialized.base_place);
            }
            UserConversionSequence sequence =
                resolve_initialization_user_conversion(
                    operand, target_type,
                    UserConversionContext::DirectInitialization, loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_overload_ambiguity_notes(sequence.ambiguity, loc);
                return make_error(std::move(operand),
                                  "static_cast conversion is ambiguous");
            }
            if (sequence.kind ==
                UserConversionSequence::Kind::ConversionFunction) {
                return apply_user_conversion_sequence(
                    std::move(operand), target_type, sequence, loc);
            }

            return make_error(std::move(operand),
                              "cannot convert expression of type '" +
                                  source_name + "' to '" + target_name + "'");
        }
        ExprResult value = require_value(std::move(operand), UseContext::RValue, loc);
        cir::TypeId source = file_.resolved_type(value.type);
        const auto* target_pointer = pointer_payload(file_, resolved_target);
        const auto* source_pointer = pointer_payload(file_, source);
        const auto* target_member = member_pointer_payload(file_, resolved_target);
        const auto* source_member = member_pointer_payload(file_, source);
        bool source_scoped_enum = is_scoped_enum_type(source);
        bool source_enum = file_.valid(source) &&
                           file_.type(source).kind == cir::TypeKind::Enum;
        bool target_enum = file_.valid(resolved_target) &&
                           file_.type(resolved_target).kind == cir::TypeKind::Enum;
        if ((source_scoped_enum &&
             (is_integer_type(resolved_target) ||
              is_floating_type(resolved_target) || target_enum)) ||
            (target_enum &&
             (is_integer_type(source) || is_floating_type(source) ||
              source_enum))) {
            return cast_if_needed(std::move(value),
                                  target_type,
                                  "static_cast",
                                  loc);
        }
        if (target_pointer) {
            if (source_pointer) {
                if (!qualifiers_preserved_in_similar_type(
                        file_, source_pointer->pointee,
                        target_pointer->pointee) &&
                    (similar_types_ignoring_cv(file_,
                                               source_pointer->pointee,
                                               target_pointer->pointee) ||
                     is_void_type_for_cast(file_, source_pointer->pointee.type) ||
                     is_void_type_for_cast(file_, target_pointer->pointee.type))) {
                    return make_error(std::move(value),
                                      "static_cast cannot cast away qualifiers");
                }
                if (is_void_type_for_cast(file_, source_pointer->pointee.type) ||
                    is_void_type_for_cast(file_, target_pointer->pointee.type) ||
                    same_unqualified_type(file_,
                                          source_pointer->pointee.type,
                                          target_pointer->pointee.type)) {
                    return cast_if_needed(std::move(value),
                                          target_type,
                                          "static_cast",
                                          loc);
                }
                auto require_complete_cast_record =
                    [&](cir::TypeId candidate) {
                        cir::TypeId resolved = file_.resolved_type(candidate);
                        if (!file_.valid(resolved) ||
                            file_.type(resolved).kind !=
                                cir::TypeKind::Record) {
                            return InstantiationDemandResult::Satisfied;
                        }
                        return require_complete_class_type_result(
                            resolved,
                            loc,
                            cir::InstantiationDemandKind::CompleteClass);
                    };
                for (cir::TypeId candidate : {
                         source_pointer->pointee.type,
                         target_pointer->pointee.type}) {
                    InstantiationDemandResult completion =
                        require_complete_cast_record(candidate);
                    if (completion ==
                        InstantiationDemandResult::Satisfied) {
                        continue;
                    }
                    if (completion ==
                            InstantiationDemandResult::Unavailable &&
                        template_replay_outcome_) {
                        cir::EntityId blocker = file_.record_entity(
                            file_.resolved_type(candidate));
                        template_replay_outcome_->note_unavailable(blocker);
                        return make_deferred_conversion_expr(
                            std::move(value), target_type, loc);
                    }
                    return make_error(
                        std::move(value),
                        "static_cast between class pointer types requires complete classes");
                }
                DerivedToBasePathResult up_result =
                    analyze_derived_to_base_path(source_pointer->pointee.type,
                                                 target_pointer->pointee.type);
                if (up_result.kind == DerivedToBasePathKind::Ambiguous) {
                    return make_error(
                        std::move(value),
                        "ambiguous conversion from derived class '" +
                            file_.format_type(source_pointer->pointee.type) +
                            "' to base class '" +
                            file_.format_type(target_pointer->pointee.type) + "'");
                }
                if (up_result.kind == DerivedToBasePathKind::Unique) {
                    if ((source_pointer->pointee.qualifiers &
                         static_cast<uint8_t>(
                             ~target_pointer->pointee.qualifiers)) != 0) {
                        return make_error(
                            std::move(value),
                            "static_cast cannot cast away qualifiers");
                    }
                    int64_t offset = 0;
                    if (static_path_offset(up_result.path, &offset)) {
                        return adjust_pointer_by_offset(std::move(value),
                                                        target_type,
                                                        offset,
                                                        "static_cast");
                    }
                    return convert_to(std::move(value),
                                      target_type,
                                      UseContext::RValue,
                                      loc);
                }
                DerivedToBasePathResult down_result =
                    analyze_derived_to_base_path(target_pointer->pointee.type,
                                                 source_pointer->pointee.type);
                if (down_result.kind == DerivedToBasePathKind::Ambiguous) {
                    return make_error(
                        std::move(value),
                        "invalid static_cast through an ambiguous base class");
                }
                if (down_result.kind == DerivedToBasePathKind::Unique) {
                    if ((source_pointer->pointee.qualifiers &
                         static_cast<uint8_t>(
                             ~target_pointer->pointee.qualifiers)) != 0) {
                        return make_error(
                            std::move(value),
                            "static_cast cannot cast away qualifiers");
                    }
                    int64_t offset = 0;
                    if (!static_path_offset(down_result.path, &offset)) {
                        return make_error(
                            std::move(value),
                            "invalid static_cast between pointer types across virtual or inaccessible base class");
                    }
                    return adjust_pointer_by_offset(std::move(value),
                                                    target_type,
                                                    -offset,
                                                    "static_cast");
                }
                return make_error(std::move(value),
                                  "invalid static_cast between unrelated pointer types");
            }
            if (is_nullptr_type(source) ||
                (is_integer_type(source) && is_integer_zero_literal(file_, value))) {
                return cast_if_needed(std::move(value),
                                      target_type,
                                      "static_cast",
                                      loc);
            }
            return make_error(std::move(value),
                              "invalid static_cast to pointer type");
        }
        if (source_pointer && is_integer_type(resolved_target)) {
            return make_error(std::move(value),
                              "invalid static_cast from pointer to integer type");
        }
        if (target_member) {
            if (source_member) {
                bool same_member_type = similar_types_ignoring_cv(
                    file_,
                    source_member->member_type,
                    target_member->member_type);
                bool related_class =
                    same_unqualified_type(file_,
                                          source_member->class_type.type,
                                          target_member->class_type.type) ||
                    derived_to_base_path(source_member->class_type.type,
                                         target_member->class_type.type,
                                         nullptr) ||
                    derived_to_base_path(target_member->class_type.type,
                                         source_member->class_type.type,
                                         nullptr);
                if (!same_member_type || !related_class) {
                    return make_error(
                        std::move(value),
                        "invalid static_cast between pointer-to-member types");
                }
                return cast_if_needed(std::move(value),
                                      target_type,
                                      "static_cast",
                                      loc);
            }
            if (is_nullptr_type(source) ||
                (is_integer_type(source) && is_integer_zero_literal(file_, value))) {
                return cast_if_needed(std::move(value),
                                      target_type,
                                      "static_cast",
                                      loc);
            }
            return make_error(std::move(value),
                              "invalid static_cast to pointer-to-member type");
        }
        if (source_member && is_integer_type(resolved_target)) {
            return make_error(
                std::move(value),
                "invalid static_cast from member pointer to integer type");
        }
        return convert_to(std::move(value), target_type, UseContext::Init, loc);
    }

    if (kind == CppNamedCastKind::Dynamic) {
        if (target_kind == cir::TypeKind::Pointer) {
            const auto* target_pointer = pointer_payload(file_, resolved_target);
            ExprResult value =
                require_value(std::move(operand), UseContext::RValue, loc);
            cir::TypeId source = file_.resolved_type(value.type);
            const auto* source_pointer = pointer_payload(file_, source);
            if (!target_pointer || !source_pointer) {
                return make_error(std::move(value),
                                  "dynamic_cast requires pointer operand types");
            }
            cir::TypeId source_object =
                file_.resolved_type(source_pointer->pointee.type);
            cir::TypeId target_object =
                file_.resolved_type(target_pointer->pointee.type);
            if (!is_complete_record_type(file_, source_object)) {
                return make_error(std::move(value),
                                  "dynamic_cast requires a pointer to complete class type");
            }
            if (!is_void_type_for_cast(file_, target_object) &&
                !is_complete_record_type(file_, target_object)) {
                return make_error(std::move(value),
                                  "dynamic_cast target must point to a complete class type or void");
            }
            if ((source_pointer->pointee.qualifiers &
                 static_cast<uint8_t>(~target_pointer->pointee.qualifiers)) != 0) {
                return make_error(std::move(value),
                                  "dynamic_cast cannot cast away qualifiers");
            }
            if (same_unqualified_type(file_, source_object, target_object) ||
                derived_to_base_path(source_object, target_object, nullptr)) {
                return collect_cpp_named_cast(CppNamedCastKind::Static,
                                              target_type,
                                              std::move(value),
                                              loc);
            }
            const cir::RecordFacts* source_facts =
                file_.record_facts_for_type(source_object);
            if (!source_facts || !source_facts->is_polymorphic) {
                return make_error(
                    std::move(value),
                    "dynamic_cast runtime checks require source type to be polymorphic");
            }
            if (is_void_type_for_cast(file_, target_object)) {
                return recover_complete_object_pointer(std::move(value));
            }
            if (!typeinfo_entity_for_type(file_.type_ref(source_object), loc).valid() ||
                !typeinfo_entity_for_type(file_.type_ref(target_object), loc).valid()) {
                return make_error(std::move(value),
                                  "dynamic_cast requires RTTI for source and target types");
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId entry =
                begin_fragment_block("expr.dynamic_cast.ptr.check");
            cir::InstId source_null = null_pointer_value(value.type);
            cir::InstId is_null = builder_.binary(cir::BinaryOpKind::Equal,
                                                  builder_.bool_type(),
                                                  value.value,
                                                  source_null,
                                                  loc);
            cir::Fragment fragment = finish_fragment_block(entry, previous);
            cir::BlockId null_block =
                builder_.create_detached_block("expr.dynamic_cast.ptr.null");
            cir::BlockId runtime_block =
                builder_.create_detached_block("expr.dynamic_cast.ptr.runtime");
            cir::BlockId merge_block =
                builder_.create_detached_block("expr.dynamic_cast.ptr.merge");
            cir::InstId merge_value =
                builder_.add_block_parameter(merge_block,
                                             target_type,
                                             ".dynamic.cast.ptr",
                                             loc);
            builder_.cond_branch_from(fragment.exit,
                                      is_null,
                                      null_block,
                                      runtime_block,
                                      {},
                                      loc);

            builder_.switch_to_block(null_block);
            builder_.branch(merge_block, {null_pointer_value(target_type)}, loc);

            builder_.switch_to_block(runtime_block);
            cir::InstId raw =
                call_dynamic_cast(value.value, source_object, target_object);
            if (!raw.valid()) {
                builder_.unreachable(loc);
            } else {
                cir::InstId casted =
                    builder_.cast(target_type, raw, "dynamic_cast", loc);
                builder_.branch(merge_block, {casted}, loc);
            }

            builder_.switch_to_block(previous);
            append_fragment_blocks(fragment, builder_.block_fragment(null_block));
            append_fragment_blocks(fragment,
                                   builder_.block_fragment(runtime_block));
            append_fragment_blocks(fragment, builder_.block_fragment(merge_block));
            fragment.exit = merge_block;

            value.fragment = chain(std::move(value.fragment), std::move(fragment), loc);
            value.value = merge_value;
            value.type = target_type;
            value.category = ValueCategory::PrValue;
            return value;
        }

        if (target_kind == cir::TypeKind::LValueReference ||
            target_kind == cir::TypeKind::RValueReference) {
            cir::TypeRef target_referred =
                file_.reference_referred_ref(resolved_target);
            bool glvalue_with_place =
                (operand.category == ValueCategory::LValue ||
                 operand.category == ValueCategory::XValue) &&
                operand.place.valid();
            if (!glvalue_with_place) {
                return make_error(std::move(operand),
                                  "dynamic_cast reference target requires a glvalue operand");
            }
            cir::TypeRef source_ref = place_object_ref(operand);
            cir::TypeId source_object = file_.resolved_type(source_ref.type);
            cir::TypeId target_object = file_.resolved_type(target_referred.type);
            if (!is_complete_record_type(file_, source_object) ||
                !is_complete_record_type(file_, target_object)) {
                return make_error(
                    std::move(operand),
                    "dynamic_cast requires references to complete class types");
            }
            if ((source_ref.qualifiers &
                 static_cast<uint8_t>(~target_referred.qualifiers)) != 0) {
                return make_error(std::move(operand),
                                  "dynamic_cast cannot cast away qualifiers");
            }
            if (same_unqualified_type(file_, source_object, target_object) ||
                derived_to_base_path(source_object, target_object, nullptr)) {
                return collect_cpp_named_cast(CppNamedCastKind::Static,
                                              target_type,
                                              std::move(operand),
                                              loc);
            }
            const cir::RecordFacts* source_facts =
                file_.record_facts_for_type(source_object);
            if (!source_facts || !source_facts->is_polymorphic) {
                return make_error(
                    std::move(operand),
                    "dynamic_cast runtime checks require source type to be polymorphic");
            }
            if (!typeinfo_entity_for_type(file_.type_ref(source_object), loc).valid() ||
                !typeinfo_entity_for_type(file_.type_ref(target_object), loc).valid()) {
                return make_error(std::move(operand),
                                  "dynamic_cast requires RTTI for source and target types");
            }

            cir::TypeId void_ptr = builder_.pointer_type(builder_.void_type());
            cir::TypeId target_pointer =
                builder_.pointer_type(file_.type_ref(target_object));
            cir::BlockId previous = builder_.current_block();
            cir::BlockId runtime_block =
                begin_fragment_block("expr.dynamic_cast.ref.runtime");
            cir::InstId source_address = builder_.addr_of(operand.place, loc);
            cir::InstId raw =
                call_dynamic_cast(source_address, source_object, target_object);
            cir::InstId null_void = null_pointer_value(void_ptr);
            cir::InstId is_null = raw.valid()
                ? builder_.binary(cir::BinaryOpKind::Equal,
                                  builder_.bool_type(),
                                  raw,
                                  null_void,
                                  loc)
                : cir::InstId{};
            cir::Fragment fragment = finish_fragment_block(runtime_block, previous);
            cir::BlockId bad_block =
                builder_.create_detached_block("expr.dynamic_cast.ref.bad");
            cir::BlockId success_block =
                builder_.create_detached_block("expr.dynamic_cast.ref.ok");
            if (is_null.valid()) {
                builder_.cond_branch_from(fragment.exit,
                                          is_null,
                                          bad_block,
                                          success_block,
                                          {},
                                          loc);
            } else {
                builder_.unreachable_from(fragment.exit, loc);
            }

            builder_.switch_to_block(bad_block);
            builder_.call(bad_cast_runtime(), builder_.void_type(), {}, loc);
            builder_.unreachable(loc);

            builder_.switch_to_block(success_block);
            cir::InstId typed =
                builder_.cast(target_pointer, raw, "dynamic_cast", loc);
            cir::InstId place = builder_.deref(typed, loc);

            builder_.switch_to_block(previous);
            append_fragment_blocks(fragment, builder_.block_fragment(bad_block));
            append_fragment_blocks(fragment,
                                   builder_.block_fragment(success_block));
            fragment.exit = success_block;
            operand.fragment =
                chain(std::move(operand.fragment), std::move(fragment), loc);
            return finish_reference_result(std::move(operand),
                                           place,
                                           target_type);
        }

        return make_error(std::move(operand),
                          "dynamic_cast requires pointer or reference target type");
    }

    return make_error(std::move(operand), "unknown C++ named cast kind");
}

ExprResult Session::collect_unsupported_expr(std::string message,
                                             std::vector<ExprResult> children,
                                             SrcLoc loc) {
    report_error(message, loc);

    cir::Fragment fragment;
    bool has_error = true;
    for (ExprResult& child : children) {
        has_error = has_error || child.has_error;
        fragment = chain(std::move(fragment), std::move(child.fragment), loc);
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.unsupported");
    cir::InstId value = builder_.name_ref("<unsupported-expression>", builder_.unknown_type(), loc);
    cir::Fragment unsupported_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(unsupported_fragment), loc);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = value;
    result.type = builder_.unknown_type();
    result.category = ValueCategory::Dependent;
    result.has_error = has_error;
    return result;
}

ExprResult Session::collect_conditional_expr(ExprResult condition,
                                             std::optional<ExprResult> true_expr,
                                             ExprResult false_expr,
                                             SrcLoc loc) {
    if (expr_is_dependent(condition) ||
        (true_expr.has_value() && expr_is_dependent(*true_expr)) ||
        expr_is_dependent(false_expr)) {
        cir::TemplateValueExpression condition_expression =
            template_value_operand_expression(condition);
        cir::TemplateValueExpression true_expression = true_expr.has_value()
            ? template_value_operand_expression(*true_expr)
            : condition_expression;
        cir::TemplateValueExpression false_expression =
            template_value_operand_expression(false_expr);

        ExprResult combined;
        combined.fragment = std::move(condition.fragment);
        if (true_expr.has_value()) {
            combined.fragment = chain(std::move(combined.fragment),
                                      std::move(true_expr->fragment), loc);
        }
        combined.fragment = chain(std::move(combined.fragment),
                                  std::move(false_expr.fragment), loc);
        combined.type = file_.dependent_type("dependent-conditional");
        combined.category = ValueCategory::Dependent;
        combined.references_template_value_parameter =
            condition.references_template_value_parameter ||
            (true_expr.has_value() &&
             true_expr->references_template_value_parameter) ||
            false_expr.references_template_value_parameter;
        combined.value_dependent = true;
        combined.has_error = condition.has_error ||
            (true_expr.has_value() && true_expr->has_error) ||
            false_expr.has_error;
        combined.template_value_expr = template_value_conditional_expr(
            condition_expression,
            true_expression,
            false_expression,
            type_ref(combined.type),
            ValueCategory::Dependent);
        combined.template_value_expr.loc = loc;
        combined.template_value_expr.definition_context =
            current_decl_context();
        combined.template_value_expr.definition_lookup_generation =
            lookup_generation_;
        return make_dependent_expr(std::move(combined), loc);
    }

    bool operands_value_dependent = expr_is_value_dependent(condition) ||
        (true_expr.has_value() && expr_is_value_dependent(*true_expr)) ||
        expr_is_value_dependent(false_expr);
    auto operand_expression =
        [&](const ExprResult& operand) {
            return operands_value_dependent
                ? template_value_operand_expression(operand)
                : operand.template_value_expr;
        };
    cir::TemplateValueExpression condition_expression =
        operand_expression(condition);
    cir::TemplateValueExpression true_expression = true_expr.has_value()
        ? operand_expression(*true_expr)
        : condition_expression;
    cir::TemplateValueExpression false_expression =
        operand_expression(false_expr);
    bool references_value_parameter =
        condition.references_template_value_parameter ||
        (true_expr.has_value() &&
         true_expr->references_template_value_parameter) ||
        false_expr.references_template_value_parameter;

    ExprResult cond;
    if (true_expr.has_value()) {
        cond = require_value(std::move(condition), UseContext::Condition, loc);
    } else {

        ExprResult cond_rvalue =
            require_value(std::move(condition), UseContext::RValue, loc);
        ExprResult true_operand;
        true_operand.value = cond_rvalue.value;
        true_operand.type = cond_rvalue.type;
        true_operand.category = ValueCategory::PrValue;
        true_operand.has_error = cond_rvalue.has_error;
        true_operand.value_dependent = cond_rvalue.value_dependent;
        true_operand.references_template_value_parameter =
            cond_rvalue.references_template_value_parameter;
        true_operand.template_value_expr = cond_rvalue.template_value_expr;
        true_expr = std::move(true_operand);
        cond = convert_to_condition(std::move(cond_rvalue), loc);
    }
    condition_expression = cond.template_value_expr;

    // The [expr.cond] lifetime invariant requires same-type glvalues to merge
    // addresses rather than load prvalues, preserving reference identity.
    auto conditional_glvalue_pointer_type =
        [&](const ExprResult& operand) -> cir::TypeId {
            if ((operand.category != ValueCategory::LValue &&
                 operand.category != ValueCategory::XValue) ||
                !operand.place.valid() || !file_.valid(operand.place)) {
                return {};
            }
            if (const cir::RecordFieldFact* field =
                    file_.field_fact(operand.entity);
                field && field->is_bitfield) {
                return {};
            }
            const cir::Inst& place = file_.inst(operand.place);
            cir::TypeId place_type = file_.resolved_type(place.result_type);
            if (!file_.valid(place_type) ||
                file_.type(place_type).kind != cir::TypeKind::Place ||
                (place.place_fact.valid() &&
                 file_.valid(place.place_fact) &&
                 !file_.place_fact(place.place_fact).addressable)) {
                return {};
            }
            return pointer_type(file_.place_object_ref(place_type));
        };
    bool same_type_glvalue_operands =
        lang_opts_.is_cxx_mode() && true_expr.has_value() &&
        true_expr->category == false_expr.category &&
        (true_expr->category == ValueCategory::LValue ||
         true_expr->category == ValueCategory::XValue) &&
        type_equal(true_expr->type, false_expr.type);
    if (same_type_glvalue_operands) {
        cir::TypeId true_pointer =
            conditional_glvalue_pointer_type(*true_expr);
        cir::TypeId false_pointer =
            conditional_glvalue_pointer_type(false_expr);
        if (true_pointer.valid() && type_equal(true_pointer, false_pointer)) {
            ExprResult true_operand = std::move(*true_expr);
            ExprResult false_operand = std::move(false_expr);
            ValueCategory result_category = true_operand.category;
            cir::TypeId result_type = true_operand.type;

            cir::BlockId previous = builder_.current_block();
            cir::BlockId true_address_block =
                builder_.create_detached_block("expr.cond.true.address");
            builder_.switch_to_block(true_address_block);
            cir::InstId true_address =
                builder_.addr_of(true_operand.place, loc);
            cir::BlockId false_address_block =
                builder_.create_detached_block("expr.cond.false.address");
            builder_.switch_to_block(false_address_block);
            cir::InstId false_address =
                builder_.addr_of(false_operand.place, loc);
            builder_.switch_to_block(previous);

            cir::Fragment fragment = adopt_or_create_fragment_entry(
                std::move(cond.fragment), "expr.cond");
            cir::BlockId true_block =
                builder_.create_detached_block("expr.cond.true");
            cir::BlockId false_block =
                builder_.create_detached_block("expr.cond.false");
            cir::BlockId merge_block =
                builder_.create_detached_block("expr.cond.end");
            cir::InstId merge_pointer = builder_.add_block_parameter(
                merge_block, true_pointer, "cond.address", loc);
            builder_.cond_branch_from(fragment.exit, cond.value,
                                      true_block, false_block, {}, loc);

            auto append_operand =
                [&](cir::BlockId entry,
                    ExprResult& operand,
                    cir::BlockId address_block,
                    cir::InstId address) {
                    append_fragment_blocks(
                        fragment, builder_.block_fragment(entry));
                    if (operand.fragment.empty()) {
                        builder_.branch_from(entry, address_block, {}, loc);
                    } else {
                        builder_.branch_from(entry,
                                             operand.fragment.entry,
                                             {},
                                             loc);
                        append_fragment_blocks(fragment, operand.fragment);
                        builder_.branch_from(operand.fragment.exit,
                                             address_block,
                                             {},
                                             loc);
                    }
                    append_fragment_blocks(
                        fragment, builder_.block_fragment(address_block));
                    builder_.branch_from(address_block,
                                         merge_block,
                                         {address},
                                         loc);
                };
            append_operand(true_block,
                           true_operand,
                           true_address_block,
                           true_address);
            append_operand(false_block,
                           false_operand,
                           false_address_block,
                           false_address);

            builder_.switch_to_block(merge_block);
            cir::InstId result_place = builder_.deref(merge_pointer, loc);
            builder_.switch_to_block(previous);
            append_fragment_blocks(
                fragment, builder_.block_fragment(merge_block));
            fragment.exit = merge_block;
            fragment.falls_through = true;

            ExprResult result;
            result.fragment = std::move(fragment);
            result.place = result_place;
            result.type = result_type;
            result.category = result_category;
            result.value_dependent = operands_value_dependent;
            result.references_template_value_parameter =
                references_value_parameter;
            result.template_value_expr = template_value_conditional_expr(
                condition_expression,
                true_expression,
                false_expression,
                type_ref(result.type),
                result.category);
            result.template_value_expr.loc = loc;
            result.template_value_expr.definition_context =
                current_decl_context();
            result.template_value_expr.definition_lookup_generation =
                lookup_generation_;
            result.has_error = cond.has_error ||
                true_operand.has_error || false_operand.has_error;
            return result;
        }
    }

    auto decayed_operand_type = [&](cir::TypeId type) -> cir::TypeId {
        if (!type.valid()) return type;
        cir::TypeId resolved = file_.resolved_type(type);
        if (!file_.valid(resolved)) return type;
        if (file_.type(resolved).kind == cir::TypeKind::Array) {
            return pointer_type(file_.array_element_ref(resolved));
        }
        if (is_function_type(file_, resolved)) {
            return pointer_type(type_ref(resolved));
        }
        return type;
    };
    cir::TypeId true_type =
        true_expr.has_value() ? decayed_operand_type(true_expr->type) : cir::TypeId{};
    cir::TypeId false_type = decayed_operand_type(false_expr.type);

    cir::TypeId result_type = true_expr.has_value() && true_type.valid()
        ? true_type
        : (false_type.valid() ? false_type : cond.type);
    bool pointer_conditional_error = false;
    bool class_conditional_error = false;
    bool selected_class_conversion = false;
    auto glvalue_category = [](ValueCategory category) {
        return category == ValueCategory::LValue ||
            category == ValueCategory::XValue;
    };
    auto has_direct_conditional_reference_sequence =
        [&](const ExprResult& source,
            const ExprResult& target) {
            if (!glvalue_category(source.category) ||
                source.category != target.category) {
                return false;
            }
            cir::TypeRef source_object =
                template_recipe_expression_type(file_, source);
            cir::TypeRef target_object =
                template_recipe_expression_type(file_, target);
            cir::ReferenceKind reference_kind =
                source.category == ValueCategory::LValue
                    ? cir::ReferenceKind::LValue
                    : cir::ReferenceKind::RValue;
            cir::TypeRef source_reference = file_.type_ref(
                reference_type(source_object, reference_kind));
            cir::TypeRef target_reference = file_.type_ref(
                reference_type(target_object, reference_kind));
            OperationProbe binding = probe_construction(
                target_reference, {source_reference});
            return binding.viable &&
                !probe_reference_binds_to_temporary(
                    target_reference, source_reference);
        };
    auto is_record_operand_type = [&](cir::TypeId type) {
        cir::TypeId resolved = file_.resolved_type(type);
        return file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Record;
    };
    bool different_class_operand_types = lang_opts_.is_cxx_mode() &&
        true_expr.has_value() &&
        !type_equal(true_type, false_type) &&
        (is_record_operand_type(true_type) ||
         is_record_operand_type(false_type));
    bool both_prvalues = true_expr.has_value() &&
        true_expr->category == ValueCategory::PrValue &&
        false_expr.category == ValueCategory::PrValue;
    bool same_category_glvalues = true_expr.has_value() &&
        glvalue_category(true_expr->category) &&
        true_expr->category == false_expr.category;
    bool has_direct_reference_sequence =
        different_class_operand_types && same_category_glvalues &&
        (has_direct_conditional_reference_sequence(*true_expr, false_expr) ||
         has_direct_conditional_reference_sequence(false_expr, *true_expr));
    bool use_class_value_conversion_stage =
        both_prvalues ||
        (same_category_glvalues && !has_direct_reference_sequence);
    if (different_class_operand_types && use_class_value_conversion_stage) {

        // [expr.cond] forms an implicit conversion sequence in both
        // directions. That decision depends on the conversion functions and
        // constructors of class operands, so identity-only template
        // specializations must be completed here rather than incidentally
        // while an earlier overload candidate is formed.
        if (is_record_operand_type(true_type)) {
            (void)require_complete_class_type(
                true_type,
                loc,
                cir::InstantiationDemandKind::CompleteClass);
        }
        if (is_record_operand_type(false_type)) {
            (void)require_complete_class_type(
                false_type,
                loc,
                cir::InstantiationDemandKind::CompleteClass);
        }

        OperationProbe true_to_false = probe_implicit_conversion(
            file_.type_ref(true_type), file_.type_ref(false_type),
            /*core_convertibility=*/true);
        OperationProbe false_to_true = probe_implicit_conversion(
            file_.type_ref(false_type), file_.type_ref(true_type),
            /*core_convertibility=*/true);
        bool true_to_false_ambiguous =
            true_to_false.failure == OperationProbeFailure::Ambiguous;
        bool false_to_true_ambiguous =
            false_to_true.failure == OperationProbeFailure::Ambiguous;
        bool true_to_false_viable = true_to_false.viable;
        bool false_to_true_viable = false_to_true.viable;
        if (true_to_false_ambiguous || false_to_true_ambiguous ||
            (true_to_false_viable && false_to_true_viable)) {
            report_error(
                "conditional expression has ambiguous class conversions",
                loc);
            class_conditional_error = true;
        } else if (true_to_false_viable) {
            result_type = false_type;
            selected_class_conversion = true;
        } else if (false_to_true_viable) {
            result_type = true_type;
            selected_class_conversion = true;
        }
    }
    if (!selected_class_conversion && same_type_glvalue_operands) {

        result_type = true_type;
    } else if (!selected_class_conversion && true_expr.has_value() &&
               type_equal(true_type, false_type)) {

        result_type = true_type;
    } else if (!selected_class_conversion && true_expr.has_value() &&
        is_arithmetic_type(true_type) &&
        is_arithmetic_type(false_type)) {
        result_type = usual_arithmetic_conversion_type(true_type, false_type);
    } else if (!selected_class_conversion && true_expr.has_value() &&
               (is_cir_pointer_type(file_, true_type) ||
                is_cir_pointer_type(file_, false_type))) {

        if (is_cir_pointer_type(file_, true_type) &&
            is_null_pointer_constant(false_expr)) {
            result_type = true_type;
        } else if (is_null_pointer_constant(*true_expr) &&
                   is_cir_pointer_type(file_, false_type)) {
            result_type = false_type;
        } else if (is_cir_pointer_type(file_, true_type) &&
            is_cir_pointer_type(file_, false_type)) {
            if (std::optional<cir::TypeRef> pointee =
                    common_pointer_pointee(*this,
                                           file_,
                                           true_type,
                                           false_type,
                                           PointerPointeeMode::Composite)) {
                result_type = pointer_type(*pointee);
            } else {
                report_error("conditional expression requires compatible pointer operands", loc);
                pointer_conditional_error = true;
                result_type = true_type;
            }
        } else if (is_cir_pointer_type(file_, true_type) ||
                   is_cir_pointer_type(file_, false_type)) {
            report_error("conditional expression requires a pointer or null pointer constant", loc);
            pointer_conditional_error = true;
            result_type = is_cir_pointer_type(file_, true_type)
                ? true_type
                : false_type;
        }
    }
    if (!result_type.valid()) {
        result_type = builder_.int_type();
    }

    bool is_void_result = is_void_type(result_type);

    cir::TypeId resolved_result = file_.resolved_type(result_type);
    cir::EntityId conditional_result_entity;
    if (lang_opts_.is_cxx_mode() && !is_void_result &&
        file_.valid(resolved_result) &&
        file_.type(resolved_result).kind == cir::TypeKind::Record) {
        conditional_result_entity = builder_.add_entity(
            cir::EntityKind::Variable,
            ".conditional.result.tmp." +
                std::to_string(compound_literal_counter_++),
            result_type,
            {},
            loc,
            cir::StorageDuration::Temporary,
            cir::MemorySpace::Default,
            {});
        file_.entity_mut(conditional_result_entity).is_definition = true;
    }

    cir::Fragment fragment = adopt_or_create_fragment_entry(std::move(cond.fragment), "expr.cond");
    cir::BlockId true_block = builder_.create_detached_block("expr.cond.true");
    cir::BlockId false_block = builder_.create_detached_block("expr.cond.false");
    cir::BlockId merge_block = builder_.create_detached_block("expr.cond.end");
    cir::InstId merge_value = is_void_result
        ? cir::InstId{}
        : builder_.add_block_parameter(merge_block, result_type, "cond.result", loc);
    auto merge_args = [&](cir::InstId value) -> std::vector<cir::InstId> {
        if (is_void_result) {
            return {};
        }
        return {value};
    };

    builder_.cond_branch_from(fragment.exit, cond.value, true_block, false_block, {}, loc);

    const UseContext arm_context =
        is_void_result ? UseContext::Discard : UseContext::RValue;

    append_fragment_blocks(fragment, builder_.block_fragment(true_block));
    bool has_error = cond.has_error || pointer_conditional_error ||
        class_conditional_error;
    std::vector<cir::LifetimeId> conditional_operand_lifetimes;
    bool adopted_true_result = !conditional_result_entity.valid();
    bool adopted_false_result = !conditional_result_entity.valid();
    if (true_expr.has_value()) {
        ExprResult true_value =
            convert_to(std::move(*true_expr), result_type, arm_context, loc);
        if (conditional_result_entity.valid()) {
            adopted_true_result = adopt_materialized_object_storage(
                true_value, {}, conditional_result_entity);
        }
        conditional_operand_lifetimes.insert(
            conditional_operand_lifetimes.end(),
            true_value.materialized_lifetimes.begin(),
            true_value.materialized_lifetimes.end());
        true_expression = operand_expression(true_value);
        has_error = has_error || true_value.has_error;
        if (true_value.fragment.empty()) {
            builder_.branch_from(true_block, merge_block, merge_args(true_value.value), loc);
        } else {
            builder_.branch_from(true_block, true_value.fragment.entry, {}, loc);
            append_fragment_blocks(fragment, true_value.fragment);
            builder_.branch_from(true_value.fragment.exit, merge_block, merge_args(true_value.value), loc);
        }
    } else {
        builder_.branch_from(true_block, merge_block, merge_args(cond.value), loc);
    }

    append_fragment_blocks(fragment, builder_.block_fragment(false_block));
    ExprResult false_value =
        convert_to(std::move(false_expr), result_type, arm_context, loc);
    if (conditional_result_entity.valid()) {
        adopted_false_result = adopt_materialized_object_storage(
            false_value, {}, conditional_result_entity);
    }
    conditional_operand_lifetimes.insert(
        conditional_operand_lifetimes.end(),
        false_value.materialized_lifetimes.begin(),
        false_value.materialized_lifetimes.end());
    false_expression = operand_expression(false_value);
    has_error = has_error || false_value.has_error;
    if (false_value.fragment.empty()) {
        builder_.branch_from(false_block, merge_block, merge_args(false_value.value), loc);
    } else {
        builder_.branch_from(false_block, false_value.fragment.entry, {}, loc);
        append_fragment_blocks(fragment, false_value.fragment);
        builder_.branch_from(false_value.fragment.exit, merge_block, merge_args(false_value.value), loc);
    }

    append_fragment_blocks(fragment, builder_.block_fragment(merge_block));
    fragment.exit = merge_block;
    fragment.falls_through = true;

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = merge_value;
    result.type = result_type;
    result.category = ValueCategory::PrValue;
    result.value_dependent = operands_value_dependent;
    result.references_template_value_parameter = references_value_parameter;
    result.template_value_expr = template_value_conditional_expr(
        condition_expression,
        true_expression,
        false_expression,
        type_ref(result.type));
    result.template_value_expr.loc = loc;
    result.template_value_expr.definition_context = current_decl_context();
    result.template_value_expr.definition_lookup_generation = lookup_generation_;
    result.has_error = has_error;

    if (lang_opts_.is_cxx_mode() && result.value.valid() &&
        file_.valid(resolved_result) &&
        file_.type(resolved_result).kind == cir::TypeKind::Record) {
        cir::EntityId temp = conditional_result_entity;
        if (!temp.valid()) {
            temp = builder_.add_entity(
                cir::EntityKind::Variable,
                ".conditional.result.tmp." +
                    std::to_string(compound_literal_counter_++),
                result.type,
                {},
                loc,
                cir::StorageDuration::Temporary,
                cir::MemorySpace::Default,
                {});
            file_.entity_mut(temp).is_definition = true;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block =
            begin_fragment_block("expr.conditional.result.materialize");
        cir::InstId place = builder_.local_place(temp, result.type, loc);
        cir::InstId store = builder_.store(place, result.value, loc);
        bool adopted_result =
            adopted_true_result && adopted_false_result;
        if (adopted_result) {
            file_.inst_mut(store).runtime_elided_object_operation = true;
        }
        result.value = builder_.lvalue_to_rvalue(place, loc);
        result.fragment = chain(
            std::move(result.fragment),
            finish_fragment_block(block, previous), loc);
        if (adopted_result) {
            for (cir::LifetimeId lifetime : conditional_operand_lifetimes) {
                retire_lifetime(lifetime);
            }
        }
        if (cir::LifetimeId lifetime = register_destructor_cleanup(
                temp, result.type, loc,
                /*full_expression_temporary=*/true);
            lifetime.valid()) {
            result.materialized_lifetimes.push_back(lifetime);
        }
    }
    return result;
}

ExprResult Session::collect_vector_binary_expr(syntax::BinaryOperator op,
                                               ExprResult lhs_value,
                                               ExprResult rhs_value,
                                               SrcLoc loc) {
    bool comparison = is_comparison_operator(op);
    bool integer_only = is_vector_integer_operator(op);
    bool numeric = is_vector_numeric_operator(op) || comparison;
    bool shift = op == syntax::BinaryOperator::Shl || op == syntax::BinaryOperator::Shr;
    bool has_error = lhs_value.has_error || rhs_value.has_error;

    auto make_result = [&](cir::TypeId result_type,
                           cir::Fragment fragment,
                           cir::InstId value,
                           bool error) {
        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = value;
        result.type = result_type.valid() ? result_type : builder_.int_type();
        result.category = ValueCategory::PrValue;
        result.has_error = error;
        return result;
    };

    if (!comparison && !integer_only && !is_vector_numeric_operator(op)) {
        report_error("operator '" + std::string(cir::binary_op_spelling(binary_op_kind(op))) +
                         "' is not supported for vector operands",
                     loc);
        has_error = true;
    }

    bool lhs_vector = is_vector_type(lhs_value.type);
    bool rhs_vector = is_vector_type(rhs_value.type);
    cir::TypeId vector_type_id = lhs_vector ? lhs_value.type : rhs_value.type;
    uint32_t element_count = file_.vector_element_count(vector_type_id);
    cir::TypeId lhs_element = lhs_vector ? file_.vector_element_type(lhs_value.type) : lhs_value.type;
    cir::TypeId rhs_element = rhs_vector ? file_.vector_element_type(rhs_value.type) : rhs_value.type;
    cir::TypeId computation_element = lhs_element;

    if (!lhs_vector && !rhs_vector) {
        has_error = true;
    }
    if (lhs_vector && rhs_vector) {
        uint32_t lhs_count = file_.vector_element_count(lhs_value.type);
        uint32_t rhs_count = file_.vector_element_count(rhs_value.type);
        if (lhs_count != rhs_count) {
            report_error("vector operands must have the same number of elements", loc);
            has_error = true;
        }
        element_count = lhs_count;
        if (shift) {
            computation_element = lhs_element;
        } else if (type_equal(lhs_element, rhs_element)) {

            computation_element = lhs_element;
        } else {
            computation_element =
                usual_arithmetic_conversion_type(lhs_element, rhs_element);
            if (!computation_element.valid()) {
                computation_element = lhs_element.valid() ? lhs_element : rhs_element;
            }
        }
    } else {
        cir::TypeId scalar_type = lhs_vector ? rhs_value.type : lhs_value.type;
        if (!is_arithmetic_type(scalar_type)) {
            report_error("vector operation requires arithmetic scalar operand", loc);
            has_error = true;
        }
        computation_element = file_.vector_element_type(vector_type_id);
    }

    if (integer_only) {
        if (!is_integer_type(computation_element)) {
            report_error("vector operator requires integer elements", loc);
            has_error = true;
        }
        if (!lhs_vector && !is_integer_type(lhs_value.type)) {
            report_error("vector operator requires an integer scalar operand", loc);
            has_error = true;
        }
        if (!rhs_vector && !is_integer_type(rhs_value.type)) {
            report_error("vector operator requires an integer scalar operand", loc);
            has_error = true;
        }
        if (lhs_vector && !is_integer_type(lhs_element)) {
            report_error("vector operator requires integer elements", loc);
            has_error = true;
        }
        if (rhs_vector && !is_integer_type(rhs_element)) {
            report_error("vector operator requires integer elements", loc);
            has_error = true;
        }
    } else if (numeric && !is_arithmetic_type(computation_element)) {
        report_error("vector operator requires integer or floating-point elements", loc);
        has_error = true;
    }

    auto make_vector_type = [&](cir::TypeId element_type) -> cir::TypeId {
        if (!element_type.valid() || element_count == 0) {
            return {};
        }
        std::optional<std::pair<size_t, size_t>> element_layout =
            size_align_of_type(element_type, loc);
        uint64_t size_bytes = element_layout.has_value()
            ? static_cast<uint64_t>(element_layout->first) * element_count
            : static_cast<uint64_t>(file_.vector_size_bytes(vector_type_id));
        if (size_bytes == 0) {
            size_bytes = element_count;
        }
        return vector_type(file_.type_ref(element_type), element_count, size_bytes);
    };

    cir::TypeId computation_type = make_vector_type(computation_element);
    if (!computation_type.valid()) {
        computation_type = vector_type_id.valid() ? vector_type_id : builder_.unknown_type();
        has_error = true;
    }

    auto signed_integer_for_size = [&](size_t bytes) -> cir::TypeId {
        switch (bytes) {
            case 1: return file_.builtin_type(cir::BuiltinTypeKind::SChar);
            case 2: return file_.builtin_type(cir::BuiltinTypeKind::Short);
            case 4: return file_.builtin_type(cir::BuiltinTypeKind::Int);
            case 8: return file_.builtin_type(cir::BuiltinTypeKind::LongLong);
            case 16: return file_.builtin_type(cir::BuiltinTypeKind::Int128);
            default: return file_.builtin_type(cir::BuiltinTypeKind::Int);
        }
    };

    cir::TypeId result_type = computation_type;
    if (comparison) {
        std::optional<std::pair<size_t, size_t>> element_layout =
            size_align_of_type(computation_element, loc);
        cir::TypeId comparison_element =
            signed_integer_for_size(element_layout.has_value() ? element_layout->first : 4);
        result_type = make_vector_type(comparison_element);
        if (!result_type.valid()) {
            result_type = computation_type;
        }
    }

    if (lhs_vector) {
        lhs_value = convert_to(std::move(lhs_value), computation_type, UseContext::RValue, loc);
    } else {
        lhs_value = convert_to(std::move(lhs_value), computation_type, UseContext::RValue, loc);
    }
    rhs_value = convert_to(std::move(rhs_value), computation_type, UseContext::RValue, loc);
    has_error = has_error || lhs_value.has_error || rhs_value.has_error;

    cir::Fragment fragment =
        chain(std::move(lhs_value.fragment), std::move(rhs_value.fragment), loc);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.binary.vector");
    cir::InstId inst = builder_.binary(binary_op_kind(op),
                                       result_type,
                                       lhs_value.value,
                                       rhs_value.value,
                                       loc);
    cir::Fragment op_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(op_fragment), loc);

    return make_result(result_type, std::move(fragment), inst, has_error);
}

ExprResult Session::collect_binary_expr_builtin(syntax::BinaryOperator op,
                                        ExprResult lhs,
                                        ExprResult rhs,
                                        SrcLoc loc) {
    if (op == syntax::BinaryOperator::Invalid) {
        report_error("unsupported binary operator", loc);

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.error");
        cir::InstId inst = builder_.error("unsupported binary operator", loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);

        ExprResult error;
        error.fragment = std::move(fragment);
        error.value = inst;
        error.type = builder_.unknown_type();
        error.category = ValueCategory::PrValue;
        error.has_error = true;
        return error;
    }

    if (op == syntax::BinaryOperator::PtrMemDot ||
        op == syntax::BinaryOperator::PtrMemArrow) {
        return collect_data_member_pointer_expr(op,
                                                std::move(lhs),
                                                std::move(rhs),
                                                loc);
    }

    if (op == syntax::BinaryOperator::ThreeWay) {
        return collect_builtin_three_way_compare(std::move(lhs),
                                                 std::move(rhs), loc);
    }

    if (op == syntax::BinaryOperator::Comma) {
        ExprResult lhs_value = std::move(lhs);
        if (lhs_value.category != ValueCategory::LValue &&
            lhs_value.category != ValueCategory::XValue) {
            lhs_value = require_value(std::move(lhs_value),
                                      UseContext::Discard, loc);
        }

        if ((rhs.category == ValueCategory::LValue ||
             rhs.category == ValueCategory::XValue) &&
            (rhs.place.valid() || rhs.deferred_entity_place)) {
            cir::TemplateValueExpression rhs_expression = rhs.template_value_expr;
            bool value_dependent = expr_is_value_dependent(lhs_value) ||
                                   expr_is_value_dependent(rhs);
            rhs.fragment = chain(std::move(lhs_value.fragment), std::move(rhs.fragment), loc);
            rhs.value_dependent = value_dependent;
            rhs.references_template_value_parameter =
                lhs_value.references_template_value_parameter ||
                rhs.references_template_value_parameter;
            rhs.template_value_expr = template_value_binary_expr(
                cir::TemplateValueExprOp::Comma,
                lhs_value.template_value_expr,
                rhs_expression,
                type_ref(rhs.type));
            rhs.template_value_expr.loc = loc;
            rhs.template_value_expr.definition_context = current_decl_context();
            rhs.template_value_expr.definition_lookup_generation = lookup_generation_;
            rhs.has_error = rhs.has_error || lhs_value.has_error;
            return rhs;
        }

        if (rhs.category == ValueCategory::PrValue && is_void_type(rhs.type)) {
            rhs.fragment = chain(std::move(lhs_value.fragment), std::move(rhs.fragment), loc);
            rhs.has_error = rhs.has_error || lhs_value.has_error;
            return rhs;
        }
        ExprResult rhs_value = require_value(std::move(rhs), UseContext::RValue, loc);
        bool value_dependent = expr_is_value_dependent(lhs_value) ||
                               expr_is_value_dependent(rhs_value);
        rhs_value.fragment = chain(std::move(lhs_value.fragment), std::move(rhs_value.fragment), loc);
        rhs_value.value_dependent = value_dependent;
        rhs_value.references_template_value_parameter =
            lhs_value.references_template_value_parameter ||
            rhs_value.references_template_value_parameter;
        rhs_value.template_value_expr = template_value_binary_expr(
            cir::TemplateValueExprOp::Comma,
            lhs_value.template_value_expr,
            rhs_value.template_value_expr,
            type_ref(rhs_value.type));
        rhs_value.template_value_expr.loc = loc;
        rhs_value.template_value_expr.definition_context = current_decl_context();
        rhs_value.template_value_expr.definition_lookup_generation = lookup_generation_;
        rhs_value.has_error = rhs_value.has_error || lhs_value.has_error;
        return rhs_value;
    }

    if (op == syntax::BinaryOperator::LogicalAnd ||
        op == syntax::BinaryOperator::LogicalOr) {
        bool operands_value_dependent =
            expr_is_value_dependent(lhs) || expr_is_value_dependent(rhs);
        cir::TemplateValueExpression lhs_expression;
        cir::TemplateValueExpression rhs_expression;
        if (operands_value_dependent) {
            lhs_expression = template_value_operand_expression(lhs);
            rhs_expression = template_value_operand_expression(rhs);
        }
        ExprResult lhs_value = require_value(std::move(lhs), UseContext::Condition, loc);
        cir::TypeId bool_type = builder_.bool_type();
        cir::TypeId result_type = lang_opts_.is_cxx_mode() ? bool_type : builder_.int_type();

        cir::Fragment fragment =
            adopt_or_create_fragment_entry(std::move(lhs_value.fragment),
                                           op == syntax::BinaryOperator::LogicalAnd
                                               ? "expr.logical_and.lhs"
                                               : "expr.logical_or.lhs");
        cir::BlockId rhs_block = builder_.create_detached_block("expr.logical.rhs");
        cir::BlockId short_block = builder_.create_detached_block("expr.logical.short");
        cir::BlockId merge_block = builder_.create_detached_block("expr.logical.end");
        cir::InstId merge_value = builder_.add_block_parameter(merge_block,
                                                               result_type,
                                                               "logical.result",
                                                               loc);

        if (op == syntax::BinaryOperator::LogicalAnd) {
            builder_.cond_branch_from(fragment.exit, lhs_value.value, rhs_block, short_block, {}, loc);
        } else {
            builder_.cond_branch_from(fragment.exit, lhs_value.value, short_block, rhs_block, {}, loc);
        }

        append_fragment_blocks(fragment, builder_.block_fragment(short_block));
        cir::BlockId previous = builder_.current_block();
        builder_.switch_to_block(short_block);
        bool short_value = op == syntax::BinaryOperator::LogicalOr;
        cir::InstId short_literal = result_type == bool_type
            ? builder_.boolean_literal(short_value, short_value ? "true" : "false", loc)
            : builder_.integer_literal(short_value ? 1 : 0, short_value ? "1" : "0", loc);
        builder_.switch_to_block(previous);
        builder_.branch_from(short_block, merge_block, {short_literal}, loc);

        append_fragment_blocks(fragment, builder_.block_fragment(rhs_block));
        ExprResult rhs_value = require_value(std::move(rhs), UseContext::Condition, loc);
        rhs_value = cast_if_needed(std::move(rhs_value), result_type, "logical.result", loc);
        if (rhs_value.fragment.empty()) {
            builder_.branch_from(rhs_block, merge_block, {rhs_value.value}, loc);
        } else {
            builder_.branch_from(rhs_block, rhs_value.fragment.entry, {}, loc);
            append_fragment_blocks(fragment, rhs_value.fragment);
            builder_.branch_from(rhs_value.fragment.exit, merge_block, {rhs_value.value}, loc);
        }

        append_fragment_blocks(fragment, builder_.block_fragment(merge_block));
        fragment.exit = merge_block;
        fragment.falls_through = true;

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = merge_value;
        result.type = result_type;
        result.category = ValueCategory::PrValue;
        result.references_template_value_parameter =
            lhs_value.references_template_value_parameter ||
            rhs_value.references_template_value_parameter;
        result.value_dependent = operands_value_dependent;
        if (auto graph_op = template_value_expr_op(op)) {
            result.template_value_expr = template_value_binary_expr(
                *graph_op,
                operands_value_dependent ? lhs_expression
                                         : lhs_value.template_value_expr,
                operands_value_dependent ? rhs_expression
                                         : rhs_value.template_value_expr,
                type_ref(result.type));
            result.template_value_expr.loc = loc;
            result.template_value_expr.definition_context = current_decl_context();
            result.template_value_expr.definition_lookup_generation = lookup_generation_;
        }
        result.has_error = lhs_value.has_error || rhs_value.has_error;
        return result;
    }

    if (op == syntax::BinaryOperator::Assign) {
        ExprResult lhs_place = require_place(std::move(lhs), UseContext::Assignment, loc);
        cir::TypeId object_type = lhs_place.type.valid()
            ? lhs_place.type
            : object_type_from_place(lhs_place.place);
        ExprResult rhs_value = convert_to(std::move(rhs), object_type, UseContext::Assignment, loc);

        cir::Fragment fragment =
            chain(std::move(lhs_place.fragment), std::move(rhs_value.fragment), loc);

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.assign");

        cir::TypeRef assign_object_ref =
            file_.place_object_ref(file_.inst(lhs_place.place).result_type);

        bool arc_self_store = false;
        bool arc_strong_assign = false;
        bool arc_weak_assign = false;
        bool arc_autoreleasing_assign = false;
        bool arc_assign_error = false;
        if (arc_enabled() && arc_retainable_type(object_type) &&
            (assign_object_ref.qualifiers & cir::QualAtomic) == 0) {
            if (expr_reads_objc_self(lhs_place)) {
                if (objc_.current_method_family !=
                    cir::ObjCMethodFamily::Init) {
                    report_error("cannot assign to 'self' outside of a "
                                 "method in the init family", loc);
                    arc_assign_error = true;
                }
                arc_self_store = true;
            } else {
                cir::ObjCOwnership ownership =
                    arc_ownership_of_ref(assign_object_ref);

                bool entity_backed = false;
                const cir::Inst& lhs_inst = file_.inst(lhs_place.place);
                if (lhs_inst.kind == cir::InstKind::ObjCIvarAddr) {

                    entity_backed = true;
                } else if (lhs_inst.place_fact.valid() &&
                           file_.valid(lhs_inst.place_fact) &&
                           file_.place_fact(lhs_inst.place_fact)
                               .entity.valid()) {
                    entity_backed = true;
                }
                if (!entity_backed &&
                    cir::ownership_of(assign_object_ref.qualifiers) ==
                        cir::ObjCOwnership::Unspecified) {
                    arc_autoreleasing_assign =
                        ownership == cir::ObjCOwnership::Strong;
                } else {
                    arc_strong_assign =
                        ownership == cir::ObjCOwnership::Strong;
                }
                arc_weak_assign = ownership == cir::ObjCOwnership::Weak;
            }
        }
        if (assign_object_ref.qualifiers & cir::QualAtomic) {
            builder_.atomic_store(lhs_place.place, rhs_value.value,
                                  cir::MemoryOrder::SeqCst, loc);
        } else if (arc_autoreleasing_assign && rhs_value.value.valid()) {

            cir::InstId kept = rhs_value.value;
            if (rhs_value.arc_plus_one) {
                arc_claim_plus_one(rhs_value);
            } else {
                kept = builder_.objc_arc_op(
                    cir::ObjCArcOpKind::Retain, {kept},
                    file_.resolved_type(object_type), loc);
            }
            kept = builder_.objc_arc_op(cir::ObjCArcOpKind::Autorelease,
                                        {kept},
                                        file_.resolved_type(object_type),
                                        loc);
            builder_.store(lhs_place.place, kept, loc);
        } else if (arc_weak_assign) {
            cir::InstId slot = builder_.addr_of(lhs_place.place, loc);
            (void)builder_.objc_arc_op(cir::ObjCArcOpKind::StoreWeak,
                                       {slot, rhs_value.value},
                                       file_.resolved_type(object_type), loc);
            if (rhs_value.arc_plus_one) {
                arc_claim_plus_one(rhs_value);
                (void)builder_.objc_arc_op(cir::ObjCArcOpKind::Release,
                                           {rhs_value.value}, {}, loc);
            }
        } else if (arc_strong_assign && rhs_value.arc_plus_one) {
            arc_claim_plus_one(rhs_value);
            cir::InstId displaced = builder_.load(lhs_place.place, loc);
            builder_.store(lhs_place.place, rhs_value.value, loc);
            (void)builder_.objc_arc_op(cir::ObjCArcOpKind::Release,
                                       {displaced}, {}, loc);
        } else if (arc_strong_assign) {
            cir::InstId slot = builder_.addr_of(lhs_place.place, loc);
            (void)builder_.objc_arc_op(cir::ObjCArcOpKind::StoreStrong,
                                       {slot, rhs_value.value}, {}, loc);
        } else {
            if (arc_self_store && rhs_value.arc_plus_one) {

                arc_claim_plus_one(rhs_value);
            }
            builder_.store(lhs_place.place, rhs_value.value, loc);
        }
        cir::Fragment store_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(store_fragment), loc);

        cir::InstId result_value = rhs_value.value;

        if (!lang_opts_.is_cxx_mode()) {
            const cir::RecordFieldFact* field = file_.field_fact(lhs_place.entity);
            if (field && field->is_bitfield) {
                cir::BlockId reload_prev = builder_.current_block();
                cir::BlockId reload_block = begin_fragment_block("expr.assign.bitfield");
                result_value = builder_.lvalue_to_rvalue(lhs_place.place, loc);
                cir::Fragment reload_fragment =
                    finish_fragment_block(reload_block, reload_prev);
                fragment = chain(std::move(fragment), std::move(reload_fragment), loc);
                object_type = file_.inst(result_value).result_type;
            }
        }

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = result_value;
        result.place = lang_opts_.is_cxx_mode() ? lhs_place.place
                                                : cir::InstId{};
        result.type = object_type;
        result.category = lang_opts_.is_cxx_mode() ? ValueCategory::LValue
                                                   : ValueCategory::PrValue;
        result.has_error = lhs_place.has_error || rhs_value.has_error ||
                           arc_assign_error;
        return result;
    }

    if (is_compound_assignment(op)) {
        ExprResult lhs_place = require_place(std::move(lhs), UseContext::Assignment, loc);
        cir::TypeId object_type = lhs_place.type.valid()
            ? lhs_place.type
            : object_type_from_place(lhs_place.place);
        if (!object_type.valid()) {
            object_type = builder_.int_type();
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId load_block = begin_fragment_block("expr.compound_assign.load");
        cir::InstId lhs_value = builder_.lvalue_to_rvalue(lhs_place.place, loc);
        cir::Fragment load_fragment = finish_fragment_block(load_block, previous);

        ExprResult rhs_value = require_value(std::move(rhs), UseContext::RValue, loc);
        syntax::BinaryOperator base_op = compound_base_operator(op);
        if (is_vector_type(object_type) || is_vector_type(rhs_value.type)) {
            ExprResult lhs_loaded;
            lhs_loaded.fragment = std::move(load_fragment);
            lhs_loaded.value = lhs_value;
            lhs_loaded.type = object_type;
            lhs_loaded.category = ValueCategory::PrValue;

            ExprResult computed_result =
                collect_vector_binary_expr(base_op,
                                           std::move(lhs_loaded),
                                           std::move(rhs_value),
                                           loc);
            ExprResult assigned_value =
                convert_to(std::move(computed_result), object_type, UseContext::Assignment, loc);

            previous = builder_.current_block();
            cir::BlockId store_block = begin_fragment_block("expr.compound_assign.vector_store");
            builder_.store(lhs_place.place, assigned_value.value, loc);
            cir::Fragment store_fragment = finish_fragment_block(store_block, previous);

            cir::Fragment fragment =
                chain(std::move(lhs_place.fragment), std::move(assigned_value.fragment), loc);
            fragment = chain(std::move(fragment), std::move(store_fragment), loc);

            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = assigned_value.value;
            result.place = lang_opts_.is_cxx_mode() ? lhs_place.place
                                                    : cir::InstId{};
            result.type = object_type;
            result.category = lang_opts_.is_cxx_mode()
                ? ValueCategory::LValue
                : ValueCategory::PrValue;
            result.has_error = lhs_place.has_error || assigned_value.has_error;
            return result;
        }
        if ((base_op == syntax::BinaryOperator::Add ||
             base_op == syntax::BinaryOperator::Sub) &&
            is_pointer_type(object_type) &&
            is_integer_type(rhs_value.type)) {
            cir::TypeId rhs_promoted = integer_promotion_type(rhs_value.type);
            rhs_value = convert_to_arithmetic_type(std::move(rhs_value), rhs_promoted, loc);

            previous = builder_.current_block();
            cir::BlockId op_block = begin_fragment_block("expr.compound_assign.ptr_op");
            cir::InstId computed = builder_.binary(binary_op_kind(base_op),
                                                   object_type,
                                                   lhs_value,
                                                   rhs_value.value,
                                                   loc);
            cir::Fragment op_fragment = finish_fragment_block(op_block, previous);

            previous = builder_.current_block();
            cir::BlockId store_block = begin_fragment_block("expr.compound_assign.store");
            builder_.store(lhs_place.place, computed, loc);
            cir::Fragment store_fragment = finish_fragment_block(store_block, previous);

            cir::Fragment fragment =
                chain(std::move(lhs_place.fragment), std::move(load_fragment), loc);
            fragment = chain(std::move(fragment), std::move(rhs_value.fragment), loc);
            fragment = chain(std::move(fragment), std::move(op_fragment), loc);
            fragment = chain(std::move(fragment), std::move(store_fragment), loc);

            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = computed;
            result.place = lang_opts_.is_cxx_mode() ? lhs_place.place
                                                    : cir::InstId{};
            result.type = object_type;
            result.category = lang_opts_.is_cxx_mode()
                ? ValueCategory::LValue
                : ValueCategory::PrValue;
            result.has_error = lhs_place.has_error || rhs_value.has_error;
            return result;
        }
        cir::TypeId arithmetic_type = {};
        if (base_op == syntax::BinaryOperator::Shl ||
            base_op == syntax::BinaryOperator::Shr) {
            diagnose_if_not_integer(object_type, loc, "compound assignment");
            diagnose_if_not_integer(rhs_value.type, loc, "compound assignment");
            arithmetic_type = integer_promotion_type(object_type);
            cir::TypeId rhs_promoted = integer_promotion_type(rhs_value.type);
            rhs_value = convert_to_arithmetic_type(std::move(rhs_value), rhs_promoted, loc);
        } else {
            arithmetic_type = binary_result_type(base_op, object_type, rhs_value.type, loc);
            if (!arithmetic_type.valid()) {
                arithmetic_type = object_type;
            }
            rhs_value = convert_to_arithmetic_type(std::move(rhs_value), arithmetic_type, loc);
        }
        if (!arithmetic_type.valid()) {
            arithmetic_type = builder_.int_type();
        }

        cir::TypeRef compound_object_ref =
            file_.place_object_ref(file_.inst(lhs_place.place).result_type);
        if ((compound_object_ref.qualifiers & cir::QualAtomic) &&
            is_integer_type(object_type)) {
            cir::AtomicRmwOp rmw_op = cir::AtomicRmwOp::Xchg;
            bool direct = true;
            switch (base_op) {
                case syntax::BinaryOperator::Add: rmw_op = cir::AtomicRmwOp::Add; break;
                case syntax::BinaryOperator::Sub: rmw_op = cir::AtomicRmwOp::Sub; break;
                case syntax::BinaryOperator::BitAnd: rmw_op = cir::AtomicRmwOp::And; break;
                case syntax::BinaryOperator::BitOr: rmw_op = cir::AtomicRmwOp::Or; break;
                case syntax::BinaryOperator::BitXor: rmw_op = cir::AtomicRmwOp::Xor; break;
                default: direct = false; break;
            }
            if (direct && is_integer_type(rhs_value.type)) {
                ExprResult operand =
                    convert_to(std::move(rhs_value), object_type, UseContext::Assignment, loc);
                cir::BlockId atomic_previous = builder_.current_block();
                cir::BlockId atomic_block =
                    begin_fragment_block("expr.compound_assign.atomic");
                cir::InstId atomic_old = builder_.atomic_rmw(lhs_place.place,
                                                             operand.value,
                                                             rmw_op,
                                                             cir::MemoryOrder::SeqCst,
                                                             loc);
                cir::InstId atomic_new = builder_.binary(binary_op_kind(base_op),
                                                         object_type,
                                                         atomic_old,
                                                         operand.value,
                                                         loc);
                cir::Fragment atomic_fragment =
                    finish_fragment_block(atomic_block, atomic_previous);
                cir::Fragment fragment =
                    chain(std::move(lhs_place.fragment), std::move(operand.fragment), loc);
                fragment = chain(std::move(fragment), std::move(atomic_fragment), loc);

                ExprResult result;
                result.fragment = std::move(fragment);
                result.value = atomic_new;
                result.place = lang_opts_.is_cxx_mode() ? lhs_place.place
                                                        : cir::InstId{};
                result.type = object_type;
                result.category = lang_opts_.is_cxx_mode()
                    ? ValueCategory::LValue
                    : ValueCategory::PrValue;
                result.has_error = lhs_place.has_error || operand.has_error;
                return result;
            }
        }

        ExprResult lhs_loaded;
        lhs_loaded.fragment = std::move(load_fragment);
        lhs_loaded.value = lhs_value;
        lhs_loaded.type = object_type;
        lhs_loaded.category = ValueCategory::PrValue;
        lhs_loaded = convert_to_arithmetic_type(std::move(lhs_loaded), arithmetic_type, loc);

        previous = builder_.current_block();
        cir::BlockId op_block = begin_fragment_block("expr.compound_assign.op");
        cir::InstId computed = builder_.binary(binary_op_kind(base_op),
                                               arithmetic_type,
                                               lhs_loaded.value,
                                               rhs_value.value,
                                               loc);
        cir::Fragment op_fragment = finish_fragment_block(op_block, previous);

        ExprResult computed_result;
        computed_result.fragment = std::move(op_fragment);
        computed_result.value = computed;
        computed_result.type = arithmetic_type;
        computed_result.category = ValueCategory::PrValue;
        ExprResult assigned_value =
            convert_to(std::move(computed_result), object_type, UseContext::Assignment, loc);

        previous = builder_.current_block();
        cir::BlockId store_block = begin_fragment_block("expr.compound_assign.store");
        builder_.store(lhs_place.place, assigned_value.value, loc);
        cir::Fragment store_fragment = finish_fragment_block(store_block, previous);

        cir::Fragment fragment =
            chain(std::move(lhs_place.fragment), std::move(lhs_loaded.fragment), loc);
        fragment = chain(std::move(fragment), std::move(rhs_value.fragment), loc);
        fragment = chain(std::move(fragment), std::move(assigned_value.fragment), loc);
        fragment = chain(std::move(fragment), std::move(store_fragment), loc);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = assigned_value.value;
        result.place = lang_opts_.is_cxx_mode() ? lhs_place.place
                                                : cir::InstId{};
        result.type = object_type;
        result.category = lang_opts_.is_cxx_mode() ? ValueCategory::LValue
                                                   : ValueCategory::PrValue;
        result.has_error = lhs_place.has_error || rhs_value.has_error || assigned_value.has_error;
        return result;
    }

    ExprResult lhs_value = require_value(std::move(lhs), UseContext::RValue, loc);
    ExprResult rhs_value = require_value(std::move(rhs), UseContext::RValue, loc);
    bool operands_value_dependent =
        expr_is_value_dependent(lhs_value) ||
        expr_is_value_dependent(rhs_value);
    bool comparison = is_comparison_operator(op);

    if (comparison && op != syntax::BinaryOperator::Equal &&
        op != syntax::BinaryOperator::NotEqual &&
        (is_complex_type(lhs_value.type) || is_complex_type(rhs_value.type))) {

        report_error("relational comparison is not defined for complex types", loc);
        ExprResult result = make_integer_literal(0, "0", loc);
        result.has_error = true;
        return result;
    }

    if (is_vector_type(lhs_value.type) || is_vector_type(rhs_value.type)) {
        return collect_vector_binary_expr(op,
                                          std::move(lhs_value),
                                          std::move(rhs_value),
                                          loc);
    }

    if ((op == syntax::BinaryOperator::Equal ||
         op == syntax::BinaryOperator::NotEqual) &&
        ((is_nullptr_type(lhs_value.type) &&
          is_nullptr_type(rhs_value.type)) ||
         (is_nullptr_type(lhs_value.type) &&
          is_integer_zero_literal(file_, rhs_value)) ||
         (is_integer_zero_literal(file_, lhs_value) &&
          is_nullptr_type(rhs_value.type)))) {
        cir::TypeId comparison_type =
            lang_opts_.is_cxx_mode() ? builder_.bool_type() : builder_.int_type();
        cir::Fragment fragment =
            chain(std::move(lhs_value.fragment), std::move(rhs_value.fragment), loc);

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.binary.nullptr_cmp");
        bool equal = op == syntax::BinaryOperator::Equal;
        cir::InstId inst = comparison_type == builder_.bool_type()
            ? builder_.boolean_literal(equal, equal ? "true" : "false", loc)
            : builder_.integer_literal(equal ? 1 : 0, equal ? "1" : "0", loc);
        cir::Fragment op_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(op_fragment), loc);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = inst;
        result.type = comparison_type;
        result.category = ValueCategory::PrValue;
        result.references_template_value_parameter =
            lhs_value.references_template_value_parameter ||
            rhs_value.references_template_value_parameter;
        result.value_dependent = operands_value_dependent;
        result.has_error = lhs_value.has_error || rhs_value.has_error;
        return result;
    }

    bool lhs_scoped_enum = is_scoped_enum_type(lhs_value.type);
    bool rhs_scoped_enum = is_scoped_enum_type(rhs_value.type);
    if (lhs_scoped_enum || rhs_scoped_enum) {
        if (comparison && lhs_scoped_enum && rhs_scoped_enum &&
            type_equal(lhs_value.type, rhs_value.type)) {
            cir::TypeId comparison_type = builder_.bool_type();
            cir::Fragment fragment =
                chain(std::move(lhs_value.fragment),
                      std::move(rhs_value.fragment),
                      loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.binary.scoped_enum");
            cir::InstId inst = builder_.binary(binary_op_kind(op),
                                               comparison_type,
                                               lhs_value.value,
                                               rhs_value.value,
                                               loc);
            cir::Fragment op_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(op_fragment), loc);

            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = inst;
            result.type = comparison_type;
            result.category = ValueCategory::PrValue;
            result.value_dependent = operands_value_dependent;
            result.has_error = lhs_value.has_error || rhs_value.has_error;
            return result;
        }

        report_error("invalid operands to binary expression involving scoped enum",
                     loc);
        ExprResult result = comparison
            ? make_boolean_literal(false, "false", loc)
            : make_integer_literal(0, "0", loc);
        cir::Fragment fragment =
            chain(std::move(lhs_value.fragment),
                  std::move(rhs_value.fragment),
                  loc);
        result.fragment = chain(std::move(fragment),
                                std::move(result.fragment),
                                loc);
        result.has_error = true;
        return result;
    }

    if (comparison &&
        (is_cir_pointer_type(file_, lhs_value.type) ||
         is_cir_pointer_type(file_, rhs_value.type))) {
        cir::TypeId comparison_type =
            lang_opts_.is_cxx_mode() ? builder_.bool_type() : builder_.int_type();
        cir::TypeId pointer_result_type;
        bool has_error = lhs_value.has_error || rhs_value.has_error;
        if (is_cir_pointer_type(file_, lhs_value.type) &&
            is_cir_pointer_type(file_, rhs_value.type)) {
            if (std::optional<cir::TypeRef> pointee =
                    common_pointer_pointee(*this,
                                           file_,
                                           lhs_value.type,
                                           rhs_value.type,
                                           PointerPointeeMode::Composite)) {
                pointer_result_type = pointer_type(*pointee);
            } else if (lang_opts_.is_c_mode()) {

                report_warning(WarningId::PointerIntegerComparison,
                               "comparison of distinct pointer types", loc);
                pointer_result_type = lhs_value.type;
            } else {
                report_error("comparison requires compatible pointer operands", loc);
                has_error = true;
                pointer_result_type = lhs_value.type;
            }
        } else if (is_cir_pointer_type(file_, lhs_value.type) &&
                   (is_integer_zero_literal(file_, rhs_value) ||
                    is_nullptr_type(rhs_value.type))) {
            pointer_result_type = lhs_value.type;
        } else if ((is_integer_zero_literal(file_, lhs_value) ||
                    is_nullptr_type(lhs_value.type)) &&
                   is_cir_pointer_type(file_, rhs_value.type)) {
            pointer_result_type = rhs_value.type;
        } else if (lang_opts_.is_c_mode()) {

            report_warning(WarningId::PointerIntegerComparison,
                           "comparison between pointer and integer", loc);
            pointer_result_type = is_cir_pointer_type(file_, lhs_value.type)
                ? lhs_value.type
                : rhs_value.type;
        } else {
            report_error("comparison requires a pointer or null pointer constant", loc);
            has_error = true;
            pointer_result_type = is_cir_pointer_type(file_, lhs_value.type)
                ? lhs_value.type
                : rhs_value.type;
        }

        lhs_value = convert_to(std::move(lhs_value), pointer_result_type, UseContext::RValue, loc);
        rhs_value = convert_to(std::move(rhs_value), pointer_result_type, UseContext::RValue, loc);

        cir::Fragment fragment =
            chain(std::move(lhs_value.fragment), std::move(rhs_value.fragment), loc);

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.binary.ptr_cmp");
        cir::InstId inst =
            builder_.binary(binary_op_kind(op),
                            comparison_type,
                            lhs_value.value,
                            rhs_value.value,
                            loc);
        cir::Fragment op_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(op_fragment), loc);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = inst;
        result.type = comparison_type;
        result.category = ValueCategory::PrValue;
        result.references_template_value_parameter =
            lhs_value.references_template_value_parameter ||
            rhs_value.references_template_value_parameter;
        result.value_dependent = operands_value_dependent;
        result.has_error = has_error || lhs_value.has_error || rhs_value.has_error;
        return result;
    }

    if ((op == syntax::BinaryOperator::Add || op == syntax::BinaryOperator::Sub) &&
        (is_cir_pointer_type(file_, lhs_value.type) || is_cir_pointer_type(file_, rhs_value.type))) {
        bool lhs_pointer = is_cir_pointer_type(file_, lhs_value.type);
        bool rhs_pointer = is_cir_pointer_type(file_, rhs_value.type);
        cir::TypeId result_type;
        bool has_error = lhs_value.has_error || rhs_value.has_error;

        if (op == syntax::BinaryOperator::Add &&
            lhs_pointer != rhs_pointer &&
            (is_integer_type(lhs_value.type) || is_integer_type(rhs_value.type))) {
            result_type = lhs_pointer ? lhs_value.type : rhs_value.type;
            if (is_integer_type(lhs_value.type)) {
                lhs_value = convert_to_arithmetic_type(
                    std::move(lhs_value), integer_promotion_type(lhs_value.type), loc);
            }
            if (is_integer_type(rhs_value.type)) {
                rhs_value = convert_to_arithmetic_type(
                    std::move(rhs_value), integer_promotion_type(rhs_value.type), loc);
            }
        } else if (op == syntax::BinaryOperator::Sub &&
                   lhs_pointer &&
                   !rhs_pointer &&
                   is_integer_type(rhs_value.type)) {
            result_type = lhs_value.type;
            rhs_value = convert_to_arithmetic_type(
                std::move(rhs_value), integer_promotion_type(rhs_value.type), loc);
        } else if (op == syntax::BinaryOperator::Sub && lhs_pointer && rhs_pointer) {
            if (!common_pointer_pointee(*this,
                                        file_,
                                        lhs_value.type,
                                        rhs_value.type,
                                        PointerPointeeMode::Compatible).has_value()) {
                report_error("pointer subtraction requires compatible pointer operands", loc);
                has_error = true;
            }
            result_type = file_.builtin_type(cir::BuiltinTypeKind::Long);
        } else {
            report_error("pointer arithmetic requires one pointer and one integer operand", loc);
            has_error = true;
            result_type = lhs_pointer ? lhs_value.type : rhs_value.type;
        }

        cir::Fragment fragment =
            chain(std::move(lhs_value.fragment), std::move(rhs_value.fragment), loc);

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.binary.ptr");
        cir::InstId inst = builder_.binary(binary_op_kind(op),
                                           result_type,
                                           lhs_value.value,
                                           rhs_value.value,
                                           loc);
        cir::Fragment op_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(op_fragment), loc);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = inst;
        result.type = result_type;
        result.category = ValueCategory::PrValue;
        result.references_template_value_parameter =
            lhs_value.references_template_value_parameter ||
            rhs_value.references_template_value_parameter;
        result.value_dependent = operands_value_dependent;
        result.has_error = has_error || lhs_value.has_error || rhs_value.has_error;
        return result;
    }

    cir::TypeId computation_type = {};
    cir::TypeId result_type = binary_result_type(op, lhs_value.type, rhs_value.type, loc);

    if (op == syntax::BinaryOperator::Shl ||
        op == syntax::BinaryOperator::Shr) {
        computation_type = integer_promotion_type(lhs_value.type);
        cir::TypeId rhs_promoted = integer_promotion_type(rhs_value.type);
        lhs_value = convert_to_arithmetic_type(std::move(lhs_value), computation_type, loc);
        rhs_value = convert_to_arithmetic_type(std::move(rhs_value), rhs_promoted, loc);
    } else if (comparison && is_meta_info_type(lhs_value.type) &&
               is_meta_info_type(rhs_value.type)) {

        computation_type = lhs_value.type;
    } else if (comparison ||
               op == syntax::BinaryOperator::Add ||
               op == syntax::BinaryOperator::Sub ||
               op == syntax::BinaryOperator::Mul ||
               op == syntax::BinaryOperator::Div ||
               op == syntax::BinaryOperator::Mod ||
               op == syntax::BinaryOperator::BitAnd ||
               op == syntax::BinaryOperator::BitOr ||
               op == syntax::BinaryOperator::BitXor) {
        computation_type =
            usual_arithmetic_conversion_type(lhs_value.type, rhs_value.type);
        if (!computation_type.valid()) {
            computation_type = builder_.int_type();
        }
        lhs_value = convert_to_arithmetic_type(std::move(lhs_value), computation_type, loc);
        rhs_value = convert_to_arithmetic_type(std::move(rhs_value), computation_type, loc);
    }
    if (!result_type.valid()) {
        result_type = computation_type.valid() ? computation_type : builder_.int_type();
    }

    cir::TemplateValueExpression lhs_expression;
    cir::TemplateValueExpression rhs_expression;
    if (operands_value_dependent) {
        lhs_expression = template_value_operand_expression(lhs_value);
        rhs_expression = template_value_operand_expression(rhs_value);
    }

    cir::Fragment fragment =
        chain(std::move(lhs_value.fragment), std::move(rhs_value.fragment), loc);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.binary");
    cir::InstId inst = builder_.binary(binary_op_kind(op), result_type, lhs_value.value, rhs_value.value, loc);
    cir::Fragment op_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(op_fragment), loc);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = result_type;
    result.category = ValueCategory::PrValue;
    result.references_template_value_parameter =
        lhs_value.references_template_value_parameter ||
        rhs_value.references_template_value_parameter;
    result.value_dependent = operands_value_dependent;
    if (auto expr_op = template_value_expr_op(op)) {
        result.template_value_expr =
            template_value_binary_expr(*expr_op,
                                       operands_value_dependent
                                           ? lhs_expression
                                           : lhs_value.template_value_expr,
                                       operands_value_dependent
                                           ? rhs_expression
                                           : rhs_value.template_value_expr,
                                       type_ref(result.type));
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context = current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
    }
    result.has_error = lhs_value.has_error || rhs_value.has_error;
    return result;
}

ExprResult Session::collect_data_member_pointer_expr(syntax::BinaryOperator op,
                                                     ExprResult lhs,
                                                     ExprResult rhs,
                                                     SrcLoc loc) {
    bool operands_value_dependent =
        expr_is_value_dependent(lhs) || expr_is_value_dependent(rhs);
    cir::TemplateValueExpression lhs_expression;
    cir::TemplateValueExpression rhs_expression;
    if (operands_value_dependent) {
        lhs_expression = template_value_operand_expression(lhs);
        rhs_expression = template_value_operand_expression(rhs);
    }
    auto retain_expression = [&](ExprResult result) {
        result.value_dependent = operands_value_dependent;
        if (!operands_value_dependent) {
            return result;
        }
        std::optional<cir::TemplateValueExprOp> graph_op =
            template_value_expr_op(op);
        if (!graph_op.has_value()) {
            return result;
        }
        result.template_value_expr = template_value_binary_expr(
            *graph_op,
            lhs_expression,
            rhs_expression,
            type_ref(result.type),
            result.category);
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context =
            current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
        return result;
    };

    bool is_arrow = op == syntax::BinaryOperator::PtrMemArrow;
    MemberAccessBase access =
        collect_member_access_base(std::move(lhs), is_arrow, loc);

    if (rhs.category == ValueCategory::MemberPointerDesignator &&
        rhs.type.valid() &&
        member_pointer_payload(file_, file_.resolved_type(rhs.type))) {
        rhs = convert_member_pointer_designator_to_target(std::move(rhs),
                                                          rhs.type,
                                                          loc);
    }
    ExprResult member_value = require_value(std::move(rhs),
                                            UseContext::RValue,
                                            loc);

    auto make_error_result = [&](std::string message) {
        report_error(std::move(message), loc);
        cir::Fragment fragment =
            chain(std::move(access.base_place.fragment),
                  std::move(member_value.fragment),
                  loc);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.memberptr.error");
        cir::InstId value = builder_.error("invalid pointer-to-member access", loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(error_fragment), loc);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = value;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    };

    cir::TypeId member_pointer_type = file_.resolved_type(member_value.type);
    if (!file_.valid(member_pointer_type) ||
        file_.type(member_pointer_type).kind != cir::TypeKind::MemberPointer) {
        return make_error_result(
            "pointer-to-member operator requires a pointer-to-member operand");
    }
    cir::TypeId object_type = file_.resolved_type(access.record_type);
    cir::TypeId member_class =
        file_.resolved_type(file_.member_pointer_class_ref(member_pointer_type).type);
    if (!file_.valid(object_type) || !file_.valid(member_class)) {
        return make_error_result(
            "pointer-to-member operator has invalid operand type");
    }

    if (object_type != member_class) {
        std::vector<cir::EntityId> base_path;
        if (!derived_to_base_path(object_type, member_class, &base_path)) {
            return make_error_result(
                "pointer-to-member operator requires an object of the member pointer class or a derived class");
        }
        if (!base_path.empty()) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.memberptr.base");
            cir::InstId adjusted =
                emit_subobject_path(access.base_place.place, base_path, loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            access.base_place.fragment =
                chain(std::move(access.base_place.fragment),
                      std::move(fragment),
                      loc);
            access.base_place.place = adjusted;
            access.base_place.type = object_type_from_place(adjusted);
        }
    }

    if (file_.member_pointer_points_to_function(member_pointer_type)) {
        cir::TypeRef member_ref =
            file_.member_pointer_member_ref(member_pointer_type);
        cir::TypeId function_type = file_.resolved_type(member_ref.type);
        if (!file_.valid(function_type) ||
            file_.type(function_type).kind != cir::TypeKind::Function) {
            return make_error_result(
                "pointer-to-member function operand has invalid function type");
        }
        const auto* function_payload =
            std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(function_type));
        if (function_payload) {
            bool object_is_lvalue =
                access.base_place.category == ValueCategory::LValue;
            if (object_is_lvalue &&
                function_payload->member_ref_qualifier ==
                    cir::FunctionRefQualifierKind::RValue) {
                return make_error_result(
                    "pointer-to-member function with '&&' ref-qualifier requires an rvalue object");
            }
            if (!object_is_lvalue &&
                function_payload->member_ref_qualifier ==
                    cir::FunctionRefQualifierKind::LValue &&
                !function_payload->member_is_const) {
                return make_error_result(
                    "pointer-to-member function with '&' ref-qualifier requires an lvalue object or const-qualified member function");
            }
        }

        ExprResult result;
        result.fragment =
            chain(std::move(access.base_place.fragment),
                  std::move(member_value.fragment),
                  loc);
        result.place = access.base_place.place;
        result.value = member_value.value;
        result.type = member_ref.type;
        result.category = ValueCategory::MemberFunctionPointerCallee;
        result.has_error = access.base_place.has_error || member_value.has_error;
        return retain_expression(std::move(result));
    }

    cir::Fragment fragment =
        chain(std::move(access.base_place.fragment),
              std::move(member_value.fragment),
              loc);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.memberptr.place");
    cir::InstId place = builder_.data_member_pointer_place(access.base_place.place,
                                                           member_value.value,
                                                           loc);
    cir::Fragment place_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(place_fragment), loc);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.place = place;
    result.type = object_type_from_place(place);
    result.category = access.base_place.category == ValueCategory::XValue
        ? ValueCategory::XValue
        : ValueCategory::LValue;
    result.has_error = access.base_place.has_error || member_value.has_error;
    return retain_expression(std::move(result));
}

std::optional<ConstMetaInfoValue> Session::evaluate_splice_operand(
    ExprResult operand,
    SrcLoc loc,
    bool* dependent) {
    if (dependent) {
        *dependent = false;
    }
    if (operand.has_error || !operand.value.valid()) {
        return std::nullopt;
    }
    bool concrete_meta_parameter = false;
    if (operand.entity.valid() && file_.valid(operand.entity)) {
        const cir::Entity& entity = file_.entity(operand.entity);
        concrete_meta_parameter = entity.has_constant_value &&
            entity.constant_value_kind == cir::TemplateValueKind::MetaInfo &&
            entity.constant_meta_kind != cir::MetaInfoKind::Null;
        if (!concrete_meta_parameter &&
            entity.kind == cir::EntityKind::TemplateParam &&
            entity.has_constant_value &&
            entity.constant_value_kind == cir::TemplateValueKind::MetaInfo &&
            entity.constant_meta_kind == cir::MetaInfoKind::Null &&
            !entity.constant_entity.valid() &&
            !entity.constant_meta_type.type.valid()) {

            if (dependent) {
                *dependent = true;
            }
            return std::nullopt;
        }
    }
    if (!concrete_meta_parameter &&
        (operand.references_template_value_parameter ||
         (in_template_definition() && expr_is_dependent(operand)))) {

        if (dependent) {
            *dependent = true;
        }
        return std::nullopt;
    }
    if (!is_meta_info_type(operand.type)) {
        report_error("splice operand must be a 'std::meta::info' value", loc);
        return std::nullopt;
    }
    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_splice_operand();
    request.loc = loc;
    request.required = true;
    ConstEvalResult result = engine.evaluate_fragment(
        operand.fragment, cir::ValueRef(operand.value), request);
    if (result.status != ConstEvalStatus::Constant ||
        !result.value.has_value() ||
        result.value->kind != ConstValueKind::MetaInfo) {
        if (result.status == ConstEvalStatus::Error &&
            !result.diagnostics.empty()) {
            report_error(result.diagnostics.front().message,
                         result.diagnostics.front().loc);
        } else {
            report_error("splice operand is not a constant reflection", loc);
        }
        return std::nullopt;
    }
    const std::shared_ptr<ConstMetaInfoValue>& handle =
        result.value->meta_info_value;
    if (!handle || handle->kind == cir::MetaInfoKind::Null) {
        report_error("cannot splice a null reflection", loc);
        return std::nullopt;
    }
    return *handle;
}

Session::SpliceTemplateResolution Session::resolve_splice_template_operand(
    ExprResult operand,
    SrcLoc loc) {
    SpliceTemplateResolution result;
    bool dependent = false;
    std::optional<ConstMetaInfoValue> handle =
        evaluate_splice_operand(std::move(operand), loc, &dependent);
    if (dependent) {
        result.dependent = true;
        return result;
    }
    if (!handle.has_value()) {
        result.has_error = true;
        return result;
    }
    if (handle->kind != cir::MetaInfoKind::Template ||
        !handle->entity.valid() || !file_.valid(handle->entity)) {
        report_error("splice-specialization operand does not designate a template",
                     loc);
        result.has_error = true;
        return result;
    }
    result.template_entity = handle->entity;
    const TemplateInfo* info = template_info(handle->entity);
    if (!info) {
        report_error("reflected template is unavailable for specialization",
                     loc);
        result.has_error = true;
        return result;
    }
    if (file_.entity(handle->entity).kind == cir::EntityKind::TemplateParam ||
        info->template_parameter_index !=
            cir::ArrayTypePayload::no_extent_param) {
        result.dependent = true;
    }
    return result;
}

Session::QualifierResolution Session::resolve_splice_scope_operand(
    ExprResult operand,
    SrcLoc loc,
    bool* dependent) {
    QualifierResolution result;
    if (dependent) {
        *dependent = false;
    }
    bool operand_dependent = false;
    std::optional<ConstMetaInfoValue> handle =
        evaluate_splice_operand(std::move(operand), loc, &operand_dependent);
    if (operand_dependent) {
        if (dependent) {
            *dependent = true;
        }
        result.dependent_type =
            type_ref(file_.dependent_type("[:splice-scope:]"));
        return result;
    }
    if (!handle.has_value()) {
        result.has_error = true;
        return result;
    }
    if (handle->kind == cir::MetaInfoKind::Namespace &&
        file_.valid(handle->entity)) {
        result.entity = handle->entity;
        result.context = file_.entity(handle->entity).semantic_context;
        result.is_namespace = true;
    } else if (handle->kind == cir::MetaInfoKind::Type) {
        cir::TypeId type = file_.resolved_type(handle->type.type);
        if (file_.valid(type) && file_.type(type).kind == cir::TypeKind::Record) {
            result.entity = file_.record_entity(type);
        } else if (file_.valid(type) &&
                   file_.type(type).kind == cir::TypeKind::Enum) {
            result.entity =
                std::get<cir::EnumTypePayload>(file_.type_payload(type)).entity;
        }
        if (result.entity.valid() && file_.valid(result.entity)) {
            result.context = file_.entity(result.entity).semantic_context;
        }
    }
    if (!result.context.valid()) {
        report_error(
            "splice before '::' must designate a namespace, class, or enumeration",
            loc);
        result.has_error = true;
    }
    return result;
}

ExprResult Session::collect_splice_expr(ExprResult operand, SrcLoc loc) {
    ExprResult result;
    result.type = builder_.unknown_type();
    result.category = ValueCategory::PrValue;
    cir::Fragment operand_fragment = operand.fragment;
    bool dependent = false;
    std::optional<ConstMetaInfoValue> handle =
        evaluate_splice_operand(std::move(operand), loc, &dependent);
    if (dependent) {
        result.fragment = std::move(operand_fragment);
        return make_dependent_expr(std::move(result), loc);
    }
    if (!handle.has_value()) {
        result.has_error = true;
        return result;
    }
    switch (handle->kind) {
        case cir::MetaInfoKind::Entity: {
            if (!file_.valid(handle->entity)) {
                break;
            }
            const cir::Entity& record = file_.entity(handle->entity);
            bool is_local =
                record.kind == cir::EntityKind::Parameter ||
                (record.kind == cir::EntityKind::Variable &&
                 (record.storage_duration == cir::StorageDuration::Automatic ||
                  record.storage_duration == cir::StorageDuration::Parameter));
            if (is_local) {

                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("expr.splice_place");
                cir::InstId place =
                    builder_.local_place(handle->entity, record.type, loc);
                result.fragment = finish_fragment_block(block, previous);
                result.place = place;
                result.entity = handle->entity;
                result.type = record.type;
                result.category = ValueCategory::LValue;
                if (is_reference_type(result.type)) {
                    result = deref_reference_lvalue(std::move(result), loc);
                }
                return result;
            }
            std::string_view name;
            if (record.name.valid()) {
                name = file_.name(record.name);
            }
            return make_entity_reference(handle->entity, name, loc);
        }
        case cir::MetaInfoKind::Type:
            report_error("a type splice is not an expression; use it in a "
                         "type position (typename[: :])",
                         loc);
            break;
        case cir::MetaInfoKind::Namespace:
            report_error("a namespace splice must form a qualified name "
                         "([: :]::)",
                         loc);
            break;
        case cir::MetaInfoKind::Template:
            report_error("splicing a template requires 'template[: :]', "
                         "which is not supported yet",
                         loc);
            break;
        case cir::MetaInfoKind::Value:
        case cir::MetaInfoKind::Null:
            report_error("cannot splice this reflection in an expression",
                         loc);
            break;
    }
    result.has_error = true;
    return result;
}

ExprResult Session::collect_splice_qualified_expr(
    ExprResult operand,
    const std::vector<std::string>& path,
    SrcLoc loc) {
    ExprResult result;
    result.type = builder_.unknown_type();
    result.category = ValueCategory::PrValue;
    result.has_error = true;
    cir::Fragment operand_fragment = operand.fragment;
    bool dependent = false;
    QualifierResolution root =
        resolve_splice_scope_operand(std::move(operand), loc, &dependent);
    if (dependent) {

        result.fragment = std::move(operand_fragment);
        result.has_error = false;
        return make_dependent_expr(std::move(result), loc);
    }
    if (root.has_error || path.empty()) {
        return result;
    }
    cir::DeclContextId scope = root.context;
    for (size_t index = 0; index + 1 < path.size(); ++index) {
        QualifierResolution component =
            resolve_qualifier_component(scope, path[index], loc);
        if (component.has_error || !component.context.valid()) {
            return result;
        }
        scope = component.context;
    }
    return lookup_qualified_name(scope, path.back(), loc);
}

cir::TypeRef Session::splice_type_operand(ExprResult operand, SrcLoc loc) {
    bool dependent = false;
    std::optional<ConstMetaInfoValue> handle =
        evaluate_splice_operand(std::move(operand), loc, &dependent);
    if (dependent) {

        return type_ref(file_.dependent_type("[:splice:]"));
    }
    if (!handle.has_value()) {
        return type_ref(file_.unknown_type());
    }
    if (handle->kind == cir::MetaInfoKind::Type && handle->type.type.valid()) {
        return handle->type;
    }
    if (handle->kind == cir::MetaInfoKind::Entity &&
        file_.valid(handle->entity) &&
        file_.entity(handle->entity).kind == cir::EntityKind::TypeAlias) {
        return type_ref(file_.entity(handle->entity).type);
    }
    report_error("splice does not designate a type", loc);
    return type_ref(file_.unknown_type());
}

ExprResult Session::collect_reflect_type_expr(cir::TypeRef type, SrcLoc loc) {
    ExprResult result;
    result.type = file_.builtin_type(cir::BuiltinTypeKind::MetaInfo);
    result.category = ValueCategory::PrValue;
    if (!type.type.valid()) {
        result.has_error = true;
        return result;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.reflect");
    cir::InstId inst = builder_.reflect_type(type, loc);
    result.fragment = finish_fragment_block(block, previous);
    result.value = inst;
    return result;
}

ExprResult Session::collect_reflect_global_namespace_expr(SrcLoc loc) {
    ExprResult result;
    result.type = file_.builtin_type(cir::BuiltinTypeKind::MetaInfo);
    result.category = ValueCategory::PrValue;
    cir::EntityId tu = file_.decl_context(translation_unit_context_).owner;
    if (!tu.valid()) {
        report_error("global namespace reflection is unavailable", loc);
        result.has_error = true;
        return result;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.reflect");
    cir::InstId inst =
        builder_.reflect_entity(cir::MetaInfoKind::Namespace, tu, loc);
    result.fragment = finish_fragment_block(block, previous);
    result.value = inst;
    return result;
}

ExprResult Session::collect_reflect_name_expr(
    bool global_qualifier,
    const std::vector<std::string>& path,
    SrcLoc loc) {
    ExprResult result;
    result.type = file_.builtin_type(cir::BuiltinTypeKind::MetaInfo);
    result.category = ValueCategory::PrValue;
    if (path.empty()) {
        result.has_error = true;
        return result;
    }

    cir::DeclContextId scope{};
    if (global_qualifier) {
        scope = resolve_qualifier_root().context;
    }
    for (size_t index = 0; index + 1 < path.size(); ++index) {
        QualifierResolution component =
            resolve_qualifier_component(scope, path[index], loc);
        if (component.has_error || !component.context.valid()) {
            result.has_error = true;
            return result;
        }
        scope = component.context;
    }

    const std::string& terminal = path.back();
    bool qualified = global_qualifier || path.size() > 1;
    cir::DeclContextId lookup_context =
        qualified ? scope : current_decl_context();

    auto emit_handle = [&](cir::MetaInfoKind kind,
                           cir::EntityId entity) -> ExprResult& {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.reflect");
        cir::InstId inst = builder_.reflect_entity(kind, entity, loc);
        result.fragment = finish_fragment_block(block, previous);
        result.value = inst;
        return result;
    };

    if (const cir::Binding* namespace_binding =
            file_.lookup_namespace_name_binding(lookup_context,
                                                terminal,
                                                /*include_parents=*/!qualified);
        namespace_binding && !namespace_binding->entities.empty()) {
        cir::EntityId named = namespace_binding->entities.back();
        if (file_.valid(named) &&
            file_.entity(named).kind == cir::EntityKind::NamespaceAlias) {
            named = file_.entity(named).namespace_alias_target;
        }
        return emit_handle(cir::MetaInfoKind::Namespace,
                           named);
    }

    const TemplateInfo* reflected_template = qualified
        ? template_info_in_context(lookup_context,
                                   terminal,
                                   /*include_parents=*/false)
        : template_info_for_name(terminal);
    if (reflected_template && reflected_template->entity.valid()) {
        return emit_handle(cir::MetaInfoKind::Template,
                           reflected_template->entity);
    }

    if (const cir::Binding* binding =
            file_.lookup_ordinary_binding(lookup_context,
                                          terminal,
                                          /*include_parents=*/!qualified);
        binding && !binding->entities.empty()) {
        if (binding->is_template_name) {
            return emit_handle(cir::MetaInfoKind::Template,
                               binding->entities.back());
        }
        if (binding->entities.size() > 1) {
            report_error("reflection of an overload set is not supported yet",
                         loc);
            result.has_error = true;
            return result;
        }
        cir::EntityId named = binding->entities.back();

        if (file_.valid(named) &&
            (file_.entity(named).kind == cir::EntityKind::Record ||
             file_.entity(named).kind == cir::EntityKind::Enum)) {

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.reflect");
            cir::InstId inst = builder_.reflect_type(
                type_ref(file_.entity(named).type), loc);
            result.fragment = finish_fragment_block(block, previous);
            result.value = inst;
            return result;
        }
        return emit_handle(cir::MetaInfoKind::Entity, named);
    }

    report_error("cannot reflect '" + terminal +
                     "': no type, namespace, or entity with that name",
                 loc);
    result.has_error = true;
    return result;
}

ExprResult Session::collect_builtin_types_compatible_expr(cir::TypeId lhs,
                                                          cir::TypeId rhs,
                                                          SrcLoc loc) {

    bool compatible =
        types_compatible(cir::TypeRef{lhs, cir::QualNone, cir::MemorySpace::Default},
                         cir::TypeRef{rhs, cir::QualNone, cir::MemorySpace::Default},
                         /*ignore_top_qualifiers=*/true);
    return make_integer_literal(compatible ? 1 : 0, compatible ? "1" : "0", loc);
}

#define ABURI_BUILTIN_TYPE_TRAIT_MAP(X)                                      \
    X(IS_SAME, IsSame)                                                       \
    X(IS_FUNCTION, IsFunction)                                               \
    X(IS_REFERENCE, IsReference)                                             \
    X(IS_LVALUE_REFERENCE, IsLValueReference)                                \
    X(IS_RVALUE_REFERENCE, IsRValueReference)                                \
    X(HAS_VIRTUAL_DESTRUCTOR, HasVirtualDestructor)                          \
    X(IS_ABSTRACT, IsAbstract)                                               \
    X(IS_ARRAY, IsArray)                                                     \
    X(IS_BOUNDED_ARRAY, IsBoundedArray)                                      \
    X(IS_UNION, IsUnion)                                                     \
    X(IS_VOLATILE, IsVolatile)                                               \
    X(IS_CONST, IsConst)                                                     \
    X(IS_EMPTY, IsEmpty)                                                     \
    X(IS_ENUM, IsEnum)                                                       \
    X(IS_SCOPED_ENUM, IsScopedEnum)                                          \
    X(IS_FUNDAMENTAL, IsFundamental)                                         \
    X(IS_VOID, IsVoid)                                                       \
    X(IS_INTEGRAL, IsIntegral)                                               \
    X(IS_FLOATING_POINT, IsFloatingPoint)                                    \
    X(IS_ARITHMETIC, IsArithmetic)                                          \
    X(IS_SCALAR, IsScalar)                                                  \
    X(IS_COMPOUND, IsCompound)                                              \
    X(IS_UNSIGNED, IsUnsigned)                                               \
    X(IS_ASSIGNABLE, IsAssignable)                                           \
    X(IS_TRIVIALLY_ASSIGNABLE, IsTriviallyAssignable)                        \
    X(IS_NOTHROW_ASSIGNABLE, IsNothrowAssignable)                            \
    X(IS_BASE_OF, IsBaseOf)                                                  \
    X(IS_CLASS, IsClass)                                                     \
    X(IS_FINAL, IsFinal)                                                     \
    X(IS_AGGREGATE, IsAggregate)                                             \
    X(IS_MEMBER_POINTER, IsMemberPointer)                                    \
    X(IS_MEMBER_OBJECT_POINTER, IsMemberObjectPointer)                       \
    X(IS_MEMBER_FUNCTION_POINTER, IsMemberFunctionPointer)                   \
    X(IS_NULL_POINTER, IsNullPointer)                                        \
    X(IS_OBJECT, IsObject)                                                   \
    X(IS_POINTER, IsPointer)                                                 \
    X(IS_POLYMORPHIC, IsPolymorphic)                                         \
    X(IS_STANDARD_LAYOUT, IsStandardLayout)                                  \
    X(IS_TRIVIAL, IsTrivial)                                                 \
    X(IS_TRIVIALLY_COPYABLE, IsTriviallyCopyable)                            \
    X(HAS_UNIQUE_OBJECT_REPRESENTATIONS, HasUniqueObjectRepresentations)     \
    X(IS_POD, IsPod)                                                         \
    X(IS_SIGNED, IsSigned)                                                   \
    X(IS_CONSTRUCTIBLE, IsConstructible)                                     \
    X(IS_TRIVIALLY_CONSTRUCTIBLE, IsTriviallyConstructible)                  \
    X(IS_NOTHROW_CONSTRUCTIBLE, IsNothrowConstructible)                      \
    X(IS_CONVERTIBLE, IsConvertible)                                         \
    X(IS_CORE_CONVERTIBLE, IsCoreConvertible)                                \
    X(IS_NOTHROW_CONVERTIBLE, IsNothrowConvertible)                          \
    X(REFERENCE_BINDS_TO_TEMPORARY, ReferenceBindsToTemporary)               \
    X(IS_DESTRUCTIBLE, IsDestructible)                                       \
    X(IS_NOTHROW_DESTRUCTIBLE, IsNothrowDestructible)                         \
    X(IS_TRIVIALLY_DESTRUCTIBLE, IsTriviallyDestructible)                    \
    X(HAS_TRIVIAL_DESTRUCTOR, HasTrivialDestructor)                           \
    X(IS_LITERAL_TYPE, IsLiteralType)

std::optional<cir::BuiltinTypeTraitKind>
Session::builtin_type_trait_kind(BuiltinKind kind) {
    switch (kind) {
#define ABURI_TO_CIR_TRAIT(builtin, cir_kind)                                 \
        case BuiltinKind::builtin:                                            \
            return cir::BuiltinTypeTraitKind::cir_kind;
        ABURI_BUILTIN_TYPE_TRAIT_MAP(ABURI_TO_CIR_TRAIT)
#undef ABURI_TO_CIR_TRAIT
        default:
            return std::nullopt;
    }
}

std::optional<BuiltinKind> Session::builtin_kind_for_type_trait(
    cir::BuiltinTypeTraitKind kind) {
    switch (kind) {
#define ABURI_FROM_CIR_TRAIT(builtin, cir_kind)                               \
        case cir::BuiltinTypeTraitKind::cir_kind:                             \
            return BuiltinKind::builtin;
        ABURI_BUILTIN_TYPE_TRAIT_MAP(ABURI_FROM_CIR_TRAIT)
#undef ABURI_FROM_CIR_TRAIT
        case cir::BuiltinTypeTraitKind::None:
            return std::nullopt;
    }
    return std::nullopt;
}

#undef ABURI_BUILTIN_TYPE_TRAIT_MAP

std::optional<bool> Session::evaluate_builtin_type_trait(
    BuiltinKind kind,
    const std::vector<cir::TypeRef>& type_args,
    SrcLoc loc) {
    size_t minimum_args = 1;
    size_t maximum_args = 1;
    switch (kind) {
        case BuiltinKind::IS_SAME:
        case BuiltinKind::IS_ASSIGNABLE:
        case BuiltinKind::IS_TRIVIALLY_ASSIGNABLE:
        case BuiltinKind::IS_NOTHROW_ASSIGNABLE:
        case BuiltinKind::IS_BASE_OF:
        case BuiltinKind::IS_CONVERTIBLE:
        case BuiltinKind::IS_CORE_CONVERTIBLE:
        case BuiltinKind::IS_NOTHROW_CONVERTIBLE:
        case BuiltinKind::REFERENCE_BINDS_TO_TEMPORARY:
            minimum_args = 2;
            maximum_args = 2;
            break;
        case BuiltinKind::IS_CONSTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE:
            maximum_args = std::numeric_limits<size_t>::max();
            break;
        default:
            break;
    }
    if (type_args.size() < minimum_args ||
        type_args.size() > maximum_args ||
        std::any_of(type_args.begin(), type_args.end(),
                    [](cir::TypeRef type) { return !type.valid(); })) {
        return std::nullopt;
    }

    auto require_trait_record = [&](cir::TypeRef input,
                                    bool follow_references) {
        input = resolve_trait_type_ref(file_, input);
        while (input.valid() && file_.valid(input.type)) {
            cir::TypeKind input_kind = file_.type(input.type).kind;
            if (input_kind == cir::TypeKind::Array) {
                const auto* array = std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(input.type));
                if (!array) {
                    return false;
                }
                input = resolve_trait_type_ref(file_, array->element_type);
                continue;
            }
            if (follow_references &&
                (input_kind == cir::TypeKind::LValueReference ||
                 input_kind == cir::TypeKind::RValueReference)) {
                input = resolve_trait_type_ref(
                    file_, file_.reference_referred_ref(input.type));
                continue;
            }
            if (input_kind != cir::TypeKind::Record) {
                return true;
            }
            const cir::RecordFacts* facts =
                file_.record_facts_for_type(input.type);
            return facts && !facts->is_incomplete
                ? true
                : require_complete_class_type(
                      input.type, loc,
                      cir::InstantiationDemandKind::CompleteClass);
        }
        return false;
    };

    bool complete_primary_property = false;
    bool complete_operation_operands = false;
    switch (kind) {
        case BuiltinKind::IS_EMPTY:
        case BuiltinKind::HAS_VIRTUAL_DESTRUCTOR:
        case BuiltinKind::IS_ABSTRACT:
        case BuiltinKind::IS_FINAL:
        case BuiltinKind::IS_AGGREGATE:
        case BuiltinKind::IS_POLYMORPHIC:
        case BuiltinKind::IS_STANDARD_LAYOUT:
        case BuiltinKind::IS_TRIVIALLY_COPYABLE:
        case BuiltinKind::IS_TRIVIAL:
        case BuiltinKind::HAS_UNIQUE_OBJECT_REPRESENTATIONS:
        case BuiltinKind::IS_POD:
        case BuiltinKind::IS_DESTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_DESTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_DESTRUCTIBLE:
        case BuiltinKind::HAS_TRIVIAL_DESTRUCTOR:
        case BuiltinKind::IS_LITERAL_TYPE:
            complete_primary_property = true;
            break;
        case BuiltinKind::IS_ASSIGNABLE:
        case BuiltinKind::IS_TRIVIALLY_ASSIGNABLE:
        case BuiltinKind::IS_NOTHROW_ASSIGNABLE:
        case BuiltinKind::IS_CONVERTIBLE:
        case BuiltinKind::IS_CORE_CONVERTIBLE:
        case BuiltinKind::IS_NOTHROW_CONVERTIBLE:
        case BuiltinKind::REFERENCE_BINDS_TO_TEMPORARY:
        case BuiltinKind::IS_CONSTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE:
            complete_operation_operands = true;
            break;
        default:
            break;
    }
    if (complete_primary_property) {
        (void)require_trait_record(type_args.front(),
                                   /*follow_references=*/false);
    } else if (complete_operation_operands) {
        for (cir::TypeRef operand : type_args) {
            (void)require_trait_record(operand,
                                       /*follow_references=*/true);
        }
    } else if (kind == BuiltinKind::IS_BASE_OF && type_args.size() == 2) {

        (void)require_trait_record(type_args[1],
                                   /*follow_references=*/false);
    }

    cir::TypeRef ref = resolve_trait_type_ref(file_, type_args.front());
    if (!ref.valid() || !file_.valid(ref.type)) {
        return std::nullopt;
    }
    const cir::TypeKind type_kind = file_.type(ref.type).kind;
    const auto* builtin = type_kind == cir::TypeKind::Builtin
        ? std::get_if<cir::BuiltinTypePayload>(&file_.type_payload(ref.type))
        : nullptr;
    const auto* record = type_kind == cir::TypeKind::Record
        ? file_.record_facts_for_type(ref.type)
        : nullptr;

    switch (kind) {
        case BuiltinKind::IS_SAME:
            return same_type_identity(type_args[0], type_args[1]);
        case BuiltinKind::IS_FUNCTION:
            return type_kind == cir::TypeKind::Function;
        case BuiltinKind::IS_REFERENCE:
            return type_kind == cir::TypeKind::LValueReference ||
                type_kind == cir::TypeKind::RValueReference;
        case BuiltinKind::IS_LVALUE_REFERENCE:
            return type_kind == cir::TypeKind::LValueReference;
        case BuiltinKind::IS_RVALUE_REFERENCE:
            return type_kind == cir::TypeKind::RValueReference;
        case BuiltinKind::IS_ARRAY:
            return type_kind == cir::TypeKind::Array;
        case BuiltinKind::IS_BOUNDED_ARRAY: {
            if (type_kind != cir::TypeKind::Array) {
                return false;
            }
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(ref.type));
            return array &&
                array->size_kind == cir::ArraySizeKind::Constant;
        }
        case BuiltinKind::IS_UNION:
            return record && record->kind == cir::RecordKind::Union;
        case BuiltinKind::IS_VOLATILE:
            return (trait_top_level_qualifiers(file_, type_args.front()) &
                    cir::QualVolatile) != 0;
        case BuiltinKind::IS_CONST:
            return (trait_top_level_qualifiers(file_, type_args.front()) &
                    cir::QualConst) != 0;
        case BuiltinKind::IS_EMPTY:
            return record && !record->is_incomplete &&
                record->kind != cir::RecordKind::Union &&
                record->is_empty == cir::ClassPropertyState::True;
        case BuiltinKind::IS_ENUM:
            return type_kind == cir::TypeKind::Enum;
        case BuiltinKind::IS_SCOPED_ENUM: {
            if (type_kind != cir::TypeKind::Enum) {
                return false;
            }
            const auto* enumeration = std::get_if<cir::EnumTypePayload>(
                &file_.type_payload(ref.type));
            return enumeration && enumeration->is_scoped;
        }
        case BuiltinKind::IS_FUNDAMENTAL:
            return trait_is_integral(file_, ref) ||
                trait_is_floating(file_, ref) ||
                (builtin &&
                 (builtin->kind == cir::BuiltinTypeKind::Void ||
                  builtin->kind == cir::BuiltinTypeKind::NullPtr));
        case BuiltinKind::IS_VOID:
            return builtin &&
                builtin->kind == cir::BuiltinTypeKind::Void;
        case BuiltinKind::IS_INTEGRAL:
            return trait_is_integral(file_, ref);
        case BuiltinKind::IS_FLOATING_POINT:
            return trait_is_floating(file_, ref);
        case BuiltinKind::IS_ARITHMETIC:
            return trait_is_integral(file_, ref) ||
                trait_is_floating(file_, ref);
        case BuiltinKind::IS_SCALAR:
            return trait_is_integral(file_, ref) ||
                trait_is_floating(file_, ref) ||
                type_kind == cir::TypeKind::Enum ||
                type_kind == cir::TypeKind::Pointer ||
                type_kind == cir::TypeKind::MemberPointer ||
                (builtin &&
                 builtin->kind == cir::BuiltinTypeKind::NullPtr);
        case BuiltinKind::IS_COMPOUND:
            return !(trait_is_integral(file_, ref) ||
                     trait_is_floating(file_, ref) ||
                     (builtin &&
                      (builtin->kind == cir::BuiltinTypeKind::Void ||
                       builtin->kind == cir::BuiltinTypeKind::NullPtr)));
        case BuiltinKind::IS_UNSIGNED:
            return trait_is_integral(file_, ref) &&
                (file_.operator_value_domain(ref) ==
                     cir::OperatorValueDomain::UnsignedInteger ||
                 file_.operator_value_domain(ref) ==
                     cir::OperatorValueDomain::Bool);
        case BuiltinKind::IS_BASE_OF: {
            cir::TypeRef derived =
                resolve_trait_type_ref(file_, type_args[1]);
            const cir::RecordFacts* base_record =
                file_.record_facts_for_type(ref.type);
            const cir::RecordFacts* derived_record = derived.valid()
                ? file_.record_facts_for_type(derived.type)
                : nullptr;
            if (!base_record || !derived_record ||
                base_record->kind == cir::RecordKind::Union ||
                derived_record->kind == cir::RecordKind::Union) {
                return false;
            }
            if (ref.type == derived.type) {
                return true;
            }
            return analyze_derived_to_base_path(derived.type, ref.type).kind !=
                DerivedToBasePathKind::NotFound;
        }
        case BuiltinKind::IS_ASSIGNABLE:
            return probe_assignment(type_args[0], type_args[1]).viable;
        case BuiltinKind::IS_TRIVIALLY_ASSIGNABLE: {
            OperationProbe probe =
                probe_assignment(type_args[0], type_args[1]);
            return probe.viable && probe.trivial;
        }
        case BuiltinKind::IS_NOTHROW_ASSIGNABLE: {
            OperationProbe probe =
                probe_assignment(type_args[0], type_args[1]);
            return probe.viable && probe.nothrow;
        }
        case BuiltinKind::IS_CONVERTIBLE:
            return probe_implicit_conversion(type_args[0], type_args[1])
                .viable;
        case BuiltinKind::IS_CORE_CONVERTIBLE:
            return probe_implicit_conversion(type_args[0], type_args[1],
                                              /*core_convertibility=*/true)
                .viable;
        case BuiltinKind::IS_NOTHROW_CONVERTIBLE: {
            OperationProbe probe =
                probe_implicit_conversion(type_args[0], type_args[1]);
            return probe.viable && probe.nothrow;
        }
        case BuiltinKind::REFERENCE_BINDS_TO_TEMPORARY:
            return probe_reference_binds_to_temporary(type_args[0],
                                                      type_args[1]);
        case BuiltinKind::IS_CONSTRUCTIBLE: {
            std::vector<cir::TypeRef> arguments(type_args.begin() + 1,
                                                type_args.end());
            return probe_construction(type_args.front(), arguments).viable;
        }
        case BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE: {
            std::vector<cir::TypeRef> arguments(type_args.begin() + 1,
                                                type_args.end());
            OperationProbe probe =
                probe_construction(type_args.front(), arguments);
            return probe.viable && probe.trivial;
        }
        case BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE: {
            std::vector<cir::TypeRef> arguments(type_args.begin() + 1,
                                                type_args.end());
            OperationProbe probe =
                probe_construction(type_args.front(), arguments);
            return probe.viable && probe.nothrow;
        }
        case BuiltinKind::IS_CLASS:
            return record && record->kind != cir::RecordKind::Union;
        case BuiltinKind::HAS_VIRTUAL_DESTRUCTOR:
            return record && !record->is_incomplete &&
                record->has_virtual_destructor;
        case BuiltinKind::IS_ABSTRACT:
            return record && !record->is_incomplete && record->is_abstract;
        case BuiltinKind::IS_FINAL:
            return record && !record->is_incomplete && record->is_final;
        case BuiltinKind::IS_AGGREGATE:
            return type_kind == cir::TypeKind::Array ||
                (record && !record->is_incomplete &&
                 record->is_aggregate == cir::ClassPropertyState::True);
        case BuiltinKind::IS_MEMBER_POINTER:
            return type_kind == cir::TypeKind::MemberPointer;
        case BuiltinKind::IS_MEMBER_OBJECT_POINTER:
        case BuiltinKind::IS_MEMBER_FUNCTION_POINTER: {
            if (type_kind != cir::TypeKind::MemberPointer) {
                return false;
            }
            const auto* member = std::get_if<cir::MemberPointerTypePayload>(
                &file_.type_payload(ref.type));
            if (!member) {
                return false;
            }
            cir::TypeRef member_type =
                resolve_trait_type_ref(file_, member->member_type);
            bool is_function = member_type.valid() &&
                file_.valid(member_type.type) &&
                file_.type(member_type.type).kind == cir::TypeKind::Function;
            return kind == BuiltinKind::IS_MEMBER_FUNCTION_POINTER
                ? is_function
                : !is_function;
        }
        case BuiltinKind::IS_NULL_POINTER:
            return builtin &&
                builtin->kind == cir::BuiltinTypeKind::NullPtr;
        case BuiltinKind::IS_OBJECT:
            if (type_kind == cir::TypeKind::Function ||
                type_kind == cir::TypeKind::LValueReference ||
                type_kind == cir::TypeKind::RValueReference ||
                type_kind == cir::TypeKind::Invalid ||
                type_kind == cir::TypeKind::Error ||
                type_kind == cir::TypeKind::Unknown ||
                type_kind == cir::TypeKind::Place) {
                return false;
            }
            return !builtin || builtin->kind != cir::BuiltinTypeKind::Void;
        case BuiltinKind::IS_POINTER:
            return type_kind == cir::TypeKind::Pointer;
        case BuiltinKind::IS_POLYMORPHIC:
            return record && !record->is_incomplete &&
                record->is_polymorphic;
        case BuiltinKind::IS_STANDARD_LAYOUT: {
            std::function<bool(cir::TypeRef)> is_standard_layout_type;
            is_standard_layout_type = [&](cir::TypeRef input) {
                input = resolve_trait_type_ref(file_, input);
                if (!input.valid() || !file_.valid(input.type)) {
                    return false;
                }
                const cir::Type& candidate = file_.type(input.type);
                if (candidate.kind == cir::TypeKind::Array) {
                    const auto* array = std::get_if<cir::ArrayTypePayload>(
                        &file_.type_payload(input.type));
                    return array &&
                        is_standard_layout_type(array->element_type);
                }
                if (candidate.kind == cir::TypeKind::Record) {
                    const cir::RecordFacts* facts =
                        file_.record_facts_for_type(input.type);
                    return facts && !facts->is_incomplete &&
                        facts->is_standard_layout ==
                            cir::ClassPropertyState::True;
                }
                if (candidate.kind == cir::TypeKind::Builtin) {
                    const auto* candidate_builtin =
                        std::get_if<cir::BuiltinTypePayload>(
                            &file_.type_payload(input.type));
                    if (candidate_builtin &&
                        candidate_builtin->kind ==
                            cir::BuiltinTypeKind::Void) {
                        return false;
                    }
                }
                return candidate.kind != cir::TypeKind::Function &&
                    candidate.kind != cir::TypeKind::LValueReference &&
                    candidate.kind != cir::TypeKind::RValueReference;
            };
            return is_standard_layout_type(ref);
        }
        case BuiltinKind::IS_SIGNED:
            return trait_is_floating(file_, ref) ||
                (trait_is_integral(file_, ref) &&
                 file_.operator_value_domain(ref) ==
                     cir::OperatorValueDomain::SignedInteger);
        case BuiltinKind::IS_TRIVIALLY_COPYABLE: {
            std::function<bool(cir::TypeRef)> is_trivially_copyable;
            is_trivially_copyable = [&](cir::TypeRef input) {
                input = resolve_trait_type_ref(file_, input);
                if (!input.valid() || !file_.valid(input.type)) {
                    return false;
                }
                cir::TypeKind input_kind = file_.type(input.type).kind;
                if (input_kind == cir::TypeKind::Array) {
                    const auto* array = std::get_if<cir::ArrayTypePayload>(
                        &file_.type_payload(input.type));
                    return array &&
                        is_trivially_copyable(array->element_type);
                }
                if (input_kind == cir::TypeKind::Record) {
                    const cir::RecordFacts* facts =
                        file_.record_facts_for_type(input.type);
                    return facts && !facts->is_incomplete &&
                        facts->is_trivially_copyable ==
                            cir::ClassPropertyState::True;
                }
                if (input_kind == cir::TypeKind::Function ||
                    input_kind == cir::TypeKind::LValueReference ||
                    input_kind == cir::TypeKind::RValueReference) {
                    return false;
                }
                if (input_kind == cir::TypeKind::Builtin) {
                    const auto* input_builtin =
                        std::get_if<cir::BuiltinTypePayload>(
                            &file_.type_payload(input.type));
                    return input_builtin &&
                        input_builtin->kind != cir::BuiltinTypeKind::Void;
                }
                return input_kind == cir::TypeKind::Pointer ||
                    input_kind == cir::TypeKind::BlockPointer ||
                    input_kind == cir::TypeKind::MemberPointer ||
                    input_kind == cir::TypeKind::Enum ||
                    input_kind == cir::TypeKind::Vector ||
                    input_kind == cir::TypeKind::BitInt;
            };
            return is_trivially_copyable(ref);
        }
        case BuiltinKind::IS_TRIVIAL: {
            if (record) {
                return !record->is_incomplete &&
                    record->is_trivial == cir::ClassPropertyState::True;
            }
            if (type_kind == cir::TypeKind::Array) {
                const auto* array = std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(ref.type));
                return array && evaluate_builtin_type_trait(
                    BuiltinKind::IS_TRIVIAL, {array->element_type})
                    .value_or(false);
            }
            return evaluate_builtin_type_trait(
                BuiltinKind::IS_TRIVIALLY_COPYABLE, {ref})
                .value_or(false);
        }
        case BuiltinKind::HAS_UNIQUE_OBJECT_REPRESENTATIONS: {
            std::vector<cir::TypeId> record_stack;
            return trait_has_unique_object_representations(
                file_, ref, record_stack);
        }
        case BuiltinKind::IS_POD:
            return evaluate_builtin_type_trait(
                       BuiltinKind::IS_TRIVIAL, {ref})
                       .value_or(false) &&
                evaluate_builtin_type_trait(
                    BuiltinKind::IS_STANDARD_LAYOUT, {ref})
                    .value_or(false);
        case BuiltinKind::IS_DESTRUCTIBLE: {
            std::function<bool(cir::TypeRef)> is_destructible;
            is_destructible = [&](cir::TypeRef input) {
                input = resolve_trait_type_ref(file_, input);
                if (!input.valid() || !file_.valid(input.type)) {
                    return false;
                }
                cir::TypeKind input_kind = file_.type(input.type).kind;
                if (input_kind == cir::TypeKind::LValueReference ||
                    input_kind == cir::TypeKind::RValueReference) {
                    return true;
                }
                if (input_kind == cir::TypeKind::Array) {
                    const auto* array = std::get_if<cir::ArrayTypePayload>(
                        &file_.type_payload(input.type));
                    return array &&
                        array->size_kind == cir::ArraySizeKind::Constant &&
                        is_destructible(array->element_type);
                }
                if (input_kind == cir::TypeKind::Record) {
                    const cir::RecordFacts* facts =
                        file_.record_facts_for_type(input.type);
                    const cir::RecordMethodFact* destructor =
                        selected_record_destructor(input.type);
                    return facts && !facts->is_incomplete && destructor &&
                        destructor->is_selected_destructor &&
                        destructor->is_eligible && !destructor->is_deleted &&
                        destructor->declared_access ==
                            cir::RecordMemberAccess::Public;
                }
                if (input_kind == cir::TypeKind::Function) {
                    return false;
                }
                if (input_kind == cir::TypeKind::Builtin) {
                    const auto* input_builtin =
                        std::get_if<cir::BuiltinTypePayload>(
                            &file_.type_payload(input.type));
                    return input_builtin &&
                        input_builtin->kind != cir::BuiltinTypeKind::Void;
                }
                return input_kind != cir::TypeKind::Invalid &&
                    input_kind != cir::TypeKind::Error &&
                    input_kind != cir::TypeKind::Unknown &&
                    input_kind != cir::TypeKind::Place;
            };
            return is_destructible(ref);
        }
        case BuiltinKind::IS_NOTHROW_DESTRUCTIBLE: {
            std::function<bool(cir::TypeRef)> is_nothrow_destructible;
            is_nothrow_destructible = [&](cir::TypeRef input) {
                input = resolve_trait_type_ref(file_, input);
                if (!input.valid() || !file_.valid(input.type)) {
                    return false;
                }
                cir::TypeKind input_kind = file_.type(input.type).kind;
                if (input_kind == cir::TypeKind::LValueReference ||
                    input_kind == cir::TypeKind::RValueReference) {
                    return true;
                }
                if (input_kind == cir::TypeKind::Array) {
                    const auto* array = std::get_if<cir::ArrayTypePayload>(
                        &file_.type_payload(input.type));
                    return array &&
                        array->size_kind == cir::ArraySizeKind::Constant &&
                        is_nothrow_destructible(array->element_type);
                }
                if (!evaluate_builtin_type_trait(
                        BuiltinKind::IS_DESTRUCTIBLE, {input})
                         .value_or(false)) {
                    return false;
                }
                if (input_kind != cir::TypeKind::Record) {
                    return true;
                }
                const cir::RecordMethodFact* destructor =
                    selected_record_destructor(input.type);
                if (!destructor || !destructor->type.valid()) {
                    return false;
                }
                cir::TypeId destructor_type =
                    file_.resolved_type(destructor->type.type);
                const auto* payload = file_.valid(destructor_type)
                    ? std::get_if<cir::FunctionTypePayload>(
                          &file_.type_payload(destructor_type))
                    : nullptr;
                return payload &&
                    payload->exception_spec.kind ==
                        cir::FunctionExceptionSpecKind::NonThrowing;
            };
            return is_nothrow_destructible(ref);
        }
        case BuiltinKind::IS_TRIVIALLY_DESTRUCTIBLE: {
            std::vector<cir::TypeId> record_stack;
            return type_is_trivially_destructible(
                file_, type_args.front().type, record_stack);
        }
        case BuiltinKind::HAS_TRIVIAL_DESTRUCTOR: {
            std::vector<cir::TypeId> record_stack;
            return type_is_trivially_destructible(
                file_, type_args.front().type, record_stack);
        }
        case BuiltinKind::IS_LITERAL_TYPE:
            return is_literal_type(type_args.front().type);
        default:
            return std::nullopt;
    }
}

ExprResult Session::collect_builtin_type_trait_expr(
    BuiltinKind kind,
    std::vector<cir::TypeRef> type_args,
    std::vector<bool> pack_expansions,
    SrcLoc loc) {
    std::optional<cir::BuiltinTypeTraitKind> trait_kind =
        builtin_type_trait_kind(kind);
    const bool supported = trait_kind.has_value() &&
        is_supported_builtin_kind(kind);
    const bool binary_trait = kind == BuiltinKind::IS_SAME ||
        kind == BuiltinKind::IS_BASE_OF ||
        kind == BuiltinKind::IS_ASSIGNABLE ||
        kind == BuiltinKind::IS_TRIVIALLY_ASSIGNABLE ||
        kind == BuiltinKind::IS_NOTHROW_ASSIGNABLE ||
        kind == BuiltinKind::IS_CONVERTIBLE ||
        kind == BuiltinKind::IS_CORE_CONVERTIBLE ||
        kind == BuiltinKind::IS_NOTHROW_CONVERTIBLE ||
        kind == BuiltinKind::REFERENCE_BINDS_TO_TEMPORARY;
    const size_t expected_args = binary_trait ? 2 : 1;
    const bool variadic_trait = kind == BuiltinKind::IS_CONSTRUCTIBLE ||
        kind == BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE ||
        kind == BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE;
    bool valid_arguments =
        (variadic_trait ? !type_args.empty()
                        : type_args.size() == expected_args) &&
        pack_expansions.size() == type_args.size() &&
        std::all_of(type_args.begin(), type_args.end(), [](cir::TypeRef type) {
            return type.type.valid();
        });
    std::vector<uint32_t> pack_indices(
        type_args.size(), cir::TemplateValueExprNoParameter);
    if (valid_arguments) {
        for (size_t i = 0; i < type_args.size(); ++i) {
            if (!pack_expansions[i]) {
                continue;
            }
            std::optional<uint32_t> index =
                type_parameter_pack_index(type_args[i].type);
            if (!index.has_value()) {
                valid_arguments = false;
                break;
            }
            pack_indices[i] = *index;
        }
    }
    if (!supported || !valid_arguments) {
        ExprResult result = make_boolean_literal(false, "false", loc);
        result.has_error = true;
        report_error("invalid builtin type trait invocation", loc);
        return result;
    }

    bool dependent = std::any_of(
        type_args.begin(), type_args.end(), [&](cir::TypeRef type) {
            return is_dependent_type(type.type);
        });
    if (dependent) {
        ExprResult result = make_dependent_boolean_expr(loc);
        result.value_dependent = true;
        result.template_value_expr = template_value_type_trait_expr(
            file_, *trait_kind, type_args, pack_indices,
            type_ref(result.type));
        result.template_value_expr.loc = loc;
        result.template_value_expr.definition_context =
            current_decl_context();
        result.template_value_expr.definition_lookup_generation =
            lookup_generation_;
        return result;
    }

    std::optional<bool> value =
        evaluate_builtin_type_trait(kind, type_args, loc);
    if (!value.has_value()) {
        ExprResult result = make_boolean_literal(false, "false", loc);
        result.has_error = true;
        report_error("builtin type trait is not implemented", loc);
        return result;
    }
    return make_boolean_literal(*value,
                                *value ? "true" : "false",
                                loc);
}

ExprResult Session::collect_generic_selection(ExprResult controlling,
                                              std::vector<GenericAssociation> associations,
                                              SrcLoc loc) {

    bool has_error = controlling.has_error;
    ExprResult converted =
        require_value(std::move(controlling), UseContext::RValue, loc);
    cir::TypeId controlling_type = file_.resolved_type(converted.type);
    cir::TypeRef controlling_ref{controlling_type, cir::QualNone,
                                 cir::MemorySpace::Default};

    int default_index = -1;
    int match_index = -1;
    for (size_t i = 0; i < associations.size(); ++i) {
        GenericAssociation& assoc = associations[i];
        has_error = has_error || assoc.expr.has_error;
        if (assoc.is_default) {
            if (default_index >= 0) {
                report_error("duplicate default generic association", assoc.loc);
                has_error = true;
                continue;
            }
            default_index = static_cast<int>(i);
            continue;
        }
        if (!assoc.type.valid()) {
            has_error = true;
            continue;
        }
        for (size_t j = 0; j < i; ++j) {
            if (!associations[j].is_default && associations[j].type.valid() &&
                types_compatible(assoc.type, associations[j].type)) {
                report_error("generic association type '" +
                                 file_.format_type(assoc.type) +
                                 "' is compatible with a previous association type",
                             assoc.loc);
                has_error = true;
                break;
            }
        }
        if (match_index < 0 && controlling_type.valid() &&
            types_compatible(assoc.type, controlling_ref)) {
            match_index = static_cast<int>(i);
        }
    }

    int selected = match_index >= 0 ? match_index : default_index;
    if (selected < 0) {
        report_error("controlling expression type '" +
                         file_.format_type(controlling_ref) +
                         "' is not compatible with any generic association",
                     loc);
        ExprResult result = make_integer_literal(0, "0", loc);
        result.has_error = true;
        return result;
    }

    ExprResult result = std::move(associations[selected].expr);
    result.has_error = result.has_error || has_error;
    return result;
}

ExprResult Session::collect_builtin_choose_expr(ExprResult condition,
                                                ExprResult true_expr,
                                                ExprResult false_expr,
                                                SrcLoc loc) {
    int64_t choice = 0;
    if (!evaluate_integer_constant(
            condition,
            choice,
            loc,
            "__builtin_choose_expr first argument must be a compile-time integer constant expression")) {
        ExprResult result = make_integer_literal(0, "0", loc);
        result.has_error = true;
        return result;
    }
    return choice != 0 ? std::move(true_expr) : std::move(false_expr);
}

ExprResult Session::collect_builtin_convertvector_expr(ExprResult vector,
                                                       cir::TypeRef target_ref,
                                                       SrcLoc loc) {
    cir::TypeId target_type = target_ref.type;
    const bool dependent =
        expr_is_value_dependent(vector) ||
        type_contains_dependent_alias_specialization(vector.type) ||
        is_dependent_type(target_type) ||
        type_contains_dependent_alias_specialization(target_type);
    if (dependent) {
        vector.value_dependent = true;
        return make_deferred_typed_expr(
            std::move(vector),
            target_type.valid() ? target_type : builder_.unknown_type(),
            ValueCategory::PrValue,
            loc);
    }

    ExprResult source = require_value(std::move(vector), UseContext::RValue, loc);
    bool has_error = source.has_error;
    if (!is_vector_type(source.type)) {
        report_error("__builtin_convertvector first argument must have vector type", loc);
        has_error = true;
    }
    if (!is_vector_type(target_type)) {
        report_error("__builtin_convertvector second argument must be a vector type", loc);
        has_error = true;
        if (!target_type.valid()) {
            target_type = builder_.unknown_type();
        }
    }
    if (is_vector_type(source.type) && is_vector_type(target_type) &&
        file_.vector_element_count(source.type) != file_.vector_element_count(target_type)) {
        report_error("__builtin_convertvector source and destination vectors must have the same number of elements",
                     loc);
        has_error = true;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.builtin.convertvector");
    cir::InstId inst = builder_.builtin_call(BuiltinKind::CONVERTVECTOR,
                                             "__builtin_convertvector",
                                             target_type,
                                             {source.value},
                                             loc,
                                             file_.type_ref(target_type));
    cir::Fragment builtin_fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(source.fragment), std::move(builtin_fragment), loc);
    result.value = inst;
    result.type = target_type;
    result.category = ValueCategory::PrValue;
    result.has_error = has_error;
    return result;
}

ExprResult Session::collect_builtin_bit_cast_expr(cir::TypeRef target_ref,
                                                  ExprResult source,
                                                  SrcLoc loc) {
    cir::TypeId target_type = file_.resolved_type(target_ref.type);
    cir::TypeId source_type = file_.resolved_type(source.type);
    const bool dependent = is_dependent_type(target_type) ||
        expr_is_dependent(source) || is_dependent_type(source_type);
    if (dependent) {
        source.value_dependent = true;
        if (is_dependent_type(target_type)) {
            return make_dependent_expr(std::move(source), loc);
        }
        return make_deferred_typed_expr(std::move(source),
                                        target_type,
                                        ValueCategory::PrValue,
                                        loc);
    }

    bool has_error = source.has_error;
    auto is_object_type = [&](cir::TypeId type, bool allow_array) {
        if (!file_.valid(type)) {
            return false;
        }
        switch (file_.type(type).kind) {
            case cir::TypeKind::Function:
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference:
            case cir::TypeKind::Place:
                return false;
            case cir::TypeKind::Array:
                return allow_array;
            case cir::TypeKind::Builtin: {
                const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
                    &file_.type_payload(type));
                return builtin &&
                    builtin->kind != cir::BuiltinTypeKind::Void;
            }
            default:
                return true;
        }
    };

    if (!is_object_type(target_type, /*allow_array=*/false)) {
        report_error("__builtin_bit_cast destination must be a complete object type",
                     loc);
        has_error = true;
        if (!file_.valid(target_type)) {
            target_type = builder_.unknown_type();
            target_ref = file_.type_ref(target_type);
        }
    }
    if (!is_object_type(source_type, /*allow_array=*/true)) {
        report_error("__builtin_bit_cast source must have object type", loc);
        has_error = true;
    }

    if (file_.consteval_only_type_state(target_type) ==
        cir::ClassPropertyState::True) {
        report_error("__builtin_bit_cast destination type must not be consteval-only",
                     loc);
        has_error = true;
    }
    if (file_.consteval_only_type_state(source_type) ==
        cir::ClassPropertyState::True) {
        report_error("__builtin_bit_cast source type must not be consteval-only",
                     loc);
        has_error = true;
    }

    std::optional<bool> target_trivial = evaluate_builtin_type_trait(
        BuiltinKind::IS_TRIVIALLY_COPYABLE, {target_ref});
    std::optional<bool> source_trivial = evaluate_builtin_type_trait(
        BuiltinKind::IS_TRIVIALLY_COPYABLE, {file_.type_ref(source_type)});
    if (!target_trivial.value_or(false)) {
        report_error("__builtin_bit_cast destination type must be trivially copyable",
                     loc);
        has_error = true;
    }
    if (!source_trivial.value_or(false)) {
        report_error("__builtin_bit_cast source type must be trivially copyable",
                     loc);
        has_error = true;
    }

    std::optional<std::pair<size_t, size_t>> target_layout;
    std::optional<std::pair<size_t, size_t>> source_layout;
    if (is_object_type(target_type, /*allow_array=*/false)) {
        target_layout = size_align_of_type(target_type, loc);
    }
    if (is_object_type(source_type, /*allow_array=*/true)) {
        source_layout = size_align_of_type(source_type, loc);
    }
    if (!target_layout.has_value() || !source_layout.has_value()) {
        report_error("__builtin_bit_cast requires complete source and destination types",
                     loc);
        has_error = true;
    } else if (target_layout->first != source_layout->first) {
        report_error("__builtin_bit_cast source and destination must have the same size",
                     loc);
        has_error = true;
    }

    if (file_.valid(source_type) &&
        file_.type(source_type).kind == cir::TypeKind::Array &&
        source.place.valid()) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.builtin.bit_cast.source");
        source.value = builder_.lvalue_to_rvalue(source.place, loc);
        cir::Fragment load_fragment = finish_fragment_block(block, previous);
        source.fragment = chain(std::move(source.fragment),
                                std::move(load_fragment), loc);
        source.category = ValueCategory::PrValue;
    } else {
        source = require_value(std::move(source), UseContext::RValue, loc);
    }
    has_error = has_error || source.has_error;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.builtin.bit_cast");
    cir::InstId inst = builder_.builtin_call(BuiltinKind::BIT_CAST,
                                             "__builtin_bit_cast",
                                             target_type,
                                             {source.value},
                                             loc,
                                             target_ref);
    cir::Fragment builtin_fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(source.fragment),
                            std::move(builtin_fragment), loc);
    result.value = inst;
    result.type = target_type;
    result.category = ValueCategory::PrValue;
    result.has_error = has_error;
    return result;
}

ExprResult Session::collect_offsetof_expr(cir::TypeId type,
                                          std::vector<InitDesignator> designators,
                                          SrcLoc loc) {
    bool has_error = false;
    size_t offset = 0;
    std::optional<ExprResult> runtime_offset;
    cir::TypeId current_type = file_.resolved_type(type);

    if (is_dependent_type(current_type)) {
        bump_pattern_taint();
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.offsetof.dependent");
        cir::InstId value = builder_.name_ref(
            "<dependent-offsetof>", builder_.usize_type(), loc);

        ExprResult result;
        result.fragment = finish_fragment_block(block, previous);
        result.value = value;
        result.type = file_.inst(value).result_type;
        result.category = ValueCategory::PrValue;
        result.references_template_value_parameter = true;
        result.value_dependent = true;
        result.has_error = designators.empty();
        return result;
    }

    (void)require_complete_class_type(
        current_type, loc, cir::InstantiationDemandKind::CompleteClass);
    current_type = file_.resolved_type(type);

    if (!file_.valid(current_type) ||
        file_.type(current_type).kind != cir::TypeKind::Record) {
        report_error("__builtin_offsetof requires a struct, class, or union type", loc);
        has_error = true;
    }
    if (designators.empty()) {
        report_error("__builtin_offsetof requires a member designator", loc);
        has_error = true;
    }

    for (InitDesignator& designator : designators) {
        if (has_error) {
            break;
        }
        switch (designator.kind) {
            case InitDesignatorKind::Field: {
                current_type = file_.resolved_type(current_type);
                if (!file_.valid(current_type) ||
                    file_.type(current_type).kind != cir::TypeKind::Record) {
                    report_error("field designator in __builtin_offsetof applied to non-record type",
                                 designator.loc);
                    has_error = true;
                    break;
                }
                FieldPathLookupResult path =
                    lookup_field_path(current_type, designator.field_name);
                if (path.ambiguous) {
                    report_error("member '" + designator.field_name +
                                     "' is ambiguous in __builtin_offsetof",
                                 designator.loc);
                    has_error = true;
                    break;
                }
                if (!path.found || path.entities.empty()) {
                    report_error("record has no member named '" + designator.field_name +
                                     "' in __builtin_offsetof",
                                 designator.loc);
                    has_error = true;
                    break;
                }
                for (cir::EntityId field_entity : path.entities) {
                    const cir::RecordFieldFact* field = file_.field_fact(field_entity);
                    if (!field) {
                        report_error("member layout is unavailable in __builtin_offsetof",
                                     designator.loc);
                        has_error = true;
                        break;
                    }
                    if (field->is_bitfield) {
                        report_error("cannot compute __builtin_offsetof for bit-field member",
                                     designator.loc);
                        has_error = true;
                        break;
                    }
                    offset += field->offset;
                    current_type = file_.resolved_type(field->type.type);
                }
                break;
            }
            case InitDesignatorKind::Index: {
                current_type = file_.resolved_type(current_type);
                if (!file_.valid(current_type) ||
                    file_.type(current_type).kind != cir::TypeKind::Array) {
                    report_error("array designator in __builtin_offsetof applied to non-array type",
                                 designator.loc);
                    has_error = true;
                    break;
                }
                const auto* array =
                    std::get_if<cir::ArrayTypePayload>(&file_.type_payload(current_type));
                if (!array) {
                    has_error = true;
                    break;
                }
                std::optional<size_t> element_size =
                    size_of_type(array->element_type.type, designator.loc);
                if (!element_size.has_value()) {
                    report_error("array designator in __builtin_offsetof has incomplete element type",
                                 designator.loc);
                    has_error = true;
                    break;
                }
                int64_t index = 0;
                if (try_evaluate_integer_constant(designator.index, index)) {
                    if (index < 0) {
                        report_error("array designator in __builtin_offsetof cannot be negative",
                                     designator.loc);
                        has_error = true;
                        break;
                    }
                    offset += static_cast<size_t>(index) * *element_size;
                    current_type = file_.resolved_type(array->element_type.type);
                    break;
                }
                ExprResult index_value = require_value(std::move(designator.index),
                                                       UseContext::RValue,
                                                       designator.loc);
                if (index_value.value.valid() && is_integer_type(index_value.type)) {

                    ExprResult scaled = collect_binary_expr(
                        syntax::BinaryOperator::Mul,
                        std::move(index_value),
                        make_integer_literal(static_cast<int64_t>(*element_size),
                                             std::to_string(*element_size),
                                             builder_.usize_type(),
                                             designator.loc),
                        designator.loc);
                    if (runtime_offset.has_value()) {
                        runtime_offset = collect_binary_expr(syntax::BinaryOperator::Add,
                                                             std::move(*runtime_offset),
                                                             std::move(scaled),
                                                             designator.loc);
                    } else {
                        runtime_offset = std::move(scaled);
                    }
                } else {
                    report_error("array designator in __builtin_offsetof is not an integer expression",
                                 designator.loc);
                    has_error = true;
                    break;
                }
                current_type = file_.resolved_type(array->element_type.type);
                break;
            }
            case InitDesignatorKind::Range:
                report_error("range designator is not valid in __builtin_offsetof",
                             designator.loc);
                has_error = true;
                break;
        }
    }

    ExprResult result =
        make_integer_literal(static_cast<int64_t>(offset),
                             std::to_string(offset),
                             builder_.usize_type(),
                             loc);
    if (runtime_offset.has_value() && !has_error) {
        result = collect_binary_expr(syntax::BinaryOperator::Add,
                                     std::move(result),
                                     std::move(*runtime_offset),
                                     loc);
        result = convert_to_arithmetic_type(std::move(result),
                                            builder_.usize_type(),
                                            loc);
    }
    result.has_error = has_error;
    return result;
}

namespace {

bool atomic_kind_is_op_fetch(BuiltinKind kind) {
    switch (kind) {
        case BuiltinKind::ATOMIC_ADD_FETCH:
        case BuiltinKind::ATOMIC_SUB_FETCH:
        case BuiltinKind::ATOMIC_AND_FETCH:
        case BuiltinKind::ATOMIC_OR_FETCH:
        case BuiltinKind::ATOMIC_XOR_FETCH:
        case BuiltinKind::ATOMIC_NAND_FETCH:
        case BuiltinKind::SYNC_ADD_AND_FETCH:
        case BuiltinKind::SYNC_SUB_AND_FETCH:
        case BuiltinKind::SYNC_OR_AND_FETCH:
        case BuiltinKind::SYNC_AND_AND_FETCH:
        case BuiltinKind::SYNC_XOR_AND_FETCH:
        case BuiltinKind::SYNC_NAND_AND_FETCH:
            return true;
        default:
            return false;
    }
}

cir::AtomicRmwOp atomic_rmw_op_for(BuiltinKind kind) {
    switch (kind) {
        case BuiltinKind::ATOMIC_FETCH_ADD:
        case BuiltinKind::ATOMIC_ADD_FETCH:
        case BuiltinKind::C11_ATOMIC_FETCH_ADD:
        case BuiltinKind::SYNC_FETCH_AND_ADD:
        case BuiltinKind::SYNC_ADD_AND_FETCH:
            return cir::AtomicRmwOp::Add;
        case BuiltinKind::ATOMIC_FETCH_SUB:
        case BuiltinKind::ATOMIC_SUB_FETCH:
        case BuiltinKind::C11_ATOMIC_FETCH_SUB:
        case BuiltinKind::SYNC_FETCH_AND_SUB:
        case BuiltinKind::SYNC_SUB_AND_FETCH:
            return cir::AtomicRmwOp::Sub;
        case BuiltinKind::ATOMIC_FETCH_AND:
        case BuiltinKind::ATOMIC_AND_FETCH:
        case BuiltinKind::SYNC_FETCH_AND_AND:
        case BuiltinKind::SYNC_AND_AND_FETCH:
            return cir::AtomicRmwOp::And;
        case BuiltinKind::ATOMIC_FETCH_OR:
        case BuiltinKind::ATOMIC_OR_FETCH:
        case BuiltinKind::SYNC_FETCH_AND_OR:
        case BuiltinKind::SYNC_OR_AND_FETCH:
            return cir::AtomicRmwOp::Or;
        case BuiltinKind::ATOMIC_FETCH_XOR:
        case BuiltinKind::ATOMIC_XOR_FETCH:
        case BuiltinKind::SYNC_FETCH_AND_XOR:
        case BuiltinKind::SYNC_XOR_AND_FETCH:
            return cir::AtomicRmwOp::Xor;
        case BuiltinKind::ATOMIC_FETCH_NAND:
        case BuiltinKind::ATOMIC_NAND_FETCH:
        case BuiltinKind::SYNC_FETCH_AND_NAND:
        case BuiltinKind::SYNC_NAND_AND_FETCH:
            return cir::AtomicRmwOp::Nand;
        default:
            return cir::AtomicRmwOp::Xchg;
    }
}

cir::BinaryOpKind atomic_recompute_op(cir::AtomicRmwOp op) {
    switch (op) {
        case cir::AtomicRmwOp::Add: return cir::BinaryOpKind::Add;
        case cir::AtomicRmwOp::Sub: return cir::BinaryOpKind::Sub;
        case cir::AtomicRmwOp::And:
        case cir::AtomicRmwOp::Nand: return cir::BinaryOpKind::BitAnd;
        case cir::AtomicRmwOp::Or: return cir::BinaryOpKind::BitOr;
        case cir::AtomicRmwOp::Xor: return cir::BinaryOpKind::BitXor;
        default: return cir::BinaryOpKind::Invalid;
    }
}

} // namespace

ExprResult Session::collect_atomic_builtin(std::string_view name,
                                           BuiltinKind kind,
                                           std::vector<ExprResult> args,
                                           SrcLoc loc) {
    cir::Fragment fragment;
    bool has_error = false;

    auto order_from = [&](size_t index) -> cir::MemoryOrder {
        if (index >= args.size()) {
            return cir::MemoryOrder::SeqCst;
        }
        ExprResult value = require_value(std::move(args[index]), UseContext::RValue, loc);
        int64_t folded = 5;
        if (!try_evaluate_integer_constant(value, folded) || folded < 0 || folded > 5) {
            folded = 5;
        }
        fragment = chain(std::move(fragment), std::move(value.fragment), loc);
        return static_cast<cir::MemoryOrder>(folded);
    };

    auto place_from_pointer = [&](size_t index) -> std::pair<cir::InstId, cir::TypeId> {
        ExprResult pointer = require_value(std::move(args[index]), UseContext::RValue, loc);
        has_error = has_error || pointer.has_error;
        if (!is_pointer_type(pointer.type)) {
            report_error("atomic builtin requires a pointer argument", loc);
            has_error = true;
        }
        fragment = chain(std::move(fragment), std::move(pointer.fragment), loc);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("atomic.place");
        cir::InstId place = builder_.deref(pointer.value, loc);
        fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
        cir::TypeId value_type = file_.place_object_type(file_.inst(place).result_type);
        return {place, value_type};
    };

    auto value_arg = [&](size_t index, cir::TypeId type) -> cir::InstId {
        ExprResult value = require_value(std::move(args[index]), UseContext::RValue, loc);
        has_error = has_error || value.has_error;
        if (type.valid()) {
            value = convert_to(std::move(value), type, UseContext::Assignment, loc);
        }
        fragment = chain(std::move(fragment), std::move(value.fragment), loc);
        return value.value;
    };

    auto finish = [&](cir::InstId value, cir::TypeId type) {
        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = value;
        result.type = type;
        result.category = ValueCategory::PrValue;
        result.has_error = has_error;
        return result;
    };

    auto void_result = [&]() {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("atomic.void");
        cir::InstId zero = builder_.integer_literal(0, "0", loc);
        fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
        return finish(zero, builder_.int_type());
    };

    switch (kind) {
        case BuiltinKind::ATOMIC_THREAD_FENCE:
        case BuiltinKind::ATOMIC_SIGNAL_FENCE:
        case BuiltinKind::SYNC_SYNCHRONIZE: {
            cir::MemoryOrder order = kind == BuiltinKind::SYNC_SYNCHRONIZE
                ? cir::MemoryOrder::SeqCst
                : order_from(0);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.fence");
            builder_.atomic_fence(order, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            return void_result();
        }
        case BuiltinKind::ATOMIC_IS_LOCK_FREE:
        case BuiltinKind::ATOMIC_ALWAYS_LOCK_FREE: {

            ExprResult size_value =
                require_value(std::move(args[0]), UseContext::RValue, loc);
            int64_t size = 0;
            bool lock_free = false;
            if (try_evaluate_integer_constant(size_value, size)) {
                lock_free = size > 0 && size <= 16 && (size & (size - 1)) == 0;
            }
            return make_boolean_literal(lock_free, lock_free ? "1" : "0", loc);
        }
        case BuiltinKind::C11_ATOMIC_INIT: {
            auto [place, value_type] = place_from_pointer(0);
            cir::InstId value = value_arg(1, value_type);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.init");
            builder_.store(place, value, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            return void_result();
        }
        case BuiltinKind::ATOMIC_LOAD_N: {
            bool has_return_slot = name == "__atomic_load";
            auto [place, value_type] = place_from_pointer(0);
            std::pair<cir::InstId, cir::TypeId> return_slot{};
            if (has_return_slot) {
                return_slot = place_from_pointer(1);
            }
            cir::MemoryOrder order = order_from(has_return_slot ? 2 : 1);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.load");
            cir::InstId old_value = builder_.atomic_load(place, order, loc);
            if (has_return_slot) {
                builder_.store(return_slot.first, old_value, loc);
            }
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            if (has_return_slot) {
                return void_result();
            }
            return finish(old_value, value_type);
        }
        case BuiltinKind::ATOMIC_STORE_N: {
            bool value_by_pointer = name == "__atomic_store";
            auto [place, value_type] = place_from_pointer(0);
            cir::InstId value{};
            if (value_by_pointer) {
                auto [value_place, source_type] = place_from_pointer(1);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("atomic.store.read");
                value = builder_.load(value_place, loc);
                fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            } else {
                value = value_arg(1, value_type);
            }
            cir::MemoryOrder order = order_from(2);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.store");
            builder_.atomic_store(place, value, order, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            return void_result();
        }
        case BuiltinKind::ATOMIC_EXCHANGE_N: {
            bool generic_form = name == "__atomic_exchange";
            auto [place, value_type] = place_from_pointer(0);
            cir::InstId desired{};
            std::pair<cir::InstId, cir::TypeId> return_slot{};
            if (generic_form) {
                auto [value_place, source_type] = place_from_pointer(1);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("atomic.xchg.read");
                desired = builder_.load(value_place, loc);
                fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
                return_slot = place_from_pointer(2);
            } else {
                desired = value_arg(1, value_type);
            }
            cir::MemoryOrder order = order_from(generic_form ? 3 : 2);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.xchg");
            cir::InstId old_value =
                builder_.atomic_rmw(place, desired, cir::AtomicRmwOp::Xchg, order, loc);
            if (generic_form) {
                builder_.store(return_slot.first, old_value, loc);
            }
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            if (generic_form) {
                return void_result();
            }
            return finish(old_value, value_type);
        }
        case BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N: {
            bool c11 = name.rfind("__c11_", 0) == 0;
            bool desired_by_pointer = name == "__atomic_compare_exchange";
            bool weak = name == "__c11_atomic_compare_exchange_weak";
            auto [place, value_type] = place_from_pointer(0);
            auto [expected_place, expected_type] = place_from_pointer(1);
            cir::InstId desired{};
            if (desired_by_pointer) {
                auto [desired_place, desired_type] = place_from_pointer(2);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("atomic.cas.read");
                desired = builder_.load(desired_place, loc);
                fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            } else {
                desired = value_arg(2, value_type);
            }
            if (!c11) {
                ExprResult weak_value =
                    require_value(std::move(args[3]), UseContext::RValue, loc);
                int64_t weak_constant = 0;
                if (try_evaluate_integer_constant(weak_value, weak_constant)) {
                    weak = weak_constant != 0;
                }
                fragment = chain(std::move(fragment), std::move(weak_value.fragment), loc);
            }
            size_t order_index = c11 ? 3 : 4;
            cir::MemoryOrder success = order_from(order_index);
            cir::MemoryOrder failure = order_from(order_index + 1);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.cas");
            cir::InstId ok = builder_.atomic_cmpxchg(place,
                                                     expected_place,
                                                     desired,
                                                     success,
                                                     failure,
                                                     weak,
                                                     loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            return finish(ok, builder_.bool_type());
        }
        case BuiltinKind::ATOMIC_TEST_AND_SET: {
            args[0] = cast_if_needed(
                require_value(std::move(args[0]), UseContext::RValue, loc),
                pointer_type(file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::UChar))),
                "atomic",
                loc);
            auto [place, value_type] = place_from_pointer(0);
            cir::MemoryOrder order = order_from(1);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.tas");
            cir::InstId one = builder_.integer_literal(1, "1", loc);
            cir::InstId one_byte = builder_.cast(value_type, one, "arith", loc);
            cir::InstId old_value =
                builder_.atomic_rmw(place, one_byte, cir::AtomicRmwOp::Xchg, order, loc);
            cir::InstId zero = builder_.integer_literal(0, "0", loc);
            cir::InstId zero_byte = builder_.cast(value_type, zero, "arith", loc);
            cir::InstId truth = builder_.binary(cir::BinaryOpKind::NotEqual,
                                                builder_.bool_type(),
                                                old_value,
                                                zero_byte,
                                                loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            return finish(truth, builder_.bool_type());
        }
        case BuiltinKind::ATOMIC_CLEAR:
        case BuiltinKind::SYNC_LOCK_RELEASE: {
            args[0] = cast_if_needed(
                require_value(std::move(args[0]), UseContext::RValue, loc),
                pointer_type(file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::UChar))),
                "atomic",
                loc);
            auto [place, value_type] = place_from_pointer(0);
            cir::MemoryOrder order = kind == BuiltinKind::SYNC_LOCK_RELEASE
                ? cir::MemoryOrder::Release
                : order_from(1);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.clear");
            cir::InstId zero = builder_.integer_literal(0, "0", loc);
            cir::InstId zero_byte = builder_.cast(value_type, zero, "arith", loc);
            builder_.atomic_store(place, zero_byte, order, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            return void_result();
        }
        case BuiltinKind::SYNC_BOOL_COMPARE_AND_SWAP:
        case BuiltinKind::SYNC_VAL_COMPARE_AND_SWAP: {
            auto [place, value_type] = place_from_pointer(0);
            cir::InstId expected = value_arg(1, value_type);
            cir::InstId desired = value_arg(2, value_type);
            std::string temp_name =
                ".sync.cas.tmp." + std::to_string(compound_literal_counter_++);
            cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                                     temp_name,
                                                     value_type,
                                                     {},
                                                     loc,
                                                     cir::StorageDuration::Automatic,
                                                     cir::MemorySpace::Default,
                                                     {});
            file_.entity_mut(temp).is_definition = true;
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.sync.cas");
            cir::InstId expected_place = builder_.local_place(temp, value_type, loc);
            builder_.store(expected_place, expected, loc);
            cir::InstId ok = builder_.atomic_cmpxchg(place,
                                                     expected_place,
                                                     desired,
                                                     cir::MemoryOrder::SeqCst,
                                                     cir::MemoryOrder::SeqCst,
                                                     false,
                                                     loc);
            cir::InstId old_value = builder_.load(expected_place, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            if (kind == BuiltinKind::SYNC_BOOL_COMPARE_AND_SWAP) {
                return finish(ok, builder_.bool_type());
            }
            return finish(old_value, value_type);
        }
        case BuiltinKind::SYNC_LOCK_TEST_AND_SET: {
            auto [place, value_type] = place_from_pointer(0);
            cir::InstId value = value_arg(1, value_type);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("atomic.sync.tas");
            cir::InstId old_value = builder_.atomic_rmw(place,
                                                        value,
                                                        cir::AtomicRmwOp::Xchg,
                                                        cir::MemoryOrder::Acquire,
                                                        loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            return finish(old_value, value_type);
        }
        default:
            break;
    }

    bool is_sync = name.rfind("__sync_", 0) == 0;
    cir::AtomicRmwOp rmw_op = atomic_rmw_op_for(kind);
    bool op_fetch = atomic_kind_is_op_fetch(kind);
    auto [place, value_type] = place_from_pointer(0);
    bool c11_pointer_arithmetic =
        (kind == BuiltinKind::C11_ATOMIC_FETCH_ADD ||
         kind == BuiltinKind::C11_ATOMIC_FETCH_SUB) &&
        is_pointer_type(value_type);
    cir::TypeId operand_type =
        c11_pointer_arithmetic ? builder_.usize_type() : value_type;
    cir::InstId value = value_arg(1, operand_type);
    if (c11_pointer_arithmetic) {
        cir::TypeId element_type =
            file_.pointer_pointee_type(file_.resolved_type(value_type));
        std::optional<size_t> element_size = size_of_type(element_type, loc);
        if (!element_size.has_value()) {
            has_error = true;
        }
        cir::BlockId scale_previous = builder_.current_block();
        cir::BlockId scale_block =
            begin_fragment_block("atomic.pointer.delta");
        size_t scale = element_size.value_or(1);
        cir::InstId scale_value = builder_.integer_literal(
            static_cast<int64_t>(scale),
            operand_type,
            std::to_string(scale),
            loc);
        value = builder_.binary(cir::BinaryOpKind::Mul,
                                operand_type,
                                value,
                                scale_value,
                                loc);
        fragment = chain(
            std::move(fragment),
            finish_fragment_block(scale_block, scale_previous),
            loc);
    }
    cir::MemoryOrder order = is_sync ? cir::MemoryOrder::SeqCst : order_from(2);
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("atomic.rmw");
    cir::InstId old_value = builder_.atomic_rmw(place, value, rmw_op, order, loc);
    cir::InstId result_value = old_value;
    if (op_fetch) {
        cir::BinaryOpKind recompute = atomic_recompute_op(rmw_op);
        result_value =
            builder_.binary(recompute, value_type, old_value, value, loc);
        if (rmw_op == cir::AtomicRmwOp::Nand) {
            result_value = builder_.unary(cir::UnaryOpKind::BitwiseNot,
                                          value_type,
                                          result_value,
                                          loc);
        }
    }
    fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
    return finish(result_value, value_type);
}

ExprResult Session::collect_source_location_builtin(SrcLoc loc) {
    cir::TypeId result_type = builder_.pointer_type(file_.type_ref(
        builder_.void_type(), cir::QualConst));
    cir::TypeId implementation = peek_qualified_type_ref(
        /*global_qualifier=*/true, {"std", "source_location"},
        "__impl").type;
    implementation = file_.resolved_type(implementation);
    const cir::RecordFacts* implementation_facts =
        file_.record_facts_for_type(implementation);
    if (!implementation_facts || implementation_facts->is_incomplete) {
        report_error(
            "__builtin_source_location requires a complete nested "
            "'__impl' class",
            loc);
        ExprResult result = make_nullptr_literal(loc);
        result = convert_to(std::move(result), result_type,
                            UseContext::Assignment, loc);
        result.has_error = true;
        return result;
    }
    if (in_unevaluated_operand()) {

        ExprResult result;
        result.type = result_type;
        result.category = ValueCategory::PrValue;
        return result;
    }

    SrcLoc effective_loc = default_argument_call_site();
    if (effective_loc.isInvalid()) {
        effective_loc = loc;
    }
    LogicalLocation logical = source_manager_
        ? source_manager_->getLogicalLocation(effective_loc)
        : LogicalLocation{"", 0, 0};

    std::string function_name;
    cir::EntityId function = current_function_entity();
    if (function.valid() && file_.valid(function) &&
        file_.entity(function).name.valid()) {
        function_name = file_.name(file_.entity(function).name);
    }

    uint32_t identity = source_location_counter_++;
    auto add_string = [&](std::string_view role,
                          const std::string& value) {
        std::vector<uint8_t> bytes(value.begin(), value.end());
        bytes.push_back(0);
        cir::TypeId type =
            builder_.array_type(builder_.char_type(), bytes.size());
        cir::EntityId entity = builder_.add_entity(
            cir::EntityKind::Variable,
            ".source_location." + std::string(role) + "." +
                std::to_string(identity),
            type, {}, effective_loc, cir::StorageDuration::Static,
            cir::MemorySpace::Default, {});
        cir::Entity& record = file_.entity_mut(entity);
        record.is_definition = true;
        record.linkage = cir::LinkageKind::Internal;
        record.qualifiers = cir::QualConst;
        record.decl_flags.is_constexpr = true;
        record.object_origin = cir::EntityObjectOrigin::StringLiteral;
        record.has_static_initializer = true;
        record.static_initializer_bytes = std::move(bytes);
        return entity;
    };

    cir::EntityId file_name = add_string("file", logical.file);
    cir::EntityId function_name_entity =
        add_string("function", function_name);
    std::optional<size_t> implementation_size =
        cir::size_of_type(file_, implementation);
    if (!implementation_size.has_value()) {
        report_error(
            "__builtin_source_location implementation type has no layout",
            loc);
        ExprResult result = make_nullptr_literal(loc);
        result = convert_to(std::move(result), result_type,
                            UseContext::Assignment, loc);
        result.has_error = true;
        return result;
    }

    cir::EntityId storage = builder_.add_entity(
        cir::EntityKind::Variable,
        ".source_location." + std::to_string(identity),
        implementation, {}, effective_loc, cir::StorageDuration::Static,
        cir::MemorySpace::Default, {});
    cir::Entity& object = file_.entity_mut(storage);
    object.is_definition = true;
    object.linkage = cir::LinkageKind::Internal;
    object.qualifiers = cir::QualConst;
    object.decl_flags.is_constexpr = true;
    object.has_static_initializer = true;
    object.static_initializer_bytes.assign(*implementation_size, 0);

    bool has_file = false;
    bool has_function = false;
    bool has_line = false;
    bool has_column = false;
    auto write_unsigned = [&](size_t offset, size_t size, uint64_t value) {
        if (size > sizeof(value) ||
            offset > object.static_initializer_bytes.size() ||
            size > object.static_initializer_bytes.size() - offset) {
            return false;
        }
        for (size_t byte = 0; byte < size; ++byte) {
            size_t destination =
                file_.target_info().endianness == EndiannessKind::Little
                    ? offset + byte
                    : offset + (size - byte - 1);
            object.static_initializer_bytes[destination] =
                static_cast<uint8_t>((value >> (byte * 8)) & 0xffu);
        }
        return true;
    };
    for (const cir::RecordFieldFact& field : implementation_facts->fields) {
        if (!field.name.valid() || field.is_base_subobject ||
            field.is_virtual_base_storage) {
            continue;
        }
        std::string_view field_name = file_.name(field.name);
        if (field_name == "_M_file_name") {
            object.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{
                    field.offset, file_name, 0});
            has_file = true;
        } else if (field_name == "_M_function_name") {
            object.static_initializer_relocations.push_back(
                cir::StaticInitializerRelocation{
                    field.offset, function_name_entity, 0});
            has_function = true;
        } else if (field_name == "_M_line" ||
                   field_name == "_M_column") {
            std::optional<size_t> field_size =
                cir::size_of_type(file_, field.type.type);
            uint64_t value = field_name == "_M_line"
                ? logical.line
                : logical.column;
            bool written = field_size.has_value() &&
                write_unsigned(field.offset, *field_size, value);
            has_line = has_line ||
                (field_name == "_M_line" && written);
            has_column = has_column ||
                (field_name == "_M_column" && written);
        }
    }
    if (!has_file || !has_function || !has_line || !has_column) {
        report_error(
            "__builtin_source_location nested '__impl' has an unsupported "
            "layout",
            loc);
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.source_location");
    cir::InstId place = builder_.global_place(storage, effective_loc);
    cir::InstId address = builder_.addr_of(place, effective_loc);
    cir::InstId erased = builder_.cast(result_type, address, "conversion",
                                       effective_loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = erased;
    result.type = result_type;
    result.category = ValueCategory::PrValue;
    result.has_error = !has_file || !has_function || !has_line || !has_column;
    return result;
}

ExprResult Session::collect_builtin_call(std::string_view name,
                                         BuiltinKind kind,
                                         std::vector<ExprResult> args,
                                         SrcLoc loc) {
    const BuiltinInfo* info = BuiltinRegistry::instance().lookup(name);
    if (!info || !info->supported) {
        report_error("unsupported builtin '" + std::string(name) + "'", loc);
        ExprResult result = make_integer_literal(0, "0", loc);
        result.has_error = true;
        return result;
    }

    switch (kind) {
        case BuiltinKind::SOURCE_LOCATION:
            return collect_source_location_builtin(loc);
        case BuiltinKind::CORO_DONE:
        case BuiltinKind::CORO_RESUME:
        case BuiltinKind::CORO_DESTROY:
        case BuiltinKind::CORO_PROMISE:
            return collect_coro_handle_builtin(kind, std::move(args), loc);
        default:
            break;
    }

    args.erase(std::remove_if(args.begin(),
                              args.end(),
                              [](const ExprResult& arg) {
                                  return !arg.value.valid() &&
                                         arg.name == "__builtin_va_arg_pack";
                              }),
               args.end());

    int arg_count = static_cast<int>(args.size());
    if (arg_count < info->min_args ||
        (info->max_args >= 0 && arg_count > info->max_args)) {
        report_error(std::string(info->name) + " called with invalid argument count", loc);
        ExprResult result = make_integer_literal(0, "0", loc);
        result.has_error = true;
        return result;
    }

    auto make_void_va_result = [&](cir::InstId inst,
                                   cir::Fragment fragment,
                                   bool has_error) {
        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = inst;
        result.type = builder_.void_type();
        result.category = ValueCategory::PrValue;
        result.has_error = has_error;
        return result;
    };

    auto make_nan_result = [&](syntax::FloatingLiteralKind literal_kind,
                               bool signaling,
                               std::string spelling) {
        cir::TypeId type = floating_literal_type(literal_kind);
        cir::FloatingSemantics semantics =
            floating::semantics_for_type(file_, type);
        std::optional<std::string> payload = args.empty()
            ? std::optional<std::string>(std::string())
            : string_literal_text(file_, args.front());
        floating::FloatParseResult value;
        if (payload) {
            value = floating::nan(semantics, *payload, signaling);
        } else {
            value.error = numeric::ParseError::InvalidPayload;
        }
        if (!value) {
            report_error("NaN payload must be an integer string", loc);
            value = floating::nan(semantics, {}, signaling);
        }
        return make_floating_value(
            value ? value.value : floating::zero(semantics),
            type,
            std::move(spelling),
            loc);
    };

    switch (kind) {
        case BuiltinKind::ATOMIC_LOAD_N:
        case BuiltinKind::ATOMIC_STORE_N:
        case BuiltinKind::ATOMIC_EXCHANGE_N:
        case BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N:
        case BuiltinKind::ATOMIC_FETCH_ADD:
        case BuiltinKind::ATOMIC_FETCH_SUB:
        case BuiltinKind::ATOMIC_FETCH_AND:
        case BuiltinKind::ATOMIC_FETCH_OR:
        case BuiltinKind::ATOMIC_FETCH_XOR:
        case BuiltinKind::ATOMIC_FETCH_NAND:
        case BuiltinKind::ATOMIC_ADD_FETCH:
        case BuiltinKind::ATOMIC_SUB_FETCH:
        case BuiltinKind::ATOMIC_AND_FETCH:
        case BuiltinKind::ATOMIC_OR_FETCH:
        case BuiltinKind::ATOMIC_XOR_FETCH:
        case BuiltinKind::ATOMIC_NAND_FETCH:
        case BuiltinKind::C11_ATOMIC_FETCH_ADD:
        case BuiltinKind::C11_ATOMIC_FETCH_SUB:
        case BuiltinKind::C11_ATOMIC_INIT:
        case BuiltinKind::ATOMIC_TEST_AND_SET:
        case BuiltinKind::ATOMIC_CLEAR:
        case BuiltinKind::ATOMIC_THREAD_FENCE:
        case BuiltinKind::ATOMIC_SIGNAL_FENCE:
        case BuiltinKind::ATOMIC_IS_LOCK_FREE:
        case BuiltinKind::ATOMIC_ALWAYS_LOCK_FREE:
        case BuiltinKind::SYNC_FETCH_AND_ADD:
        case BuiltinKind::SYNC_FETCH_AND_SUB:
        case BuiltinKind::SYNC_FETCH_AND_OR:
        case BuiltinKind::SYNC_FETCH_AND_AND:
        case BuiltinKind::SYNC_FETCH_AND_XOR:
        case BuiltinKind::SYNC_FETCH_AND_NAND:
        case BuiltinKind::SYNC_ADD_AND_FETCH:
        case BuiltinKind::SYNC_SUB_AND_FETCH:
        case BuiltinKind::SYNC_OR_AND_FETCH:
        case BuiltinKind::SYNC_AND_AND_FETCH:
        case BuiltinKind::SYNC_XOR_AND_FETCH:
        case BuiltinKind::SYNC_NAND_AND_FETCH:
        case BuiltinKind::SYNC_BOOL_COMPARE_AND_SWAP:
        case BuiltinKind::SYNC_VAL_COMPARE_AND_SWAP:
        case BuiltinKind::SYNC_LOCK_TEST_AND_SET:
        case BuiltinKind::SYNC_LOCK_RELEASE:
        case BuiltinKind::SYNC_SYNCHRONIZE:
            return collect_atomic_builtin(name, kind, std::move(args), loc);
        default:
            break;
    }

    switch (kind) {
        case BuiltinKind::MEMCPY_CHK:
        case BuiltinKind::MEMMOVE_CHK:
        case BuiltinKind::MEMSET_CHK:
        case BuiltinKind::STRNCPY_CHK:
        case BuiltinKind::STRNCAT_CHK:
            if (args.size() == 4) {
                args.pop_back();
            }
            kind = kind == BuiltinKind::MEMCPY_CHK ? BuiltinKind::MEMCPY
                 : kind == BuiltinKind::MEMMOVE_CHK ? BuiltinKind::MEMMOVE
                 : kind == BuiltinKind::MEMSET_CHK ? BuiltinKind::MEMSET
                 : kind == BuiltinKind::STRNCPY_CHK ? BuiltinKind::STRNCPY
                                                    : BuiltinKind::STRNCAT;
            break;
        case BuiltinKind::STRCPY_CHK:
        case BuiltinKind::STPCPY_CHK:
        case BuiltinKind::STRCAT_CHK:
            if (args.size() == 3) {
                args.pop_back();
            }
            kind = kind == BuiltinKind::STRCPY_CHK ? BuiltinKind::STRCPY
                 : kind == BuiltinKind::STPCPY_CHK ? BuiltinKind::STPCPY
                                                   : BuiltinKind::STRCAT;
            break;
        case BuiltinKind::SPRINTF_CHK:

            if (args.size() >= 4) {
                args.erase(args.begin() + 1, args.begin() + 3);
            }
            kind = BuiltinKind::SPRINTF;
            break;
        case BuiltinKind::SNPRINTF_CHK:

            if (args.size() >= 5) {
                args.erase(args.begin() + 2, args.begin() + 4);
            }
            kind = BuiltinKind::SNPRINTF;
            break;
        default:
            break;
    }

    switch (kind) {
        case BuiltinKind::COMPLEX: {

            ExprResult real = require_value(std::move(args[0]), UseContext::RValue, loc);
            ExprResult imag = require_value(std::move(args[1]), UseContext::RValue, loc);
            bool has_error = real.has_error || imag.has_error;
            cir::TypeId element = real.type;
            if (!is_floating_type(element)) {
                report_error("__builtin_complex requires floating-point arguments", loc);
                element = builder_.double_type();
                has_error = true;
            }
            imag = convert_to(std::move(imag), element, UseContext::Assignment, loc);
            cir::TypeId complex = complex_type(file_.type_ref(element));
            cir::Fragment fragment =
                chain(std::move(real.fragment), std::move(imag.fragment), loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("builtin.complex");
            cir::InstId inst = builder_.complex_make(complex, real.value, imag.value, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = inst;
            result.type = complex;
            result.category = ValueCategory::PrValue;
            result.has_error = has_error;
            return result;
        }
        case BuiltinKind::CONJF: {

            ExprResult value = require_value(std::move(args[0]), UseContext::RValue, loc);
            cir::TypeId element = complex_element_type(value.type);
            bool has_error = value.has_error;
            if (!element.valid()) {
                report_error("__builtin_conjf requires a complex argument", loc);
                return collect_unsupported_expr("invalid conj", {}, loc);
            }
            cir::Fragment fragment = std::move(value.fragment);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("builtin.conj");
            cir::InstId real = builder_.complex_real(value.value, loc);
            cir::InstId imag = builder_.complex_imag(value.value, loc);
            cir::UnaryOpDescriptor negate;
            negate.op = cir::UnaryOpKind::Minus;
            negate.computation_type = file_.type_ref(element);
            cir::InstId neg_imag = builder_.unary(cir::UnaryOpKind::Minus, element, imag, loc);
            cir::InstId inst = builder_.complex_make(value.type, real, neg_imag, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = inst;
            result.type = value.type;
            result.category = ValueCategory::PrValue;
            result.has_error = has_error;
            return result;
        }
        case BuiltinKind::CEXPI: {

            ExprResult value = require_value(std::move(args[0]), UseContext::RValue, loc);
            value = convert_to(std::move(value), builder_.double_type(),
                               UseContext::Assignment, loc);
            cir::TypeId complex = complex_type(file_.type_ref(builder_.double_type()));
            cir::Fragment fragment = std::move(value.fragment);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("builtin.cexpi");
            cir::InstId cos_call = builder_.builtin_call(
                BuiltinKind::COS, "__builtin_cos", builder_.double_type(), {value.value}, loc);
            cir::InstId sin_call = builder_.builtin_call(
                BuiltinKind::SIN, "__builtin_sin", builder_.double_type(), {value.value}, loc);
            cir::InstId inst = builder_.complex_make(complex, cos_call, sin_call, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = inst;
            result.type = complex;
            result.category = ValueCategory::PrValue;
            result.has_error = value.has_error;
            return result;
        }
        case BuiltinKind::CPOW: {
            cir::TypeId complex = complex_type(file_.type_ref(builder_.double_type()));
            ExprResult base = require_value(std::move(args[0]), UseContext::RValue, loc);
            base = convert_to(std::move(base), complex, UseContext::Assignment, loc);
            ExprResult exponent = require_value(std::move(args[1]), UseContext::RValue, loc);
            exponent = convert_to(std::move(exponent), complex, UseContext::Assignment, loc);
            cir::Fragment fragment =
                chain(std::move(base.fragment), std::move(exponent.fragment), loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("builtin.cpow");
            cir::InstId inst = builder_.builtin_call(
                BuiltinKind::CPOW, "__builtin_cpow", complex,
                {base.value, exponent.value}, loc);
            fragment = chain(std::move(fragment), finish_fragment_block(block, previous), loc);
            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = inst;
            result.type = complex;
            result.category = ValueCategory::PrValue;
            result.has_error = base.has_error || exponent.has_error;
            return result;
        }
        case BuiltinKind::VA_ARG_PACK: {

            const cir::Function* pack_fn = current_function_.valid()
                ? &file_.function(current_function_)
                : nullptr;
            const auto* pack_payload = pack_fn
                ? std::get_if<cir::FunctionTypePayload>(
                      &file_.type_payload(file_.resolved_type(pack_fn->type)))
                : nullptr;
            ExprResult result;
            if (!pack_payload || !pack_payload->is_variadic) {
                report_error("__builtin_va_arg_pack may only be used in a variadic function",
                             loc);
                result.has_error = true;
            }
            result.name = "__builtin_va_arg_pack";
            result.type = builder_.void_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        case BuiltinKind::EXTRACT_RETURN_ADDR: {

            if (args.empty()) {
                report_error("__builtin_extract_return_addr requires an argument",
                             loc);
                return collect_unsupported_expr("invalid __builtin_extract_return_addr",
                                                std::move(args), loc);
            }
            return require_value(std::move(args.front()), UseContext::RValue, loc);
        }
        case BuiltinKind::VA_START: {
            ExprResult va_list = require_place(std::move(args[0]), UseContext::Assignment, loc);
            bool has_error = va_list.has_error;
            const cir::Function* current_fn = current_function_.valid()
                ? &file_.function(current_function_)
                : nullptr;
            const auto* current_payload = current_fn
                ? std::get_if<cir::FunctionTypePayload>(
                      &file_.type_payload(file_.resolved_type(current_fn->type)))
                : nullptr;
            if (!current_payload || !current_payload->is_variadic) {
                report_error("cannot use __builtin_va_start in a non-variadic function", loc);
                has_error = true;
            } else if (current_fn->parameters.empty()) {
                report_error("__builtin_va_start requires a final named parameter", loc);
                has_error = true;
            } else if (args.size() > 1 && args[1].entity.valid() &&
                       args[1].entity != current_fn->parameters.back().entity) {
                report_error("__builtin_va_start second argument must name the final fixed parameter",
                             loc);
                has_error = true;
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.va_start");
            cir::InstId inst = builder_.emit_va_start(va_list.place, loc);
            cir::Fragment va_fragment = finish_fragment_block(block, previous);
            cir::Fragment fragment = chain(std::move(va_list.fragment),
                                           std::move(va_fragment),
                                           loc);
            return make_void_va_result(inst, std::move(fragment), has_error);
        }
        case BuiltinKind::VA_END: {
            ExprResult va_list = require_place(std::move(args[0]), UseContext::Assignment, loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.va_end");
            cir::InstId inst = builder_.emit_va_end(va_list.place, loc);
            cir::Fragment va_fragment = finish_fragment_block(block, previous);
            cir::Fragment fragment = chain(std::move(va_list.fragment),
                                           std::move(va_fragment),
                                           loc);
            return make_void_va_result(inst, std::move(fragment), va_list.has_error);
        }
        case BuiltinKind::VA_COPY: {
            ExprResult dest = require_place(std::move(args[0]), UseContext::Assignment, loc);
            ExprResult src = require_place(std::move(args[1]), UseContext::Assignment, loc);
            bool has_error = dest.has_error || src.has_error;
            cir::Fragment fragment = chain(std::move(dest.fragment),
                                           std::move(src.fragment),
                                           loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.va_copy");
            cir::InstId inst = builder_.emit_va_copy(dest.place, src.place, loc);
            cir::Fragment va_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(va_fragment), loc);
            return make_void_va_result(inst, std::move(fragment), has_error);
        }
        case BuiltinKind::VA_ARG:
            report_error("__builtin_va_arg requires a type operand", loc);
            return collect_unsupported_expr("invalid __builtin_va_arg", std::move(args), loc);
        default:
            break;
    }

    auto try_builtin_constant = [&](const ExprResult& expr) {
        if (!expr.value.valid()) {
            return false;
        }
        LangOptions consteval_options = lang_opts_;
        consteval_options.enable_consteval_engine = true;
        ConstEvalEngine engine(make_consteval_context(consteval_options));
        ConstEvalRequest request;
        request.mode = ConstEvalMode::builtin_query();
        request.loc = loc;
        request.required = false;
        ConstEvalResult result =
            engine.evaluate_fragment(expr.fragment, cir::ValueRef(expr.value), request);
        return result.status == ConstEvalStatus::Constant;
    };

    auto try_builtin_object_size =
        [&](const ExprResult& arg, int64_t query_kind) -> std::optional<int64_t> {

        cir::InstId place_inst{};
        if (arg.value.valid() && file_.valid(arg.value)) {
            const cir::Inst& value_inst = file_.inst(arg.value);
            if (value_inst.kind == cir::InstKind::AddrOf) {
                std::vector<cir::ValueRef> ops =
                    file_.value_operands(value_inst.operands);
                if (!ops.empty()) {
                    place_inst = ops.front().inst;
                }
            }
        }

        if (!place_inst.valid() && arg.place.valid() && file_.valid(arg.place)) {
            cir::TypeId place_type =
                file_.place_object_type(file_.inst(arg.place).result_type);
            if (file_.valid(place_type) &&
                file_.type(file_.resolved_type(place_type)).kind ==
                    cir::TypeKind::Array) {
                place_inst = arg.place;
            }
        }
        if (!place_inst.valid()) {
            return std::nullopt;
        }

        auto read_index = [&](cir::InstId index) -> std::optional<int64_t> {
            if (!index.valid() || !file_.valid(index)) {
                return std::nullopt;
            }
            const cir::Inst& index_inst = file_.inst(index);
            if (index_inst.kind != cir::InstKind::IntegerLiteral) {
                return std::nullopt;
            }
            const auto* literal = std::get_if<cir::LiteralPayload>(
                &file_.payload(index_inst.payload_index));
            if (!literal) {
                return std::nullopt;
            }
            const auto* as_int =
                std::get_if<cir::IntegerValue>(&literal->value);
            return as_int ? as_int->try_as_int64() : std::nullopt;
        };

        int64_t offset_from_base = 0;
        int64_t offset_in_subobject = 0;
        cir::TypeId subobject_type{};
        bool subobject_captured = false;
        cir::TypeId base_type{};
        cir::InstId cursor = place_inst;
        for (int guard = 0; guard < 4096 && cursor.valid(); ++guard) {
            if (!file_.valid(cursor)) {
                return std::nullopt;
            }
            const cir::Inst& place = file_.inst(cursor);
            if (place.kind == cir::InstKind::LocalPlace ||
                place.kind == cir::InstKind::GlobalPlace) {
                base_type = file_.place_object_type(place.result_type);
                if (!subobject_captured) {
                    subobject_type = base_type;
                    offset_in_subobject = 0;
                }
                break;
            }
            if (place.kind == cir::InstKind::FieldAddr) {
                std::vector<cir::ValueRef> ops =
                    file_.value_operands(place.operands);
                std::vector<cir::Operand> raw = file_.operands(place.operands);
                if (ops.empty() || raw.size() < 2) {
                    return std::nullopt;
                }
                const auto* field_entity =
                    std::get_if<cir::EntityId>(&raw[1].data);
                const cir::RecordFieldFact* fact =
                    field_entity ? file_.field_fact(*field_entity) : nullptr;
                if (!fact || fact->is_bitfield) {
                    return std::nullopt;
                }
                if (!subobject_captured) {
                    subobject_type = fact->type.type;
                    offset_in_subobject = 0;
                    subobject_captured = true;
                }
                offset_from_base += static_cast<int64_t>(fact->offset);
                cursor = ops.front().inst;
                continue;
            }
            if (place.kind == cir::InstKind::ArrayElementPlace) {
                std::vector<cir::ValueRef> ops =
                    file_.value_operands(place.operands);
                if (ops.size() < 2) {
                    return std::nullopt;
                }
                std::optional<int64_t> index = read_index(ops[1].inst);
                cir::TypeId element = file_.place_object_type(place.result_type);
                std::optional<size_t> element_size =
                    cir::size_of_type(file_, element);
                if (!index.has_value() || !element_size.has_value()) {
                    return std::nullopt;
                }
                int64_t step = *index * static_cast<int64_t>(*element_size);
                if (!subobject_captured && file_.valid(ops[0].inst)) {

                    subobject_type = file_.place_object_type(
                        file_.inst(ops[0].inst).result_type);
                    offset_in_subobject = step;
                    subobject_captured = true;
                }
                offset_from_base += step;
                cursor = ops.front().inst;
                continue;
            }

            break;
        }

        const bool subobject_mode = (query_kind & 1) != 0;

        if (subobject_mode && subobject_captured) {
            std::optional<size_t> total =
                cir::size_of_type(file_, subobject_type);
            if (!total.has_value()) {
                return std::nullopt;
            }
            int64_t remaining =
                static_cast<int64_t>(*total) - offset_in_subobject;
            return remaining < 0 ? 0 : remaining;
        }

        if (!file_.valid(base_type)) {
            return std::nullopt;
        }
        cir::TypeId object = subobject_mode ? subobject_type : base_type;
        int64_t within = subobject_mode ? offset_in_subobject : offset_from_base;
        std::optional<size_t> total = cir::size_of_type(file_, object);
        if (!total.has_value()) {
            return std::nullopt;
        }
        int64_t remaining = static_cast<int64_t>(*total) - within;
        return remaining < 0 ? 0 : remaining;
    };

    switch (kind) {
        case BuiltinKind::FLT_ROUNDS:

            return make_integer_literal(1, "1", loc);
        case BuiltinKind::CONSTANT_P: {

            if (args.empty()) {
                return make_integer_literal(0, "0", loc);
            }
            if (try_builtin_constant(args.front())) {
                return make_integer_literal(1, "1", loc);
            }
            break;
        }
        case BuiltinKind::IS_CONSTANT_EVALUATED: {

            if (!lang_opts_.is_cxx_mode()) {
                return make_boolean_literal(false, "false", loc);
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("expr.is_constant_evaluated");
            cir::InstId inst =
                builder_.builtin_call(BuiltinKind::IS_CONSTANT_EVALUATED,
                                      "__builtin_is_constant_evaluated",
                                      builder_.bool_type(),
                                      {},
                                      loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            ExprResult result;
            result.fragment = std::move(fragment);
            result.value = inst;
            result.type = builder_.bool_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        case BuiltinKind::METAFN_QUERY_INT:
        case BuiltinKind::METAFN_QUERY_INFO:
        case BuiltinKind::METAFN_NAME_DATA:
        case BuiltinKind::METAFN_NAME_SIZE:
        case BuiltinKind::METAFN_RANGE_COUNT:
        case BuiltinKind::METAFN_RANGE_AT: {

            if (!lang_opts_.is_cxx_mode() ||
                !lang_opts_.enable_cpp_reflection) {
                report_error("'" + std::string(name) +
                                 "' requires C++ reflection",
                             loc);
                ExprResult result = make_integer_literal(0, "0", loc);
                result.has_error = true;
                return result;
            }
            cir::TypeId result_type;
            switch (kind) {
                case BuiltinKind::METAFN_QUERY_INFO:
                case BuiltinKind::METAFN_RANGE_AT:
                    result_type =
                        file_.builtin_type(cir::BuiltinTypeKind::MetaInfo);
                    break;
                case BuiltinKind::METAFN_NAME_DATA:
                    result_type = builder_.pointer_type(file_.type_ref(
                        file_.builtin_type(cir::BuiltinTypeKind::Char),
                        cir::QualConst));
                    break;
                default:
                    result_type = builder_.usize_type();
                    break;
            }
            cir::Fragment fragment;
            std::vector<cir::InstId> values;
            bool has_error = false;
            for (ExprResult& argument : args) {
                ExprResult value =
                    require_value(std::move(argument), UseContext::RValue, loc);
                has_error = has_error || value.has_error;
                fragment = chain(std::move(fragment),
                                 std::move(value.fragment),
                                 loc);
                values.push_back(value.value);
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.metafn");
            cir::InstId inst =
                builder_.builtin_call(kind, name, result_type, values, loc);
            cir::Fragment call_fragment = finish_fragment_block(block, previous);
            ExprResult result;
            result.fragment = chain(std::move(fragment),
                                    std::move(call_fragment),
                                    loc);
            result.value = inst;
            result.type = result_type;
            result.category = ValueCategory::PrValue;
            result.has_error = has_error;
            return result;
        }
        case BuiltinKind::OPERATOR_NEW:
        case BuiltinKind::OPERATOR_DELETE: {

            if (!lang_opts_.is_cxx_mode()) {
                report_error("'" + std::string(name) + "' requires C++", loc);
                ExprResult result = make_integer_literal(0, "0", loc);
                result.has_error = true;
                return result;
            }
            if (args.size() != 1) {
                report_error("aligned and sized forms of '" +
                                 std::string(name) +
                                 "' are not supported yet",
                             loc);
                ExprResult result = make_integer_literal(0, "0", loc);
                result.has_error = true;
                return result;
            }
            cir::TypeId void_type =
                file_.builtin_type(cir::BuiltinTypeKind::Void);
            cir::TypeId void_pointer = builder_.pointer_type(void_type);
            if (kind == BuiltinKind::OPERATOR_NEW) {
                ExprResult size = convert_to(std::move(args[0]),
                                             builder_.usize_type(),
                                             UseContext::Init,
                                             loc);

                const char* new_name =
                    file_.target_info().pointer_width <= 32 ? "_Znwj"
                    : file_.target_info().long_width >= 64  ? "_Znwm"
                                                            : "_Znwy";
                cir::EntityId operator_new = runtime_function(
                    new_name,
                    function_type(file_.type_ref(void_pointer),
                                  {file_.type_ref(builder_.usize_type())},
                                  false,
                                  true),
                    loc);
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("expr.builtin_new");
                cir::InstId raw =
                    builder_.call(operator_new, void_pointer, {size.value}, loc);
                cir::Fragment call_fragment =
                    finish_fragment_block(block, previous);
                ExprResult result;
                result.fragment = chain(std::move(size.fragment),
                                        std::move(call_fragment),
                                        loc);
                result.value = raw;
                result.type = void_pointer;
                result.category = ValueCategory::PrValue;
                result.has_error = size.has_error;
                return result;
            }
            ExprResult pointer = convert_to(std::move(args[0]),
                                            void_pointer,
                                            UseContext::Init,
                                            loc);
            cir::EntityId operator_delete = runtime_function(
                "_ZdlPv",
                function_type(file_.type_ref(void_type),
                              {file_.type_ref(void_pointer)},
                              false,
                              true),
                loc);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.builtin_delete");
            cir::InstId inst =
                builder_.call(operator_delete, void_type, {pointer.value}, loc);
            cir::Fragment call_fragment = finish_fragment_block(block, previous);
            ExprResult result;
            result.fragment = chain(std::move(pointer.fragment),
                                    std::move(call_fragment),
                                    loc);
            result.value = inst;
            result.type = void_type;
            result.category = ValueCategory::PrValue;
            result.has_error = pointer.has_error;
            return result;
        }
        case BuiltinKind::NAN_BUILTIN:
            return make_nan_result(syntax::FloatingLiteralKind::Double,
                                   false, "nan");
        case BuiltinKind::NANS:
            return make_nan_result(syntax::FloatingLiteralKind::Double,
                                   true, "nans");
        case BuiltinKind::NANF:
            return make_nan_result(syntax::FloatingLiteralKind::Float,
                                   false, "nanf");
        case BuiltinKind::NANSF:
            return make_nan_result(syntax::FloatingLiteralKind::Float,
                                   true, "nansf");
        case BuiltinKind::NANL:
            return make_nan_result(syntax::FloatingLiteralKind::LongDouble,
                                   false, "nanl");
        case BuiltinKind::NANSL:
            return make_nan_result(syntax::FloatingLiteralKind::LongDouble,
                                   true, "nansl");
        case BuiltinKind::BUILTIN_HUGE_VAL:
        case BuiltinKind::INF:
            return make_floating_literal(syntax::FloatingLiteralKind::Double,
                                         "inf", loc);
        case BuiltinKind::BUILTIN_HUGE_VALF:
        case BuiltinKind::INFF:
            return make_floating_literal(syntax::FloatingLiteralKind::Float,
                                         "inff", loc);
        case BuiltinKind::BUILTIN_HUGE_VALL:
        case BuiltinKind::INFL:
            return make_floating_literal(syntax::FloatingLiteralKind::LongDouble,
                                         "infl", loc);
        case BuiltinKind::CLASSIFY_TYPE: {

            int64_t type_class = -1;
            if (!args.empty()) {
                cir::TypeId arg_type = file_.resolved_type(args[0].type);
                if (file_.valid(arg_type)) {
                    switch (file_.type(arg_type).kind) {
                        case cir::TypeKind::Builtin: {
                            if (is_void_type(arg_type)) { type_class = 0; break; }
                            if (is_bool_type(arg_type)) { type_class = 4; break; }
                            if (is_floating_type(arg_type)) { type_class = 8; break; }
                            cir::BuiltinTypeKind builtin_kind =
                                std::get_if<cir::BuiltinTypePayload>(
                                    &file_.type_payload(arg_type))->kind;
                            type_class = (builtin_kind == cir::BuiltinTypeKind::Char ||
                                          builtin_kind == cir::BuiltinTypeKind::SChar ||
                                          builtin_kind == cir::BuiltinTypeKind::UChar)
                                ? 2 : 1;
                            break;
                        }
                        case cir::TypeKind::Enum: type_class = 3; break;
                        case cir::TypeKind::Pointer: type_class = 5; break;
                        case cir::TypeKind::Complex: type_class = 9; break;
                        case cir::TypeKind::BitInt: type_class = 18; break;
                        case cir::TypeKind::Function: type_class = 10; break;
                        case cir::TypeKind::Record: {
                            const auto* facts = file_.record_facts(
                                std::get_if<cir::RecordTypePayload>(
                                    &file_.type_payload(arg_type))->entity);
                            type_class = facts && facts->kind == cir::RecordKind::Union
                                ? 13 : 12;
                            break;
                        }
                        case cir::TypeKind::Array: type_class = 5; break;
                        default: type_class = 1; break;
                    }
                }
            }
            return make_integer_literal(type_class, std::to_string(type_class), loc);
        }
        case BuiltinKind::FPCLASSIFY: {

            if (args.size() != 6) {
                report_error("__builtin_fpclassify requires six arguments", loc);
                return collect_unsupported_expr("invalid __builtin_fpclassify",
                                                std::move(args), loc);
            }
            ExprResult value = require_value(std::move(args[5]), UseContext::RValue, loc);
            if (!is_floating_type(value.type)) {
                report_error("__builtin_fpclassify requires a floating-point classification argument",
                             loc);
                value.has_error = true;
            }
            std::string temp_name =
                ".fpclassify.tmp." + std::to_string(compound_literal_counter_++);
            cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                                     temp_name,
                                                     value.type,
                                                     {},
                                                     loc,
                                                     cir::StorageDuration::Automatic,
                                                     cir::MemorySpace::Default,
                                                     {});
            file_.entity_mut(temp).is_definition = true;
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.fpclassify.temp");
            cir::InstId temp_place = builder_.local_place(temp, value.type, loc);
            builder_.store(temp_place, value.value, loc);
            cir::Fragment store_fragment = finish_fragment_block(block, previous);
            cir::Fragment setup =
                chain(std::move(value.fragment), std::move(store_fragment), loc);

            auto temp_lvalue = [&]() {
                ExprResult lvalue;
                lvalue.place = temp_place;
                lvalue.type = value.type;
                lvalue.entity = temp;
                lvalue.category = ValueCategory::LValue;
                return lvalue;
            };
            auto predicate = [&](BuiltinKind predicate_kind, const char* name_text) {
                std::vector<ExprResult> predicate_args;
                predicate_args.push_back(temp_lvalue());
                return collect_builtin_call(name_text, predicate_kind,
                                            std::move(predicate_args), loc);
            };
            ExprResult is_zero = collect_binary_expr(
                syntax::BinaryOperator::Equal,
                temp_lvalue(),
                make_floating_literal(syntax::FloatingLiteralKind::Double,
                                      "0.0", loc),
                loc);
            ExprResult zero_or_subnormal = collect_conditional_expr(
                std::move(is_zero), std::move(args[4]), std::move(args[3]), loc);
            ExprResult normal_chain = collect_conditional_expr(
                predicate(BuiltinKind::ISNORMAL, "__builtin_isnormal"),
                std::move(args[2]), std::move(zero_or_subnormal), loc);
            ExprResult inf_chain = collect_conditional_expr(
                predicate(BuiltinKind::ISINF, "__builtin_isinf"),
                std::move(args[1]), std::move(normal_chain), loc);
            ExprResult nan_chain = collect_conditional_expr(
                predicate(BuiltinKind::ISNAN, "__builtin_isnan"),
                std::move(args[0]), std::move(inf_chain), loc);
            nan_chain.fragment = chain(std::move(setup),
                                       std::move(nan_chain.fragment), loc);
            nan_chain.has_error = nan_chain.has_error || value.has_error;
            return nan_chain;
        }
        case BuiltinKind::OBJECT_SIZE:
        case BuiltinKind::DYNAMIC_OBJECT_SIZE: {
            int64_t query_kind = 0;
            if (args.size() > 1) {
                evaluate_integer_constant(args[1], query_kind, loc, "object size kind is not an integer constant expression");
            }
            bool min_mode = query_kind == 2 || query_kind == 3;

            if (!args.empty()) {
                if (std::optional<int64_t> size =
                        try_builtin_object_size(args.front(), query_kind)) {
                    return make_integer_literal(*size, std::to_string(*size),
                                                builder_.usize_type(), loc);
                }
            }
            return make_integer_literal(min_mode ? 0 : -1,
                                        min_mode ? "0" : "-1",
                                        builder_.usize_type(),
                                        loc);
        }
        case BuiltinKind::ASSUME_ALIGNED: {
            cir::TypeId result_type = builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
            bool dependent = std::any_of(
                args.begin(), args.end(), [&](const ExprResult& argument) {
                    return expr_is_dependent(argument) ||
                        (argument.type.valid() &&
                         is_dependent_type(argument.type)) ||
                        type_contains_dependent_alias_specialization(
                            argument.type);
                });
            if (dependent) {
                ExprResult anchor = std::move(args.front());
                anchor.value_dependent = true;
                return make_deferred_typed_expr(
                    std::move(anchor), result_type,
                    ValueCategory::PrValue, loc);
            }

            ExprResult pointer =
                require_value(std::move(args[0]), UseContext::RValue, loc);
            bool has_error = pointer.has_error;
            if (!is_pointer_type(pointer.type)) {
                report_error(
                    "non-pointer argument to '__builtin_assume_aligned' is not allowed",
                    loc);
                has_error = true;
                ExprResult fallback = convert_to(
                    make_integer_literal(0, "0", loc), result_type,
                    UseContext::Assignment, loc);
                pointer.fragment = chain(std::move(pointer.fragment),
                                         std::move(fallback.fragment), loc);
                pointer.value = fallback.value;
                pointer.type = fallback.type;
            }

            int64_t alignment = 0;
            bool valid_alignment = false;
            if (!evaluate_integer_constant(
                    args[1], alignment, loc,
                    "argument to '__builtin_assume_aligned' must be a constant integer")) {
                has_error = true;
            } else if (alignment <= 0 ||
                       (static_cast<uint64_t>(alignment) &
                        (static_cast<uint64_t>(alignment) - 1)) != 0) {
                report_error("requested alignment is not a power of 2", loc);
                has_error = true;
            } else {
                valid_alignment = true;
            }

            std::vector<cir::InstId> operands{pointer.value};
            cir::Fragment fragment = std::move(pointer.fragment);
            if (args.size() == 3) {
                ExprResult offset =
                    convert_to(std::move(args[2]), builder_.usize_type(),
                               UseContext::RValue, loc);
                has_error = has_error || offset.has_error;
                operands.push_back(offset.value);
                fragment = chain(std::move(fragment),
                                 std::move(offset.fragment), loc);
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("expr.builtin.assume.aligned");
            cir::InstId inst = builder_.builtin_call(
                kind, name, result_type, operands, loc, {},
                {valid_alignment ? alignment : 1});
            cir::Fragment builtin_fragment =
                finish_fragment_block(block, previous);

            ExprResult result;
            result.fragment = chain(std::move(fragment),
                                    std::move(builtin_fragment), loc);
            result.value = inst;
            result.type = result_type;
            result.category = ValueCategory::PrValue;
            result.has_error = has_error;
            return result;
        }
        case BuiltinKind::LAUNDER: {
            ExprResult pointer =
                require_value(std::move(args[0]), UseContext::RValue, loc);
            bool has_error = pointer.has_error;
            if (!is_pointer_type(pointer.type)) {
                report_error(
                    "non-pointer argument to '__builtin_launder' is not allowed",
                    loc);
                pointer.has_error = true;
                return pointer;
            }

            cir::TypeRef pointee = file_.pointer_pointee_ref(
                file_.resolved_type(pointer.type));
            cir::TypeId resolved_pointee =
                file_.resolved_type(pointee.type);
            if (is_void_type(resolved_pointee)) {
                report_error(
                    "void pointer argument to '__builtin_launder' is not allowed",
                    loc);
                has_error = true;
            } else if (is_function_type(file_, resolved_pointee)) {
                report_error(
                    "function pointer argument to '__builtin_launder' is not allowed",
                    loc);
                has_error = true;
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("expr.builtin.launder");
            cir::InstId inst = builder_.builtin_call(
                kind, name, pointer.type, {pointer.value}, loc);
            cir::Fragment builtin_fragment =
                finish_fragment_block(block, previous);

            ExprResult result;
            result.fragment = chain(std::move(pointer.fragment),
                                    std::move(builtin_fragment), loc);
            result.value = inst;
            result.type = pointer.type;
            result.category = ValueCategory::PrValue;
            result.has_error = has_error;
            return result;
        }
        case BuiltinKind::ADDRESSOF: {
            ExprResult place = require_place(std::move(args[0]), UseContext::LValue, loc);
            if (const cir::RecordFieldFact* field = file_.field_fact(place.entity);
                field && field->is_bitfield) {
                report_error("cannot take address of bit-field", loc);
                place.has_error = true;
            }
            if (file_.valid(place.place)) {
                const cir::Inst& place_inst = file_.inst(place.place);
                if (place_inst.place_fact.valid() &&
                    file_.valid(place_inst.place_fact) &&
                    !file_.place_fact(place_inst.place_fact).addressable) {
                    report_error("cannot take address of non-addressable vector element",
                                 loc);
                    place.has_error = true;
                }
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.builtin.addressof");
            cir::InstId inst = builder_.addr_of(place.place, loc);
            cir::Fragment op_fragment = finish_fragment_block(block, previous);

            ExprResult result;
            result.fragment = chain(std::move(place.fragment), std::move(op_fragment), loc);
            result.value = inst;
            result.type = file_.inst(inst).result_type;
            result.category = ValueCategory::PrValue;
            result.has_error = place.has_error;
            return result;
        }
        default:
            break;
    }

    if (kind == BuiltinKind::REDUCE_AND) {
        if (expr_is_value_dependent(args[0]) ||
            is_dependent_type(args[0].type) ||
            type_contains_dependent_alias_specialization(args[0].type)) {
            args[0].value_dependent = true;
            return make_dependent_expr(std::move(args[0]), loc);
        }

        ExprResult vector =
            require_value(std::move(args[0]), UseContext::RValue, loc);
        bool has_error = vector.has_error;
        cir::TypeRef element_type;
        if (!is_vector_type(vector.type)) {
            report_error("__builtin_reduce_and requires an integer vector operand",
                         loc);
            has_error = true;
        } else {
            element_type = file_.vector_element_ref(vector.type);
            cir::OperatorValueDomain domain =
                file_.operator_value_domain(element_type);
            if (domain != cir::OperatorValueDomain::Bool &&
                domain != cir::OperatorValueDomain::SignedInteger &&
                domain != cir::OperatorValueDomain::UnsignedInteger) {
                report_error(
                    "__builtin_reduce_and requires an integer vector operand",
                    loc);
                has_error = true;
            }
        }
        if (!element_type.valid()) {
            element_type = file_.type_ref(builder_.int_type());
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.builtin.reduce.and");
        cir::InstId inst = builder_.builtin_call(
            kind,
            name,
            element_type.type,
            {vector.value},
            loc);
        cir::Fragment builtin_fragment =
            finish_fragment_block(block, previous);

        ExprResult result;
        result.fragment = chain(std::move(vector.fragment),
                                std::move(builtin_fragment),
                                loc);
        result.value = inst;
        result.type = element_type.type;
        result.category = ValueCategory::PrValue;
        result.has_error = has_error;
        return result;
    }

    if (kind == BuiltinKind::SHUFFLEVECTOR) {
        ExprResult lhs = require_value(std::move(args[0]), UseContext::RValue, loc);

        if (args.size() > 1 && !args[1].init_list &&
            !is_vector_type(args[1].type)) {
            ExprResult duplicate;
            duplicate.value = lhs.value;
            duplicate.type = lhs.type;
            duplicate.category = ValueCategory::PrValue;
            args.insert(args.begin() + 1, std::move(duplicate));
        }
        ExprResult rhs = require_value(std::move(args[1]), UseContext::RValue, loc);
        bool has_error = lhs.has_error || rhs.has_error;
        if (!is_vector_type(lhs.type) || !is_vector_type(rhs.type)) {
            report_error("__builtin_shufflevector requires vector operands", loc);
            has_error = true;
        } else if (!type_equal(lhs.type, rhs.type)) {
            report_error("__builtin_shufflevector vector operands must have the same type",
                         loc);
            has_error = true;
        }

        uint32_t input_count = file_.vector_element_count(lhs.type);
        int64_t lane_limit = static_cast<int64_t>(input_count) * 2;
        std::vector<int64_t> mask;
        std::vector<cir::InstId> arg_values{lhs.value, rhs.value};
        cir::Fragment fragment = chain(std::move(lhs.fragment), std::move(rhs.fragment), loc);
        if (args.size() < 3) {
            report_error("__builtin_shufflevector requires at least one mask index", loc);
            has_error = true;
        }
        for (size_t index = 2; index < args.size(); ++index) {
            int64_t lane = 0;
            if (!evaluate_integer_constant(args[index],
                                           lane,
                                           loc,
                                           "__builtin_shufflevector mask must be an integer constant expression")) {
                has_error = true;
            }
            if (lane < -1 || lane >= lane_limit) {
                report_error("__builtin_shufflevector mask index is out of range", loc);
                has_error = true;
            }
            mask.push_back(lane);
            ExprResult value = require_value(std::move(args[index]), UseContext::RValue, loc);
            has_error = has_error || value.has_error;
            arg_values.push_back(value.value);
            fragment = chain(std::move(fragment), std::move(value.fragment), loc);
        }

        if (mask.empty()) {
            mask.push_back(0);
        }
        if (mask.size() > std::numeric_limits<uint32_t>::max()) {
            report_error("__builtin_shufflevector result has too many lanes", loc);
            has_error = true;
        }
        cir::TypeRef element_ref = file_.vector_element_ref(lhs.type);
        if (!element_ref.valid()) {
            element_ref = file_.type_ref(builder_.int_type());
        }
        std::optional<std::pair<size_t, size_t>> element_layout =
            size_align_of_type(element_ref.type, loc);
        uint64_t size_bytes = element_layout.has_value()
            ? static_cast<uint64_t>(element_layout->first) * mask.size()
            : mask.size();
        cir::TypeId result_type = vector_type(element_ref,
                                              static_cast<uint32_t>(mask.size()),
                                              size_bytes);

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.builtin.shufflevector");
        cir::InstId inst = builder_.builtin_call(kind,
                                                 name,
                                                 result_type,
                                                 arg_values,
                                                 loc,
                                                 {},
                                                 mask);
        cir::Fragment builtin_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(builtin_fragment), loc);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.value = inst;
        result.type = result_type;
        result.category = ValueCategory::PrValue;
        result.has_error = has_error;
        return result;
    }

    auto type_for_signature_char = [&](char spec) -> cir::TypeId {
        switch (spec) {
            case 'v': return builder_.void_type();
            case 'i': return builder_.int_type();
            case 'l': return file_.builtin_type(cir::BuiltinTypeKind::Long);
            case 'L': return file_.builtin_type(cir::BuiltinTypeKind::LongLong);
            case 'z': return builder_.usize_type();
            case 'f': return file_.builtin_type(cir::BuiltinTypeKind::Float);
            case 'd': return file_.builtin_type(cir::BuiltinTypeKind::Double);
            case 'e': return file_.builtin_type(cir::BuiltinTypeKind::LongDouble);
            case 'p': return builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
            case 'q': return builder_.pointer_type(file_.type_ref(
                file_.builtin_type(cir::BuiltinTypeKind::Void),
                cir::QualConst));
            case 'I': return builder_.pointer_type(builder_.int_type());
            case 'D': return builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Double));
            case 'F': return builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Float));
            case 'E': return builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::LongDouble));
            default: return cir::TypeId{};
        }
    };

    auto fixed_arg_type = [&](size_t index) -> cir::TypeId {
        auto float_type = [&]() { return file_.builtin_type(cir::BuiltinTypeKind::Float); };
        auto double_type = [&]() { return file_.builtin_type(cir::BuiltinTypeKind::Double); };
        auto long_double_type = [&]() { return file_.builtin_type(cir::BuiltinTypeKind::LongDouble); };
        switch (kind) {
            case BuiltinKind::ABS:
                return index == 0 ? builder_.int_type() : cir::TypeId{};
            case BuiltinKind::LABS:
                return index == 0 ? file_.builtin_type(cir::BuiltinTypeKind::Long) : cir::TypeId{};
            case BuiltinKind::LLABS:
                return index == 0 ? file_.builtin_type(cir::BuiltinTypeKind::LongLong) : cir::TypeId{};
            case BuiltinKind::FABS: case BuiltinKind::SQRT: case BuiltinKind::SIN:
            case BuiltinKind::COS: case BuiltinKind::EXP: case BuiltinKind::EXP2:
            case BuiltinKind::LOG: case BuiltinKind::LOG2: case BuiltinKind::LOG10:
            case BuiltinKind::FLOOR: case BuiltinKind::CEIL: case BuiltinKind::TRUNC:
            case BuiltinKind::RINT: case BuiltinKind::NEARBYINT: case BuiltinKind::ROUND:
            case BuiltinKind::POW: case BuiltinKind::COPYSIGN: case BuiltinKind::FMIN:
            case BuiltinKind::FMAX: case BuiltinKind::FMOD: case BuiltinKind::FMA:
                return double_type();
            case BuiltinKind::FABSF: case BuiltinKind::SQRTF: case BuiltinKind::SINF:
            case BuiltinKind::COSF: case BuiltinKind::EXPF: case BuiltinKind::EXP2F:
            case BuiltinKind::LOGF: case BuiltinKind::LOG2F: case BuiltinKind::LOG10F:
            case BuiltinKind::FLOORF: case BuiltinKind::CEILF: case BuiltinKind::TRUNCF:
            case BuiltinKind::RINTF: case BuiltinKind::NEARBYINTF: case BuiltinKind::ROUNDF:
            case BuiltinKind::POWF: case BuiltinKind::COPYSIGNF: case BuiltinKind::FMINF:
            case BuiltinKind::FMAXF: case BuiltinKind::FMODF: case BuiltinKind::FMAF:
                return float_type();
            case BuiltinKind::FABSL: case BuiltinKind::SQRTL: case BuiltinKind::SINL:
            case BuiltinKind::COSL: case BuiltinKind::EXPL: case BuiltinKind::EXP2L:
            case BuiltinKind::LOGL: case BuiltinKind::LOG2L: case BuiltinKind::LOG10L:
            case BuiltinKind::FLOORL: case BuiltinKind::CEILL: case BuiltinKind::TRUNCL:
            case BuiltinKind::RINTL: case BuiltinKind::NEARBYINTL: case BuiltinKind::ROUNDL:
            case BuiltinKind::POWL: case BuiltinKind::COPYSIGNL: case BuiltinKind::FMINL:
            case BuiltinKind::FMAXL: case BuiltinKind::FMODL: case BuiltinKind::FMAL:
                return long_double_type();
            case BuiltinKind::ALLOCA:
                return index == 0 ? builder_.usize_type() : cir::TypeId{};
            case BuiltinKind::RETURN_ADDRESS:
            case BuiltinKind::FRAME_ADDRESS:
                return index == 0 ? builder_.int_type() : cir::TypeId{};
            case BuiltinKind::IA32_BZHI_SI:
                return file_.builtin_type(cir::BuiltinTypeKind::UInt);
            case BuiltinKind::CLZG:
            case BuiltinKind::CTZG:
            case BuiltinKind::POPCOUNTG:

                return index == 1 ? builder_.int_type() : cir::TypeId{};
            case BuiltinKind::CLZ: case BuiltinKind::CTZ:
            case BuiltinKind::POPCOUNT: case BuiltinKind::FFS:
            case BuiltinKind::PARITY: case BuiltinKind::CLRSB:

                return builder_.int_type();
            case BuiltinKind::CLZL: case BuiltinKind::CTZL:
            case BuiltinKind::POPCOUNTL: case BuiltinKind::FFSL:
            case BuiltinKind::PARITYL: case BuiltinKind::CLRSBL:
                return file_.builtin_type(cir::BuiltinTypeKind::Long);
            case BuiltinKind::CLZLL: case BuiltinKind::CTZLL:
            case BuiltinKind::POPCOUNTLL: case BuiltinKind::FFSLL:
            case BuiltinKind::PARITYLL: case BuiltinKind::CLRSBLL:
                return file_.builtin_type(cir::BuiltinTypeKind::LongLong);
            case BuiltinKind::ISEQSIG:
                return file_.builtin_type(cir::BuiltinTypeKind::Double);
            default:
                break;
        }
        if (const BuiltinLibcall* libcall = builtin_libcall(kind)) {
            const char* signature = libcall->signature;
            size_t length = std::strlen(signature);
            if (index + 1 < length && signature[index + 1] != '.') {
                return type_for_signature_char(signature[index + 1]);
            }
        }
        return cir::TypeId{};
    };

    std::vector<cir::InstId> arg_values;
    cir::Fragment fragment;
    bool has_error = false;
    arg_values.reserve(args.size());
    const BuiltinLibcall* libcall_spec = builtin_libcall(kind);
    bool libcall_is_variadic = libcall_spec &&
        std::strchr(libcall_spec->signature, '.') != nullptr;
    size_t fixed_param_count = libcall_spec
        ? std::strlen(libcall_spec->signature) -
              (libcall_is_variadic ? 2 : 1)
        : args.size();
    bool generic_count_zero =
        kind == BuiltinKind::CLZG || kind == BuiltinKind::CTZG;
    bool generic_unsigned_bit =
        generic_count_zero || kind == BuiltinKind::POPCOUNTG;
    size_t arg_index = 0;
    for (ExprResult& arg : args) {
        size_t index = arg_index++;
        bool type_dependent =
            (arg.type.valid() && is_dependent_type(arg.type)) ||
            type_contains_dependent_alias_specialization(arg.type);
        if (generic_count_zero && index == 1 && !type_dependent &&
            file_.resolved_type(arg.type) !=
                file_.resolved_type(builder_.int_type())) {
            report_error(std::string(name) +
                             " second argument must have type int",
                         loc);
            has_error = true;
        }
        cir::TypeId expected = fixed_arg_type(index);
        ExprResult value;
        if (expected.valid()) {
            value = convert_to(std::move(arg), expected, UseContext::RValue, loc);
        } else if (libcall_is_variadic && index >= fixed_param_count) {
            value = apply_default_argument_promotion(
                require_value(std::move(arg), UseContext::RValue, loc), loc);
        } else {
            value = require_value(std::move(arg), UseContext::RValue, loc);
        }
        if (generic_unsigned_bit && index == 0 && !type_dependent) {
            cir::TypeId resolved = file_.resolved_type(value.type);
            bool scalar_integer = file_.valid(resolved) &&
                (file_.type(resolved).kind == cir::TypeKind::Builtin ||
                 file_.type(resolved).kind == cir::TypeKind::BitInt ||
                 file_.type(resolved).kind == cir::TypeKind::Enum);
            cir::OperatorValueDomain domain =
                file_.operator_value_domain(file_.type_ref(resolved));
            if (!scalar_integer ||
                (domain != cir::OperatorValueDomain::Bool &&
                 domain != cir::OperatorValueDomain::UnsignedInteger)) {
                report_error(std::string(name) +
                                 " first argument must have scalar unsigned "
                                 "integer type",
                             loc);
                has_error = true;
            }
        }
        has_error = has_error || value.has_error;
        arg_values.push_back(value.value);
        fragment = chain(std::move(fragment), std::move(value.fragment), loc);
    }

    cir::TypeId result_type = builder_.int_type();
    switch (kind) {
        case BuiltinKind::EXPECT:
        case BuiltinKind::EXPECT_WITH_PROBABILITY:
            if (!args.empty() && file_.valid(file_.inst(arg_values.front()).result_type)) {
                result_type = file_.inst(arg_values.front()).result_type;
            }
            break;
        case BuiltinKind::UNREACHABLE:
        case BuiltinKind::TRAP:
            result_type = builder_.void_type();
            break;
        case BuiltinKind::MEMCPY:
        case BuiltinKind::MEMMOVE:
        case BuiltinKind::MEMSET:
            if (!arg_values.empty()) {
                result_type = file_.inst(arg_values.front()).result_type;
            }
            break;
        case BuiltinKind::BSWAP16:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::UShort);
            break;
        case BuiltinKind::BSWAP32:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::UInt);
            break;
        case BuiltinKind::BSWAP64:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
            break;
        case BuiltinKind::STRLEN:
            result_type = builder_.usize_type();
            break;
        case BuiltinKind::ALLOCA:
        case BuiltinKind::RETURN_ADDRESS:
        case BuiltinKind::FRAME_ADDRESS:
            result_type = builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
            break;
        case BuiltinKind::ADD_OVERFLOW:
        case BuiltinKind::SUB_OVERFLOW:
        case BuiltinKind::MUL_OVERFLOW:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::Bool);
            break;
        case BuiltinKind::ABS:
            result_type = builder_.int_type();
            break;
        case BuiltinKind::LABS:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::Long);
            break;
        case BuiltinKind::LLABS:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::LongLong);
            break;
        case BuiltinKind::FABS: case BuiltinKind::SQRT: case BuiltinKind::SIN:
        case BuiltinKind::COS: case BuiltinKind::EXP: case BuiltinKind::EXP2:
        case BuiltinKind::LOG: case BuiltinKind::LOG2: case BuiltinKind::LOG10:
        case BuiltinKind::FLOOR: case BuiltinKind::CEIL: case BuiltinKind::TRUNC:
        case BuiltinKind::RINT: case BuiltinKind::NEARBYINT: case BuiltinKind::ROUND:
        case BuiltinKind::POW: case BuiltinKind::COPYSIGN: case BuiltinKind::FMIN:
        case BuiltinKind::FMAX: case BuiltinKind::FMOD: case BuiltinKind::FMA:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::Double);
            break;
        case BuiltinKind::FABSF: case BuiltinKind::SQRTF: case BuiltinKind::SINF:
        case BuiltinKind::COSF: case BuiltinKind::EXPF: case BuiltinKind::EXP2F:
        case BuiltinKind::LOGF: case BuiltinKind::LOG2F: case BuiltinKind::LOG10F:
        case BuiltinKind::FLOORF: case BuiltinKind::CEILF: case BuiltinKind::TRUNCF:
        case BuiltinKind::RINTF: case BuiltinKind::NEARBYINTF: case BuiltinKind::ROUNDF:
        case BuiltinKind::POWF: case BuiltinKind::COPYSIGNF: case BuiltinKind::FMINF:
        case BuiltinKind::FMAXF: case BuiltinKind::FMODF: case BuiltinKind::FMAF:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::Float);
            break;
        case BuiltinKind::FABSL: case BuiltinKind::SQRTL: case BuiltinKind::SINL:
        case BuiltinKind::COSL: case BuiltinKind::EXPL: case BuiltinKind::EXP2L:
        case BuiltinKind::LOGL: case BuiltinKind::LOG2L: case BuiltinKind::LOG10L:
        case BuiltinKind::FLOORL: case BuiltinKind::CEILL: case BuiltinKind::TRUNCL:
        case BuiltinKind::RINTL: case BuiltinKind::NEARBYINTL: case BuiltinKind::ROUNDL:
        case BuiltinKind::POWL: case BuiltinKind::COPYSIGNL: case BuiltinKind::FMINL:
        case BuiltinKind::FMAXL: case BuiltinKind::FMODL: case BuiltinKind::FMAL:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::LongDouble);
            break;
        case BuiltinKind::IA32_BZHI_SI:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::UInt);
            break;
        case BuiltinKind::ADD_OVERFLOW_P:
        case BuiltinKind::SUB_OVERFLOW_P:
            result_type = file_.builtin_type(cir::BuiltinTypeKind::Bool);
            break;
        case BuiltinKind::MEMCMP_EQ:
        case BuiltinKind::ISEQSIG:
            result_type = builder_.int_type();
            break;
        case BuiltinKind::CLEAR_CACHE:
        case BuiltinKind::PREFETCH:
        case BuiltinKind::STACK_RESTORE:
        case BuiltinKind::CLEAR_PADDING:
            result_type = builder_.void_type();
            break;
        case BuiltinKind::STACK_SAVE:
            result_type = builder_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
            break;
        case BuiltinKind::SIGNBIT:
        case BuiltinKind::SIGNBITF:
        case BuiltinKind::SIGNBITL:
        case BuiltinKind::ISUNORDERED:
        case BuiltinKind::ISGREATER:
        case BuiltinKind::ISLESS:
        case BuiltinKind::ISLESSEQUAL:
        case BuiltinKind::ISLESSGREATER:
        case BuiltinKind::ISGREATEREQUAL:
            result_type = builder_.int_type();
            break;
        default:
            if (const BuiltinLibcall* libcall = builtin_libcall(kind)) {
                cir::TypeId from_signature =
                    type_for_signature_char(libcall->signature[0]);
                result_type = from_signature.valid() ? from_signature
                                                     : builder_.int_type();
            } else {
                result_type = builder_.int_type();
            }
            break;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.builtin");
    cir::InstId inst = builder_.builtin_call(kind, name, result_type, arg_values, loc);
    cir::Fragment builtin_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(builtin_fragment), loc);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = result_type;
    result.category = ValueCategory::PrValue;
    result.has_error = has_error;
    return result;
}

ExprResult Session::collect_va_arg_expr(ExprResult va_list,
                                        cir::TypeId arg_type,
                                        SrcLoc loc) {
    ExprResult list_place = require_place(std::move(va_list), UseContext::Assignment, loc);
    bool has_error = list_place.has_error;
    if (!file_.valid(arg_type)) {
        report_error("__builtin_va_arg requires a valid type argument", loc);
        arg_type = file_.unknown_type();
        has_error = true;
    } else {
        cir::TypeId resolved = file_.resolved_type(arg_type);
        if (file_.valid(resolved) && file_.type(resolved).kind == cir::TypeKind::Function) {
            report_error("__builtin_va_arg cannot use function type", loc);
            has_error = true;
        }
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.va_arg");
    cir::InstId inst = builder_.emit_va_arg(list_place.place, arg_type, loc);
    cir::Fragment va_fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(list_place.fragment), std::move(va_fragment), loc);
    result.value = inst;
    result.type = arg_type;
    result.category = ValueCategory::PrValue;
    result.has_error = has_error;
    return result;
}

ExprResult Session::collect_call_expr(ExprResult callee,
                                      std::vector<ExprResult> args,
                                      SrcLoc loc) {
    ExprResult result =
        collect_call_expr_impl(std::move(callee), std::move(args), loc);
    return fold_immediate_invocation(std::move(result), loc);
}

ExprResult Session::fold_immediate_invocation(ExprResult call, SrcLoc loc) {
    if (call.has_error || !call.value.valid() || !lang_opts_.is_cxx_mode() ||
        !file_.valid(call.value)) {
        return call;
    }
    cir::InstId invocation = call.value;
    const cir::Inst* invocation_inst = &file_.inst(invocation);
    if (invocation_inst->kind != cir::InstKind::Call &&
        invocation_inst->kind == cir::InstKind::LValueToRValue) {

        std::vector<cir::ValueRef> load_operands =
            file_.value_operands(invocation_inst->operands);
        cir::EntityId result_object{};
        if (!load_operands.empty() &&
            file_.valid(load_operands.front().inst)) {
            const cir::Inst& place = file_.inst(load_operands.front().inst);
            if (place.kind == cir::InstKind::LocalPlace &&
                place.place_fact.valid()) {
                result_object = file_.place_fact(place.place_fact).entity;
            }
        }
        if (result_object.valid()) {
            for (auto block_it = call.fragment.blocks.rbegin();
                 block_it != call.fragment.blocks.rend() &&
                     invocation_inst->kind != cir::InstKind::Call;
                 ++block_it) {
                const cir::Block& block = file_.block(*block_it);
                for (auto inst_it = block.instructions.rbegin();
                     inst_it != block.instructions.rend(); ++inst_it) {
                    const cir::Inst& candidate = file_.inst(*inst_it);
                    if (candidate.kind == cir::InstKind::Call &&
                        candidate.result_object_entity == result_object) {
                        invocation = *inst_it;
                        invocation_inst = &candidate;
                        break;
                    }
                }
            }
        }
    }
    if (invocation_inst->kind != cir::InstKind::Call) {
        return call;
    }
    std::vector<cir::Operand> operands =
        file_.operands(invocation_inst->operands);
    if (operands.empty()) {
        return call;
    }
    const auto* callee_entity = std::get_if<cir::EntityId>(&operands[0].data);
    if (!callee_entity || !callee_entity->valid() ||
        !file_.valid(*callee_entity) ||
        !file_.entity(*callee_entity).decl_flags.is_consteval) {
        return call;
    }

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_immediate_function();
    request.loc = loc;
    request.required = true;
    ConstEvalResult evaluated = engine.evaluate_fragment(
        call.fragment, cir::ValueRef(call.value), request);
    if (evaluated.status != ConstEvalStatus::Constant ||
        !evaluated.value.has_value()) {
        return call;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.immediate");
    cir::InstId folded{};
    switch (evaluated.value->kind) {
        case ConstValueKind::Integer: {
            cir::IntegerValue value = evaluated.value->int_value;
            folded = builder_.integer_literal(value,
                                              call.type,
                                              value.decimal(),
                                              loc);
            break;
        }
        case ConstValueKind::Boolean:
            folded = builder_.boolean_literal(
                evaluated.value->bool_value,
                evaluated.value->bool_value ? "true" : "false",
                loc);
            break;
        case ConstValueKind::MetaInfo: {
            const std::shared_ptr<ConstMetaInfoValue>& handle =
                evaluated.value->meta_info_value;
            if (handle && handle->kind == cir::MetaInfoKind::Type) {
                folded = builder_.reflect_type(handle->type, loc);
            } else if (handle && handle->entity.valid()) {
                folded = builder_.reflect_entity(handle->kind,
                                                 handle->entity,
                                                 loc);
            }
            break;
        }
        case ConstValueKind::Object: {
            std::vector<cir::TypeId> record_stack;
            if (!type_is_trivially_destructible(file_, call.type,
                                                record_stack)) {
                break;
            }
            std::optional<size_t> size = size_of_type(call.type, loc);
            if (!size.has_value()) {
                break;
            }
            ConstantStateAddressPolicy address_is_durable =
                [this](cir::EntityId target) {
                    if (!target.valid() || !file_.valid(target)) {
                        return false;
                    }
                    cir::StorageDuration duration =
                        file_.entity(target).storage_duration;
                    return duration == cir::StorageDuration::Static ||
                        duration == cir::StorageDuration::Thread;
                };
            std::string state_error;
            std::optional<cir::ConstantStateFact> state =
                constant_state_from_value(
                    file_, call.type, *evaluated.value, &state_error,
                    &address_is_durable);
            std::vector<uint8_t> bytes(*size, 0);
            std::vector<cir::StaticInitializerRelocation> relocations;
            if (!state.has_value()) {
                break;
            }
            if (!write_static_const_value(
                    bytes, 0, call.type, *evaluated.value, loc,
                    &relocations)) {
                break;
            }
            std::string name = ".immediate.result." +
                std::to_string(compound_literal_counter_++);
            cir::EntityId backing = builder_.add_entity(
                cir::EntityKind::Variable, name, call.type, {}, loc,
                cir::StorageDuration::Static,
                cir::MemorySpace::Default, {});
            cir::Entity& record = file_.entity_mut(backing);
            record.is_definition = true;
            record.linkage = cir::LinkageKind::Internal;
            record.qualifiers = cir::QualConst;
            record.decl_flags.is_constexpr = true;
            record.has_static_initializer = true;
            record.static_initializer_bytes = std::move(bytes);
            record.static_initializer_relocations =
                std::move(relocations);
            record.constant_state =
                file_.add_constant_state(std::move(*state));
            mark_static_initializer_relocations_required(
                record.static_initializer_relocations, loc);
            cir::InstId place = builder_.global_place(backing, loc);
            folded = builder_.lvalue_to_rvalue(place, loc);
            break;
        }
        default:
            break;
    }
    cir::Fragment fragment = finish_fragment_block(block, previous);
    if (!folded.valid()) {

        return call;
    }
    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = folded;
    result.type = call.type;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::collect_call_expr_impl(ExprResult callee,
                                           std::vector<ExprResult> args,
                                           SrcLoc loc) {
    if (lang_opts_.is_cxx_mode() && callee.destructor_designator) {
        bool has_error = callee.has_error;
        if (!args.empty()) {
            report_error("destructor call cannot have arguments", loc);
            has_error = true;
        }
        ExprResult object = collect_this_expr(loc);
        object.fragment = chain(std::move(callee.fragment),
                                std::move(object.fragment), loc);
        ExprResult result = collect_explicit_destructor_call(
            std::move(object), callee.type, callee.type,
            /*is_arrow=*/true, /*is_qualified=*/true, loc);
        result.has_error = result.has_error || has_error;
        return result;
    }

    if (lang_opts_.is_cxx_mode() && callee.category == ValueCategory::Type &&
        callee.type.valid()) {
        return collect_functional_cast(callee.type, std::move(args), loc);
    }
    if (lang_opts_.is_cxx_mode()) {
        bool dependent = expr_is_dependent(callee);
        bool value_dependent_callee =
            !dependent && expr_is_value_dependent(callee);

        if (!dependent && collecting_pattern_ &&
            callee.category == ValueCategory::FunctionDesignator) {
            std::vector<cir::EntityId> candidates = callee.candidates;
            if (candidates.empty() && callee.entity.valid()) {
                candidates.push_back(callee.entity);
            }
            bool conversion_depends_on_substitution = false;
            for (cir::EntityId candidate : candidates) {
                if (!candidate.valid() || !file_.valid(candidate) ||
                    template_info(candidate) != nullptr) {
                    continue;
                }
                cir::TypeId function_type =
                    file_.resolved_type(file_.entity(candidate).type);
                const cir::FunctionTypePayload* function =
                    file_.valid(function_type) &&
                            file_.type(function_type).kind ==
                                cir::TypeKind::Function
                        ? std::get_if<cir::FunctionTypePayload>(
                              &file_.type_payload(function_type))
                        : nullptr;
                if (!function) {
                    continue;
                }
                const cir::RecordMethodFact* method =
                    file_.method_fact(candidate);
                size_t parameter_offset =
                    method && !method->is_static ? 1 : 0;
                size_t compared = std::min(
                    args.size(),
                    function->parameters.size() > parameter_offset
                        ? function->parameters.size() - parameter_offset
                        : size_t{0});
                for (size_t index = 0; index < compared; ++index) {
                    cir::TypeId parameter =
                        function->parameters[parameter_offset + index].type;
                    if (is_dependent_type(parameter) ||
                        type_contains_dependent_alias_specialization(
                            parameter)) {
                        conversion_depends_on_substitution = true;
                        break;
                    }
                }
                if (conversion_depends_on_substitution) {
                    break;
                }
            }
            if (conversion_depends_on_substitution) {
                mark_pattern_unusable();
                dependent = true;
            }
        }

        if (!dependent && collecting_pattern_ &&
            callee.category == ValueCategory::FunctionDesignator &&
            callee.entity.valid() && file_.valid(callee.entity) &&
            callee.candidates.size() <= 1) {
            const cir::Entity& entity = file_.entity(callee.entity);
            cir::PlaceholderResultFactId placeholder =
                entity.placeholder_result;
            dependent =
                entity.has_deferred_definition &&
                file_.valid(placeholder) &&
                file_.placeholder_result_fact(placeholder).state ==
                    cir::PlaceholderResultState::Undeduced;
        }

        for (const cir::TemplateArgument& argument :
             callee.explicit_template_arguments) {
            dependent = dependent || argument.is_dependent ||
                (argument.kind == cir::TemplateArgumentKind::Type &&
                 argument.type.type.valid() &&
                 is_dependent_type(argument.type.type)) ||
                (argument.kind == cir::TemplateArgumentKind::Value &&
                 (argument.dependent_value_expr.valid() ||
                  (argument.value_type.type.valid() &&
                   is_dependent_type(argument.value_type.type)))) ||
                (argument.kind == cir::TemplateArgumentKind::Template &&
                 !argument.template_entity.valid());
        }
        for (const CandidateExplicitTemplateArguments& candidate :
             callee.candidate_explicit_template_arguments) {
            if (!candidate.viable) {
                continue;
            }
            for (const cir::TemplateArgument& argument :
                 candidate.arguments) {
                dependent = dependent || argument.is_dependent ||
                    (argument.kind == cir::TemplateArgumentKind::Type &&
                     argument.type.type.valid() &&
                     is_dependent_type(argument.type.type)) ||
                    (argument.kind == cir::TemplateArgumentKind::Value &&
                     (argument.dependent_value_expr.valid() ||
                      (argument.value_type.type.valid() &&
                       is_dependent_type(argument.value_type.type)))) ||
                    (argument.kind == cir::TemplateArgumentKind::Template &&
                     !argument.template_entity.valid());
            }
        }
        bool value_dependent_arguments = false;
        for (const ExprResult& arg : args) {
            dependent = dependent || expr_is_dependent(arg);
            value_dependent_arguments =
                value_dependent_arguments ||
                expr_is_value_dependent(arg);
        }
        bool known_result_type = !dependent;
        if (known_result_type &&
            (value_dependent_callee || value_dependent_arguments) &&
            callee.category == ValueCategory::FunctionDesignator) {

            cir::EntityId selected =
                resolve_call_overload(callee, args, loc);
            if (selected.valid()) {
                callee.entity = selected;
                callee.type = file_.entity(selected).type;
                callee.candidates = {selected};
                callee.overload_designator.reset();
            } else {
                known_result_type = false;
            }
        }
        dependent = dependent || value_dependent_callee ||
                    value_dependent_arguments;
        if (dependent) {
            cir::TypeId result_type =
                file_.dependent_type("dependent-call-result");
            if (known_result_type && callee.type.valid()) {
                cir::TypeId resolved_callee =
                    file_.resolved_type(callee.type);
                const auto* function =
                    file_.valid(resolved_callee) &&
                            file_.type(resolved_callee).kind ==
                                cir::TypeKind::Function
                        ? std::get_if<cir::FunctionTypePayload>(
                              &file_.type_payload(resolved_callee))
                        : nullptr;
                if (function && function->return_type.type.valid()) {
                    result_type = function->return_type.type;
                }
            }

            if (!callee.name.empty() &&
                (!callee.qualified_name ||
                 callee.builtin_call_designator)) {
                if (const BuiltinInfo* builtin_info =
                        BuiltinRegistry::instance().lookup(callee.name);
                    builtin_info && is_builtin_call_syntax(*builtin_info)) {
                    switch (builtin_info->kind) {
                        case BuiltinKind::OPERATOR_NEW:
                            result_type = builder_.pointer_type(
                                file_.builtin_type(
                                    cir::BuiltinTypeKind::Void));
                            break;
                        case BuiltinKind::OPERATOR_DELETE:
                            result_type = file_.builtin_type(
                                cir::BuiltinTypeKind::Void);
                            break;
                        case BuiltinKind::LAUNDER:
                            if (!args.empty() && args.front().type.valid()) {
                                result_type = args.front().type;
                            }
                            break;
                        default:
                            break;
                    }
                }
            }
            cir::TemplateValueExpression call_expression =
                template_value_call_expr(
                    *this,
                    file_,
                    callee,
                    args,
                    type_ref(result_type),
                    current_decl_context(),
                    lookup_generation_,
                    loc);
            ExprResult combined = std::move(callee);
            for (ExprResult& arg : args) {
                combined.fragment = chain(std::move(combined.fragment),
                                          std::move(arg.fragment), loc);
            }
            combined.template_value_expr = std::move(call_expression);
            combined.value_dependent = true;

            combined.entity = {};
            combined.name.clear();
            combined.candidates.clear();
            combined.overload_designator.reset();
            combined.explicit_template_arguments.clear();
            combined.candidate_explicit_template_arguments.clear();
            combined.dependent_value_qualifier = {};
            combined.dependent_value_name = {};
            combined.dependent_member_access.reset();
            combined.builtin_call_designator = false;
            combined.qualified_name = false;
            combined.unresolved_unqualified_name = false;
            combined.suppress_argument_dependent_lookup = false;
            if (!is_dependent_type(result_type)) {

                cir::TypeId resolved_result =
                    file_.resolved_type(result_type);
                if (is_reference_type(resolved_result)) {
                    cir::TypeRef referred =
                        file_.reference_referred_ref(resolved_result);
                    cir::TypeId resolved_referred =
                        file_.resolved_type(referred.type);
                    bool refers_to_function =
                        file_.valid(resolved_referred) &&
                        file_.type(resolved_referred).kind ==
                            cir::TypeKind::Function;
                    bool is_lvalue =
                        file_.type(resolved_result).kind ==
                            cir::TypeKind::LValueReference ||
                        refers_to_function;
                    return make_deferred_typed_expr(
                        std::move(combined),
                        referred.type.valid() ? referred.type
                                              : builder_.unknown_type(),
                        is_lvalue ? ValueCategory::LValue
                                  : ValueCategory::XValue,
                        loc);
                }
                return make_deferred_typed_expr(
                    std::move(combined),
                    result_type,
                    ValueCategory::PrValue,
                    loc);
            }
            return make_dependent_expr(std::move(combined), loc);
        }
    }

    if (!callee.name.empty() &&
        (!callee.qualified_name || callee.builtin_call_designator)) {
        if (const BuiltinInfo* builtin_info =
                BuiltinRegistry::instance().lookup(callee.name)) {

            bool has_declared_overloads =
                callee.category == ValueCategory::FunctionDesignator &&
                callee.candidates.size() > 1;
            if (is_builtin_call_syntax(*builtin_info) &&
                !has_declared_overloads) {
                return collect_builtin_call(callee.name,
                                            builtin_info->kind,
                                            std::move(args),
                                            loc);
            }
            if (has_reserved_builtin_prefix(callee.name)) {
                report_error("unsupported builtin '" + callee.name + "'", loc);
                return collect_unsupported_expr("unsupported builtin", std::move(args), loc);
            }
        }
    }

    if (callee.category == ValueCategory::Dependent && !callee.entity.valid() &&
        !callee.name.empty() && lang_opts_.is_c_mode()) {
        report_warning(WarningId::ImplicitFunctionDeclaration,
                       "implicit declaration of function '" + callee.name + "'",
                       loc);
        cir::TypeId implicit_type = function_type(
            file_.type_ref(builder_.int_type()), {}, false, false);
        DeclResult implicit =
            declare_function_type(callee.name, implicit_type,
                                  file_.type_ref(builder_.int_type()), {}, loc);
        callee.entity = implicit.entity;
        callee.category = ValueCategory::FunctionDesignator;
        callee.fragment = {};
        callee.value = {};
    }

    std::vector<cir::InstId> arg_values;
    bool has_error = callee.has_error;
    cir::Fragment fragment;
    cir::InstId indirect_callee{};
    cir::TypeId source_function_type{};
    bool direct = callee.category == ValueCategory::FunctionDesignator && callee.entity.valid();
    bool dependent = callee.category == ValueCategory::Dependent;
    bool member_pointer_call =
        callee.category == ValueCategory::MemberFunctionPointerCallee;
    bool block_call = false;
    bool missing_implicit_object = false;
    cir::EntityId virtual_declaration{};

    if (lang_opts_.is_cxx_mode() && dependent && !callee.name.empty() &&
        !callee.qualified_name &&
        !callee.suppress_argument_dependent_lookup) {
        std::vector<cir::EntityId> adl_candidates;
        add_adl_candidates(callee.name, args, adl_candidates);
        if (!adl_candidates.empty()) {
            bool ambiguous = false;
            OverloadAmbiguityInfo ambiguity_info;
            cir::EntityId selected = adl_candidates.size() == 1
                ? adl_candidates.front()
                : select_overload(adl_candidates, args,
                                  /*member_object_leading=*/false,
                                  &ambiguous,
                                  {},
                                  &ambiguity_info);
            if (selected.valid()) {

                callee.fragment = {};
                callee.value = {};
                callee.entity = selected;
                callee.category = ValueCategory::FunctionDesignator;
                direct = true;
                dependent = false;
            } else if (ambiguous) {
                report_error("call to '" + callee.name + "' is ambiguous", loc);
                report_overload_ambiguity_notes(ambiguity_info, loc);
                has_error = true;
            }
        } else if (callee.unresolved_unqualified_name) {
            report_error("use of undeclared identifier '" + callee.name + "'",
                         loc);
            note_module_hidden_name(callee.name, loc);
            has_error = true;
        }
    }
    if (member_pointer_call) {
        fragment = std::move(callee.fragment);
        cir::TypeId member_pointer_type =
            callee.value.valid() && file_.valid(callee.value)
                ? file_.resolved_type(file_.inst(callee.value).result_type)
                : cir::TypeId{};
        cir::TypeId member_class = file_.valid(member_pointer_type)
            ? file_.resolved_type(
                  file_.member_pointer_class_ref(member_pointer_type).type)
            : cir::TypeId{};
        source_function_type = member_class.valid()
            ? member_function_type_with_this(member_class, callee.type)
            : cir::TypeId{};
        cir::TypeId resolved_function_type =
            file_.resolved_type(source_function_type);
        const auto* payload =
            file_.valid(resolved_function_type) &&
                    file_.type(resolved_function_type).kind ==
                        cir::TypeKind::Function
                ? std::get_if<cir::FunctionTypePayload>(
                      &file_.type_payload(resolved_function_type))
                : nullptr;
        if (!payload || payload->parameters.empty()) {
            report_error("member function pointer call has invalid function type",
                         loc);
            has_error = true;
        } else {
            cir::TypeId this_pointer_type = payload->parameters.front().type;
            cir::TypeId function_pointer_type =
                pointer_type(file_.type_ref(source_function_type));
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.memberptr.call");
            cir::InstId this_value = builder_.addr_of(callee.place, loc);
            if (this_pointer_type.valid() &&
                !type_equal(file_.inst(this_value).result_type,
                            this_pointer_type)) {
                this_value = builder_.cast(this_pointer_type,
                                           this_value,
                                           "conversion",
                                           loc);
            }
            this_value = builder_.member_function_pointer_this(
                this_value, callee.value, this_pointer_type, loc);
            indirect_callee = builder_.member_function_pointer_callee(
                this_value, callee.value, function_pointer_type, loc);
            cir::Fragment member_call_fragment =
                finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment),
                             std::move(member_call_fragment), loc);

            ExprResult this_arg;
            this_arg.value = this_value;
            this_arg.type = file_.inst(this_value).result_type;
            this_arg.category = ValueCategory::PrValue;
            args.insert(args.begin(), std::move(this_arg));
        }
    } else if (!direct && !dependent) {

        if (lang_opts_.is_cxx_mode()) {
            bool call_handled = false;
            ExprResult overloaded =
                try_overloaded_call(callee, args, &call_handled, loc);
            if (call_handled) {
                return overloaded;
            }
        }
        ExprResult callee_value = require_value(std::move(callee), UseContext::RValue, loc);
        has_error = has_error || callee_value.has_error;
        cir::TypeId callee_type = file_.resolved_type(callee_value.type);
        if (file_.valid(callee_type) &&
            file_.type(callee_type).kind == cir::TypeKind::BlockPointer) {

            const auto* payload =
                std::get_if<cir::BlockPointerTypePayload>(&file_.type_payload(callee_type));
            cir::TypeId block_fn = payload
                ? file_.resolved_type(payload->pointee.type)
                : cir::TypeId{};
            fragment = std::move(callee_value.fragment);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("block.call");
            cir::TypeId header = block_header_record_type(loc);
            cir::InstId header_ptr = builder_.cast(
                builder_.pointer_type(header), callee_value.value, "arith", loc);
            cir::InstId header_place = builder_.deref(header_ptr, loc);
            const cir::RecordFacts* header_facts = file_.record_facts_for_type(header);
            cir::InstId invoke_value{};
            if (header_facts && header_facts->fields.size() >= 4) {
                const cir::RecordFieldFact& invoke_field = header_facts->fields[3];
                cir::InstId invoke_place = builder_.field_addr(
                    header_place, invoke_field.entity, invoke_field.type.type, loc);
                invoke_value = builder_.load(invoke_place, loc);

                if (const auto* fn_payload =
                        std::get_if<cir::FunctionTypePayload>(
                            &file_.type_payload(block_fn))) {
                    std::vector<cir::TypeId> invoke_params;
                    invoke_params.push_back(callee_type);
                    for (const auto& parameter : fn_payload->parameters) {
                        invoke_params.push_back(parameter.type);
                    }
                    cir::TypeId invoke_fn = file_.function_type(
                        fn_payload->return_type.type, invoke_params);
                    invoke_value = builder_.cast(
                        builder_.pointer_type(invoke_fn), invoke_value,
                        "arith", loc);
                }
            }
            fragment = chain(std::move(fragment),
                             finish_fragment_block(block, previous), loc);
            source_function_type = block_fn;
            indirect_callee = invoke_value;
            block_call = true;

            ExprResult literal_arg;
            literal_arg.value = callee_value.value;
            literal_arg.type = callee_type;
            literal_arg.category = ValueCategory::PrValue;
            args.insert(args.begin(), std::move(literal_arg));
        } else {
            cir::TypeId function_type = file_.pointer_pointee_type(callee_type);
            function_type = file_.resolved_type(function_type);
            if (!file_.valid(function_type) ||
                file_.type(function_type).kind != cir::TypeKind::Function) {
                report_error("called object is not a function or function pointer", loc);
                has_error = true;
            }
            source_function_type = function_type;
            indirect_callee = callee_value.value;
            fragment = std::move(callee_value.fragment);
        }
    } else {
        if (direct) {
            source_function_type = file_.entity(callee.entity).type;
        }
        fragment = std::move(callee.fragment);
        if (direct && lang_opts_.is_cxx_mode()) {
            cir::EntityId selected = resolve_call_overload(callee, args, loc);
            if (selected.valid()) {
                callee.entity = selected;
                source_function_type = file_.entity(selected).type;
                if (const cir::RecordMethodFact* selected_method =
                        file_.method_fact(selected);
                    selected_method &&
                    selected_method->is_conversion_function) {
                    retain_selected_conversion_template_emission(
                        selected, callee.candidates);
                }

                cir::EntityKind selected_kind = file_.entity(selected).kind;
                if (callee.place.valid() &&
                    (selected_kind == cir::EntityKind::Method ||
                     selected_kind == cir::EntityKind::Destructor)) {
                    const cir::RecordMethodFact* selected_fact =
                        file_.method_fact(selected);
                    cir::EntityId selected_owner = file_.entity(selected).parent;
                    cir::TypeId selected_owner_type =
                        selected_owner.valid() && file_.valid(selected_owner)
                            ? file_.entity(selected_owner).type
                            : cir::TypeId{};
                    cir::TypeId bound_object_type =
                        object_type_from_place(callee.place);
                    cir::TypeId access_object_type =
                        callee.member_access_object_type.valid()
                            ? callee.member_access_object_type
                            : bound_object_type;
                    const MemberCandidateObjectPaths* canonical_paths =
                        nullptr;
                    for (const MemberCandidateObjectPaths& paths :
                         callee.member_candidate_object_paths) {
                        if (paths.entity == selected) {
                            canonical_paths = &paths;
                            break;
                        }
                    }
                    if (canonical_paths &&
                        canonical_paths->has_declared_access) {
                        if (selected_fact && !selected_fact->is_static &&
                            canonical_paths->declared_access ==
                                cir::RecordMemberAccess::Protected &&
                            !protected_member_object_access_allowed(
                                canonical_paths->access_owner,
                                access_object_type)) {
                            report_error(
                                "protected member of '" +
                                    file_.format_type(file_.entity(
                                        canonical_paths->access_owner).type) +
                                    "' is only accessible through an object "
                                    "of the granting class or one derived "
                                    "from it",
                                loc);
                            has_error = true;
                        }
                    }
                    bool used_canonical_path = false;
                    if (selected_fact && !selected_fact->is_static &&
                        canonical_paths) {
                        used_canonical_path = true;
                        if (canonical_paths->paths.size() != 1) {
                            report_error("member '" + callee.name +
                                             "' is ambiguous through base classes",
                                         loc);
                            has_error = true;

                            if (!canonical_paths->paths.empty()) {
                                cir::BlockId previous =
                                    builder_.current_block();
                                cir::BlockId block = begin_fragment_block(
                                    "expr.call.owner.error-recovery");
                                callee.place = emit_subobject_path(
                                    callee.place,
                                    canonical_paths->paths.front(), loc);
                                cir::Fragment adjust_fragment =
                                    finish_fragment_block(block, previous);
                                fragment = chain(std::move(fragment),
                                                 std::move(adjust_fragment),
                                                 loc);
                            }
                        } else {
                            const std::vector<cir::EntityId>& base_path =
                                canonical_paths->paths.front();
                            if (!base_path.empty()) {
                                if (!canonical_paths->found_through_using &&
                                    selected_owner_type.valid() &&
                                    !check_base_path_access(
                                        base_path,
                                        bound_object_type,
                                        selected_owner_type,
                                        loc)) {
                                    has_error = true;
                                }
                                cir::BlockId previous =
                                    builder_.current_block();
                                cir::BlockId block = begin_fragment_block(
                                    "expr.call.owner.canonical");
                                cir::InstId adjusted = emit_subobject_path(
                                    callee.place, base_path, loc);
                                cir::Fragment adjust_fragment =
                                    finish_fragment_block(block, previous);
                                fragment = chain(std::move(fragment),
                                                 std::move(adjust_fragment),
                                                 loc);
                                callee.place = adjusted;
                            }
                        }
                    }
                    if (!used_canonical_path && selected_owner_type.valid() &&
                        bound_object_type.valid() &&
                        file_.resolved_type(selected_owner_type) !=
                            file_.resolved_type(bound_object_type)) {
                        std::vector<cir::EntityId> base_path;
                        if (derived_to_base_path(bound_object_type,
                                                 selected_owner_type,
                                                 &base_path) &&
                            !base_path.empty()) {
                            cir::BlockId previous = builder_.current_block();
                            cir::BlockId block = begin_fragment_block(
                                "expr.call.owner.adjust");
                            cir::InstId adjusted = emit_subobject_path(
                                callee.place, base_path, loc);
                            cir::Fragment adjust_fragment =
                                finish_fragment_block(block, previous);
                            fragment = chain(std::move(fragment),
                                             std::move(adjust_fragment), loc);
                            callee.place = adjusted;
                        }
                    }
                }
            } else {
                has_error = true;
            }
        }
        if (direct) {
            cir::EntityKind callee_kind = file_.entity(callee.entity).kind;
            bool is_member_callee = callee_kind == cir::EntityKind::Method ||
                                    callee_kind == cir::EntityKind::Constructor ||
                                    callee_kind == cir::EntityKind::Destructor;
            const cir::RecordMethodFact* fact =
                is_member_callee ? file_.method_fact(callee.entity) : nullptr;

            const cir::RecordMethodFact* pattern_fact = nullptr;
            if (is_member_callee) {
                std::vector<TemplateArgument> member_arguments;
                const TemplateInfo* member_template =
                    member_instantiation_template(callee.entity,
                                                  &member_arguments,
                                                  nullptr);
                if (member_template) {
                    cir::EntityId pattern_member =
                        class_template_member_pattern_entity(
                            callee.entity, *member_template);
                    if (pattern_member.valid()) {
                        pattern_fact = file_.method_fact(pattern_member);
                        if (!fact) {
                            fact = pattern_fact;
                        }
                    }
                }
            }
            if (file_.entity(callee.entity).is_deleted &&
                !(fact && fact->is_deleted)) {
                std::string deleted_name = callee.name.empty()
                    ? std::string(file_.name(
                          file_.entity(callee.entity).name))
                    : callee.name;
                report_error("call to deleted function '" +
                                 deleted_name + "'",
                             loc);
                has_error = true;
            }
            if (fact && fact->is_deleted) {
                const cir::RecordFacts* owner =
                    file_.record_facts(file_.entity(callee.entity).parent);
                if (owner && owner->is_lambda_closure &&
                    !owner->fields.empty() && fact->name.valid() &&
                    file_.name(fact->name) == "operator=") {
                    report_error("the closure type's copy assignment operator "
                                 "is deleted",
                                 loc);
                } else {
                    report_error("call to deleted member function '" +
                                     std::string(file_.name(fact->name)) +
                                     "'",
                                 loc);
                }
                has_error = true;
            }
            if (const cir::DefaultedComparisonFact* comparison =
                    file_.defaulted_comparison_fact(callee.entity);
                comparison && comparison->is_deleted &&
                !(fact && fact->is_deleted)) {
                report_error("call to deleted comparison function '" +
                                 callee.name + "'",
                             loc);
                if (!comparison->deletion_reason.empty()) {
                    file_.add_note(comparison->deletion_reason,
                                   file_.entity(callee.entity).loc);
                }
                has_error = true;
            }
            bool is_static_member =
                file_.entity(callee.entity).is_static_member_function ||
                (fact && fact->is_static) ||
                (pattern_fact && pattern_fact->is_static);
            if (is_member_callee && !is_static_member) {

                if (!callee.place.valid() &&
                    current_complete_class_object_place_.valid()) {
                    callee.place = current_complete_class_object_place_;
                } else if (!callee.place.valid() &&
                           current_this_place_.valid()) {
                    cir::TypeId method_class =
                        file_.entity(file_.entity(callee.entity).parent).type;
                    cir::TypeId current_class =
                        file_.entity(current_member_record_).type;
                    std::vector<cir::EntityId> base_path;
                    bool reachable =
                        file_.resolved_type(method_class) ==
                            file_.resolved_type(current_class) ||
                        derived_to_base_path(current_class, method_class,
                                             &base_path);
                    if (reachable) {
                        cir::BlockId previous = builder_.current_block();
                        cir::BlockId block =
                            begin_fragment_block("expr.call.this.qualified");
                        cir::InstId this_value =
                            builder_.lvalue_to_rvalue(current_this_place_, loc);
                        cir::InstId place = builder_.deref(this_value, loc);
                        place = emit_subobject_path(place, base_path, loc);
                        cir::Fragment this_fragment =
                            finish_fragment_block(block, previous);
                        fragment = chain(std::move(fragment),
                                         std::move(this_fragment), loc);
                        callee.place = place;
                    }
                }
                if (!callee.place.valid()) {
                    report_error("cannot call a non-static member function without an object",
                                 loc);
                    has_error = true;
                    missing_implicit_object = true;
                } else {
                    cir::TypeId method_class =
                        file_.entity(file_.entity(callee.entity).parent).type;
                    cir::TypeId object_class =
                        object_type_from_place(callee.place);
                    if (file_.resolved_type(object_class) !=
                        file_.resolved_type(method_class)) {
                        std::vector<cir::EntityId> base_path;
                        if (derived_to_base_path(object_class, method_class,
                                                 &base_path) &&
                            !base_path.empty()) {
                            cir::BlockId previous = builder_.current_block();
                            cir::BlockId block = begin_fragment_block(
                                "expr.call.this.base");
                            cir::InstId adjusted = emit_subobject_path(
                                callee.place, base_path, loc);
                            cir::Fragment adjustment =
                                finish_fragment_block(block, previous);
                            fragment = chain(std::move(fragment),
                                             std::move(adjustment), loc);
                            callee.place = adjusted;
                        }
                    }
                    bool dispatch_virtually =
                        fact && fact->is_virtual && fact->vtable_slot >= 0 &&
                        !callee.qualified_name;
                    cir::BlockId previous = builder_.current_block();
                    cir::BlockId block = begin_fragment_block("expr.call.this");
                    cir::InstId this_value = builder_.addr_of(callee.place, loc);
                    if (dispatch_virtually) {
                        virtual_declaration = callee.entity;

                        cir::TypeId method_class =
                            file_.entity(file_.entity(callee.entity).parent).type;
                        std::vector<cir::EntityId> vptr_path;
                        if (vptr_field_path(method_class, &vptr_path)) {
                            cir::TypeId usize = builder_.usize_type();
                            cir::TypeId fn_pointer = builder_.pointer_type(
                                file_.entity(callee.entity).type);
                            cir::InstId vptr_place = callee.place;
                            for (cir::EntityId step : vptr_path) {
                                vptr_place = builder_.field_addr(
                                    vptr_place, step,
                                    file_.entity(step).type, loc);
                            }
                            cir::InstId vptr =
                                builder_.lvalue_to_rvalue(vptr_place, loc);
                            cir::InstId raw = builder_.cast(usize, vptr, "value", loc);
                            int64_t vslot_bytes =
                                static_cast<int64_t>(
                                    file_.target_info().pointer_width / 8) *
                                fact->vtable_slot;
                            cir::InstId slot_offset = builder_.integer_literal(
                                vslot_bytes, usize,
                                std::to_string(vslot_bytes), loc);
                            cir::InstId slot_address = builder_.binary(
                                cir::BinaryOpKind::Add, usize, raw, slot_offset,
                                loc);
                            cir::InstId slot_pointer = builder_.cast(
                                builder_.pointer_type(fn_pointer), slot_address,
                                "value", loc);
                            cir::InstId slot_place =
                                builder_.deref(slot_pointer, loc);
                            indirect_callee =
                                builder_.lvalue_to_rvalue(slot_place, loc);
                            direct = false;
                        }
                    }
                    cir::Fragment this_fragment =
                        finish_fragment_block(block, previous);
                    fragment = chain(std::move(fragment), std::move(this_fragment), loc);
                    ExprResult this_arg;
                    this_arg.value = this_value;
                    this_arg.type = file_.inst(this_value).result_type;
                    this_arg.category = ValueCategory::PrValue;
                    args.insert(args.begin(), std::move(this_arg));
                }
            }
        }
    }

    if (callee.entity.valid() && file_.valid(callee.entity) &&
        !require_placeholder_result(
            callee.entity,
            (in_unevaluated_operand() ||
             in_discarded_statement_validation())
                ? cir::InstantiationDemandKind::ResultType
                : cir::InstantiationDemandKind::OdrUse,
            loc)) {
        has_error = true;
    } else if (direct && callee.entity.valid() &&
               file_.valid(callee.entity)) {

        source_function_type = file_.entity(callee.entity).type;
    }
    if (!has_error && direct && callee.entity.valid() &&
        file_.valid(callee.entity) &&
        (!file_.entity(callee.entity).is_definition ||
         file_.entity(callee.entity).result_type_only_definition) &&
        !in_unevaluated_operand() &&
        !in_discarded_statement_validation()) {
        InstantiationDemandResult definition_demand =
            request_function_instantiation(
                callee.entity,
                cir::InstantiationDemandKind::OdrUse,
                loc);
        if (definition_demand == InstantiationDemandResult::Failed) {
            has_error = true;
        } else if (definition_demand ==
                   InstantiationDemandResult::Satisfied) {
            source_function_type = file_.entity(callee.entity).type;
        }
    }

    const cir::FunctionTypePayload* function_payload = nullptr;
    if (file_.valid(source_function_type)) {
        cir::TypeId resolved_function_type = file_.resolved_type(source_function_type);
        if (file_.valid(resolved_function_type) &&
            file_.type(resolved_function_type).kind == cir::TypeKind::Function) {
            function_payload =
                std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(resolved_function_type));
        }
    }

    size_t fixed_param_count = 0;
    bool has_prototype = false;
    bool is_variadic = false;
    bool have_function_payload = function_payload != nullptr;
    size_t hidden_args = block_call ? 1 : 0;

    std::vector<cir::TypeRef> parameter_types;
    if (function_payload) {
        fixed_param_count = function_payload->parameters.size();
        has_prototype = function_payload->has_prototype;
        is_variadic = function_payload->is_variadic;
        parameter_types = function_payload->parameters;
        function_payload = nullptr;
        size_t visible_args = args.size() - hidden_args;
        if (!missing_implicit_object && has_prototype && is_variadic &&
            visible_args < fixed_param_count) {
            report_error("too few arguments passed to variadic function", loc);
            has_error = true;
        } else if (!missing_implicit_object && has_prototype && !is_variadic &&
                   visible_args != fixed_param_count) {
            report_error("incorrect number of arguments passed to function", loc);
            has_error = true;
        }
    }

    if (have_function_payload) {
        has_error = diagnose_abstract_function_use(
                        source_function_type,
                        AbstractFunctionUse::Call,
                        loc) ||
                    has_error;
    }

    args.erase(std::remove_if(args.begin(),
                              args.end(),
                              [](const ExprResult& arg) {
                                  return !arg.value.valid() &&
                                         arg.name == "__builtin_va_arg_pack";
                              }),
               args.end());

    for (size_t index = 0; index < args.size(); ++index) {
        ExprResult& arg = args[index];
        if (index < hidden_args) {
            arg_values.push_back(arg.value);
            fragment = chain(std::move(fragment), std::move(arg.fragment), loc);
            continue;
        }
        size_t param_index = index - hidden_args;
        ExprResult value;
        if (have_function_payload && param_index < fixed_param_count &&
            arg.init_list && arg.category == ValueCategory::InitList &&
            !is_reference_type(parameter_types[param_index].type)) {
            arg = convert_call_argument_to_parameter(
                std::move(arg), parameter_types[param_index].type, loc);
        }

        cir::TypeId nontrivial_param{};
        if (lang_opts_.is_cxx_mode() && have_function_payload &&
            param_index < fixed_param_count) {
            cir::TypeId param_resolved =
                file_.resolved_type(parameter_types[param_index].type);
            if (file_.valid(param_resolved) &&
                file_.type(param_resolved).kind == cir::TypeKind::Record) {
                const cir::RecordFacts* param_record =
                    file_.record_facts_for_type(param_resolved);
                if (param_record && param_record->is_non_trivial_for_calls) {
                    nontrivial_param = param_resolved;
                }
            }
        }
        if (nontrivial_param.valid()) {
            cir::EntityId copy_ctor = record_copy_constructor(nontrivial_param);

            bool adopt_prvalue =
                arg.category == ValueCategory::PrValue &&
                file_.resolved_type(arg.type) == nontrivial_param;
            if (adopt_prvalue) {
                if (!arg.materialized_lifetimes.empty()) {
                    for (cir::LifetimeId lifetime :
                         arg.materialized_lifetimes) {
                        retire_lifetime(lifetime);
                    }
                } else {
                    remove_destructor_cleanup(
                        temporary_entity_of_value(arg.value));
                }
            }
            cir::BlockId temp_previous = builder_.current_block();
            cir::BlockId temp_block = begin_fragment_block("call.arg.temp");
            cir::EntityId temp_entity = builder_.add_entity(
                cir::EntityKind::Variable, ".arg.temp", nontrivial_param, {},
                loc, cir::StorageDuration::Temporary);
            file_.entity_mut(temp_entity).is_parameter_argument_object = true;
            cir::InstId temp_place =
                builder_.local_place(temp_entity, nontrivial_param, loc);
            if (adopt_prvalue) {

                adopt_materialized_object_storage(
                    arg, temp_place, temp_entity);
            }
            cir::Fragment temp_fragment =
                finish_fragment_block(temp_block, temp_previous);
            fragment = chain(std::move(fragment), std::move(temp_fragment), loc);
            if (copy_ctor.valid() && !adopt_prvalue) {
                cir::TypeId ref_type = reference_type(
                    cir::TypeRef{nontrivial_param, cir::QualConst,
                                 cir::MemorySpace::Default},
                    cir::ReferenceKind::LValue);
                if (const cir::RecordMethodFact* ctor_fact =
                        file_.method_fact(copy_ctor)) {
                    if (const auto* ctor_payload =
                            std::get_if<cir::FunctionTypePayload>(
                                &file_.type_payload(file_.resolved_type(
                                    ctor_fact->type.type)))) {
                        if (!ctor_payload->parameters.empty()) {
                            ref_type = file_.resolved_type(
                                ctor_payload->parameters.front().type);
                        }
                    }
                }
                ExprResult bound =
                    bind_to_reference(std::move(arg), ref_type, loc);
                has_error = has_error || bound.has_error;
                fragment = chain(std::move(fragment),
                                 std::move(bound.fragment), loc);
                cir::BlockId copy_previous = builder_.current_block();
                cir::BlockId copy_block =
                    begin_fragment_block("call.arg.copy");
                emit_construct_in_place(
                    temp_place, structor_complete_variant(copy_ctor),
                    {bound.value}, loc);
                fragment = chain(
                    std::move(fragment),
                    finish_fragment_block(copy_block, copy_previous), loc);
            } else {
                ExprResult source =
                    require_value(std::move(arg), UseContext::RValue, loc);
                has_error = has_error || source.has_error;
                fragment = chain(std::move(fragment),
                                 std::move(source.fragment), loc);
                cir::BlockId store_previous = builder_.current_block();
                cir::BlockId store_block =
                    begin_fragment_block("call.arg.store");
                cir::InstId store =
                    builder_.store(temp_place, source.value, loc);
                if (adopt_prvalue) {
                    file_.inst_mut(store).runtime_elided_object_operation = true;
                }
                fragment = chain(
                    std::move(fragment),
                    finish_fragment_block(store_block, store_previous), loc);
            }

            register_destructor_cleanup(
                temp_entity, nontrivial_param, loc,
                /*full_expression_temporary=*/true);
            cir::BlockId load_previous = builder_.current_block();
            cir::BlockId load_block = begin_fragment_block("call.arg.load");
            value.value = builder_.lvalue_to_rvalue(temp_place, loc);
            value.type = nontrivial_param;
            value.category = ValueCategory::PrValue;
            fragment = chain(std::move(fragment),
                             finish_fragment_block(load_block, load_previous),
                             loc);
            arg_values.push_back(value.value);
            continue;
        }
        if (have_function_payload && param_index < fixed_param_count &&
            is_reference_type(parameter_types[param_index].type)) {

            value = bind_to_reference(std::move(arg),
                                      parameter_types[param_index].type,
                                      loc);
        } else {
            bool preserve_class_object_for_conversion = false;
            if (have_function_payload && param_index < fixed_param_count) {
                cir::TypeId source_type = file_.resolved_type(arg.type);
                cir::TypeId parameter_type = file_.resolved_type(
                    parameter_types[param_index].type);
                preserve_class_object_for_conversion =
                    file_.valid(source_type) &&
                    file_.type(source_type).kind == cir::TypeKind::Record &&
                    file_.valid(parameter_type) &&
                    source_type != parameter_type;
            }
            if (have_function_payload && param_index < fixed_param_count &&
                (arg.category == ValueCategory::FunctionDesignator ||
                 arg.category == ValueCategory::OverloadDesignator ||
                 arg.category == ValueCategory::MemberPointerDesignator ||
                 preserve_class_object_for_conversion)) {

                value = convert_call_argument_to_parameter(
                    std::move(arg),
                    parameter_types[param_index].type,
                    loc);
            } else {
                value = require_value(std::move(arg), UseContext::RValue, loc);
            }
            if (have_function_payload && param_index < fixed_param_count &&
                value.category != ValueCategory::FunctionDesignator) {
                value = convert_call_argument_to_parameter(
                    std::move(value),
                    parameter_types[param_index].type,
                    loc);
            } else if (!have_function_payload ||
                       !has_prototype ||
                       (is_variadic && param_index >= fixed_param_count)) {
                value = apply_default_argument_promotion(std::move(value), loc);
            }
        }
        has_error = has_error || value.has_error;
        arg_values.push_back(value.value);
        fragment = chain(std::move(fragment), std::move(value.fragment), loc);
    }

    if (has_error) {
        ExprResult result;
        result.fragment = std::move(fragment);
        result.type = function_return_type(file_, source_function_type);
        if (!result.type.valid() || contains_auto_type(result.type)) {
            result.type = file_.unknown_type();
        }
        result.category = dependent ? ValueCategory::Dependent
                                    : ValueCategory::PrValue;
        result.has_error = true;
        return result;
    }

    if (direct && callee.entity.valid() && file_.valid(callee.entity) &&
        !in_unevaluated_operand() &&
        !in_discarded_statement_validation()) {
        cir::EntityKind kind = file_.entity(callee.entity).kind;
        if (kind == cir::EntityKind::Method ||
            kind == cir::EntityKind::Constructor ||
            kind == cir::EntityKind::Destructor) {

            if (!file_.entity(callee.entity).decl_flags.is_constexpr &&
                !file_.entity(callee.entity).decl_flags.is_consteval) {
                (void)request_class_member_instantiation(
                    callee.entity,
                    cir::InstantiationDemandKind::OdrUse,
                    loc);
            }
        }
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.call");
    cir::InstId inst;
    ValueCategory category = ValueCategory::PrValue;
    if (direct) {
        cir::TypeId result_type = function_return_type(file_, file_.entity(callee.entity).type);
        if (!result_type.valid()) {
            result_type = builder_.int_type();
        }
        if (lang_opts_.is_cxx_mode() &&
            file_.entity(callee.entity).kind == cir::EntityKind::Method &&
            !file_.template_specialization(callee.entity) &&
            !in_discarded_statement_validation()) {
            mark_record_method_required(callee.entity, loc);
        }
        inst = builder_.call(callee.entity, result_type, arg_values, loc);
    } else if (dependent) {
        inst = builder_.dependent_call(callee.name.empty() ? "<dependent-call>" : callee.name,
            builder_.int_type(), arg_values, loc);
        category = ValueCategory::Dependent;
    } else {
        cir::TypeId result_type =
            function_return_type(file_, file_.pointer_pointee_type(file_.inst(indirect_callee).result_type));
        if (!result_type.valid()) {
            result_type = builder_.int_type();
        }
        inst = virtual_declaration.valid()
            ? builder_.call_virtual(indirect_callee, virtual_declaration,
                                    result_type, arg_values, loc)
            : builder_.call_indirect(indirect_callee, result_type, arg_values,
                                     loc);
    }
    cir::Fragment call_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(call_fragment), loc);

    cir::EntityId nodiscard_callee{};
    if (direct && callee.entity.valid()) {
        const cir::EntityAttributeFacts& callee_facts =
            file_.entity(callee.entity).attr_facts;
        if (callee_facts.is_nodiscard || callee_facts.is_warn_unused_result) {
            nodiscard_callee = callee.entity;
        }
    }

    ExprResult result;
    result.nodiscard_callee = nodiscard_callee;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = file_.inst(inst).result_type;
    result.category = category;
    result.has_error = has_error;

    if (category == ValueCategory::PrValue && is_reference_type(result.type)) {
        cir::TypeId resolved_reference = file_.resolved_type(result.type);
        bool rvalue_reference =
            file_.valid(resolved_reference) &&
            file_.type(resolved_reference).kind == cir::TypeKind::RValueReference;
        cir::BlockId deref_previous = builder_.current_block();
        cir::BlockId deref_block = begin_fragment_block("expr.call.ref");
        cir::InstId place = builder_.deref(result.value, loc);
        cir::Fragment deref_fragment =
            finish_fragment_block(deref_block, deref_previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(deref_fragment), loc);
        result.place = place;
        result.value = {};
        result.type =
            file_.reference_referred_type(file_.resolved_type(result.type));
        result.category = rvalue_reference ? ValueCategory::XValue
                                           : ValueCategory::LValue;
    }
    if (result.category == ValueCategory::PrValue) {
        const cir::RecordFacts* result_facts =
            file_.record_facts_for_type(file_.resolved_type(result.type));
        if (result_facts && result_facts->is_abstract) {
            if (decltype_operand_depth_ > 0) {
                result.unmaterialized_abstract_call_result = true;
                result.abstract_call_loc = loc;
            } else {
                report_error(
                    "function call cannot use a return type of abstract class type '" +
                        file_.format_type(result.type) + "'",
                    loc);
                result.has_error = true;
            }
        }
    }
    if (result.category == ValueCategory::PrValue &&
        !in_unevaluated_operand() &&
        !result.unmaterialized_abstract_call_result &&
        !validate_potentially_invoked_destructor(result.type, loc)) {
        result.has_error = true;
    }

    cir::TypeId result_resolved = file_.resolved_type(result.type);
    if (result.category == ValueCategory::PrValue &&
        !in_unevaluated_operand() && !result.has_error &&
        !result.unmaterialized_abstract_call_result &&
        file_.valid(result_resolved) &&
        file_.type(result_resolved).kind == cir::TypeKind::Record &&
        result.value.valid()) {
        cir::EntityId temp = builder_.add_entity(
            cir::EntityKind::Variable,
            ".call.result.tmp." + std::to_string(compound_literal_counter_++),
            result.type,
            {},
            loc,
            cir::StorageDuration::Temporary,
            cir::MemorySpace::Default,
            {});
        file_.entity_mut(temp).is_definition = true;
        file_.inst_mut(inst).result_object_entity = temp;
        cir::BlockId materialize_previous = builder_.current_block();
        cir::BlockId materialize_block =
            begin_fragment_block("expr.call.result.materialize");
        cir::InstId place = builder_.local_place(temp, result.type, loc);
        builder_.store(place, result.value, loc);
        result.value = builder_.lvalue_to_rvalue(place, loc);
        cir::Fragment materialize_fragment =
            finish_fragment_block(materialize_block, materialize_previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(materialize_fragment), loc);
        if (cir::LifetimeId lifetime = register_destructor_cleanup(
                temp, result.type, loc,
                /*full_expression_temporary=*/true);
            lifetime.valid()) {
            result.materialized_lifetimes.push_back(lifetime);
        }
    }
    return result;
}

ExprResult Session::collect_array_subscript_expr(ExprResult base,
                                                 ExprResult index,
                                                 SrcLoc loc) {
    if (base.deferred_entity_place && base.entity.valid() &&
        !lambda_stack_.empty() &&
        lambda_stack_.back().capture_memo.contains(
            static_cast<uint64_t>(base.entity.index))) {

        base = materialize_deferred_entity_place(
            std::move(base), /*allow_non_odr_constant=*/false, loc);
    }
    if (expr_is_dependent(base) || expr_is_dependent(index)) {
        base.fragment = chain(std::move(base.fragment),
                              std::move(index.fragment), loc);
        return make_dependent_expr(std::move(base), loc);
    }

    if (objc_.initialized) {
        cir::TypeId base_resolved = file_.resolved_type(base.type);
        if (file_.valid(base_resolved) &&
            file_.type(base_resolved).kind == cir::TypeKind::Pointer) {
            cir::TypeId pointee = file_.resolved_type(
                file_.pointer_pointee_type(base_resolved));
            if (objc_interface_for_object_type(pointee).valid() ||
                (file_.valid(pointee) &&
                 pointee == file_.resolved_type(objc_id_pointee_type()))) {
                return collect_objc_subscript_reference(std::move(base),
                                                        std::move(index),
                                                        loc);
            }
        }
    }

    if (lang_opts_.is_cxx_mode() && base.type.valid()) {
        cir::TypeId base_resolved = file_.resolved_type(base.type);
        if (file_.valid(base_resolved) &&
            file_.type(base_resolved).kind == cir::TypeKind::Record) {
            bool handled = false;
            ExprResult overloaded =
                try_overloaded_subscript(base, index, &handled, loc);
            if (handled) {
                return overloaded;
            }
            report_error("no viable 'operator[]' for type '" +
                             file_.format_type(base.type) + "'",
                         loc);
            ExprResult result;
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            result.fragment = chain(std::move(base.fragment),
                                    std::move(index.fragment), loc);
            return result;
        }
    }

    auto subscriptable = [&](cir::TypeId type) {
        return is_pointer_type(type) ||
               (file_.valid(type) &&
                file_.type(file_.resolved_type(type)).kind == cir::TypeKind::Array);
    };
    bool operands_transposed = base.type.valid() && index.type.valid() &&
                               is_integer_type(base.type) &&
                               subscriptable(index.type);
    if (operands_transposed) {
        std::swap(base, index);
        if (base.deferred_entity_place && base.entity.valid() &&
            !lambda_stack_.empty() &&
            lambda_stack_.back().capture_memo.contains(
                static_cast<uint64_t>(base.entity.index))) {
            base = materialize_deferred_entity_place(
                std::move(base), /*allow_non_odr_constant=*/false, loc);
        }
    }

    ExprResult index_value = require_value(std::move(index), UseContext::RValue, loc);
    if (index_value.type.valid() && !is_integer_type(index_value.type)) {
        report_error("subscript index must have integer type", loc);
        index_value.has_error = true;
    }

    if (index_value.type.valid() && is_integer_type(index_value.type)) {
        cir::TypeId promoted = integer_promotion_type(index_value.type);
        if (promoted.valid() && !type_equal(promoted, index_value.type)) {
            index_value = convert_to_arithmetic_type(std::move(index_value), promoted, loc);
        }
    }
    bool use_array_place =
        base.category == ValueCategory::LValue &&
        base.type.valid() &&
        file_.valid(base.type) &&
        file_.type(file_.resolved_type(base.type)).kind == cir::TypeKind::Array;
    bool use_vector_place =
        base.category == ValueCategory::LValue &&
        base.type.valid() &&
        is_vector_type(base.type);

    ExprResult base_result = (use_array_place || use_vector_place)
        ? std::move(base)
        : require_value(std::move(base), UseContext::RValue, loc);

    cir::Fragment fragment =
        operands_transposed
            ? chain(std::move(index_value.fragment), std::move(base_result.fragment), loc)
            : chain(std::move(base_result.fragment), std::move(index_value.fragment), loc);
    if (base_result.deferred_entity_place) {
        ExprResult result = std::move(base_result);
        result.fragment = std::move(fragment);
        cir::TypeId resolved_base = file_.resolved_type(result.type);
        if (file_.valid(resolved_base) &&
            file_.type(resolved_base).kind == cir::TypeKind::Array) {
            result.type = file_.array_element_type(resolved_base);
        } else if (is_vector_type(resolved_base)) {
            result.type = file_.vector_element_type(resolved_base);
        } else {
            result.type = builder_.unknown_type();
            result.has_error = true;
        }
        result.category = ValueCategory::LValue;
        return result;
    }
    cir::InstId base_inst = use_array_place ? base_result.place : base_result.value;
    if (use_vector_place || is_vector_type(base_result.type)) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.vector_subscript");
        cir::InstId inst = use_vector_place
            ? builder_.vector_element_place(base_result.place, index_value.value, loc)
            : builder_.vector_extract(base_result.value, index_value.value, loc);
        cir::Fragment subscript_fragment = finish_fragment_block(block, previous);
        fragment = chain(std::move(fragment), std::move(subscript_fragment), loc);

        ExprResult result;
        result.fragment = std::move(fragment);
        result.type = use_vector_place ? object_type_from_place(inst) : file_.inst(inst).result_type;
        result.category = use_vector_place ? ValueCategory::LValue : ValueCategory::PrValue;
        if (use_vector_place) {
            result.place = inst;
        } else {
            result.value = inst;
        }
        result.has_error = base_result.has_error || index_value.has_error;
        result.potential_results = std::move(base_result.potential_results);
        return result;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.subscript");
    cir::InstId place = builder_.array_element_place(base_inst, index_value.value, loc);
    cir::Fragment subscript_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(subscript_fragment), loc);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.place = place;
    result.type = object_type_from_place(place);
    result.category = ValueCategory::LValue;
    result.potential_results = std::move(base_result.potential_results);
    result.materialized_lifetimes =
        std::move(base_result.materialized_lifetimes);
    result.has_error = base_result.has_error || index_value.has_error;
    return result;
}

Session::MemberAccessBase Session::collect_member_access_base(ExprResult base,
                                                              bool is_arrow,
                                                              SrcLoc loc) {
    diagnose_abstract_call_result_materialization(base, loc);
    if (!is_arrow && base.deferred_entity_place && base.entity.valid() &&
        !lambda_stack_.empty() &&
        lambda_stack_.back().capture_memo.contains(
            static_cast<uint64_t>(base.entity.index))) {

        base = materialize_deferred_entity_place(
            std::move(base), /*allow_non_odr_constant=*/false, loc);
    }
    MemberAccessBase access;
    if (is_arrow) {
        ExprResult pointer = require_value(std::move(base), UseContext::RValue,
                                           loc);
        cir::TypeId pointer_type_id = pointer.type;
        cir::TypeId record_type = {};
        if (file_.valid(pointer_type_id) &&
            file_.type(file_.resolved_type(pointer_type_id)).kind ==
                cir::TypeKind::Pointer) {
            record_type =
                file_.pointer_pointee_type(file_.resolved_type(pointer_type_id));
        }
        if (!record_type.valid() ||
            !file_.valid(record_type) ||
            file_.type(file_.resolved_type(record_type)).kind !=
                cir::TypeKind::Record) {
            report_error("arrow member access requires pointer to record type",
                         loc);
            pointer.has_error = true;
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.arrow_base");
        cir::InstId place = builder_.deref(pointer.value, loc);
        cir::Fragment deref_fragment = finish_fragment_block(block, previous);

        access.base_place.fragment =
            chain(std::move(pointer.fragment), std::move(deref_fragment), loc);
        access.base_place.place = place;
        access.base_place.type = object_type_from_place(place);
        access.base_place.category = ValueCategory::LValue;
        access.base_place.has_error = pointer.has_error;
        access.base_place.type_originates_from_template_parameter =
            pointer.type_originates_from_template_parameter;
    } else if (base.deferred_entity_place) {

        access.base_place = std::move(base);
    } else if (base.category == ValueCategory::PrValue && base.value.valid() &&
               base.type.valid() && file_.valid(base.type) &&
               file_.type(file_.resolved_type(base.type)).kind ==
                   cir::TypeKind::Record) {

        cir::EntityId temp = temporary_entity_of_value(base.value);
        bool existing_materialization =
            temp.valid() && !base.materialized_lifetimes.empty();
        if (!existing_materialization) {
            std::string temp_name =
                ".member.tmp." + std::to_string(compound_literal_counter_++);
            temp = builder_.add_entity(cir::EntityKind::Variable,
                                       temp_name,
                                       base.type,
                                       {},
                                       loc,
                                       cir::StorageDuration::Temporary,
                                       cir::MemorySpace::Default,
                                       {});
            file_.entity_mut(temp).is_definition = true;
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.member.temp");
        cir::InstId temp_place = builder_.local_place(temp, base.type, loc);
        if (!existing_materialization) {
            builder_.store(temp_place, base.value, loc);
        }
        cir::Fragment fragment = finish_fragment_block(block, previous);

        access.base_place.fragment =
            chain(std::move(base.fragment), std::move(fragment), loc);
        access.base_place.place = temp_place;
        access.base_place.type = base.type;
        access.base_place.category = ValueCategory::XValue;
        access.base_place.has_error = base.has_error;
        access.base_place.materialized_lifetimes =
            std::move(base.materialized_lifetimes);
        if (!existing_materialization) {
            if (cir::LifetimeId lifetime = register_destructor_cleanup(
                    temp, base.type, loc,
                    /*full_expression_temporary=*/true);
                lifetime.valid()) {
                access.base_place.materialized_lifetimes.push_back(lifetime);
            }
        }
        access.base_place.type_originates_from_template_parameter =
            base.type_originates_from_template_parameter;
    } else if ((base.category == ValueCategory::LValue ||
                base.category == ValueCategory::XValue) &&
               base.place.valid()) {
        access.base_place = std::move(base);
    } else {
        access.base_place = require_place(std::move(base), UseContext::LValue,
                                          loc);
    }

    access.record_type = access.base_place.type.valid()
        ? access.base_place.type
        : object_type_from_place(access.base_place.place);
    if (!access.record_type.valid() ||
        !file_.valid(access.record_type) ||
        file_.type(file_.resolved_type(access.record_type)).kind !=
            cir::TypeKind::Record) {
        report_error("member access requires record type", loc);
        access.base_place.has_error = true;
    }
    return access;
}

const Session::TemplateInfo* Session::member_template_info_for_access(
    const ExprResult& base,
    std::string_view member_name,
    bool is_arrow) const {
    if (expr_is_dependent(base)) {
        return nullptr;
    }
    cir::TypeId type = file_.resolved_type(base.type);
    if (!file_.valid(type)) {
        return nullptr;
    }
    if (is_arrow) {
        if (file_.type(type).kind != cir::TypeKind::Pointer) {
            return nullptr;
        }
        type = file_.resolved_type(file_.pointer_pointee_type(type));
    } else {
        if (file_.type(type).kind == cir::TypeKind::LValueReference ||
            file_.type(type).kind == cir::TypeKind::RValueReference) {
            type = file_.resolved_type(file_.reference_referred_type(type));
        }
    }
    if (!file_.valid(type) || file_.type(type).kind != cir::TypeKind::Record) {
        return nullptr;
    }
    cir::EntityId record = file_.record_entity(type);
    const cir::RecordFacts* facts = file_.record_facts(record);
    if (!facts || facts->is_incomplete) {
        (void)const_cast<Session*>(this)->require_complete_class_type(
            type,
            SrcLoc(),
            cir::InstantiationDemandKind::BaseMemberList);
    }
    cir::DeclContextId context = record.valid()
        ? file_.entity(record).semantic_context
        : cir::DeclContextId{};
    if (context.valid()) {
        if (const TemplateInfo* info =
                template_info_in_context(context, member_name,
                                         /*include_parents=*/false);
            info && template_info_is_function_template(*info)) {
            return info;
        }
    }
    return nullptr;
}

ExprResult Session::collect_bound_member_function_access_expr(
    MemberAccessBase access,
    std::vector<cir::EntityId> candidates,
    std::string_view member_name_view,
    SrcLoc loc,
    const MemberLookupResult* lookup) {
    std::string member_name(member_name_view);
    if (candidates.empty()) {
        report_error("type has no member named '" + member_name + "'", loc);
        access.base_place.has_error = true;
        return access.base_place;
    }
    if (access.base_place.deferred_entity_place) {
        bool all_static = std::all_of(
            candidates.begin(), candidates.end(), [&](cir::EntityId candidate) {
                const cir::RecordMethodFact* method =
                    file_.method_fact(candidate);
                return method && method->is_static;
            });
        if (!all_static) {
            access.base_place = materialize_deferred_entity_place(
                std::move(access.base_place),
                /*allow_non_odr_constant=*/false,
                loc);
        }
    }
    cir::EntityId representative = candidates.back();
    cir::EntityId owner = file_.valid(representative)
        ? file_.entity(representative).parent
        : cir::EntityId{};
    cir::TypeId owner_type = owner.valid() && file_.valid(owner)
        ? file_.entity(owner).type
        : cir::TypeId{};

    bool owners_differ = false;
    for (cir::EntityId candidate : candidates) {
        if (file_.valid(candidate) &&
            file_.entity(candidate).parent != owner) {
            owners_differ = true;
            break;
        }
    }
    if (!lookup && owner_type.valid() && !owners_differ &&
        file_.resolved_type(owner_type) !=
            file_.resolved_type(access.record_type)) {
        std::vector<cir::EntityId> base_path;
        if (derived_to_base_path(access.record_type, owner_type, &base_path) &&
            !base_path.empty()) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.base.adjust");
            cir::InstId adjusted =
                emit_subobject_path(access.base_place.place, base_path, loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            access.base_place.fragment =
                chain(std::move(access.base_place.fragment),
                      std::move(fragment), loc);
            access.base_place.place = adjusted;
        }
    }

    ExprResult result;
    result.fragment = std::move(access.base_place.fragment);
    result.place = access.base_place.place;
    result.entity = representative;
    result.type = file_.entity(result.entity).type;
    result.name = member_name;
    result.category = ValueCategory::FunctionDesignator;
    result.bound_member_object_category = access.base_place.category;
    result.member_access_object_type =
        access.base_place.member_access_object_type.valid()
            ? access.base_place.member_access_object_type
            : access.record_type;

    result.suppress_argument_dependent_lookup = true;
    result.has_error = access.base_place.has_error;
    if (lookup) {
        for (cir::EntityId candidate : candidates) {
            MemberCandidateObjectPaths candidate_paths;
            candidate_paths.entity = candidate;
            const MemberLookupDeclaration* declaration = nullptr;
            cir::EntityId lookup_candidate = candidate;
            if (const cir::TemplateSpecializationFact* specialization =
                    file_.template_specialization(candidate);
                specialization &&
                specialization->template_entity.valid()) {
                lookup_candidate = specialization->template_entity;
            }
            for (const MemberLookupDeclaration& item : lookup->declarations) {
                if (item.entity == candidate ||
                    item.entity == lookup_candidate) {
                    declaration = &item;
                    break;
                }
            }
            cir::EntityId candidate_owner =
                file_.valid(candidate) ? file_.entity(candidate).parent
                                       : cir::EntityId{};
            cir::TypeId candidate_owner_type =
                candidate_owner.valid() && file_.valid(candidate_owner)
                    ? file_.resolved_type(file_.entity(candidate_owner).type)
                    : cir::TypeId{};
            if (declaration && !declaration->object_paths.empty()) {
                candidate_paths.paths = declaration->object_paths;
                candidate_paths.implicit_object_class =
                    declaration->implicit_object_class;
                candidate_paths.found_through_using =
                    declaration->found_through_using;
                candidate_paths.access_owner = declaration->access_owner;
                candidate_paths.declaring_class =
                    declaration->declaring_class;
                candidate_paths.lookup_class = access.record_type;
                candidate_paths.declared_access =
                    declaration->declared_access;
                candidate_paths.has_declared_access =
                    declaration->has_declared_access;
                candidate_paths.base_paths = declaration->base_paths;
                result.member_candidate_object_paths.push_back(
                    std::move(candidate_paths));
                continue;
            }
            for (const MemberLookupSubobject& subobject :
                 lookup->subobjects) {
                std::vector<cir::EntityId> path = subobject.path;
                cir::TypeId found_in = file_.resolved_type(subobject.type);
                cir::TypeId declared_in = declaration &&
                        declaration->declaring_class.valid()
                    ? file_.resolved_type(declaration->declaring_class)
                    : candidate_owner_type;
                if (candidate_owner_type.valid() &&
                    found_in != candidate_owner_type) {
                    std::vector<cir::EntityId> suffix;
                    if (!derived_to_base_path(found_in,
                                              candidate_owner_type,
                                              &suffix)) {
                        continue;
                    }
                    path.insert(path.end(), suffix.begin(), suffix.end());
                } else if (declared_in.valid() && found_in != declared_in) {
                    std::vector<cir::EntityId> suffix;
                    if (!derived_to_base_path(found_in, declared_in,
                                              &suffix)) {
                        continue;
                    }
                    path.insert(path.end(), suffix.begin(), suffix.end());
                }
                if (std::find(candidate_paths.paths.begin(),
                              candidate_paths.paths.end(), path) ==
                    candidate_paths.paths.end()) {
                    candidate_paths.paths.push_back(std::move(path));
                }
            }
            if (declaration) {
                candidate_paths.implicit_object_class =
                    declaration->implicit_object_class;
                candidate_paths.found_through_using =
                    declaration->found_through_using;
                candidate_paths.access_owner = declaration->access_owner;
                candidate_paths.declaring_class =
                    declaration->declaring_class;
                candidate_paths.lookup_class = access.record_type;
                candidate_paths.declared_access =
                    declaration->declared_access;
                candidate_paths.has_declared_access =
                    declaration->has_declared_access;
                candidate_paths.base_paths = declaration->base_paths;
            }
            result.member_candidate_object_paths.push_back(
                std::move(candidate_paths));
        }
    }
    if (candidates.size() > 1) {
        result.candidates = std::move(candidates);
    }
    return result;
}

ExprResult Session::collect_resolved_member_function_access_expr(
    ExprResult base,
    cir::EntityId method,
    std::string_view member_name,
    bool is_arrow,
    SrcLoc loc) {
    return collect_resolved_member_function_access_expr(
        std::move(base),
        method.valid() ? std::vector<cir::EntityId>{method}
                       : std::vector<cir::EntityId>{},
        member_name,
        is_arrow,
        loc);
}

ExprResult Session::collect_resolved_member_function_access_expr(
    ExprResult base,
    std::vector<cir::EntityId> methods,
    std::string_view member_name,
    bool is_arrow,
    SrcLoc loc) {
    if (expr_is_dependent(base)) {
        return make_dependent_expr(
            prepare_dependent_member_access(std::move(base), member_name,
                                            is_arrow, file_),
            loc);
    }
    MemberAccessBase access =
        collect_member_access_base(std::move(base), is_arrow, loc);
    return collect_bound_member_function_access_expr(
        std::move(access),
        std::move(methods),
        member_name,
        loc);
}

ExprResult Session::collect_conversion_function_id_access_expr(
    ExprResult base,
    cir::TypeRef target_type,
    bool is_arrow,
    SrcLoc loc,
    cir::TypeId qualifier_type) {
    std::string display = "operator " + file_.format_type(target_type);
    if (expr_is_dependent(base) || is_dependent_type(target_type.type)) {
        return make_dependent_expr(
            prepare_dependent_member_access(std::move(base), display,
                                            is_arrow, file_),
            loc);
    }

    MemberAccessBase access =
        collect_member_access_base(std::move(base), is_arrow, loc);
    cir::TypeId lookup_type = file_.resolved_type(qualifier_type);
    if (lookup_type.valid()) {
        cir::TypeId object_type = file_.resolved_type(access.record_type);
        if (!file_.valid(lookup_type) ||
            file_.type(lookup_type).kind != cir::TypeKind::Record ||
            (lookup_type != object_type &&
             !derived_to_base_path(object_type, lookup_type, nullptr))) {
            report_error(
                "conversion-function-id qualifier does not designate the object class or a base class",
                loc);
            access.base_place.has_error = true;
        }
    } else {
        lookup_type = access.record_type;
    }
    ExprResult lookup_source;
    lookup_source.type = lookup_type;
    std::vector<cir::EntityId> candidates;
    collect_conversion_function_candidates(lookup_source,
                                           target_type.type,
                                           /*allow_explicit=*/true,
                                           loc,
                                           candidates);
    candidates.erase(
        std::remove_if(
            candidates.begin(), candidates.end(),
            [&](cir::EntityId candidate) {
                const cir::RecordMethodFact* method =
                    file_.method_fact(candidate);
                if (!method || !method->is_conversion_function) {
                    return true;
                }
                const cir::TemplateSpecializationFact* specialization =
                    file_.template_specialization(candidate);
                if (specialization &&
                    specialization->template_entity.valid()) {
                    return false;
                }
                cir::TypeId declared = file_.resolved_type(method->type.type);
                const auto* function =
                    file_.valid(declared)
                        ? std::get_if<cir::FunctionTypePayload>(
                              &file_.type_payload(declared))
                        : nullptr;
                return !function ||
                       !types_compatible(function->return_type, target_type);
            }),
        candidates.end());
    ExprResult result = collect_bound_member_function_access_expr(
        std::move(access), std::move(candidates), display, loc);
    result.qualified_name = qualifier_type.valid();
    return result;
}

ExprResult Session::collect_qualified_member_access_expr(
    ExprResult base,
    cir::TypeId qualifier_type,
    std::string_view member_name,
    bool is_arrow,
    SrcLoc loc,
    std::vector<cir::EntityId> resolved_methods) {

    if (expr_is_dependent(base) || is_dependent_type(qualifier_type)) {
        ExprResult dependent = prepare_dependent_member_access(
            std::move(base), member_name, is_arrow, file_);
        dependent.dependent_value_qualifier = type_ref(qualifier_type);
        if (dependent.template_value_expr.valid()) {
            cir::TemplateValueExprNode& root =
                dependent.template_value_expr.nodes[
                    dependent.template_value_expr.root];
            cir::TemplateCalleeFlag flags =
                static_cast<cir::TemplateCalleeFlag>(root.value);
            if ((static_cast<uint32_t>(flags) &
                 static_cast<uint32_t>(
                     cir::TemplateCalleeFlag::MemberAccess)) != 0) {
                root.qualifier_type = type_ref(qualifier_type);
                dependent.template_value_expr.canonical_id = {};
                file_.canonicalize_template_value_expression(
                    dependent.template_value_expr);
            }
        }
        dependent.qualified_name = true;
        return make_dependent_expr(std::move(dependent), loc);
    }
    cir::TypeId resolved_qualifier = file_.resolved_type(qualifier_type);
    if (!file_.valid(resolved_qualifier) ||
        file_.type(resolved_qualifier).kind != cir::TypeKind::Record) {
        report_error("member access qualifier does not name a class", loc);
        base.has_error = true;
        return base;
    }
    cir::TypeId qualifier_pointer = builder_.pointer_type(qualifier_type);
    ExprResult pointer;
    if (is_arrow) {
        pointer = require_value(std::move(base), UseContext::RValue, loc);
    } else {
        ExprResult place = require_place(std::move(base), UseContext::LValue, loc);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.qualified.addr");
        cir::InstId address = builder_.addr_of(place.place, loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        pointer.fragment = chain(std::move(place.fragment), std::move(fragment), loc);
        pointer.value = address;
        pointer.type = builder_.pointer_type(place.type.valid()
            ? place.type
            : object_type_from_place(place.place));
        pointer.category = ValueCategory::PrValue;
        pointer.has_error = place.has_error;
    }
    cir::TypeId source_pointer_type = file_.resolved_type(pointer.type);
    cir::TypeId source_object_type =
        file_.valid(source_pointer_type) &&
                file_.type(source_pointer_type).kind == cir::TypeKind::Pointer
            ? file_.resolved_type(
                  file_.pointer_pointee_type(source_pointer_type))
            : cir::TypeId{};
    if (source_object_type.valid() &&
        source_object_type != resolved_qualifier) {
        DerivedToBasePathResult designating_path =
            analyze_derived_to_base_path(source_object_type,
                                         resolved_qualifier);
        if (designating_path.kind != DerivedToBasePathKind::Unique) {
            report_error(
                "member access object cannot be converted to the "
                "designating class '" +
                    file_.format_type(resolved_qualifier) + "'",
                loc);
            pointer.has_error = true;
        }
    }
    ExprResult adjusted = convert_to(std::move(pointer), qualifier_pointer,
                                     UseContext::RValue, loc);
    adjusted.member_access_object_type = source_object_type;
    ExprResult result = resolved_methods.empty()
        ? collect_member_access_expr(std::move(adjusted),
                                     member_name,
                                     /*is_arrow=*/true,
                                     loc)
        : collect_resolved_member_function_access_expr(
              std::move(adjusted),
              std::move(resolved_methods),
              member_name,
              /*is_arrow=*/true,
              loc);
    result.qualified_name = true;
    return result;
}

ExprResult Session::collect_member_access_expr(ExprResult base,
                                               std::string_view member_name_view,
                                               bool is_arrow,
                                               SrcLoc loc) {
    cir::TypeId replay_record_type = file_.resolved_type(base.type);
    if (is_arrow && file_.valid(replay_record_type) &&
        file_.type(replay_record_type).kind == cir::TypeKind::Pointer) {
        replay_record_type = file_.resolved_type(
            file_.pointer_pointee_type(replay_record_type));
    }
    cir::EntityId validation_record = current_validation_record();
    bool names_current_instantiation =
        in_template_definition() && validation_record.valid() &&
        file_.valid(replay_record_type) &&
        file_.type(replay_record_type).kind == cir::TypeKind::Record &&
        file_.record_entity(replay_record_type) == validation_record;
    bool current_instantiation_has_dependent_bases =
        names_current_instantiation &&
        current_instantiation_type_has_dependent_bases(replay_record_type);
    if (expr_is_dependent(base) &&
        (!names_current_instantiation ||
         current_instantiation_has_dependent_bases)) {
        return make_dependent_expr(
            prepare_dependent_member_access(std::move(base), member_name_view,
                                            is_arrow, file_),
            loc);
    }

    if (current_instantiation_has_dependent_bases) {
        return make_dependent_expr(
            prepare_dependent_member_access(std::move(base),
                                            member_name_view,
                                            is_arrow,
                                            file_),
            loc);
    }

    // The [over.ref] lookup invariant repeatedly resolves zero-argument
    // operator-> until a pointer is produced, preserving normal access rules.
    if (lang_opts_.is_cxx_mode() && is_arrow) {
        constexpr size_t max_arrow_delegations = 64;
        size_t delegation_count = 0;
        while (true) {
            cir::TypeId arrow_type = file_.resolved_type(base.type);
            if (file_.valid(arrow_type) &&
                (file_.type(arrow_type).kind ==
                     cir::TypeKind::LValueReference ||
                 file_.type(arrow_type).kind ==
                     cir::TypeKind::RValueReference)) {
                arrow_type = file_.resolved_type(
                    file_.reference_referred_type(arrow_type));
            }
            if (!file_.valid(arrow_type) ||
                file_.type(arrow_type).kind != cir::TypeKind::Record) {
                break;
            }
            if (delegation_count++ == max_arrow_delegations) {
                report_error("circular pointer delegation detected", loc);
                base.has_error = true;
                return base;
            }
            ExprResult operation = collect_member_access_expr(
                std::move(base), "operator->", /*is_arrow=*/false, loc);
            if (operation.has_error) {
                return operation;
            }
            base = collect_call_expr(std::move(operation), {}, loc);
            if (base.has_error || expr_is_dependent(base)) {
                return base;
            }
        }
    }

    if (objc_.initialized) {
        cir::TypeId objc_pointee{};
        cir::TypeId base_resolved = file_.resolved_type(base.type);
        if (file_.valid(base_resolved) &&
            file_.type(base_resolved).kind == cir::TypeKind::Pointer) {
            objc_pointee =
                file_.resolved_type(file_.pointer_pointee_type(base_resolved));
        }
        cir::EntityId interface =
            objc_interface_for_object_type(objc_pointee);
        if (interface.valid()) {
            if (is_arrow) {
                return collect_objc_ivar_access(std::move(base), interface,
                                                member_name_view, loc);
            }
            return collect_objc_property_reference(std::move(base), interface,
                                                   member_name_view, loc);
        }
    }

    std::string member_name(member_name_view);
    cir::TypeId inherited_access_object_type =
        base.member_access_object_type;
    if (names_current_instantiation && is_arrow &&
        (base.category == ValueCategory::LValue ||
         base.category == ValueCategory::XValue) &&
        base.place.valid()) {

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block =
            begin_fragment_block("expr.lvalue_to_rvalue");
        cir::InstId value = builder_.lvalue_to_rvalue(base.place, loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        base.fragment =
            chain(std::move(base.fragment), std::move(fragment), loc);
        base.value = value;
        base.place = {};
        base.category = ValueCategory::PrValue;
    }
    MemberAccessBase access =
        collect_member_access_base(std::move(base), is_arrow, loc);
    if (inherited_access_object_type.valid()) {
        access.base_place.member_access_object_type =
            inherited_access_object_type;
    }
    ExprResult& base_place = access.base_place;
    cir::TypeId record_type = access.record_type;
    cir::TypeId access_object_type =
        access.base_place.member_access_object_type.valid()
            ? access.base_place.member_access_object_type
            : record_type;

    MemberLookupResult member_lookup =
        lookup_member_name(record_type, member_name);
    if (member_lookup.ambiguous) {
        report_error("member '" + member_name +
                         (lang_opts_.is_cxx_mode()
                              ? "' is ambiguous through base classes"
                              : "' is ambiguous through anonymous members"),
                     loc);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.error");
        cir::InstId value = builder_.name_ref("<invalid-member>",
                                              builder_.unknown_type(), loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        base_place.fragment = chain(std::move(base_place.fragment),
                                    std::move(error_fragment), loc);
        base_place.place = {};
        base_place.value = value;
        base_place.type = builder_.unknown_type();
        base_place.category = ValueCategory::PrValue;
        base_place.has_error = true;
        return base_place;
    }

    const cir::RecordStaticDataMemberFact* static_member = nullptr;
    const MemberLookupDeclaration* static_declaration = nullptr;
    for (const MemberLookupDeclaration& declaration :
         member_lookup.declarations) {
        if (const cir::RecordStaticDataMemberFact* candidate =
                static_data_member_fact(declaration.entity)) {
            static_member = candidate;
            static_declaration = &declaration;
            break;
        }
    }
    if (static_member) {
        if (static_declaration) {
            (void)check_member_lookup_access(*static_declaration, loc,
                                             access_object_type);
            (void)check_member_lookup_base_access(
                *static_declaration, record_type, loc);
        } else {
            check_member_access(static_member->entity,
                                static_member->declared_access,
                                loc);
        }
        ExprResult result = make_entity_reference(static_member->entity,
                                                  member_name,
                                                  loc);
        result.fragment = chain(std::move(base_place.fragment),
                                std::move(result.fragment),
                                loc);
        result.has_error = result.has_error || base_place.has_error;
        return result;
    }

    FieldPathLookupResult field_path;
    const MemberLookupDeclaration* field_declaration = nullptr;
    std::vector<cir::EntityId> callable_declarations;
    for (const MemberLookupDeclaration& declaration :
         member_lookup.declarations) {
        if (!declaration.entity.valid() ||
            !file_.valid(declaration.entity)) {
            continue;
        }
        cir::EntityKind kind = file_.entity(declaration.entity).kind;
        if (kind == cir::EntityKind::Field) {
            if (field_declaration &&
                field_declaration->entity != declaration.entity) {
                field_path.ambiguous = true;
            } else {
                field_declaration = &declaration;
            }
        } else if (kind == cir::EntityKind::Method ||
                   kind == cir::EntityKind::Destructor ||
                   (template_info(declaration.entity) &&
                    template_info_is_function_template(
                        *template_info(declaration.entity)))) {
            callable_declarations.push_back(declaration.entity);
        }
    }
    if (field_declaration) {
        field_path.found = true;
        field_path.type = file_.entity(field_declaration->entity).type;
        if (field_declaration->object_paths.size() != 1) {
            field_path.ambiguous = true;
        } else {
            field_path.entities = field_declaration->object_paths.front();
            field_path.entities.insert(
                field_path.entities.end(),
                field_declaration->member_path.begin(),
                field_declaration->member_path.end());
        }
    }
    if (!field_path.found && !callable_declarations.empty()) {

        return collect_bound_member_function_access_expr(
            std::move(access), std::move(callable_declarations), member_name,
            loc, &member_lookup);
    }
    if (!field_path.found) {
        if (!member_lookup.found_name &&
            member_lookup.has_dependent_bases &&
            current_instantiation_type_has_dependent_bases(record_type)) {
            base_place.name = member_name;
            base_place.category = ValueCategory::Dependent;
            base_place.type = file_.dependent_type("dependent member access");
            return make_dependent_expr(std::move(base_place), loc);
        }
        if (!member_lookup.found_name &&
            current_instantiation_type_has_dependent_bases(record_type)) {

            base_place.name = member_name;
            base_place.category = ValueCategory::Dependent;
            base_place.type = file_.dependent_type("dependent member access");
            return make_dependent_expr(std::move(base_place), loc);
        }
        if (!callable_declarations.empty()) {
            return collect_bound_member_function_access_expr(
                std::move(access), std::move(callable_declarations),
                member_name, loc, &member_lookup);
        }
    }
    if (!field_path.found || field_path.ambiguous) {
        if (field_path.ambiguous) {
            report_error("member '" + member_name +
                             "' is ambiguous through base classes",
                         loc);
        } else {
            report_error("type has no member named '" + member_name + "'", loc);
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.error");
        cir::InstId value =
            builder_.name_ref("<invalid-member>", builder_.unknown_type(), loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        base_place.fragment = chain(std::move(base_place.fragment), std::move(error_fragment), loc);
        base_place.place = {};
        base_place.value = value;
        base_place.type = builder_.unknown_type();
        base_place.category = ValueCategory::PrValue;
        base_place.has_error = true;
        return base_place;
    }

    if (field_declaration &&
        field_declaration->declared_access !=
            cir::RecordMemberAccess::Protected) {
        (void)check_member_lookup_access(*field_declaration, loc,
                                         access_object_type);
    }

    if (base_place.deferred_entity_place) {
        ExprResult result = std::move(base_place);
        result.type = field_path.type;
        result.name = member_name;
        result.category = ValueCategory::LValue;

        return result;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.field");
    cir::InstId place = base_place.place;
    cir::EntityId final_entity{};
    // The [class.access.base] lookup invariant applies path accessibility to
    // the leading base subobjects, including the any-route virtual-base join.
    std::vector<cir::EntityId> base_prefix;
    for (cir::EntityId field_entity : field_path.entities) {
        const cir::RecordFieldFact* field = file_.field_fact(field_entity);
        if (!field || !field->is_base_subobject) {
            break;
        }
        base_prefix.push_back(field_entity);
    }
    if (!base_prefix.empty()) {
        const cir::RecordFieldFact* naming = file_.field_fact(base_prefix.back());
        if (!check_base_path_access(base_prefix, record_type,
                                    file_.resolved_type(naming->type.type),
                                    loc)) {
            base_place.has_error = true;
        }
    }
    bool named_member_step = true;
    for (cir::EntityId field_entity : field_path.entities) {
        const cir::RecordFieldFact* field = file_.field_fact(field_entity);
        if (!field) {
            report_error("field path references a field without record facts", loc);
            continue;
        }
        if (!field->is_base_subobject) {
            // The [class.protected] lookup invariant restricts the named member
            // to objects of the granting derived class or its descendants.
            bool selected_named_member = field_declaration &&
                field_entity == field_declaration->entity;
            cir::RecordMemberAccess effective_access =
                selected_named_member
                    ? field_declaration->declared_access
                    : field->declared_access;
            cir::EntityId member_owner =
                selected_named_member
                    ? field_declaration->access_owner
                    : (field_entity.valid() && file_.valid(field_entity)
                           ? file_.entity(field_entity).parent
                           : cir::EntityId{});
            if (named_member_step &&
                effective_access == cir::RecordMemberAccess::Protected) {
                if (!protected_member_object_access_allowed(member_owner,
                                                            access_object_type)) {
                    if (member_owner.valid() &&
                        member_access_allowed(member_owner,
                                              effective_access)) {

                        report_error(
                            "protected member of '" +
                                file_.format_type(
                                    file_.entity(member_owner).type) +
                                "' is only accessible through an object of "
                                "the granting class or one derived from it",
                            loc);
                    } else {
                        if (selected_named_member) {
                            (void)check_member_lookup_access(
                                *field_declaration, loc,
                                access_object_type);
                        } else {
                            check_member_access(field->entity,
                                                field->declared_access,
                                                loc);
                        }
                    }
                }
            } else if (!selected_named_member) {
                check_member_access(field->entity,
                                    field->declared_access,
                                    loc);
            }
            named_member_step = false;
        }
        if (field->is_virtual_base_storage) {
            place = emit_virtual_base_adjust(place, field->entity, loc);
        } else {
            place = builder_.field_addr(place, field->entity, field->type.type,
                                        loc);
        }
        final_entity = field->entity;
    }
    cir::Fragment field_fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(base_place.fragment), std::move(field_fragment), loc);
    result.place = place;
    result.type = field_path.type;
    result.entity = final_entity;
    result.potential_results = std::move(base_place.potential_results);
    result.name = member_name;
    result.category = base_place.category == ValueCategory::XValue
        ? ValueCategory::XValue
        : ValueCategory::LValue;
    result.materialized_lifetimes =
        std::move(base_place.materialized_lifetimes);
    if (const cir::RecordFieldFact* field = file_.field_fact(final_entity)) {
        result.designates_bitfield = field->is_bitfield;
    }
    result.type_originates_from_template_parameter =
        base_place.type_originates_from_template_parameter;
    result.has_error = base_place.has_error;

    if (is_reference_type(result.type)) {
        result = deref_reference_lvalue(std::move(result), loc);
    }
    return result;
}

ExprResult Session::collect_explicit_destructor_call(
    ExprResult base,
    cir::TypeId named_type,
    cir::TypeId qualifier_type,
    bool is_arrow,
    bool is_qualified,
    SrcLoc loc) {
    ExprResult result;
    result.type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    result.category = ValueCategory::PrValue;

    if (expr_is_dependent(base) || is_dependent_type(named_type) ||
        (qualifier_type.valid() && is_dependent_type(qualifier_type))) {
        result = make_dependent_expr(std::move(base), loc);
        result.type = file_.dependent_type("explicit destructor call");
        return result;
    }

    cir::TypeId named = file_.resolved_type(named_type);
    if (!file_.valid(named)) {
        report_error("explicit destructor type name does not name a type", loc);
        base.has_error = true;
        base.type = result.type;
        base.category = ValueCategory::PrValue;
        return base;
    }

    if (file_.type(named).kind != cir::TypeKind::Record) {

        ExprResult evaluated;
        cir::TypeId object_type{};
        if (is_arrow) {
            evaluated = require_value(std::move(base), UseContext::RValue, loc);
            cir::TypeId pointer = file_.resolved_type(evaluated.type);
            if (file_.valid(pointer) &&
                file_.type(pointer).kind == cir::TypeKind::Pointer) {
                object_type = file_.pointer_pointee_type(pointer);
            }
        } else {

            evaluated = std::move(base);
            object_type = evaluated.type.valid()
                ? evaluated.type
                : object_type_from_place(evaluated.place);
        }
        if (!same_unqualified_type(file_, object_type, named)) {
            report_error(
                "pseudo-destructor type does not match the object type", loc);
            evaluated.has_error = true;
        }
        result.fragment = std::move(evaluated.fragment);
        result.has_error = evaluated.has_error;
        return result;
    }

    cir::TypeId qualifier = qualifier_type.valid()
        ? file_.resolved_type(qualifier_type)
        : named;
    if (is_qualified && qualifier != named) {
        report_error(
            "qualified destructor name does not denote the qualifier class",
            loc);
        base.has_error = true;
    }

    const cir::RecordFacts* named_facts = file_.record_facts_for_type(named);
    const cir::RecordMethodFact* selected = nullptr;
    if (named_facts) {
        for (const cir::RecordMethodFact& method : named_facts->methods) {
            if (method.special_member_kind !=
                    cir::SpecialMemberKind::Destructor ||
                !method.is_selected_destructor) {
                continue;
            }
            if (selected) {
                report_error("destructor selection is ambiguous", loc);
                base.has_error = true;
                break;
            }
            selected = &method;
        }
    }
    if (!selected || !selected->entity.valid()) {
        report_error("no selected destructor for explicit call", loc);
        base.has_error = true;
        base.type = result.type;
        base.category = ValueCategory::PrValue;
        return base;
    }
    if (selected->is_deleted) {
        report_error("call to deleted destructor", loc);
        base.has_error = true;
    }
    check_member_access(selected->entity, selected->declared_access, loc);

    MemberAccessBase access =
        collect_member_access_base(std::move(base), is_arrow, loc);
    cir::TypeId object_record = file_.resolved_type(access.record_type);
    if (object_record != named &&
        !derived_to_base_path(object_record, named, nullptr)) {
        report_error(
            "explicit destructor object is not of the named class or a derived class",
            loc);
        access.base_place.has_error = true;
    }
    ExprResult bound = collect_bound_member_function_access_expr(
        std::move(access), {selected->entity}, "~destructor", loc);
    result.fragment = std::move(bound.fragment);
    result.has_error = bound.has_error;
    if (!bound.place.valid() || result.has_error) {
        return result;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.destructor.call");
    bool dispatched = false;
    if (!is_qualified && selected->is_virtual &&
        selected->vtable_slot >= 0) {
        std::vector<cir::EntityId> vptr_path;
        if (vptr_field_path(named, &vptr_path)) {
            cir::EntityId complete =
                structor_complete_variant(selected->entity);
            cir::TypeId function_type = file_.entity(complete).type;
            cir::TypeId function_pointer = builder_.pointer_type(function_type);
            cir::TypeId usize = builder_.usize_type();
            cir::InstId vptr_place = bound.place;
            for (cir::EntityId step : vptr_path) {
                vptr_place = builder_.field_addr(
                    vptr_place, step, file_.entity(step).type, loc);
            }
            cir::InstId vptr = builder_.lvalue_to_rvalue(vptr_place, loc);
            cir::InstId raw = builder_.cast(usize, vptr, "value", loc);
            int64_t vslot_bytes =
                static_cast<int64_t>(file_.target_info().pointer_width / 8) *
                selected->vtable_slot;
            cir::InstId slot_offset = builder_.integer_literal(
                vslot_bytes, usize, std::to_string(vslot_bytes), loc);
            cir::InstId slot_address = builder_.binary(
                cir::BinaryOpKind::Add, usize, raw, slot_offset, loc);
            cir::InstId slot_pointer = builder_.cast(
                builder_.pointer_type(function_pointer), slot_address,
                "value", loc);
            cir::InstId target = builder_.lvalue_to_rvalue(
                builder_.deref(slot_pointer, loc), loc);
            cir::InstId object = builder_.addr_of(bound.place, loc);
            builder_.call_indirect(
                target, file_.builtin_type(cir::BuiltinTypeKind::Void),
                {object}, loc);
            mark_record_method_required(selected->entity, loc);
            dispatched = true;
        }
    }
    if (!dispatched) {
        emit_destroy(bound.place,
                     structor_complete_variant(selected->entity), loc);
    }
    cir::Fragment call_fragment = finish_fragment_block(block, previous);
    result.fragment = chain(std::move(result.fragment),
                            std::move(call_fragment), loc);
    return result;
}

ExprResult Session::materialize_qualified_data_member(ExprResult expr,
                                                      SrcLoc loc) {
    if (expr.category != ValueCategory::QualifiedMember ||
        !expr.entity.valid() || !file_.valid(expr.entity) ||
        file_.entity(expr.entity).kind != cir::EntityKind::Field) {
        return expr;
    }

    cir::TypeId owner_type = file_.resolved_type(expr.qualified_member_owner);
    if (!owner_type.valid()) {
        cir::EntityId owner = file_.entity(expr.entity).parent;
        owner_type = owner.valid() && file_.valid(owner)
            ? file_.resolved_type(file_.entity(owner).type)
            : cir::TypeId{};
    }

    ExprResult this_value = collect_this_expr(loc);
    if (this_value.has_error || !owner_type.valid()) {
        expr.fragment = chain(std::move(expr.fragment),
                              std::move(this_value.fragment), loc);
        expr.has_error = true;
        expr.type = builder_.unknown_type();
        expr.category = ValueCategory::PrValue;
        return expr;
    }
    MemberAccessBase access = collect_member_access_base(
        std::move(this_value), /*is_arrow=*/true, loc);

    std::vector<cir::EntityId> path;
    cir::TypeId object_type = file_.resolved_type(access.record_type);
    if (object_type != owner_type) {
        DerivedToBasePathResult owner_path =
            analyze_derived_to_base_path(object_type, owner_type);
        if (owner_path.kind != DerivedToBasePathKind::Unique) {
            report_error(owner_path.kind == DerivedToBasePathKind::Ambiguous
                             ? "qualified member object has an ambiguous base"
                             : "qualified member does not belong to the current object",
                         loc);
            access.base_place.has_error = true;
        } else {
            if (!check_base_path_access(owner_path.path, object_type,
                                        owner_type, loc)) {
                access.base_place.has_error = true;
            }
            path = std::move(owner_path.path);
        }
    }

    MemberLookupResult lookup = lookup_member_name(owner_type, expr.name);
    const MemberLookupDeclaration* declaration = nullptr;
    for (const MemberLookupDeclaration& candidate : lookup.declarations) {
        if (candidate.entity == expr.entity) {
            declaration = &candidate;
            break;
        }
    }
    if (!declaration || declaration->object_paths.size() != 1) {
        report_error("qualified member '" + expr.name +
                         "' has an ambiguous object subobject",
                     loc);
        access.base_place.has_error = true;
    } else {
        path.insert(path.end(), declaration->object_paths.front().begin(),
                    declaration->object_paths.front().end());
        path.insert(path.end(), declaration->member_path.begin(),
                    declaration->member_path.end());
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.qualified.member");
    cir::InstId place = access.base_place.place;
    if (!access.base_place.has_error && !path.empty() && place.valid()) {
        place = emit_subobject_path(place, path, loc);
    }
    cir::Fragment member_fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(expr.fragment),
                            std::move(access.base_place.fragment), loc);
    result.fragment = chain(std::move(result.fragment),
                            std::move(member_fragment), loc);
    result.place = access.base_place.has_error ? cir::InstId{} : place;
    result.type = access.base_place.has_error
        ? builder_.unknown_type()
        : file_.entity(expr.entity).type;
    result.entity = expr.entity;
    result.name = std::move(expr.name);
    result.qualified_name = true;
    result.category = access.base_place.has_error
        ? ValueCategory::PrValue
        : ValueCategory::LValue;
    result.has_error = expr.has_error || access.base_place.has_error;
    if (!access.base_place.has_error) {
        if (const cir::RecordFieldFact* field = file_.field_fact(result.entity)) {
            result.designates_bitfield = field->is_bitfield;
        }
    }
    if (!access.base_place.has_error && is_reference_type(result.type)) {
        result = deref_reference_lvalue(std::move(result), loc);
    }
    return result;
}

cir::EntityId Session::current_function_entity() const {
    cir::DeclContextId context = current_decl_context();
    while (context.valid() && file_.valid(context)) {
        const cir::DeclContext& declaration_context =
            file_.decl_context(context);
        if (declaration_context.kind == cir::DeclContextKind::Function &&
            declaration_context.owner.valid()) {
            return declaration_context.owner;
        }
        context = declaration_context.parent;
    }
    if (!current_function_.valid() || !file_.valid(current_function_)) {
        return {};
    }
    return file_.function(current_function_).entity;
}

bool Session::is_cross_function_local(cir::EntityId entity_id) const {
    if (!entity_id.valid() || !file_.valid(entity_id)) {
        return false;
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if (entity.storage_duration != cir::StorageDuration::Automatic &&
        entity.storage_duration != cir::StorageDuration::Parameter) {
        return false;
    }
    cir::EntityId current = current_function_entity();
    return current.valid() && entity.owning_function.valid() &&
           entity.owning_function != current;
}

bool Session::is_default_argument_local(cir::EntityId entity_id) const {
    if (!in_default_argument_replay() || !entity_id.valid() ||
        !file_.valid(entity_id)) {
        return false;
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if (entity.storage_duration != cir::StorageDuration::Automatic &&
        entity.storage_duration != cir::StorageDuration::Parameter) {
        return false;
    }

    return !entity.owning_function.valid() ||
        (default_argument_boundary_function_.valid() &&
         entity.owning_function == default_argument_boundary_function_);
}

ExprResult Session::materialize_deferred_entity_place(
    ExprResult expr,
    bool allow_non_odr_constant,
    SrcLoc loc) {
    if (!expr.deferred_entity_place || !expr.entity.valid() ||
        !file_.valid(expr.entity)) {
        return expr;
    }

    cir::EntityId source_id{};
    auto is_deferred_source = [&](cir::EntityId candidate) {
        if (!candidate.valid() || !file_.valid(candidate)) {
            return false;
        }
        const cir::Entity& entity = file_.entity(candidate);
        bool local = entity.storage_duration ==
                         cir::StorageDuration::Automatic ||
                     entity.storage_duration ==
                         cir::StorageDuration::Parameter;
        return local &&
            (is_cross_function_local(candidate) ||
             is_default_argument_local(candidate));
    };
    for (cir::EntityId candidate : expr.potential_results) {
        if (is_deferred_source(candidate)) {
            source_id = candidate;
            break;
        }
    }
    if (!source_id.valid()) {
        source_id = expr.entity;
    }
    if (!source_id.valid() || !file_.valid(source_id)) {
        return expr;
    }
    const cir::Entity& source = file_.entity(source_id);
    cir::TypeId source_decl_type = source.type.valid() ? source.type : expr.type;
    cir::TypeId expression_type = expr.type.valid() ? expr.type
                                                    : source_decl_type;

    cir::TypeId resolved = file_.resolved_type(source_decl_type);
    bool scalar_constant =
        allow_non_odr_constant && source.has_constant_value &&
        (source.qualifiers & cir::QualConst) != 0 &&
        (source.qualifiers & cir::QualVolatile) == 0 &&
        file_.valid(resolved) &&
        file_.type(resolved).kind != cir::TypeKind::Record &&
        cir::is_integer_like_type(file_, resolved);
    if (scalar_constant) {
        ExprResult constant = is_bool_type(resolved)
            ? make_boolean_literal(!source.constant_integer_value.is_zero(),
                                   !source.constant_integer_value.is_zero()
                                       ? "true"
                                       : "false",
                                   loc)
            : make_integer_literal(source.constant_integer_value,
                                   source.constant_integer_value.decimal(),
                                   source_decl_type,
                                   loc);
        constant.fragment = chain(std::move(expr.fragment),
                                  std::move(constant.fragment), loc);
        constant.entity = source_id;
        constant.name = expr.name;
        constant.potential_results = std::move(expr.potential_results);
        constant.has_error = expr.has_error;
        return constant;
    }

    auto make_placeholder_place = [&](bool error) {
        std::string temp_name = error ? ".odr.error." : ".odr.unevaluated.";
        temp_name += std::to_string(compound_literal_counter_++);
        cir::EntityId temp = builder_.add_entity(
            cir::EntityKind::Variable,
            temp_name,
            expression_type,
            {},
            loc,
            cir::StorageDuration::Temporary,
            cir::MemorySpace::Default,
            {});
        cir::Entity& temp_entity = file_.entity_mut(temp);
        temp_entity.is_definition = true;
        temp_entity.owning_function = current_function_entity();
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block(
            error ? "expr.odr.error" : "expr.odr.unevaluated");
        cir::InstId place = builder_.local_place(temp, expression_type, loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        expr.fragment = chain(std::move(expr.fragment), std::move(fragment), loc);
        expr.place = place;
        expr.type = expression_type;
        expr.category = ValueCategory::LValue;
        expr.deferred_entity_place = false;
    };

    if (in_unevaluated_operand()) {
        make_placeholder_place(/*error=*/false);
        return expr;
    }

    if (!is_default_argument_local(source_id) &&
        lambda_capture_source_usable(source_id)) {
        std::string capture_name = expr.name;
        expr = lambda_capture_access(std::move(expr), capture_name, loc);
        expr.deferred_entity_place = false;
        if (!expr.has_error && expr.category == ValueCategory::LValue &&
            is_reference_type(expr.type)) {
            expr = deref_reference_lvalue(std::move(expr), loc);
        }
        return expr;
    }

    std::string name = source.name.valid()
        ? std::string(file_.name(source.name))
        : (expr.name.empty() ? std::string("<local>") : expr.name);
    report_error("local entity '" + name +
                     "' is not odr-usable in this context",
                 loc);
    expr.has_error = true;
    make_placeholder_place(/*error=*/true);
    return expr;
}

ExprResult Session::require_value(ExprResult expr, UseContext context, SrcLoc loc) {
    if (expr.objc_property) {
        expr = resolve_objc_property_load(std::move(expr), loc);
    }
    expr = materialize_qualified_data_member(std::move(expr), loc);
    expr = materialize_deferred_entity_place(
        std::move(expr), /*allow_non_odr_constant=*/true, loc);
    if (context == UseContext::Discard) {
        diagnose_abstract_call_result_materialization(expr, loc);
    }
    if (expr.unresolved_unqualified_name && !expr.has_error) {
        report_error("use of undeclared identifier '" + expr.name + "'", loc);
        note_module_hidden_name(expr.name, loc);
        expr.has_error = true;
    }
    if (expr_is_dependent(expr)) {

        bump_pattern_taint();
        return expr;
    }

    if (context == UseContext::Condition && lang_opts_.is_cxx_mode()) {
        cir::TypeId condition_type = file_.resolved_type(expr.type);
        if (file_.valid(condition_type) &&
            file_.type(condition_type).kind == cir::TypeKind::Record) {
            return convert_to_condition(std::move(expr), loc);
        }
    }

    if (expr.category == ValueCategory::InitList) {
        report_error("initializer list cannot be used as a scalar expression", loc);
        expr.has_error = true;
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.error");
        cir::InstId value = builder_.error("initializer list used as scalar expression", loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        expr.fragment = chain(std::move(expr.fragment), std::move(error_fragment), loc);
        expr.value = value;
        expr.type = builder_.unknown_type();
        expr.category = ValueCategory::PrValue;
        return expr;
    }
    if (expr.category == ValueCategory::PrValue || expr.category == ValueCategory::Dependent) {
        if (!expr.value.valid()) {
            if (expr.category == ValueCategory::PrValue && is_void_type(expr.type)) {
                if (context == UseContext::Discard) {
                    return expr;
                }
                report_error("void expression cannot be used as a value", loc);
                expr.has_error = true;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.name");
            expr.value = expr.has_error
                ? builder_.error("void expression used as value", loc)
                : builder_.name_ref(expr.name.empty() ? "<dependent>" : expr.name,
                    expr.type.valid() ? expr.type : builder_.unknown_type(), loc);
            cir::Fragment name_fragment = finish_fragment_block(block, previous);
            expr.fragment = chain(std::move(expr.fragment), std::move(name_fragment), loc);
            if (expr.has_error) {
                expr.type = builder_.unknown_type();
            }
        }
        expr.category = expr.category == ValueCategory::Dependent
            ? ValueCategory::Dependent
            : ValueCategory::PrValue;
        if (context == UseContext::Condition) {
            expr = convert_to_condition(std::move(expr), loc);
        }
        return expr;
    }
    if ((expr.category == ValueCategory::LValue ||
         expr.category == ValueCategory::XValue) &&
        expr.place.valid()) {
        cir::TypeId place_type = file_.inst(expr.place).result_type;
        cir::TypeRef object_ref = file_.place_object_ref(place_type);
        cir::TypeId object_type = file_.resolved_type(object_ref.type);
        if (is_nullptr_type(object_type)) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.nullptr.lvalue");
            cir::InstId value = builder_.nullptr_literal("nullptr", loc);
            cir::Fragment conversion_fragment = finish_fragment_block(block, previous);
            expr.fragment = chain(std::move(expr.fragment), std::move(conversion_fragment), loc);
            expr.value = value;
            expr.type = file_.inst(value).result_type;
            expr.category = ValueCategory::PrValue;
            if (context == UseContext::Condition) {
                expr = convert_to_condition(std::move(expr), loc);
            }
            return expr;
        }
        if (file_.valid(object_type) && file_.type(object_type).kind == cir::TypeKind::Array) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.array_to_pointer");
            cir::InstId zero = builder_.integer_literal(0, "0", loc);
            cir::InstId element_place = builder_.array_element_place(expr.place, zero, loc);
            cir::InstId value = builder_.addr_of(element_place, loc);
            cir::Fragment conversion_fragment = finish_fragment_block(block, previous);
            expr.fragment = chain(std::move(expr.fragment), std::move(conversion_fragment), loc);
            expr.value = value;
            expr.type = file_.inst(value).result_type;
            expr.category = ValueCategory::PrValue;
            if (context == UseContext::Condition) {
                expr = convert_to_condition(std::move(expr), loc);
            }
            return expr;
        }
        if (file_.valid(object_type) &&
            file_.type(object_type).kind == cir::TypeKind::Function) {

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.function_to_pointer");
            cir::InstId value = builder_.addr_of(expr.place, loc);
            cir::Fragment conversion_fragment = finish_fragment_block(block, previous);
            expr.fragment = chain(std::move(expr.fragment), std::move(conversion_fragment), loc);
            expr.value = value;
            expr.type = file_.inst(value).result_type;
            expr.category = ValueCategory::PrValue;
            if (context == UseContext::Condition) {
                expr = convert_to_condition(std::move(expr), loc);
            }
            return expr;
        }

        if (expr.entity.valid() && file_.valid(expr.entity)) {
            const cir::Entity& entity = file_.entity(expr.entity);
            if (entity.kind == cir::EntityKind::Variable &&
                entity.has_constant_value &&
                (entity.qualifiers & cir::QualConst) &&
                (entity.qualifiers & cir::QualVolatile) == 0 &&
                cir::is_integer_like_type(file_, object_type)) {
                ExprResult constant = is_bool_type(object_type)
                    ? make_boolean_literal(
                          !entity.constant_integer_value.is_zero(),
                          !entity.constant_integer_value.is_zero()
                              ? "true"
                              : "false",
                          loc)
                    : make_integer_literal(entity.constant_integer_value,
                                           entity.constant_integer_value.decimal(),
                                           object_type,
                                           loc);
                constant.fragment = chain(std::move(expr.fragment),
                                          std::move(constant.fragment), loc);
                constant.has_error = expr.has_error;
                constant.name = expr.name;
                constant.entity = expr.entity;
                return constant;
            }
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.lvalue_to_rvalue");

        cir::TypeRef loaded_object_ref =
            file_.place_object_ref(file_.inst(expr.place).result_type);

        bool arc_weak_read = arc_enabled() &&
            arc_retainable_type(loaded_object_ref.type) &&
            arc_ownership_of_ref(loaded_object_ref) ==
                cir::ObjCOwnership::Weak;
        cir::InstId value;
        if (arc_weak_read) {
            cir::InstId slot = builder_.addr_of(expr.place, loc);
            value = builder_.objc_arc_op(
                cir::ObjCArcOpKind::LoadWeak, {slot},
                file_.resolved_type(loaded_object_ref.type), loc);
        } else if (loaded_object_ref.qualifiers & cir::QualAtomic) {
            value = builder_.atomic_load(expr.place, cir::MemoryOrder::SeqCst,
                                         loc);
        } else {
            value = builder_.lvalue_to_rvalue(expr.place, loc);
        }
        if (arc_weak_read) {
            expr.arc_plus_one = true;
        }

        if (const cir::RecordFieldFact* field = file_.field_fact(expr.entity);
            field && field->is_bitfield) {
            cir::TypeId loaded_type = file_.inst(value).result_type;
            cir::TypeId promoted =
                bitfield_promoted_type(loaded_type, field->bit_width);
            if (file_.valid(promoted) && !type_equal(promoted, loaded_type)) {
                value = builder_.cast(promoted, value, "arith", loc);
            }
        }
        cir::Fragment conversion_fragment = finish_fragment_block(block, previous);
        expr.fragment = chain(std::move(expr.fragment), std::move(conversion_fragment), loc);
        expr.value = value;
        expr.type = file_.inst(value).result_type;
        expr.category = ValueCategory::PrValue;
        if (arc_weak_read) {
            arc_schedule_pending_release(expr);
        }
        if (context == UseContext::Condition) {
            expr = convert_to_condition(std::move(expr), loc);
        }
        return expr;
    }
    if (expr.category == ValueCategory::OverloadDesignator) {
        std::shared_ptr<const OverloadDesignator> designator =
            canonical_overload_designator(expr);
        std::vector<cir::EntityId> resolved_functions;
        if (designator) {
            for (const OverloadDesignatorCandidate& candidate :
                 designator->candidates) {
                if (candidate.address_category !=
                        OverloadAddressCategory::FunctionPointer ||
                    !candidate.entity.valid() ||
                    !file_.valid(candidate.entity) ||
                    template_info(candidate.entity) != nullptr) {
                    continue;
                }
                const cir::RecordMethodFact* method =
                    file_.method_fact(candidate.entity);
                if (method &&
                    (method->constraint_satisfaction ==
                         cir::ConstraintSatisfactionKind::Unsatisfied ||
                     method->constraint_satisfaction ==
                         cir::ConstraintSatisfactionKind::Invalid)) {
                    continue;
                }
                resolved_functions.push_back(candidate.entity);
            }
        }
        if (resolved_functions.size() == 1) {
            expr.entity = resolved_functions.front();
            expr.candidates.clear();
            expr.overload_designator.reset();
            expr.type = file_.entity(expr.entity).type;
            expr.category = ValueCategory::FunctionDesignator;
            return require_value(std::move(expr), context, loc);
        }
        report_error("cannot resolve targetless overloaded function address",
                     loc);
        expr.has_error = true;
        expr.type = builder_.unknown_type();
        expr.category = ValueCategory::PrValue;
        return expr;
    }
    if (expr.category == ValueCategory::FunctionDesignator) {
        if (!expr.entity.valid() && expr.candidates.size() == 1) {
            cir::EntityId candidate = expr.candidates.front();
            if (candidate.valid() && file_.valid(candidate)) {
                const cir::Entity& entity = file_.entity(candidate);
                const cir::RecordMethodFact* method =
                    entity.kind == cir::EntityKind::Method
                        ? file_.method_fact(candidate)
                        : nullptr;
                if (entity.kind == cir::EntityKind::Function ||
                    (method && method->is_static)) {
                    expr.entity = candidate;
                }
            }
        }
        if (!expr.entity.valid()) {
            report_error("cannot resolve overloaded function address", loc);
            expr.has_error = true;
            expr.type = builder_.unknown_type();
            expr.category = ValueCategory::PrValue;
            return expr;
        }
        if (!expr.has_error && callable_is_deleted(expr.entity)) {
            report_error("cannot take the address of a deleted function", loc);
            expr.has_error = true;
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.function_to_pointer");
        cir::InstId value = builder_.function_to_pointer(expr.entity, loc);
        cir::Fragment conversion_fragment = finish_fragment_block(block, previous);
        expr.fragment = chain(std::move(expr.fragment), std::move(conversion_fragment), loc);
        expr.value = value;
        expr.type = file_.inst(value).result_type;
        expr.category = ValueCategory::PrValue;
        if (context == UseContext::Condition) {
            expr = convert_to_condition(std::move(expr), loc);
        }
        return expr;
    }

    if (expr.category == ValueCategory::MemberFunctionPointerCallee) {
        report_error("pointer-to-member function result can only be used as the operand of a function call",
                     loc);
        expr.has_error = true;
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.memberptr.call_only");
        expr.value = builder_.error("pointer-to-member function used as value", loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        expr.fragment = chain(std::move(expr.fragment), std::move(error_fragment), loc);
        expr.type = builder_.unknown_type();
        expr.category = ValueCategory::PrValue;
        return expr;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.error");
    cir::InstId value = builder_.error("expression cannot be used as a value", loc);
    cir::Fragment error_fragment = finish_fragment_block(block, previous);
    expr.fragment = chain(std::move(expr.fragment), std::move(error_fragment), loc);
    expr.has_error = true;
    expr.value = value;
    expr.type = builder_.unknown_type();
    expr.category = ValueCategory::PrValue;
    return expr;
}

ExprResult Session::call_conversion_function(ExprResult expr,
                                             cir::EntityId conversion_function,
                                             cir::TypeId target_type,
                                             SrcLoc loc) {
    ExprResult callee;
    callee.fragment = std::move(expr.fragment);
    callee.place = expr.place;
    callee.entity = conversion_function;
    callee.type = file_.valid(conversion_function)
        ? file_.entity(conversion_function).type
        : cir::TypeId{};
    callee.name = file_.valid(conversion_function) &&
                  file_.entity(conversion_function).name.valid()
        ? std::string(file_.name(file_.entity(conversion_function).name))
        : std::string("operator");
    callee.candidates.push_back(conversion_function);
    callee.category = ValueCategory::FunctionDesignator;
    callee.bound_member_object_category = expr.category;
    callee.has_error = expr.has_error;

    cir::TypeId source_type = file_.resolved_type(expr.type);
    if (file_.valid(source_type) &&
        file_.type(source_type).kind == cir::TypeKind::Record &&
        file_.valid(conversion_function) &&
        file_.entity(conversion_function).name.valid()) {
        MemberLookupResult lookup = lookup_member_name(
            source_type,
            file_.name(file_.entity(conversion_function).name));
        cir::EntityId conversion_owner =
            file_.entity(conversion_function).parent;
        for (const MemberLookupDeclaration& declaration :
             lookup.declarations) {
            cir::EntityId declaration_owner =
                declaration.entity.valid() && file_.valid(declaration.entity)
                    ? file_.entity(declaration.entity).parent
                    : cir::EntityId{};
            if (declaration.entity != conversion_function &&
                declaration_owner != conversion_owner) {
                continue;
            }
            MemberCandidateObjectPaths paths;
            paths.entity = conversion_function;
            paths.paths = declaration.object_paths;
            paths.implicit_object_class = declaration.implicit_object_class;
            paths.found_through_using = declaration.found_through_using;
            paths.access_owner = declaration.access_owner;
            paths.declaring_class = declaration.declaring_class;
            paths.lookup_class = source_type;
            paths.declared_access = declaration.declared_access;
            paths.has_declared_access = declaration.has_declared_access;
            paths.base_paths = declaration.base_paths;
            callee.member_candidate_object_paths.push_back(std::move(paths));
            break;
        }
    }

    ExprResult converted =
        collect_call_expr(std::move(callee), {}, loc);
    if (target_type.valid()) {

        converted = convert_to(std::move(converted),
                               target_type,
                               UseContext::RValue,
                               loc);
    }
    return converted;
}

ExprResult Session::apply_user_conversion_sequence(
    ExprResult source,
    cir::TypeId target_type,
    const UserConversionSequence& sequence,
    SrcLoc loc) {
    if (sequence.kind == UserConversionSequence::Kind::ConversionFunction) {
        return call_conversion_function(std::move(source), sequence.callable,
                                        target_type, loc);
    }
    if (sequence.kind == UserConversionSequence::Kind::Constructor) {
        std::vector<ExprResult> arguments;
        arguments.push_back(std::move(source));
        ConstructorCallMaterialization materialized =
            materialize_selected_constructor_call(
                sequence.callable, std::move(arguments), loc);

        std::string temp_name =
            ".conversion.tmp." +
            std::to_string(compound_literal_counter_++);
        cir::EntityId temp = builder_.add_entity(
            cir::EntityKind::Variable, temp_name, target_type, {}, loc,
            cir::StorageDuration::Temporary, cir::MemorySpace::Default, {});
        file_.entity_mut(temp).is_definition = true;

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block =
            begin_fragment_block("expr.conversion.constructor");
        cir::InstId place = builder_.local_place(temp, target_type, loc);
        if (!materialized.has_error) {
            emit_construct_in_place(
                place, structor_complete_variant(sequence.callable),
                materialized.argument_values, loc);
        }
        cir::InstId value = builder_.lvalue_to_rvalue(place, loc);
        cir::Fragment construct_fragment =
            finish_fragment_block(block, previous);

        ExprResult result;
        result.fragment = chain(std::move(materialized.argument_fragment),
                                std::move(construct_fragment), loc);
        result.value = value;
        result.type = target_type;
        result.category = ValueCategory::PrValue;
        result.has_error = materialized.has_error;
        result = fold_immediate_constructor_invocation(
            std::move(result), place, sequence.callable, loc);
        if (!materialized.has_error) {
            if (cir::LifetimeId lifetime = register_destructor_cleanup(
                    temp, target_type, loc,
                    /*full_expression_temporary=*/true);
                lifetime.valid()) {
                result.materialized_lifetimes.push_back(lifetime);
            }
        }
        return result;
    }
    source.has_error = true;
    source.type = target_type;
    return source;
}

ExprResult Session::require_place(ExprResult expr, UseContext context, SrcLoc loc) {
    expr = materialize_qualified_data_member(std::move(expr), loc);
    expr = materialize_deferred_entity_place(
        std::move(expr), /*allow_non_odr_constant=*/false, loc);
    if (expr.entity.valid() && file_.valid(expr.entity) &&
        file_.entity(expr.entity).kind == cir::EntityKind::Variable) {
        // Keeping a variable as a glvalue (address-taking, reference
        // binding, assignment) is an ODR-use. A prior constant-evaluation
        // demand may have published the value of an integral static member,
        // but it must not stand in for the member's required definition.
        (void)request_class_member_instantiation(
            expr.entity, cir::InstantiationDemandKind::OdrUse, loc);
    }
    if (expr_is_dependent(expr)) {
        bump_pattern_taint();
        return expr;
    }

    if (expr.category == ValueCategory::LValue && expr.place.valid()) {
        if (context == UseContext::Assignment) {
            cir::TypeId place_type = file_.inst(expr.place).result_type;
            cir::TypeRef object_ref = file_.place_object_ref(place_type);
            if ((object_ref.qualifiers & cir::QualConst) != 0) {
                report_error("assignment to const-qualified object", loc);
                expr.has_error = true;
            }
            const cir::Inst& place_inst = file_.inst(expr.place);
            if (place_inst.place_fact.valid() && file_.valid(place_inst.place_fact)) {
                const cir::PlaceFact& fact = file_.place_fact(place_inst.place_fact);
                if (!fact.modifiable) {
                    report_error("assignment to a non-modifiable object", loc);
                    expr.has_error = true;
                }
                if (fact.entity.valid() &&
                    file_.entity(fact.entity).decl_flags.is_constexpr) {

                    report_error("assignment to constexpr object", loc);
                    expr.has_error = true;
                }
            }
        }
        return expr;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.error");
    cir::InstId place = builder_.error("expression is not assignable", loc);
    cir::Fragment error_fragment = finish_fragment_block(block, previous);
    expr.fragment = chain(std::move(expr.fragment), std::move(error_fragment), loc);
    expr.has_error = true;
    expr.place = place;
    expr.type = builder_.unknown_type();
    expr.category = ValueCategory::LValue;
    return expr;
}

ExprResult Session::convert_to(ExprResult expr, cir::TypeId type, UseContext context, SrcLoc loc) {
    UserConversionContext conversion_context =
        context == UseContext::DirectInit
            ? UserConversionContext::DirectInitialization
            : UserConversionContext::CopyInitialization;
    if (context != UseContext::Condition && type.valid() &&
        is_reference_type(type)) {
        return bind_to_reference(
            std::move(expr), type, loc,
            context == UseContext::DirectInit
                ? UserConversionContext::DirectReferenceBinding
                : UserConversionContext::CopyInitialization);
    }

    if (in_template_definition() && type.valid() && expr.type.valid() &&
        expr.value.valid() && expr.category == ValueCategory::PrValue &&
        !type_equal(expr.type, type) &&
        (expr_is_dependent(expr) || is_dependent_type(type))) {
        QualificationConversionAnalysis qualification =
            analyze_qualification_conversion(file_.type_ref(expr.type),
                                              file_.type_ref(type));
        if (qualification.has_indirection && qualification.similar &&
            qualification.allowed) {
            return cast_if_needed(std::move(expr), type, "qualification", loc);
        }
    }

    if (in_template_definition() && type.valid() && expr.type.valid() &&
        type_equal(expr.type, type) &&
        (expr_is_dependent(expr) || is_dependent_type(type))) {

        return require_value(std::move(expr), context, loc);
    }

    if (in_template_definition() &&
        (expr_is_dependent(expr) || (type.valid() && is_dependent_type(type)))) {
        bump_pattern_taint();
        if (type.valid() && is_dependent_type(type)) {

            expr.type = type;
            expr.value = {};
            expr.place = {};
            expr.category = ValueCategory::PrValue;
        }
        return expr;
    }

    if (type.valid() && expr.init_list &&
        expr.category == ValueCategory::InitList) {
        return materialize_list_initialization(std::move(expr), type,
                                               context, loc);
    }

    if (expr.category == ValueCategory::OverloadDesignator && type.valid()) {
        expr = convert_overload_designator_to_target(std::move(expr),
                                                     type,
                                                     loc);
        if (expr.has_error) {
            return expr;
        }
    } else if (expr.category == ValueCategory::FunctionDesignator &&
               type.valid()) {
        expr = convert_function_designator_to_target(std::move(expr),
                                                     type,
                                                     loc);
        if (expr.has_error) {
            return expr;
        }
    }
    if (expr.category == ValueCategory::MemberPointerDesignator &&
        member_pointer_payload(file_, type)) {
        return convert_member_pointer_designator_to_target(std::move(expr),
                                                           type,
                                                           loc);
    }
    if (lang_opts_.is_cxx_mode() && type.valid() &&
        !type_equal(expr.type, type)) {
        cir::TypeId source_record = file_.resolved_type(expr.type);
        cir::TypeId target_record = file_.resolved_type(type);
        bool source_is_record = file_.valid(source_record) &&
            file_.type(source_record).kind == cir::TypeKind::Record;
        bool target_is_record = file_.valid(target_record) &&
            file_.type(target_record).kind == cir::TypeKind::Record;
        if (target_is_record) {

            if (source_is_record &&
                expr.category == ValueCategory::PrValue && expr.value.valid()) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(expr),
                                               /*is_arrow=*/false,
                                               loc);
                expr = std::move(materialized.base_place);
            }
            UserConversionSequence sequence =
                resolve_initialization_user_conversion(
                    expr, type, conversion_context, loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_error("conversion from '" + file_.format_type(expr.type) +
                                 "' to '" + file_.format_type(type) +
                                 "' is ambiguous",
                             loc);
                report_overload_ambiguity_notes(sequence.ambiguity, loc);
                expr.has_error = true;
                expr.type = type;
                return expr;
            }
            if (sequence.kind ==
                UserConversionSequence::Kind::ConversionFunction) {
                return apply_user_conversion_sequence(
                    std::move(expr), type, sequence, loc);
            }
            if (sequence.kind == UserConversionSequence::Kind::Constructor) {
                return apply_user_conversion_sequence(
                    std::move(expr), type, sequence, loc);
            }
            if (record_has_user_constructor(target_record)) {
                std::vector<ExprResult> constructor_arguments;
                constructor_arguments.push_back(std::move(expr));
                return collect_functional_cast(
                    type,
                    std::move(constructor_arguments),
                    loc,
                    InitListSyntax::Parenthesized,
                    /*allow_explicit=*/false);
            }
            if (source_is_record) {
                DerivedToBasePathResult base_result =
                    analyze_derived_to_base_path(source_record,
                                                 target_record);
                if (base_result.kind == DerivedToBasePathKind::Ambiguous) {
                    report_error("ambiguous conversion from derived class '" +
                                     file_.format_type(source_record) +
                                     "' to base class '" +
                                     file_.format_type(target_record) + "'",
                                 loc);
                    expr.has_error = true;
                    expr.type = type;
                    return expr;
                }
                if (base_result.kind == DerivedToBasePathKind::Unique) {
                    if (!check_base_path_access(base_result.path,
                                                source_record,
                                                target_record,
                                                loc)) {
                        expr.has_error = true;
                    }
                    cir::BlockId previous = builder_.current_block();
                    cir::BlockId block =
                        begin_fragment_block("expr.base.object");
                    cir::InstId place =
                        emit_subobject_path(expr.place,
                                            base_result.path,
                                            loc);
                    cir::Fragment fragment =
                        finish_fragment_block(block, previous);
                    expr.fragment = chain(std::move(expr.fragment),
                                          std::move(fragment), loc);
                    expr.place = place;
                    expr.type = type;
                    return require_value(std::move(expr), context, loc);
                }
            }
        }

        {
            bool generic_handled = false;
            expr = convert_generic_lambda_to_function_pointer(
                std::move(expr), type, &generic_handled, loc);
            if (generic_handled) {
                return expr;
            }
        }

        if (expr.category == ValueCategory::PrValue && expr.value.valid()) {
            cir::TypeId source_resolved = file_.resolved_type(expr.type);
            cir::TypeId target_resolved = file_.resolved_type(type);
            if (file_.valid(source_resolved) && file_.valid(target_resolved) &&
                file_.type(source_resolved).kind == cir::TypeKind::Record &&
                file_.type(target_resolved).kind != cir::TypeKind::Record) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(expr),
                                               /*is_arrow=*/false,
                                               loc);
                expr = std::move(materialized.base_place);
            }
        }
        bool ambiguous = false;
        cir::EntityId conversion =
            select_conversion_function(expr, type, &ambiguous, loc,
                                       conversion_context);
        if (conversion.valid()) {
            return call_conversion_function(std::move(expr),
                                            conversion,
                                            type,
                                            loc);
        }
        if (ambiguous) {
            report_error("conversion from '" + file_.format_type(expr.type) +
                             "' to '" + file_.format_type(type) +
                             "' is ambiguous",
                         loc);
            expr.has_error = true;
            return expr;
        }
    }
    ExprResult value = require_value(std::move(expr), context, loc);
    if (context == UseContext::Condition) {
        return value;
    }
    if (!type.valid() || type_equal(value.type, type)) {
        return value;
    }

    if (lang_opts_.is_cxx_mode()) {
        cir::TypeId from_resolved = file_.resolved_type(value.type);
        cir::TypeId to_resolved = file_.resolved_type(type);
        const auto* source_member =
            member_pointer_payload(file_, from_resolved);
        const auto* target_member =
            member_pointer_payload(file_, to_resolved);
        if (source_member && target_member) {
            cir::TypeId source_class =
                file_.resolved_type(source_member->class_type.type);
            cir::TypeId target_class =
                file_.resolved_type(target_member->class_type.type);
            cir::TypeRef source_value = source_member->member_type;
            cir::TypeRef target_value = target_member->member_type;
            bool same_value =
                file_.resolved_type(source_value.type) ==
                    file_.resolved_type(target_value.type) &&
                (source_value.qualifiers &
                 static_cast<uint8_t>(~target_value.qualifiers)) == 0;
            QualificationConversionAnalysis member_qualification =
                analyze_qualification_conversion(source_value,
                                                  target_value);
            bool member_function_adjustment =
                function_type_conversion_matches(source_value,
                                                 target_value);
            bool compatible_value = same_value ||
                (member_qualification.has_indirection &&
                 member_qualification.similar &&
                 member_qualification.allowed) ||
                member_function_adjustment;
            if (source_class == target_class && !compatible_value) {
                report_error(
                    "cannot convert between incompatible pointer-to-member "
                    "types",
                    loc);
                value.has_error = true;
                return cast_if_needed(std::move(value), type,
                                      "member pointer", loc);
            }
            if (source_class != target_class) {
                DerivedToBasePathResult base_result =
                    analyze_derived_to_base_path(target_class, source_class);
                if (base_result.kind == DerivedToBasePathKind::Ambiguous) {
                    report_error(
                        "ambiguous conversion of a pointer to member of base "
                        "class '" + file_.format_type(source_class) +
                        "' to derived class '" +
                        file_.format_type(target_class) + "'",
                        loc);
                    value.has_error = true;
                    return cast_if_needed(std::move(value), type,
                                          "member pointer", loc);
                }
                if (base_result.kind == DerivedToBasePathKind::Unique &&
                    compatible_value) {
                    if (!check_base_path_access(base_result.path,
                                                target_class,
                                                source_class,
                                                loc)) {
                        value.has_error = true;
                    }
                    bool through_virtual_base = std::any_of(
                        base_result.path.begin(), base_result.path.end(),
                        [&](cir::EntityId step) {
                            const cir::RecordFieldFact* fact =
                                file_.field_fact(step);
                            return fact && fact->is_virtual_base_storage;
                        });
                    if (through_virtual_base) {
                        report_error(
                            "pointer-to-member conversion through a virtual "
                            "base class is not allowed",
                            loc);
                        value.has_error = true;
                    }
                    return cast_if_needed(std::move(value), type,
                                          "member pointer", loc);
                }
                report_error("cannot convert pointer to member of '" +
                                 file_.format_type(source_class) + "' to '" +
                                 file_.format_type(target_class) + "'",
                             loc);
                value.has_error = true;
                return cast_if_needed(std::move(value), type,
                                      "member pointer", loc);
            }
        }
        if (file_.valid(from_resolved) && file_.valid(to_resolved) &&
            file_.type(from_resolved).kind == cir::TypeKind::Pointer &&
            file_.type(to_resolved).kind == cir::TypeKind::Pointer) {
            cir::TypeRef derived_ref =
                file_.pointer_pointee_ref(from_resolved);
            cir::TypeRef base_ref =
                file_.pointer_pointee_ref(to_resolved);
            cir::TypeId derived = derived_ref.type;
            cir::TypeId base = base_ref.type;
            DerivedToBasePathResult base_result =
                analyze_derived_to_base_path(derived, base);
            if (base_result.kind == DerivedToBasePathKind::Ambiguous) {
                report_error("ambiguous conversion from derived class '" +
                                 file_.format_type(derived) +
                                 "' to base class '" +
                                 file_.format_type(base) + "'",
                             loc);
                value.has_error = true;
                return cast_if_needed(std::move(value),
                                      type,
                                      "conversion",
                                      loc);
            }
            if (base_result.kind == DerivedToBasePathKind::Unique) {
                if ((derived_ref.qualifiers &
                     static_cast<uint8_t>(~base_ref.qualifiers)) != 0) {
                    report_error(
                        "derived-to-base pointer conversion discards "
                        "qualifiers",
                        loc);
                    value.has_error = true;
                    return cast_if_needed(std::move(value),
                                          type,
                                          "conversion",
                                          loc);
                }

                if (!check_base_path_access(base_result.path, derived, base,
                                            loc)) {
                    value.has_error = true;
                }
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block = begin_fragment_block("expr.base.pointer");
                cir::InstId place = builder_.deref(value.value, loc);
                place = emit_subobject_path(place, base_result.path, loc);
                cir::InstId address = builder_.addr_of(place, loc);
                cir::InstId adjusted = builder_.cast(type, address, "value", loc);
                cir::Fragment fragment = finish_fragment_block(block, previous);
                value.fragment =
                    chain(std::move(value.fragment), std::move(fragment), loc);
                value.value = adjusted;
                value.type = type;
                return value;
            }
        }
    }

    if (lang_opts_.is_cxx_mode() &&
        function_pointer_conversion_matches(file_.type_ref(value.type),
                                            file_.type_ref(type))) {
        return cast_if_needed(std::move(value),
                              type,
                              "function pointer",
                              loc);
    }

    if (lang_opts_.is_cxx_mode()) {
        QualificationConversionAnalysis qualification =
            analyze_qualification_conversion(file_.type_ref(value.type),
                                              file_.type_ref(type));
        if (qualification.has_indirection && qualification.similar) {
            if (qualification.allowed) {
                return cast_if_needed(std::move(value),
                                      type,
                                      "qualification",
                                      loc);
            }
            report_error("cannot convert expression of type '" +
                             file_.format_type(value.type) + "' to '" +
                             file_.format_type(type) +
                             "': invalid qualification conversion",
                         loc);
            value.has_error = true;
            return cast_if_needed(std::move(value),
                                  type,
                                  "qualification",
                                  loc);
        }
    }

    bool source_scalar = is_scalar_type(value.type);
    bool target_scalar = is_scalar_type(type);
    bool source_vector = is_vector_type(value.type);
    bool target_vector = is_vector_type(type);
    bool source_void = is_void_type(value.type);
    bool target_void = is_void_type(type);
    bool target_nullptr = is_nullptr_type(type);
    if (target_nullptr && is_integer_zero_literal(file_, value)) {
        return cast_if_needed(std::move(value), type, "conversion", loc);
    }
    bool source_nullptr = is_nullptr_type(value.type);
    if (source_nullptr && file_.valid(type)) {
        cir::TypeId resolved_target = file_.resolved_type(type);
        if (!lang_opts_.is_cxx_mode() && lang_opts_.is_c23_or_later() &&
            is_bool_type(resolved_target)) {
            return convert_nullptr_to_bool(std::move(value),
                                           type,
                                           "conversion",
                                           loc);
        }
        if (file_.valid(resolved_target) &&
            (file_.type(resolved_target).kind == cir::TypeKind::Pointer ||
             file_.type(resolved_target).kind == cir::TypeKind::BlockPointer ||
             file_.type(resolved_target).kind == cir::TypeKind::MemberPointer)) {
            return cast_if_needed(std::move(value), type, "conversion", loc);
        }
    }
    bool target_pointer_like =
        is_pointer_type(type) || member_pointer_payload(file_, type);
    if (lang_opts_.is_cxx_mode() && target_pointer_like &&
        is_integer_type(value.type)) {
        if (is_null_pointer_constant(value)) {
            return cast_if_needed(std::move(value), type, "conversion", loc);
        }
        report_error("cannot convert expression of type '" +
                         file_.format_type(value.type) + "' to '" +
                         file_.format_type(type) + "'",
                     loc);
        value.has_error = true;
        return cast_if_needed(std::move(value), type, "conversion", loc);
    }
    if (!source_void && !target_void && source_scalar && target_scalar) {

        if (lang_opts_.is_cxx_mode() &&
            conversion_rank(
                value,
                file_.type_ref(type),
                value.semantic_object_qualifiers.value_or(0),
                nullptr,
                /*allow_user_defined=*/false) == ConversionRank::Bad) {
            report_error("cannot convert expression of type '" +
                             file_.format_type(value.type) + "' to '" +
                             file_.format_type(type) + "'",
                         loc);
            value.has_error = true;
        }
        return cast_if_needed(std::move(value), type, "conversion", loc);
    }
    if (!source_void && !target_void && target_vector &&
        (source_scalar || source_vector)) {
        if (source_vector) {
            uint64_t source_size = file_.vector_size_bytes(value.type);
            uint64_t target_size = file_.vector_size_bytes(type);
            cir::TypeId source_element =
                file_.vector_element_type(value.type);
            cir::TypeId target_element = file_.vector_element_type(type);
            bool lax_integer_bitcast = source_size != 0 &&
                source_size == target_size &&
                is_integer_type(source_element) &&
                is_integer_type(target_element);
            if (lax_integer_bitcast) {

                return cast_if_needed(std::move(value), type,
                                      "vector_reinterpret", loc);
            }
            report_error(
                "cannot implicitly convert between these vector types",
                loc);
            value.has_error = true;
        }
        return cast_if_needed(std::move(value), type, "conversion", loc);
    }

    if (!source_void && !target_void && file_.valid(value.type) && file_.valid(type)) {

        bool deferred_dependent_conversion = is_dependent_type(value.type);
        if (!deferred_dependent_conversion) {
            report_error("cannot convert expression of type '" +
                             file_.format_type(value.type) + "' to '" +
                             file_.format_type(type) + "'",
                         loc);
            value.has_error = true;
        }
    }
    return cast_if_needed(std::move(value), type, "conversion", loc);
}

void Session::discard_value(ExprResult expr, SrcLoc loc) {
    if (expr.nodiscard_callee.valid()) {
        const cir::Entity& callee = file_.entity(expr.nodiscard_callee);
        std::string callee_name =
            callee.name.valid() ? file_.name(callee.name) : "<function>";
        report_warning("ignoring return value of '" + callee_name +
                           "' declared with attribute 'nodiscard'",
                       loc);
    }
    if (expr.category != ValueCategory::LValue &&
        expr.category != ValueCategory::XValue) {
        (void)require_value(std::move(expr), UseContext::Discard, loc);
    }
}

cir::TypeId Session::object_type_from_place(cir::InstId place) const {
    if (!file_.valid(place)) {
        return {};
    }
    cir::TypeId place_type = file_.inst(place).result_type;
    if (!file_.valid(place_type) || file_.type(place_type).kind != cir::TypeKind::Place) {
        return {};
    }
    return file_.place_object_type(place_type);
}

cir::TypeId Session::floating_literal_type(syntax::FloatingLiteralKind kind) {
    switch (kind) {
        case syntax::FloatingLiteralKind::Float:
            return builder_.float_type();
        case syntax::FloatingLiteralKind::LongDouble:
            return builder_.long_double_type();
        case syntax::FloatingLiteralKind::Double:
            return builder_.double_type();
    }
    return builder_.double_type();
}

cir::TypeId Session::character_literal_type(LiteralPrefix prefix) {
    if (lang_opts_.is_cxx_mode()) {
        switch (prefix) {
            case LiteralPrefix::u:
                return file_.builtin_type(cir::BuiltinTypeKind::Char16);
            case LiteralPrefix::U:
                return file_.builtin_type(cir::BuiltinTypeKind::Char32);
            case LiteralPrefix::L:
                return file_.builtin_type(cir::BuiltinTypeKind::WChar);
            case LiteralPrefix::U8:
                if (lang_opts_.is_cxx20_or_later()) {
                    return file_.builtin_type(cir::BuiltinTypeKind::Char8);
                }
            case LiteralPrefix::None:
            default:
                return builder_.char_type();
        }
    }

    switch (prefix) {
        case LiteralPrefix::u:
            return file_.builtin_type(cir::BuiltinTypeKind::UShort);
        case LiteralPrefix::U:
            return file_.builtin_type(cir::BuiltinTypeKind::UInt);
        case LiteralPrefix::U8:

            if (lang_opts_.is_c23_or_later()) {
                return file_.builtin_type(cir::BuiltinTypeKind::UChar);
            }
            return builder_.int_type();
        case LiteralPrefix::L:
        case LiteralPrefix::None:
        default:
            return builder_.int_type();
    }
}

bool Session::is_void_type(cir::TypeId type) const {
    return file_.valid(type) &&
           file_.type(type).kind == cir::TypeKind::Builtin &&
           file_.format_type(type) == "void";
}

cir::UnaryOpKind Session::unary_op_kind(syntax::UnaryOperator op) const {
    switch (op) {
        case syntax::UnaryOperator::Plus: return cir::UnaryOpKind::Plus;
        case syntax::UnaryOperator::Minus: return cir::UnaryOpKind::Minus;
        case syntax::UnaryOperator::LogicalNot: return cir::UnaryOpKind::LogicalNot;
        case syntax::UnaryOperator::BitwiseNot: return cir::UnaryOpKind::BitwiseNot;
        case syntax::UnaryOperator::Invalid:
        case syntax::UnaryOperator::AddressOf:
        case syntax::UnaryOperator::Dereference:
        case syntax::UnaryOperator::PrefixIncrement:
        case syntax::UnaryOperator::PrefixDecrement:
        case syntax::UnaryOperator::PostfixIncrement:
        case syntax::UnaryOperator::PostfixDecrement:
        case syntax::UnaryOperator::SizeofExpr:
        case syntax::UnaryOperator::SizeofType:
        case syntax::UnaryOperator::AlignofExpr:
        case syntax::UnaryOperator::AlignofType:
        case syntax::UnaryOperator::TypeidExpr:
        case syntax::UnaryOperator::TypeidType:
        case syntax::UnaryOperator::LabelAddress:
            return cir::UnaryOpKind::Invalid;
    }
    return cir::UnaryOpKind::Invalid;
}

cir::BinaryOpKind Session::binary_op_kind(syntax::BinaryOperator op) const {
    switch (op) {
        case syntax::BinaryOperator::Add: return cir::BinaryOpKind::Add;
        case syntax::BinaryOperator::Sub: return cir::BinaryOpKind::Sub;
        case syntax::BinaryOperator::Mul: return cir::BinaryOpKind::Mul;
        case syntax::BinaryOperator::Div: return cir::BinaryOpKind::Div;
        case syntax::BinaryOperator::Mod: return cir::BinaryOpKind::Mod;
        case syntax::BinaryOperator::Less: return cir::BinaryOpKind::Less;
        case syntax::BinaryOperator::LessEqual: return cir::BinaryOpKind::LessEqual;
        case syntax::BinaryOperator::Greater: return cir::BinaryOpKind::Greater;
        case syntax::BinaryOperator::GreaterEqual: return cir::BinaryOpKind::GreaterEqual;
        case syntax::BinaryOperator::Equal: return cir::BinaryOpKind::Equal;
        case syntax::BinaryOperator::NotEqual: return cir::BinaryOpKind::NotEqual;
        case syntax::BinaryOperator::LogicalAnd: return cir::BinaryOpKind::LogicalAnd;
        case syntax::BinaryOperator::LogicalOr: return cir::BinaryOpKind::LogicalOr;
        case syntax::BinaryOperator::BitAnd: return cir::BinaryOpKind::BitAnd;
        case syntax::BinaryOperator::BitOr: return cir::BinaryOpKind::BitOr;
        case syntax::BinaryOperator::BitXor: return cir::BinaryOpKind::BitXor;
        case syntax::BinaryOperator::Shl: return cir::BinaryOpKind::Shl;
        case syntax::BinaryOperator::Shr: return cir::BinaryOpKind::Shr;
        case syntax::BinaryOperator::Comma: return cir::BinaryOpKind::Comma;
        case syntax::BinaryOperator::Invalid:
        case syntax::BinaryOperator::ThreeWay:
        case syntax::BinaryOperator::PtrMemDot:
        case syntax::BinaryOperator::PtrMemArrow:
        case syntax::BinaryOperator::Assign:
        case syntax::BinaryOperator::AssignAdd:
        case syntax::BinaryOperator::AssignSub:
        case syntax::BinaryOperator::AssignMul:
        case syntax::BinaryOperator::AssignDiv:
        case syntax::BinaryOperator::AssignMod:
        case syntax::BinaryOperator::AssignShl:
        case syntax::BinaryOperator::AssignShr:
        case syntax::BinaryOperator::AssignAnd:
        case syntax::BinaryOperator::AssignXor:
        case syntax::BinaryOperator::AssignOr:
            return cir::BinaryOpKind::Invalid;
    }
    return cir::BinaryOpKind::Invalid;
}

cir::TypeId Session::binary_result_type(syntax::BinaryOperator op) const {
    switch (op) {
        case syntax::BinaryOperator::Less:
        case syntax::BinaryOperator::LessEqual:
        case syntax::BinaryOperator::Greater:
        case syntax::BinaryOperator::GreaterEqual:
        case syntax::BinaryOperator::Equal:
        case syntax::BinaryOperator::NotEqual:
        case syntax::BinaryOperator::ThreeWay:
        case syntax::BinaryOperator::LogicalAnd:
        case syntax::BinaryOperator::LogicalOr:
            return const_cast<Session*>(this)->builder_.bool_type();
        default:
            return const_cast<Session*>(this)->builder_.int_type();
    }
}

} // namespace aburi::collect
