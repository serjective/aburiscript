#include "type.h"

#include <functional>
#include <sstream>
#include <type_traits>

namespace aburi::cir {
namespace {

template <typename EnumT>
auto enum_value(EnumT value) {
    return static_cast<std::underlying_type_t<EnumT>>(value);
}

void append_id(std::ostringstream& out, TypeId id) {
    if (!id.valid()) {
        out << "-";
        return;
    }
    out << id.index << ".g" << id.generation;
}

void append_id(std::ostringstream& out, EntityId id) {
    if (!id.valid()) {
        out << "-";
        return;
    }
    out << id.index << ".g" << id.generation;
}

void append_id(std::ostringstream& out, NameId id) {
    if (!id.valid()) {
        out << "-";
        return;
    }
    out << id.index << ".g" << id.generation;
}

void append_id(std::ostringstream& out, InstId id) {
    if (!id.valid()) {
        out << "-";
        return;
    }
    out << id.index << ".g" << id.generation;
}

void append_ref(std::ostringstream& out, TypeRef ref) {
    append_id(out, ref.type);
    if (ref.qualifiers != QualNone) {
        out << "q" << static_cast<unsigned>(ref.qualifiers);
    }
    if (ref.memory_space != MemorySpace::Default) {
        out << "m" << enum_value(ref.memory_space);
    }
}

void append_template_argument(std::ostringstream& out,
                              const TemplateArgument& argument);

void append_template_value_expression(
    std::ostringstream& out,
    const TemplateValueExpression& expression) {
    out << "expr(" << expression.root << ",[";
    for (const TemplateValueExprNode& node : expression.nodes) {
        out << enum_value(node.kind) << ',' << enum_value(node.op) << ','
            << enum_value(node.trait_kind) << ',' << enum_value(node.fold_kind)
            << ',' << node.value << ',' << node.integer_value.decimal() << ','
            << node.integer_value.is_unsigned << ','
            << node.integer_value.bit_width << ','
            << node.parameter_index << ',' << node.lhs << ',' << node.rhs
            << ',' << node.third << ",[";
        for (uint32_t operand : node.operands) {
            out << operand << ';';
        }
        out << "]," << node.expands_parameter_pack << ",packs[";
        for (const TemplateValuePackReference& reference :
             node.pack_references) {
            out << enum_value(reference.kind) << ',';
            append_id(out, reference.declaration);
            out << ',';
            append_id(out, reference.owner);
            out << ',' << reference.depth << ',' << reference.index << ',';
            append_id(out, reference.parameter_type);
            out << ',';
            append_id(out, reference.name);
            out << ';';
        }
        out << "],concept-arguments[";
        for (const TemplateArgument& argument :
             node.template_arguments.values()) {
            append_template_argument(out, argument);
            out << ';';
        }
        out << "],";
        append_id(out, node.type);
        out << ',';
        append_ref(out, node.result_type);
        out << ',';
        append_id(out, node.entity);
        out << ',';
        append_id(out, node.name);
        out << ',';
        append_ref(out, node.qualifier_type);
        out << ',' << node.semantic_key << ';';
    }
    out << "])";
}

void append_template_argument(std::ostringstream& out,
                              const TemplateArgument& argument) {
    out << "arg(" << enum_value(argument.kind) << ',';
    append_ref(out, argument.type);
    out << ',';
    append_ref(out, argument.value_type);
    out << ',';
    out << enum_value(argument.value_kind) << ','
        << argument.integer_value.decimal() << ','
        << argument.integer_value.is_unsigned << ','
        << argument.integer_value.bit_width << ',';
    append_id(out, argument.value_entity);
    out << ',' << argument.value_byte_offset << ','
        << enum_value(argument.meta_kind) << ",[";
    for (const TemplateArgument& element : argument.value_elements) {
        append_template_argument(out, element);
    }
    out << "]," << argument.value_param_index << ',';
    append_ref(out, argument.dependent_value_qualifier);
    out << ',';
    append_id(out, argument.dependent_value_name);
    out << ',';
    append_template_value_expression(out, argument.dependent_value_expr);
    out << ',' << enum_value(argument.generated_pack_kind) << ',';
    append_ref(out, argument.generated_pack_count_type);
    out << ',';
    append_template_value_expression(out, argument.generated_pack_count_expr);
    out << ',';
    append_id(out, argument.template_entity);
    out << ',' << argument.template_param_index << ',';
    append_ref(out, argument.dependent_template_qualifier);
    out << ',';
    append_id(out, argument.template_name);
    out << ',' << argument.is_dependent << ',' << argument.is_defaulted
        << ',' << argument.expands_parameter_pack << ','
        << argument.value_spelling << ')';
}

void append_template_arguments(std::ostringstream& out,
                               const std::vector<TemplateArgument>& arguments) {
    out << '[';
    for (const TemplateArgument& argument : arguments) {
        append_template_argument(out, argument);
        out << ';';
    }
    out << ']';
}

uint64_t hash_mix(uint64_t hash, uint64_t value) {
    hash ^= value + 0x9E3779B97F4A7C15ull + (hash << 6) + (hash >> 2);
    return hash;
}

template <typename IdT>
uint64_t structural_id_value(IdT id) {
    if (!id.valid()) {
        return 0;
    }
    return (static_cast<uint64_t>(id.generation) << 32) | id.index;
}

template <typename IdT>
bool ids_structurally_equal(IdT lhs, IdT rhs) {
    return structural_id_value(lhs) == structural_id_value(rhs);
}

uint64_t hash_ref(uint64_t hash, TypeRef ref) {
    hash = hash_mix(hash, structural_id_value(ref.type));
    hash = hash_mix(hash, ref.qualifiers);
    hash = hash_mix(hash, enum_value(ref.memory_space));
    return hash;
}

bool refs_structurally_equal(TypeRef lhs, TypeRef rhs) {
    return ids_structurally_equal(lhs.type, rhs.type) &&
           lhs.qualifiers == rhs.qualifiers &&
           lhs.memory_space == rhs.memory_space;
}

uint64_t hash_string(uint64_t hash, std::string_view value) {
    hash = hash_mix(hash, value.size());
    return hash_mix(hash, std::hash<std::string_view>{}(value));
}

uint64_t hash_template_argument(uint64_t hash,
                                const TemplateArgument& argument);

uint64_t hash_template_value_expression(
    uint64_t hash,
    const TemplateValueExpression& expression) {
    hash = hash_mix(hash, expression.root);
    hash = hash_mix(hash, expression.nodes.size());
    for (const TemplateValueExprNode& node : expression.nodes) {
        hash = hash_mix(hash, enum_value(node.kind));
        hash = hash_mix(hash, enum_value(node.op));
        hash = hash_mix(hash, enum_value(node.trait_kind));
        hash = hash_mix(hash, enum_value(node.fold_kind));
        hash = hash_mix(hash, static_cast<uint64_t>(node.value));
        hash = hash_mix(hash, node.integer_value.low_bits);
        hash = hash_mix(hash, node.integer_value.high_bits);
        hash = hash_mix(hash, node.integer_value.bit_width);
        hash = hash_mix(hash, node.integer_value.is_unsigned);
        hash = hash_mix(hash, node.parameter_index);
        hash = hash_mix(hash, node.lhs);
        hash = hash_mix(hash, node.rhs);
        hash = hash_mix(hash, node.third);
        hash = hash_mix(hash, node.operands.size());
        for (uint32_t operand : node.operands) {
            hash = hash_mix(hash, operand);
        }
        hash = hash_mix(hash, node.expands_parameter_pack);
        hash = hash_mix(hash, node.pack_references.size());
        for (const TemplateValuePackReference& reference :
             node.pack_references) {
            hash = hash_mix(hash, enum_value(reference.kind));
            hash = hash_mix(
                hash, structural_id_value(reference.declaration));
            hash = hash_mix(hash, structural_id_value(reference.owner));
            hash = hash_mix(hash, reference.depth);
            hash = hash_mix(hash, reference.index);
            hash = hash_mix(
                hash, structural_id_value(reference.parameter_type));
            hash = hash_mix(hash, structural_id_value(reference.name));
        }
        hash = hash_mix(hash, node.template_arguments.size());
        for (const TemplateArgument& argument :
             node.template_arguments.values()) {
            hash = hash_template_argument(hash, argument);
        }
        hash = hash_mix(hash, structural_id_value(node.type));
        hash = hash_ref(hash, node.result_type);
        hash = hash_mix(hash, structural_id_value(node.entity));
        hash = hash_mix(hash, structural_id_value(node.name));
        hash = hash_ref(hash, node.qualifier_type);
        hash = hash_string(hash, node.semantic_key);
    }
    return hash;
}

uint64_t hash_template_argument(uint64_t hash,
                                const TemplateArgument& argument) {
    hash = hash_mix(hash, enum_value(argument.kind));
    hash = hash_ref(hash, argument.type);
    hash = hash_ref(hash, argument.value_type);
    hash = hash_mix(hash, enum_value(argument.value_kind));
    hash = hash_mix(hash, argument.integer_value.low_bits);
    hash = hash_mix(hash, argument.integer_value.high_bits);
    hash = hash_mix(hash, argument.integer_value.bit_width);
    hash = hash_mix(hash, argument.integer_value.is_unsigned);
    hash = hash_mix(hash, structural_id_value(argument.value_entity));
    hash = hash_mix(hash, static_cast<uint64_t>(argument.value_byte_offset));
    hash = hash_mix(hash, enum_value(argument.meta_kind));
    hash = hash_mix(hash, argument.value_elements.size());
    for (const TemplateArgument& element : argument.value_elements) {
        hash = hash_template_argument(hash, element);
    }
    hash = hash_mix(hash, argument.value_param_index);
    hash = hash_ref(hash, argument.dependent_value_qualifier);
    hash = hash_mix(hash, structural_id_value(argument.dependent_value_name));
    hash = hash_template_value_expression(
        hash, argument.dependent_value_expr);
    hash = hash_mix(hash, enum_value(argument.generated_pack_kind));
    hash = hash_ref(hash, argument.generated_pack_count_type);
    hash = hash_template_value_expression(
        hash, argument.generated_pack_count_expr);
    hash = hash_mix(hash, structural_id_value(argument.template_entity));
    hash = hash_mix(hash, argument.template_param_index);
    hash = hash_ref(hash, argument.dependent_template_qualifier);
    hash = hash_mix(hash, structural_id_value(argument.template_name));
    hash = hash_mix(hash, argument.is_dependent);
    hash = hash_mix(hash, argument.is_defaulted);
    hash = hash_mix(hash, argument.expands_parameter_pack);
    hash = hash_string(hash, argument.value_spelling);
    return hash;
}

uint64_t hash_template_arguments(uint64_t hash,
                                 const std::vector<TemplateArgument>& args) {
    hash = hash_mix(hash, args.size());
    for (const TemplateArgument& argument : args) {
        hash = hash_template_argument(hash, argument);
    }
    return hash;
}

bool template_arguments_structurally_equal(const TemplateArgument& lhs,
                                           const TemplateArgument& rhs);

bool template_value_exprs_structurally_equal(
    const TemplateValueExpression& lhs,
    const TemplateValueExpression& rhs) {
    if (lhs.root != rhs.root || lhs.nodes.size() != rhs.nodes.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.nodes.size(); ++i) {
        const TemplateValueExprNode& a = lhs.nodes[i];
        const TemplateValueExprNode& b = rhs.nodes[i];
        if (a.kind != b.kind || a.op != b.op ||
            a.trait_kind != b.trait_kind || a.fold_kind != b.fold_kind ||
            a.value != b.value || a.integer_value != b.integer_value ||
            a.parameter_index != b.parameter_index || a.lhs != b.lhs ||
            a.rhs != b.rhs || a.third != b.third ||
            a.operands != b.operands ||
            a.expands_parameter_pack != b.expands_parameter_pack ||
            a.pack_references.size() != b.pack_references.size() ||
            a.template_arguments.size() != b.template_arguments.size() ||
            !ids_structurally_equal(a.type, b.type) ||
            !refs_structurally_equal(a.result_type, b.result_type) ||
            !ids_structurally_equal(a.entity, b.entity) ||
            !ids_structurally_equal(a.name, b.name) ||
            !refs_structurally_equal(a.qualifier_type, b.qualifier_type) ||
            a.semantic_key != b.semantic_key) {
            return false;
        }
        for (size_t pack_index = 0;
             pack_index < a.pack_references.size(); ++pack_index) {
            const TemplateValuePackReference& left =
                a.pack_references[pack_index];
            const TemplateValuePackReference& right =
                b.pack_references[pack_index];
            if (left.kind != right.kind ||
                !ids_structurally_equal(left.declaration,
                                        right.declaration) ||
                !ids_structurally_equal(left.owner, right.owner) ||
                left.depth != right.depth || left.index != right.index ||
                !ids_structurally_equal(left.parameter_type,
                                        right.parameter_type) ||
                !ids_structurally_equal(left.name, right.name)) {
                return false;
            }
        }
        for (size_t argument_index = 0;
             argument_index < a.template_arguments.size();
             ++argument_index) {
            if (!template_arguments_structurally_equal(
                    a.template_arguments.values()[argument_index],
                    b.template_arguments.values()[argument_index])) {
                return false;
            }
        }
    }
    return true;
}

bool template_arguments_structurally_equal(const TemplateArgument& lhs,
                                           const TemplateArgument& rhs) {
    if (lhs.meta_kind != rhs.meta_kind) {
        return false;
    }
    if (lhs.kind != rhs.kind ||
        !refs_structurally_equal(lhs.type, rhs.type) ||
        !refs_structurally_equal(lhs.value_type, rhs.value_type) ||
        lhs.value_kind != rhs.value_kind ||
        lhs.integer_value != rhs.integer_value ||
        !ids_structurally_equal(lhs.value_entity, rhs.value_entity) ||
        lhs.value_byte_offset != rhs.value_byte_offset ||
        lhs.value_param_index != rhs.value_param_index ||
        !refs_structurally_equal(lhs.dependent_value_qualifier,
                                 rhs.dependent_value_qualifier) ||
        !ids_structurally_equal(lhs.dependent_value_name,
                                rhs.dependent_value_name) ||
        !template_value_exprs_structurally_equal(lhs.dependent_value_expr,
                                                 rhs.dependent_value_expr) ||
        lhs.generated_pack_kind != rhs.generated_pack_kind ||
        !refs_structurally_equal(lhs.generated_pack_count_type,
                                 rhs.generated_pack_count_type) ||
        !template_value_exprs_structurally_equal(
            lhs.generated_pack_count_expr,
            rhs.generated_pack_count_expr) ||
        !ids_structurally_equal(lhs.template_entity, rhs.template_entity) ||
        lhs.template_param_index != rhs.template_param_index ||
        !refs_structurally_equal(lhs.dependent_template_qualifier,
                                 rhs.dependent_template_qualifier) ||
        !ids_structurally_equal(lhs.template_name, rhs.template_name) ||
        lhs.is_dependent != rhs.is_dependent ||
        lhs.is_defaulted != rhs.is_defaulted ||
        lhs.expands_parameter_pack != rhs.expands_parameter_pack ||
        lhs.value_spelling != rhs.value_spelling ||
        lhs.value_elements.size() != rhs.value_elements.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.value_elements.size(); ++i) {
        if (!template_arguments_structurally_equal(lhs.value_elements[i],
                                                   rhs.value_elements[i])) {
            return false;
        }
    }
    return true;
}

bool template_argument_lists_structurally_equal(
    const std::vector<TemplateArgument>& lhs,
    const std::vector<TemplateArgument>& rhs) {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.size(); ++i) {
        if (!template_arguments_structurally_equal(lhs[i], rhs[i])) {
            return false;
        }
    }
    return true;
}

uint64_t hash_payload(uint64_t hash, const TypePayload& payload) {
    return std::visit(
        [&](const auto& value) -> uint64_t {
            using Payload = std::decay_t<decltype(value)>;
            uint64_t h = hash;
            if constexpr (std::is_same_v<Payload, InvalidTypePayload> ||
                          std::is_same_v<Payload, ErrorTypePayload> ||
                          std::is_same_v<Payload, PlaceholderTypePayload>) {

            } else if constexpr (std::is_same_v<Payload, UnknownTypePayload>) {
                h = hash_string(h, value.debug_name);
            } else if constexpr (std::is_same_v<Payload, BuiltinTypePayload>) {
                h = hash_mix(h, enum_value(value.kind));
                h = hash_string(h, value.spelling);
                h = hash_mix(h, static_cast<uint64_t>(value.width_override));
                h = hash_mix(h, static_cast<uint64_t>(value.rank_override));
                h = hash_mix(h,
                             static_cast<uint64_t>(value.unsigned_override));
            } else if constexpr (std::is_same_v<Payload, PointerTypePayload> ||
                                 std::is_same_v<Payload,
                                                BlockPointerTypePayload>) {
                h = hash_ref(h, value.pointee);
            } else if constexpr (std::is_same_v<Payload,
                                                MemberPointerTypePayload>) {
                h = hash_ref(h, value.class_type);
                h = hash_ref(h, value.member_type);
            } else if constexpr (std::is_same_v<Payload,
                                                ReferenceTypePayload>) {
                h = hash_mix(h, enum_value(value.reference_kind));
                h = hash_ref(h, value.referred_type);
            } else if constexpr (std::is_same_v<Payload, ArrayTypePayload>) {
                h = hash_ref(h, value.element_type);
                h = hash_mix(h, enum_value(value.size_kind));
                h = hash_mix(h, value.size.has_value());
                h = hash_mix(h, value.size.value_or(0));
                h = hash_mix(h, structural_id_value(value.size_expr));
                h = hash_mix(h, value.size_expr_is_dependent);
                h = hash_mix(h, value.extent_param);
                h = hash_template_value_expression(
                    h, value.dependent_size_expr);
            } else if constexpr (std::is_same_v<Payload,
                                                FunctionTypePayload>) {
                h = hash_ref(h, value.return_type);
                h = hash_mix(h, value.parameters.size());
                for (TypeRef parameter : value.parameters) {
                    h = hash_ref(h, parameter);
                }
                h = hash_mix(h, value.parameter_pack_flags.size());
                for (uint8_t flag : value.parameter_pack_flags) {
                    h = hash_mix(h, flag);
                }
                h = hash_mix(h, value.is_variadic);
                h = hash_mix(h, value.has_prototype);
                h = hash_mix(h, enum_value(value.member_ref_qualifier));
                h = hash_mix(h, value.member_is_const);
                h = hash_mix(h, value.member_is_volatile);
                h = hash_mix(h, enum_value(value.exception_spec.kind));
                h = hash_template_value_expression(
                    h, value.exception_spec.predicate);
                h = hash_mix(h, enum_value(value.calling_convention));
            } else if constexpr (std::is_same_v<Payload, RecordTypePayload>) {
                h = hash_mix(h, structural_id_value(value.entity));
                h = hash_mix(h, structural_id_value(value.name));
                h = hash_mix(h, value.is_union);
                h = hash_mix(h, value.is_incomplete);
            } else if constexpr (std::is_same_v<Payload, EnumTypePayload>) {
                h = hash_mix(h, structural_id_value(value.entity));
                h = hash_mix(h, structural_id_value(value.name));
                h = hash_mix(h, value.is_scoped);
                h = hash_mix(h, value.is_incomplete);
                h = hash_mix(h, value.has_fixed_underlying_type);
                h = hash_ref(h, value.underlying_type);
            } else if constexpr (std::is_same_v<Payload, VectorTypePayload>) {
                h = hash_ref(h, value.element_type);
                h = hash_mix(h, value.element_count);
                h = hash_mix(h, value.size_bytes);
            } else if constexpr (std::is_same_v<Payload, ComplexTypePayload>) {
                h = hash_ref(h, value.element_type);
            } else if constexpr (std::is_same_v<Payload, BitIntTypePayload>) {
                h = hash_mix(h, value.bits);
                h = hash_mix(h, value.is_unsigned);
            } else if constexpr (std::is_same_v<Payload, TypedefTypePayload>) {
                h = hash_mix(h, structural_id_value(value.entity));
                h = hash_mix(h, structural_id_value(value.name));
                h = hash_ref(h, value.underlying_type);
            } else if constexpr (std::is_same_v<Payload,
                                                TypeParamTypePayload>) {
                h = hash_mix(h, structural_id_value(value.entity));
                h = hash_mix(h, structural_id_value(value.name));
                h = hash_mix(h, value.depth);
                h = hash_mix(h, value.index);
                h = hash_mix(h, value.is_parameter_pack);
            } else if constexpr (std::is_same_v<
                                     Payload,
                                     TemplateSpecializationTypePayload>) {
                h = hash_mix(h, structural_id_value(value.template_name));
                h = hash_mix(h, structural_id_value(value.primary_template));
                h = hash_template_value_expression(h,
                                                   value.splice_operand);
                h = hash_mix(h, value.is_dependent);
                h = hash_mix(h, value.is_class_template_placeholder);
                h = hash_template_arguments(h, value.arguments);
            } else if constexpr (std::is_same_v<
                                     Payload,
                                     AliasSpecializationTypePayload>) {
                h = hash_mix(h, structural_id_value(value.template_name));
                h = hash_mix(h, structural_id_value(value.alias_template));
                h = hash_template_arguments(h, value.arguments);
                h = hash_ref(h, value.associated_type);
            } else if constexpr (std::is_same_v<Payload,
                                                DependentNameTypePayload>) {
                h = hash_ref(h, value.qualifier_type);
                h = hash_mix(h, structural_id_value(value.member_name));
                h = hash_mix(h, value.is_current_instantiation);
                h = hash_template_arguments(h, value.template_arguments);
            } else if constexpr (std::is_same_v<Payload,
                                                DependentTypePayload>) {
                h = hash_mix(h, structural_id_value(value.debug_name));
            } else if constexpr (std::is_same_v<Payload, AutoTypePayload>) {
                h = hash_mix(h, enum_value(value.flavor));
            } else if constexpr (std::is_same_v<Payload,
                                                TypeofExprTypePayload>) {
                h = hash_mix(h, structural_id_value(value.expr));
            } else if constexpr (std::is_same_v<Payload,
                                                DecltypeExprTypePayload>) {
                h = hash_mix(h, structural_id_value(value.expr));
                h = hash_mix(h, value.use_declared_type_rule);
                h = hash_mix(h, enum_value(value.operand_category));
                h = hash_ref(h, value.operand_type);
                h = hash_ref(h, value.dependent_value_qualifier);
                h = hash_mix(h,
                             structural_id_value(value.dependent_value_name));
                h = hash_template_value_expression(
                    h, value.operand_expression);
            } else if constexpr (std::is_same_v<
                                     Payload,
                                     BuiltinTypeTransformTypePayload>) {
                h = hash_mix(h, enum_value(value.transform_kind));
                h = hash_ref(h, value.operand_type);
            } else if constexpr (std::is_same_v<
                                     Payload,
                                     BuiltinPackElementTypePayload>) {
                h = hash_template_arguments(h, value.arguments);
            } else if constexpr (std::is_same_v<Payload,
                                                PackIndexTypePayload>) {
                h = hash_ref(h, value.pack_type);
                h = hash_template_value_expression(
                    h, value.index_expression);
                h = hash_mix(h, value.expansions.size());
                for (TypeRef expansion : value.expansions) {
                    h = hash_ref(h, expansion);
                }
                h = hash_mix(h, value.fully_substituted);
            } else if constexpr (std::is_same_v<Payload, PlaceTypePayload>) {
                h = hash_ref(h, value.object_type);
            }
            return h;
        },
        payload);
}

bool payload_fields_equal(const InvalidTypePayload&,
                          const InvalidTypePayload&) {
    return true;
}
bool payload_fields_equal(const ErrorTypePayload&, const ErrorTypePayload&) {
    return true;
}
bool payload_fields_equal(const PlaceholderTypePayload&,
                          const PlaceholderTypePayload&) {
    return true;
}
bool payload_fields_equal(const UnknownTypePayload& a,
                          const UnknownTypePayload& b) {
    return a.debug_name == b.debug_name;
}
bool payload_fields_equal(const BuiltinTypePayload& a,
                          const BuiltinTypePayload& b) {
    return a.kind == b.kind && a.spelling == b.spelling &&
           a.width_override == b.width_override &&
           a.rank_override == b.rank_override &&
           a.unsigned_override == b.unsigned_override;
}
bool payload_fields_equal(const PointerTypePayload& a,
                          const PointerTypePayload& b) {
    return refs_structurally_equal(a.pointee, b.pointee);
}
bool payload_fields_equal(const BlockPointerTypePayload& a,
                          const BlockPointerTypePayload& b) {
    return refs_structurally_equal(a.pointee, b.pointee);
}
bool payload_fields_equal(const MemberPointerTypePayload& a,
                          const MemberPointerTypePayload& b) {
    return refs_structurally_equal(a.class_type, b.class_type) &&
           refs_structurally_equal(a.member_type, b.member_type);
}
bool payload_fields_equal(const ReferenceTypePayload& a,
                          const ReferenceTypePayload& b) {
    return a.reference_kind == b.reference_kind &&
           refs_structurally_equal(a.referred_type, b.referred_type);
}
bool payload_fields_equal(const ArrayTypePayload& a,
                          const ArrayTypePayload& b) {
    return refs_structurally_equal(a.element_type, b.element_type) &&
           a.size_kind == b.size_kind && a.size == b.size &&
           ids_structurally_equal(a.size_expr, b.size_expr) &&
           a.size_expr_is_dependent == b.size_expr_is_dependent &&
           a.extent_param == b.extent_param &&
           template_value_exprs_structurally_equal(a.dependent_size_expr,
                                                    b.dependent_size_expr);
}
bool payload_fields_equal(const FunctionTypePayload& a,
                          const FunctionTypePayload& b) {
    if (!refs_structurally_equal(a.return_type, b.return_type) ||
        a.parameters.size() != b.parameters.size() ||
        a.parameter_pack_flags != b.parameter_pack_flags ||
        a.is_variadic != b.is_variadic ||
        a.has_prototype != b.has_prototype ||
        a.member_ref_qualifier != b.member_ref_qualifier ||
        a.member_is_const != b.member_is_const ||
        a.member_is_volatile != b.member_is_volatile ||
        a.exception_spec.kind != b.exception_spec.kind ||
        !template_value_exprs_structurally_equal(
            a.exception_spec.predicate, b.exception_spec.predicate) ||
        a.calling_convention != b.calling_convention) {
        return false;
    }
    for (size_t i = 0; i < a.parameters.size(); ++i) {
        if (!refs_structurally_equal(a.parameters[i], b.parameters[i])) {
            return false;
        }
    }
    return true;
}
bool payload_fields_equal(const RecordTypePayload& a,
                          const RecordTypePayload& b) {
    return ids_structurally_equal(a.entity, b.entity) &&
           ids_structurally_equal(a.name, b.name) &&
           a.is_union == b.is_union && a.is_incomplete == b.is_incomplete;
}
bool payload_fields_equal(const EnumTypePayload& a, const EnumTypePayload& b) {
    return ids_structurally_equal(a.entity, b.entity) &&
           ids_structurally_equal(a.name, b.name) &&
           a.is_scoped == b.is_scoped && a.is_incomplete == b.is_incomplete &&
           a.has_fixed_underlying_type == b.has_fixed_underlying_type &&
           refs_structurally_equal(a.underlying_type, b.underlying_type);
}
bool payload_fields_equal(const VectorTypePayload& a,
                          const VectorTypePayload& b) {
    return refs_structurally_equal(a.element_type, b.element_type) &&
           a.element_count == b.element_count && a.size_bytes == b.size_bytes;
}
bool payload_fields_equal(const ComplexTypePayload& a,
                          const ComplexTypePayload& b) {
    return refs_structurally_equal(a.element_type, b.element_type);
}
bool payload_fields_equal(const BitIntTypePayload& a,
                          const BitIntTypePayload& b) {
    return a.bits == b.bits && a.is_unsigned == b.is_unsigned;
}
bool payload_fields_equal(const TypedefTypePayload& a,
                          const TypedefTypePayload& b) {
    return ids_structurally_equal(a.entity, b.entity) &&
           ids_structurally_equal(a.name, b.name) &&
           refs_structurally_equal(a.underlying_type, b.underlying_type);
}
bool payload_fields_equal(const TypeParamTypePayload& a,
                          const TypeParamTypePayload& b) {
    return ids_structurally_equal(a.entity, b.entity) &&
           ids_structurally_equal(a.name, b.name) && a.depth == b.depth &&
           a.index == b.index && a.is_parameter_pack == b.is_parameter_pack;
}
bool payload_fields_equal(const TemplateSpecializationTypePayload& a,
                          const TemplateSpecializationTypePayload& b) {
    return ids_structurally_equal(a.template_name, b.template_name) &&
           ids_structurally_equal(a.primary_template, b.primary_template) &&
           template_value_expressions_structurally_equal(a.splice_operand,
                                                         b.splice_operand) &&
           a.is_dependent == b.is_dependent &&
           a.is_class_template_placeholder == b.is_class_template_placeholder &&
           template_argument_lists_structurally_equal(a.arguments,
                                                      b.arguments);
}
bool payload_fields_equal(const AliasSpecializationTypePayload& a,
                          const AliasSpecializationTypePayload& b) {
    return ids_structurally_equal(a.template_name, b.template_name) &&
           ids_structurally_equal(a.alias_template, b.alias_template) &&
           template_argument_lists_structurally_equal(a.arguments,
                                                      b.arguments) &&
           refs_structurally_equal(a.associated_type, b.associated_type);
}
bool payload_fields_equal(const DependentNameTypePayload& a,
                          const DependentNameTypePayload& b) {
    return refs_structurally_equal(a.qualifier_type, b.qualifier_type) &&
           ids_structurally_equal(a.member_name, b.member_name) &&
           a.is_current_instantiation == b.is_current_instantiation &&
           template_argument_lists_structurally_equal(a.template_arguments,
                                                      b.template_arguments);
}
bool payload_fields_equal(const DependentTypePayload& a,
                          const DependentTypePayload& b) {
    return ids_structurally_equal(a.debug_name, b.debug_name);
}
bool payload_fields_equal(const AutoTypePayload& a, const AutoTypePayload& b) {
    return a.flavor == b.flavor;
}
bool payload_fields_equal(const TypeofExprTypePayload& a,
                          const TypeofExprTypePayload& b) {
    return ids_structurally_equal(a.expr, b.expr);
}
bool payload_fields_equal(const DecltypeExprTypePayload& a,
                          const DecltypeExprTypePayload& b) {
    return ids_structurally_equal(a.expr, b.expr) &&
           a.use_declared_type_rule == b.use_declared_type_rule &&
           a.operand_category == b.operand_category &&
           refs_structurally_equal(a.operand_type, b.operand_type) &&
           refs_structurally_equal(a.dependent_value_qualifier,
                                   b.dependent_value_qualifier) &&
           ids_structurally_equal(a.dependent_value_name,
                                  b.dependent_value_name) &&
           template_value_exprs_structurally_equal(a.operand_expression,
                                                   b.operand_expression);
}
bool payload_fields_equal(const BuiltinTypeTransformTypePayload& a,
                          const BuiltinTypeTransformTypePayload& b) {
    return a.transform_kind == b.transform_kind &&
           refs_structurally_equal(a.operand_type, b.operand_type);
}
bool payload_fields_equal(const BuiltinPackElementTypePayload& a,
                          const BuiltinPackElementTypePayload& b) {
    return template_argument_lists_structurally_equal(a.arguments,
                                                      b.arguments);
}
bool payload_fields_equal(const PackIndexTypePayload& a,
                          const PackIndexTypePayload& b) {
    if (!refs_structurally_equal(a.pack_type, b.pack_type) ||
        !template_value_exprs_structurally_equal(a.index_expression,
                                                 b.index_expression) ||
        a.fully_substituted != b.fully_substituted ||
        a.expansions.size() != b.expansions.size()) {
        return false;
    }
    for (size_t i = 0; i < a.expansions.size(); ++i) {
        if (!refs_structurally_equal(a.expansions[i], b.expansions[i])) {
            return false;
        }
    }
    return true;
}
bool payload_fields_equal(const PlaceTypePayload& a,
                          const PlaceTypePayload& b) {
    return refs_structurally_equal(a.object_type, b.object_type);
}

} // namespace

uint64_t template_value_expression_structural_hash(
    const TemplateValueExpression& expression) {
    return hash_template_value_expression(0, expression);
}

bool template_value_expressions_structurally_equal(
    const TemplateValueExpression& lhs,
    const TemplateValueExpression& rhs) {
    return template_value_exprs_structurally_equal(lhs, rhs);
}

std::string_view type_kind_name(TypeKind kind) {
    switch (kind) {
        case TypeKind::Invalid: return "Invalid";
        case TypeKind::Error: return "Error";
        case TypeKind::Unknown: return "Unknown";
        case TypeKind::Builtin: return "Builtin";
        case TypeKind::Pointer: return "Pointer";
        case TypeKind::BlockPointer: return "BlockPointer";
        case TypeKind::MemberPointer: return "MemberPointer";
        case TypeKind::LValueReference: return "LValueReference";
        case TypeKind::RValueReference: return "RValueReference";
        case TypeKind::Array: return "Array";
        case TypeKind::Function: return "Function";
        case TypeKind::Record: return "Record";
        case TypeKind::Enum: return "Enum";
        case TypeKind::Vector: return "Vector";
        case TypeKind::Complex: return "Complex";
        case TypeKind::BitInt: return "BitInt";
        case TypeKind::Typedef: return "Typedef";
        case TypeKind::TypeParam: return "TypeParam";
        case TypeKind::TemplateSpecialization: return "TemplateSpecialization";
        case TypeKind::AliasSpecialization: return "AliasSpecialization";
        case TypeKind::DependentName: return "DependentName";
        case TypeKind::Dependent: return "Dependent";
        case TypeKind::Placeholder: return "Placeholder";
        case TypeKind::Auto: return "Auto";
        case TypeKind::TypeofExpr: return "TypeofExpr";
        case TypeKind::DecltypeExpr: return "DecltypeExpr";
        case TypeKind::BuiltinTransform: return "BuiltinTransform";
        case TypeKind::BuiltinPackElement: return "BuiltinPackElement";
        case TypeKind::PackIndex: return "PackIndex";
        case TypeKind::Place: return "Place";
    }
    return "UnknownTypeKind";
}

std::string_view memory_space_name(MemorySpace space) {
    switch (space) {
        case MemorySpace::Default: return "default";
        case MemorySpace::Generic: return "generic";
        case MemorySpace::Global: return "global";
        case MemorySpace::Constant: return "constant";
        case MemorySpace::Workgroup: return "workgroup";
        case MemorySpace::Private: return "private";
        case MemorySpace::Function: return "function";
    }
    return "unknown";
}

std::string_view builtin_type_kind_name(BuiltinTypeKind kind) {
    switch (kind) {
        case BuiltinTypeKind::Void: return "void";
        case BuiltinTypeKind::NullPtr: return "nullptr";
        case BuiltinTypeKind::MetaInfo: return "std::meta::info";
        case BuiltinTypeKind::Bool: return "bool";
        case BuiltinTypeKind::Char: return "char";
        case BuiltinTypeKind::SChar: return "signed char";
        case BuiltinTypeKind::UChar: return "unsigned char";
        case BuiltinTypeKind::WChar: return "wchar_t";
        case BuiltinTypeKind::Char8: return "char8_t";
        case BuiltinTypeKind::Char16: return "char16_t";
        case BuiltinTypeKind::Char32: return "char32_t";
        case BuiltinTypeKind::Short: return "short";
        case BuiltinTypeKind::UShort: return "unsigned short";
        case BuiltinTypeKind::Int: return "int";
        case BuiltinTypeKind::UInt: return "unsigned int";
        case BuiltinTypeKind::Long: return "long";
        case BuiltinTypeKind::ULong: return "unsigned long";
        case BuiltinTypeKind::LongLong: return "long long";
        case BuiltinTypeKind::ULongLong: return "unsigned long long";
        case BuiltinTypeKind::Int128: return "__int128";
        case BuiltinTypeKind::UInt128: return "unsigned __int128";
        case BuiltinTypeKind::USize: return "usize";
        case BuiltinTypeKind::Float16: return "_Float16";
        case BuiltinTypeKind::Float: return "float";
        case BuiltinTypeKind::Double: return "double";
        case BuiltinTypeKind::LongDouble: return "long double";
        case BuiltinTypeKind::Other: return "other";
    }
    return "other";
}

TypeKind type_payload_kind(const TypePayload& payload) {
    return std::visit(
        [](const auto& value) {
            using Payload = std::decay_t<decltype(value)>;
            if constexpr (std::is_same_v<Payload, InvalidTypePayload>) {
                return TypeKind::Invalid;
            } else if constexpr (std::is_same_v<Payload, ErrorTypePayload>) {
                return TypeKind::Error;
            } else if constexpr (std::is_same_v<Payload, UnknownTypePayload>) {
                return TypeKind::Unknown;
            } else if constexpr (std::is_same_v<Payload, BuiltinTypePayload>) {
                return TypeKind::Builtin;
            } else if constexpr (std::is_same_v<Payload, PointerTypePayload>) {
                return TypeKind::Pointer;
            } else if constexpr (std::is_same_v<Payload, BlockPointerTypePayload>) {
                return TypeKind::BlockPointer;
            } else if constexpr (std::is_same_v<Payload, MemberPointerTypePayload>) {
                return TypeKind::MemberPointer;
            } else if constexpr (std::is_same_v<Payload, ReferenceTypePayload>) {
                return value.reference_kind == ReferenceKind::LValue
                    ? TypeKind::LValueReference
                    : TypeKind::RValueReference;
            } else if constexpr (std::is_same_v<Payload, ArrayTypePayload>) {
                return TypeKind::Array;
            } else if constexpr (std::is_same_v<Payload, FunctionTypePayload>) {
                return TypeKind::Function;
            } else if constexpr (std::is_same_v<Payload, RecordTypePayload>) {
                return TypeKind::Record;
            } else if constexpr (std::is_same_v<Payload, EnumTypePayload>) {
                return TypeKind::Enum;
            } else if constexpr (std::is_same_v<Payload, VectorTypePayload>) {
                return TypeKind::Vector;
            } else if constexpr (std::is_same_v<Payload, ComplexTypePayload>) {
                return TypeKind::Complex;
            } else if constexpr (std::is_same_v<Payload, BitIntTypePayload>) {
                return TypeKind::BitInt;
            } else if constexpr (std::is_same_v<Payload, TypedefTypePayload>) {
                return TypeKind::Typedef;
            } else if constexpr (std::is_same_v<Payload, TypeParamTypePayload>) {
                return TypeKind::TypeParam;
            } else if constexpr (std::is_same_v<Payload, TemplateSpecializationTypePayload>) {
                return TypeKind::TemplateSpecialization;
            } else if constexpr (std::is_same_v<Payload, AliasSpecializationTypePayload>) {
                return TypeKind::AliasSpecialization;
            } else if constexpr (std::is_same_v<Payload, DependentNameTypePayload>) {
                return TypeKind::DependentName;
            } else if constexpr (std::is_same_v<Payload, DependentTypePayload>) {
                return TypeKind::Dependent;
            } else if constexpr (std::is_same_v<Payload, PlaceholderTypePayload>) {
                return TypeKind::Placeholder;
            } else if constexpr (std::is_same_v<Payload, AutoTypePayload>) {
                return TypeKind::Auto;
            } else if constexpr (std::is_same_v<Payload, TypeofExprTypePayload>) {
                return TypeKind::TypeofExpr;
            } else if constexpr (std::is_same_v<Payload, DecltypeExprTypePayload>) {
                return TypeKind::DecltypeExpr;
            } else if constexpr (std::is_same_v<Payload, BuiltinTypeTransformTypePayload>) {
                return TypeKind::BuiltinTransform;
            } else if constexpr (std::is_same_v<Payload, BuiltinPackElementTypePayload>) {
                return TypeKind::BuiltinPackElement;
            } else if constexpr (std::is_same_v<Payload, PackIndexTypePayload>) {
                return TypeKind::PackIndex;
            } else {
                return TypeKind::Place;
            }
        },
        payload);
}

bool type_spec_matches_payload(const TypeSpec& spec) {
    return type_payload_kind(spec.payload) == spec.kind;
}

std::string type_ref_structural_key(TypeRef ref) {
    std::ostringstream out;
    append_ref(out, ref);
    return out.str();
}

std::string type_structural_key(const TypeSpec& spec) {
    std::ostringstream out;
    out << enum_value(spec.kind) << '|';
    std::visit(
        [&](const auto& payload) {
            using Payload = std::decay_t<decltype(payload)>;
            if constexpr (std::is_same_v<Payload, InvalidTypePayload> ||
                          std::is_same_v<Payload, ErrorTypePayload> ||
                          std::is_same_v<Payload, PlaceholderTypePayload>) {
                out << "empty";
            } else if constexpr (std::is_same_v<Payload, UnknownTypePayload>) {
                out << payload.debug_name;
            } else if constexpr (std::is_same_v<Payload, BuiltinTypePayload>) {
                out << enum_value(payload.kind) << ',' << payload.spelling
                    << ',' << payload.width_override << ','
                    << payload.rank_override << ','
                    << static_cast<int>(payload.unsigned_override);
            } else if constexpr (std::is_same_v<Payload, PointerTypePayload>) {
                append_ref(out, payload.pointee);
            } else if constexpr (std::is_same_v<Payload, BlockPointerTypePayload>) {
                append_ref(out, payload.pointee);
            } else if constexpr (std::is_same_v<Payload, MemberPointerTypePayload>) {
                append_ref(out, payload.class_type);
                out << ',';
                append_ref(out, payload.member_type);
            } else if constexpr (std::is_same_v<Payload, ReferenceTypePayload>) {
                out << enum_value(payload.reference_kind) << ',';
                append_ref(out, payload.referred_type);
            } else if constexpr (std::is_same_v<Payload, ArrayTypePayload>) {
                append_ref(out, payload.element_type);
                out << ',' << enum_value(payload.size_kind) << ',';
                if (payload.size.has_value()) {
                    out << *payload.size;
                }
                out << ',';
                append_id(out, payload.size_expr);
                out << ',' << payload.size_expr_is_dependent;
                out << ',' << payload.extent_param;
                out << ',';
                append_template_value_expression(
                    out, payload.dependent_size_expr);
            } else if constexpr (std::is_same_v<Payload, FunctionTypePayload>) {
                append_ref(out, payload.return_type);
                out << '(';
                for (TypeRef parameter : payload.parameters) {
                    append_ref(out, parameter);
                    out << ';';
                }
                out << ")packs(";
                for (auto flag : payload.parameter_pack_flags) {
                    out << static_cast<unsigned>(flag) << ';';
                }
                out << ")," << payload.is_variadic << ','
                    << payload.has_prototype << ','
                    << enum_value(payload.member_ref_qualifier) << ','
                    << payload.member_is_const << ','
                    << payload.member_is_volatile << ','
                    << enum_value(payload.exception_spec.kind) << ',';
                append_template_value_expression(
                    out, payload.exception_spec.predicate);
                out << ',' << enum_value(payload.calling_convention);
            } else if constexpr (std::is_same_v<Payload, RecordTypePayload>) {
                append_id(out, payload.entity);
                out << ',';
                append_id(out, payload.name);
                out << ',' << payload.is_union << ',' << payload.is_incomplete;
            } else if constexpr (std::is_same_v<Payload, EnumTypePayload>) {
                append_id(out, payload.entity);
                out << ',';
                append_id(out, payload.name);
                out << ',' << payload.is_scoped << ',' << payload.is_incomplete
                    << ',' << payload.has_fixed_underlying_type << ',';
                append_ref(out, payload.underlying_type);
            } else if constexpr (std::is_same_v<Payload, VectorTypePayload>) {
                append_ref(out, payload.element_type);
                out << ',' << payload.element_count << ',' << payload.size_bytes;
            } else if constexpr (std::is_same_v<Payload, ComplexTypePayload>) {
                append_ref(out, payload.element_type);
            } else if constexpr (std::is_same_v<Payload, BitIntTypePayload>) {
                out << payload.bits << ',' << payload.is_unsigned;
            } else if constexpr (std::is_same_v<Payload, TypedefTypePayload>) {
                append_id(out, payload.entity);
                out << ',';
                append_id(out, payload.name);
                out << ',';
                append_ref(out, payload.underlying_type);
            } else if constexpr (std::is_same_v<Payload, TypeParamTypePayload>) {
                append_id(out, payload.entity);
                out << ',';
                append_id(out, payload.name);
                out << ',' << payload.depth << ',' << payload.index << ','
                    << payload.is_parameter_pack;
            } else if constexpr (std::is_same_v<Payload, TemplateSpecializationTypePayload>) {
                append_id(out, payload.template_name);
                out << ',';
                append_id(out, payload.primary_template);
                out << ',';
                append_template_value_expression(out,
                                                 payload.splice_operand);
                out << ',' << payload.is_dependent << ','
                    << payload.is_class_template_placeholder << ',';
                append_template_arguments(out, payload.arguments);
            } else if constexpr (std::is_same_v<Payload, AliasSpecializationTypePayload>) {
                append_id(out, payload.template_name);
                out << ',';
                append_id(out, payload.alias_template);
                out << ',';
                append_template_arguments(out, payload.arguments);
                out << ',';
                append_ref(out, payload.associated_type);
            } else if constexpr (std::is_same_v<Payload, DependentNameTypePayload>) {
                append_ref(out, payload.qualifier_type);
                out << ',';
                append_id(out, payload.member_name);
                out << ',' << payload.is_current_instantiation << ',';
                append_template_arguments(out, payload.template_arguments);
            } else if constexpr (std::is_same_v<Payload, DependentTypePayload>) {
                append_id(out, payload.debug_name);
            } else if constexpr (std::is_same_v<Payload, AutoTypePayload>) {
                out << enum_value(payload.flavor);
            } else if constexpr (std::is_same_v<Payload, TypeofExprTypePayload>) {
                append_id(out, payload.expr);
            } else if constexpr (std::is_same_v<Payload, DecltypeExprTypePayload>) {
                append_id(out, payload.expr);
                out << ',' << payload.use_declared_type_rule << ','
                    << enum_value(payload.operand_category) << ',';
                append_ref(out, payload.operand_type);
                out << ',';
                append_ref(out, payload.dependent_value_qualifier);
                out << ',';
                append_id(out, payload.dependent_value_name);
                out << ',';
                append_template_value_expression(
                    out, payload.operand_expression);
            } else if constexpr (std::is_same_v<Payload, BuiltinTypeTransformTypePayload>) {
                out << enum_value(payload.transform_kind) << ',';
                append_ref(out, payload.operand_type);
            } else if constexpr (std::is_same_v<Payload, BuiltinPackElementTypePayload>) {
                append_template_arguments(out, payload.arguments);
            } else if constexpr (std::is_same_v<Payload, PackIndexTypePayload>) {
                append_ref(out, payload.pack_type);
                out << ',';
                append_template_value_expression(
                    out, payload.index_expression);
                out << ",[";
                for (TypeRef expansion : payload.expansions) {
                    append_ref(out, expansion);
                    out << ';';
                }
                out << "]," << payload.fully_substituted;
            } else if constexpr (std::is_same_v<Payload, PlaceTypePayload>) {
                append_ref(out, payload.object_type);
            }
        },
        spec.payload);
    if (spec.canonical.valid()) {
        out << "|canon:";
        append_id(out, spec.canonical);
    }
    if (spec.desugared.valid()) {
        out << "|desugar:";
        append_id(out, spec.desugared);
    }
    if (spec.resolved.valid()) {
        out << "|resolved:";
        append_id(out, spec.resolved);
    }
    return out.str();
}

uint64_t type_spec_hash(const TypeSpec& spec) {
    uint64_t hash = hash_mix(0, enum_value(spec.kind));
    hash = hash_payload(hash, spec.payload);
    hash = hash_mix(hash, structural_id_value(spec.canonical));
    hash = hash_mix(hash, structural_id_value(spec.desugared));
    hash = hash_mix(hash, structural_id_value(spec.resolved));
    return hash;
}

bool type_payloads_structurally_equal(const TypePayload& lhs,
                                      const TypePayload& rhs) {
    if (lhs.index() != rhs.index()) {
        return false;
    }
    return std::visit(
        [&](const auto& a) {
            using Payload = std::decay_t<decltype(a)>;
            return payload_fields_equal(a, std::get<Payload>(rhs));
        },
        lhs);
}

BuiltinTypeKind builtin_type_kind_from_spelling(std::string_view spelling) {
    if (spelling == "void") return BuiltinTypeKind::Void;
    if (spelling == "nullptr") return BuiltinTypeKind::NullPtr;
    if (spelling == "std::meta::info") return BuiltinTypeKind::MetaInfo;
    if (spelling == "bool" || spelling == "_Bool") return BuiltinTypeKind::Bool;
    if (spelling == "char") return BuiltinTypeKind::Char;
    if (spelling == "signed char") return BuiltinTypeKind::SChar;
    if (spelling == "unsigned char") return BuiltinTypeKind::UChar;
    if (spelling == "wchar_t") return BuiltinTypeKind::WChar;
    if (spelling == "char8_t") return BuiltinTypeKind::Char8;
    if (spelling == "char16_t") return BuiltinTypeKind::Char16;
    if (spelling == "char32_t") return BuiltinTypeKind::Char32;
    if (spelling == "short") return BuiltinTypeKind::Short;
    if (spelling == "unsigned short") return BuiltinTypeKind::UShort;
    if (spelling == "int") return BuiltinTypeKind::Int;
    if (spelling == "unsigned int" || spelling == "uint") return BuiltinTypeKind::UInt;
    if (spelling == "long") return BuiltinTypeKind::Long;
    if (spelling == "unsigned long") return BuiltinTypeKind::ULong;
    if (spelling == "long long") return BuiltinTypeKind::LongLong;
    if (spelling == "unsigned long long") return BuiltinTypeKind::ULongLong;
    if (spelling == "__int128") return BuiltinTypeKind::Int128;
    if (spelling == "unsigned __int128") return BuiltinTypeKind::UInt128;
    if (spelling == "usize" || spelling == "size_t") return BuiltinTypeKind::USize;
    if (spelling == "_Float16") return BuiltinTypeKind::Float16;
    if (spelling == "float") return BuiltinTypeKind::Float;
    if (spelling == "double") return BuiltinTypeKind::Double;
    if (spelling == "long double") return BuiltinTypeKind::LongDouble;
    return BuiltinTypeKind::Other;
}

} // namespace aburi::cir
