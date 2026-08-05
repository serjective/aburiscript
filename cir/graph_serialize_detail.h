#ifndef ABURI_CIR_GRAPH_SERIALIZE_DETAIL_H
#define ABURI_CIR_GRAPH_SERIALIZE_DETAIL_H

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "../libaburi/serialize/format.h"
#include "../source_mgnt.h"
#include "ids.h"
#include "type.h"

namespace aburi::cir::graph_detail {

using serialize::ByteReader;
using serialize::ByteWriter;

inline constexpr uint32_t max_serialized_elements = 1u << 28;

inline void write_u8(ByteWriter& writer, uint8_t value) {
    writer.u8(value);
}

inline bool read_u8(ByteReader& reader, uint8_t* value) {

    std::string_view view = reader.raw(1);
    if (!reader.ok()) {
        *value = 0;
        return false;
    }
    *value = static_cast<uint8_t>(view[0]);
    return true;
}

inline void write_u16(ByteWriter& writer, uint16_t value) {
    writer.u16(value);
}

inline bool read_u16(ByteReader& reader, uint16_t* value) {
    *value = reader.u16();
    return reader.ok();
}

inline void write_u32(ByteWriter& writer, uint32_t value) {
    writer.u32(value);
}

inline bool read_u32(ByteReader& reader, uint32_t* value) {
    *value = reader.u32();
    return reader.ok();
}

inline void write_u64(ByteWriter& writer, uint64_t value) {
    writer.u64(value);
}

inline bool read_u64(ByteReader& reader, uint64_t* value) {
    *value = reader.u64();
    return reader.ok();
}

inline void write_i64(ByteWriter& writer, int64_t value) {
    writer.u64(static_cast<uint64_t>(value));
}

inline bool read_i64(ByteReader& reader, int64_t* value) {
    *value = static_cast<int64_t>(reader.u64());
    return reader.ok();
}

inline void write_string(ByteWriter& writer, std::string_view value) {
    writer.sized_string(value);
}

inline bool read_string(ByteReader& reader, std::string* value) {
    std::string_view view = reader.sized_string();
    if (!reader.ok()) {
        return false;
    }
    value->assign(view);
    return true;
}

template <typename IdT>
void write_id(ByteWriter& writer, IdT id) {
    writer.u32(id.index);
    writer.u32(id.generation);
}

template <typename IdT>
bool read_id(ByteReader& reader, IdT* id) {
    id->index = reader.u32();
    id->generation = reader.u32();
    return reader.ok();
}

inline void write_srcloc(ByteWriter& writer, SrcLoc loc) {
    writer.u32(loc.offset);
}

inline bool read_srcloc(ByteReader& reader, SrcLoc* loc) {
    loc->offset = reader.u32();
    return reader.ok();
}

inline void write_type_ref(ByteWriter& writer, const TypeRef& ref) {
    write_id(writer, ref.type);
    writer.u8(ref.qualifiers);
    writer.u32(static_cast<uint32_t>(ref.memory_space));
}

inline bool read_type_ref(ByteReader& reader, TypeRef* ref) {
    if (!read_id(reader, &ref->type) || !read_u8(reader, &ref->qualifiers)) {
        return false;
    }
    ref->memory_space = static_cast<MemorySpace>(reader.u32());
    return reader.ok();
}

inline void write_floating(ByteWriter& writer, const FloatingValue& value) {
    writer.u32(static_cast<uint32_t>(value.semantics));
    writer.u64(value.low_bits);
    writer.u64(value.high_bits);
}

inline bool read_floating(ByteReader& reader, FloatingValue* value) {
    value->semantics = static_cast<FloatingSemantics>(reader.u32());
    value->low_bits = reader.u64();
    value->high_bits = reader.u64();
    return reader.ok();
}

inline void write_integer(ByteWriter& writer, const IntegerValue& value) {
    writer.u64(value.low_bits);
    writer.u64(value.high_bits);
    writer.u16(value.bit_width);
    writer.u8(value.is_unsigned ? 1 : 0);
}

inline bool read_integer(ByteReader& reader, IntegerValue* value) {
    value->low_bits = reader.u64();
    value->high_bits = reader.u64();
    value->bit_width = reader.u16();
    uint8_t is_unsigned = 0;
    if (!read_u8(reader, &is_unsigned)) {
        return false;
    }
    value->is_unsigned = is_unsigned != 0;
    return reader.ok() && value->canonical();
}

inline void write_value_pack_reference(
    ByteWriter& writer,
    const TemplateValuePackReference& reference) {
    writer.u32(static_cast<uint32_t>(reference.kind));
    write_id(writer, reference.declaration);
    write_id(writer, reference.owner);
    writer.u32(reference.depth);
    writer.u32(reference.index);
    write_id(writer, reference.parameter_type);
    write_id(writer, reference.name);
}

inline bool read_value_pack_reference(
    ByteReader& reader,
    TemplateValuePackReference* reference) {
    reference->kind =
        static_cast<TemplateValuePackKind>(reader.u32());
    return read_id(reader, &reference->declaration) &&
           read_id(reader, &reference->owner) &&
           read_u32(reader, &reference->depth) &&
           read_u32(reader, &reference->index) &&
           read_id(reader, &reference->parameter_type) &&
           read_id(reader, &reference->name);
}

template <typename T, typename Fn>
void write_vector(ByteWriter& writer, const std::vector<T>& values, Fn fn) {
    writer.u32(static_cast<uint32_t>(values.size()));
    for (const T& value : values) {
        fn(writer, value);
    }
}

template <typename T, typename Fn>
bool read_vector(ByteReader& reader, std::vector<T>* values, Fn fn) {
    uint32_t count = reader.u32();
    if (!reader.ok() || count > max_serialized_elements) {
        return false;
    }
    values->clear();
    for (uint32_t index = 0; index < count; ++index) {
        T value{};
        if (!fn(reader, &value)) {
            return false;
        }
        values->push_back(std::move(value));
    }
    return true;
}

inline void write_template_argument(ByteWriter& writer,
                                    const cir::TemplateArgument& argument);
inline bool read_template_argument(ByteReader& reader,
                                   cir::TemplateArgument* argument);

inline void write_value_expr_node(ByteWriter& writer,
                                  const TemplateValueExprNode& node) {
    writer.u32(static_cast<uint32_t>(node.kind));
    writer.u32(static_cast<uint32_t>(node.op));
    writer.u32(static_cast<uint32_t>(node.trait_kind));
    writer.u32(static_cast<uint32_t>(node.fold_kind));
    write_i64(writer, node.value);
    write_integer(writer, node.integer_value);
    writer.u32(node.parameter_index);
    writer.u32(node.lhs);
    writer.u32(node.rhs);
    writer.u32(node.third);
    write_vector(writer, node.operands,
                 [](ByteWriter& w, uint32_t operand) { w.u32(operand); });
    writer.u8(node.expands_parameter_pack ? 1 : 0);
    write_vector(writer, node.pack_references,
                 [](ByteWriter& w,
                    const TemplateValuePackReference& reference) {
                     write_value_pack_reference(w, reference);
                 });
    write_vector(writer, node.template_arguments.values(),
                 [](ByteWriter& w, const TemplateArgument& argument) {
                     write_template_argument(w, argument);
                 });
    write_id(writer, node.type);
    write_type_ref(writer, node.result_type);
    write_id(writer, node.entity);
    write_id(writer, node.name);
    write_type_ref(writer, node.qualifier_type);
    write_string(writer, node.semantic_key);
}

inline bool read_value_expr_node(ByteReader& reader,
                                 TemplateValueExprNode* node) {
    node->kind = static_cast<TemplateValueExprKind>(reader.u32());
    node->op = static_cast<TemplateValueExprOp>(reader.u32());
    node->trait_kind = static_cast<BuiltinTypeTraitKind>(reader.u32());
    node->fold_kind = static_cast<TemplateValueFoldKind>(reader.u32());
    if (!read_i64(reader, &node->value) ||
        !read_integer(reader, &node->integer_value)) {
        return false;
    }
    node->parameter_index = reader.u32();
    node->lhs = reader.u32();
    node->rhs = reader.u32();
    node->third = reader.u32();
    if (!read_vector(reader, &node->operands,
                     [](ByteReader& r, uint32_t* operand) {
                         return read_u32(r, operand);
                     })) {
        return false;
    }
    uint8_t expands = 0;
    if (!read_u8(reader, &expands)) {
        return false;
    }
    node->expands_parameter_pack = expands != 0;
    if (!read_vector(reader, &node->pack_references,
                     [](ByteReader& r,
                        TemplateValuePackReference* reference) {
                         return read_value_pack_reference(r, reference);
                     })) {
        return false;
    }
    if (!read_vector(reader, &node->template_arguments.values(),
                     [](ByteReader& r, TemplateArgument* argument) {
                         return read_template_argument(r, argument);
                     })) {
        return false;
    }
    return read_id(reader, &node->type) &&
           read_type_ref(reader, &node->result_type) &&
           read_id(reader, &node->entity) &&
           read_id(reader, &node->name) &&
           read_type_ref(reader, &node->qualifier_type) &&
           read_string(reader, &node->semantic_key);
}

inline void write_value_expression(ByteWriter& writer,
                                   const TemplateValueExpression& expression) {
    write_vector(writer, expression.nodes,
                 [](ByteWriter& w, const TemplateValueExprNode& node) {
                     write_value_expr_node(w, node);
                 });
    writer.u32(expression.root);
    write_id(writer, expression.canonical_id);
    write_srcloc(writer, expression.loc);
    write_id(writer, expression.definition_context);
    writer.u64(expression.definition_lookup_generation);
}

inline bool read_value_expression(ByteReader& reader,
                                  TemplateValueExpression* expression) {
    if (!read_vector(reader, &expression->nodes,
                     [](ByteReader& r, TemplateValueExprNode* node) {
                         return read_value_expr_node(r, node);
                     })) {
        return false;
    }
    expression->root = reader.u32();
    return read_id(reader, &expression->canonical_id) &&
           read_srcloc(reader, &expression->loc) &&
           read_id(reader, &expression->definition_context) &&
           read_u64(reader, &expression->definition_lookup_generation);
}

inline void write_template_argument(ByteWriter& writer,
                                    const cir::TemplateArgument& argument) {
    writer.u32(static_cast<uint32_t>(argument.kind));
    write_type_ref(writer, argument.type);
    write_type_ref(writer, argument.value_type);
    writer.u32(static_cast<uint32_t>(argument.value_kind));
    writer.u32(static_cast<uint32_t>(argument.null_kind));
    write_integer(writer, argument.integer_value);
    write_floating(writer, argument.floating_value);
    write_string(writer, argument.value_spelling);
    write_id(writer, argument.value_entity);
    write_id(writer, argument.closure_identity);
    write_i64(writer, argument.value_byte_offset);
    writer.u32(static_cast<uint32_t>(argument.meta_kind));
    write_vector(writer, argument.value_elements,
                 [](ByteWriter& w, const cir::TemplateArgument& element) {
                     write_template_argument(w, element);
                 });
    writer.u32(argument.value_param_index);
    write_value_expression(writer, argument.dependent_value_expr);
    writer.u32(static_cast<uint32_t>(argument.generated_pack_kind));
    write_type_ref(writer, argument.generated_pack_count_type);
    write_value_expression(writer, argument.generated_pack_count_expr);
    write_type_ref(writer, argument.dependent_value_qualifier);
    write_id(writer, argument.dependent_value_name);
    write_id(writer, argument.template_entity);
    writer.u32(argument.template_param_index);
    write_type_ref(writer, argument.dependent_template_qualifier);
    writer.u8(argument.is_dependent ? 1 : 0);
    writer.u8(argument.is_defaulted ? 1 : 0);
    writer.u8(argument.expands_parameter_pack ? 1 : 0);
    writer.u8(argument.expands_pack_pattern ? 1 : 0);
    write_id(writer, argument.template_name);
    writer.u8(argument.unconverted_value_alternative ? 1 : 0);
    if (argument.unconverted_value_alternative) {
        write_template_argument(writer, *argument.unconverted_value_alternative);
    }
    write_id(writer, argument.constant_state);
}

inline bool read_template_argument(ByteReader& reader,
                                   cir::TemplateArgument* argument) {
    argument->kind = static_cast<TemplateArgumentKind>(reader.u32());
    if (!read_type_ref(reader, &argument->type) ||
        !read_type_ref(reader, &argument->value_type)) {
        return false;
    }
    argument->value_kind = static_cast<TemplateValueKind>(reader.u32());
    argument->null_kind = static_cast<TemplateNullKind>(reader.u32());
    if (!read_integer(reader, &argument->integer_value) ||
        !read_floating(reader, &argument->floating_value) ||
        !read_string(reader, &argument->value_spelling) ||
        !read_id(reader, &argument->value_entity) ||
        !read_id(reader, &argument->closure_identity) ||
        !read_i64(reader, &argument->value_byte_offset)) {
        return false;
    }
    argument->meta_kind = static_cast<MetaInfoKind>(reader.u32());
    if (!read_vector(reader, &argument->value_elements,
                     [](ByteReader& r, cir::TemplateArgument* element) {
                         return read_template_argument(r, element);
                     })) {
        return false;
    }
    argument->value_param_index = reader.u32();
    if (!read_value_expression(reader, &argument->dependent_value_expr)) {
        return false;
    }
    argument->generated_pack_kind =
        static_cast<TemplateGeneratedPackKind>(reader.u32());
    if (!read_type_ref(reader, &argument->generated_pack_count_type) ||
        !read_value_expression(reader, &argument->generated_pack_count_expr) ||
        !read_type_ref(reader, &argument->dependent_value_qualifier) ||
        !read_id(reader, &argument->dependent_value_name) ||
        !read_id(reader, &argument->template_entity)) {
        return false;
    }
    argument->template_param_index = reader.u32();
    if (!read_type_ref(reader, &argument->dependent_template_qualifier)) {
        return false;
    }
    uint8_t flags[4] = {0, 0, 0, 0};
    for (uint8_t& flag : flags) {
        if (!read_u8(reader, &flag)) {
            return false;
        }
    }
    argument->is_dependent = flags[0] != 0;
    argument->is_defaulted = flags[1] != 0;
    argument->expands_parameter_pack = flags[2] != 0;
    argument->expands_pack_pattern = flags[3] != 0;
    if (!read_id(reader, &argument->template_name)) {
        return false;
    }
    uint8_t has_alternative = 0;
    if (!read_u8(reader, &has_alternative)) {
        return false;
    }
    if (has_alternative != 0) {
        auto alternative = std::make_shared<cir::TemplateArgument>();
        if (!read_template_argument(reader, alternative.get())) {
            return false;
        }
        argument->unconverted_value_alternative = std::move(alternative);
    } else {
        argument->unconverted_value_alternative.reset();
    }
    return read_id(reader, &argument->constant_state);
}

} // namespace aburi::cir::graph_detail

#endif // ABURI_CIR_GRAPH_SERIALIZE_DETAIL_H
