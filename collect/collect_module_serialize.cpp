

#include "collect.h"

#include <algorithm>
#include <bit>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "../attributes.h"
#include "../cir/graph_serialize.h"
#include "../cir/graph_serialize_detail.h"
#include "collect_template_state.h"

namespace aburi::collect {

namespace {

namespace detail = cir::graph_detail;

using serialize::ByteReader;
using serialize::ByteWriter;

constexpr uint32_t template_state_magic = 0x4C504D54u;

constexpr uint64_t max_serialized_map_entries = 1ull << 26;

void write_bool(ByteWriter& writer, bool value) {
    writer.u8(value ? 1 : 0);
}

bool read_bool(ByteReader& reader, bool* value) {
    uint8_t byte = 0;
    if (!detail::read_u8(reader, &byte)) {
        return false;
    }
    *value = byte != 0;
    return true;
}

template <typename EnumT>
void write_enum(ByteWriter& writer, EnumT value) {
    writer.u32(static_cast<uint32_t>(value));
}

template <typename EnumT>
bool read_enum(ByteReader& reader, EnumT* value) {
    uint32_t raw = 0;
    if (!detail::read_u32(reader, &raw)) {
        return false;
    }
    *value = static_cast<EnumT>(raw);
    return true;
}

void write_size(ByteWriter& writer, size_t value) {
    writer.u64(static_cast<uint64_t>(value));
}

bool read_size(ByteReader& reader, size_t* value) {
    uint64_t raw = 0;
    if (!detail::read_u64(reader, &raw)) {
        return false;
    }
    *value = static_cast<size_t>(raw);
    return true;
}

template <typename T, typename Fn>
void write_optional(ByteWriter& writer,
                    const std::optional<T>& value,
                    Fn fn) {
    write_bool(writer, value.has_value());
    if (value.has_value()) {
        fn(writer, *value);
    }
}

template <typename T, typename Fn>
bool read_optional(ByteReader& reader, std::optional<T>* value, Fn fn) {
    bool present = false;
    if (!read_bool(reader, &present)) {
        return false;
    }
    if (!present) {
        value->reset();
        return true;
    }
    T item{};
    if (!fn(reader, &item)) {
        return false;
    }
    *value = std::move(item);
    return true;
}

template <typename MapT, typename WriteKey, typename WriteValue>
void write_sorted_map(ByteWriter& writer,
                      const MapT& map,
                      WriteKey write_key,
                      WriteValue write_value) {
    writer.u64(static_cast<uint64_t>(map.size()));
    std::vector<const typename MapT::value_type*> entries;
    entries.reserve(map.size());
    for (const auto& entry : map) {
        entries.push_back(&entry);
    }
    std::sort(entries.begin(), entries.end(),
              [](const auto* lhs, const auto* rhs) {
                  return lhs->first < rhs->first;
              });
    for (const auto* entry : entries) {
        write_key(writer, entry->first);
        write_value(writer, entry->second);
    }
}

template <typename MapT, typename ReadKey, typename ReadValue>
bool read_map(ByteReader& reader,
              MapT* map,
              ReadKey read_key,
              ReadValue read_value) {
    uint64_t count = 0;
    if (!detail::read_u64(reader, &count) ||
        count > max_serialized_map_entries) {
        return false;
    }
    map->clear();
    for (uint64_t index = 0; index < count; ++index) {
        typename MapT::key_type key{};
        if (!read_key(reader, &key)) {
            return false;
        }
        typename MapT::mapped_type value{};
        if (!read_value(reader, &value)) {
            return false;
        }
        map->emplace(std::move(key), std::move(value));
    }
    return true;
}

void write_u64_key(ByteWriter& writer, uint64_t key) {
    writer.u64(key);
}

bool read_u64_key(ByteReader& reader, uint64_t* key) {
    return detail::read_u64(reader, key);
}

void write_string_key(ByteWriter& writer, const std::string& key) {
    detail::write_string(writer, key);
}

bool read_string_key(ByteReader& reader, std::string* key) {
    return detail::read_string(reader, key);
}

void write_argument(ByteWriter& writer,
                    const cir::TemplateArgument& argument) {
    detail::write_template_argument(writer, argument);
}

bool read_argument(ByteReader& reader, cir::TemplateArgument* argument) {
    return detail::read_template_argument(reader, argument);
}

void write_arguments(ByteWriter& writer,
                     const std::vector<cir::TemplateArgument>& arguments) {
    detail::write_vector(writer, arguments, write_argument);
}

bool read_arguments(ByteReader& reader,
                    std::vector<cir::TemplateArgument>* arguments) {
    return detail::read_vector(reader, arguments, read_argument);
}

void write_argument_pack(
    ByteWriter& writer,
    const std::optional<std::vector<cir::TemplateArgument>>& pack) {
    write_optional(writer, pack, write_arguments);
}

bool read_argument_pack(
    ByteReader& reader,
    std::optional<std::vector<cir::TemplateArgument>>* pack) {
    return read_optional(reader, pack, read_arguments);
}

void write_u32_vector(ByteWriter& writer,
                      const std::vector<uint32_t>& values) {
    detail::write_vector(writer, values,
                         [](ByteWriter& w, uint32_t value) { w.u32(value); });
}

bool read_u32_vector(ByteReader& reader, std::vector<uint32_t>* values) {
    return detail::read_vector(reader, values,
                               [](ByteReader& r, uint32_t* value) {
                                   return detail::read_u32(r, value);
                               });
}

void write_operator_function_identity(
    ByteWriter& writer, const cir::OperatorFunctionIdentity& identity) {
    write_enum(writer, identity.kind);
    write_enum(writer, identity.spelling);
    detail::write_type_ref(writer, identity.conversion_type);
    detail::write_id(writer, identity.literal_suffix);
}

bool read_operator_function_identity(
    ByteReader& reader, cir::OperatorFunctionIdentity* identity) {
    return read_enum(reader, &identity->kind) &&
           read_enum(reader, &identity->spelling) &&
           detail::read_type_ref(reader, &identity->conversion_type) &&
           detail::read_id(reader, &identity->literal_suffix);
}

void write_decl_semantic_flags(ByteWriter& writer,
                               const cir::DeclSemanticFlags& flags) {
    write_bool(writer, flags.is_constexpr);
    write_bool(writer, flags.is_consteval);
    write_bool(writer, flags.is_constinit);
    write_bool(writer, flags.is_inline);
    write_bool(writer, flags.is_thread_local);
    write_bool(writer, flags.is_register);
}

bool read_decl_semantic_flags(ByteReader& reader,
                              cir::DeclSemanticFlags* flags) {
    return read_bool(reader, &flags->is_constexpr) &&
           read_bool(reader, &flags->is_consteval) &&
           read_bool(reader, &flags->is_constinit) &&
           read_bool(reader, &flags->is_inline) &&
           read_bool(reader, &flags->is_thread_local) &&
           read_bool(reader, &flags->is_register);
}

void write_attribute_arg(ByteWriter& writer, const AttributeArg& arg) {
    write_enum(writer, arg.kind);
    detail::write_string(writer, arg.value);
    detail::write_string(writer, arg.key);
    detail::write_i64(writer, arg.int_value);

    writer.u64(std::bit_cast<uint64_t>(static_cast<double>(arg.float_value)));
    detail::write_u32(writer, arg.dependent_value_param_index);
    detail::write_srcloc(writer, arg.loc);
}

bool read_attribute_arg(ByteReader& reader, AttributeArg* arg) {
    if (!read_enum(reader, &arg->kind) ||
        !detail::read_string(reader, &arg->value) ||
        !detail::read_string(reader, &arg->key) ||
        !detail::read_i64(reader, &arg->int_value)) {
        return false;
    }
    uint64_t float_bits = 0;
    if (!detail::read_u64(reader, &float_bits)) {
        return false;
    }
    arg->float_value =
        static_cast<long double>(std::bit_cast<double>(float_bits));
    return detail::read_u32(reader, &arg->dependent_value_param_index) &&
           detail::read_srcloc(reader, &arg->loc);
}

void write_parsed_attribute(ByteWriter& writer,
                            const ParsedAttribute& attribute) {
    detail::write_string(writer, attribute.ns);
    detail::write_string(writer, attribute.name);
    detail::write_vector(writer, attribute.args, write_attribute_arg);
    detail::write_srcloc(writer, attribute.loc);
    write_enum(writer, attribute.syntax);
    write_enum(writer, attribute.kind);
}

bool read_parsed_attribute(ByteReader& reader, ParsedAttribute* attribute) {
    return detail::read_string(reader, &attribute->ns) &&
           detail::read_string(reader, &attribute->name) &&
           detail::read_vector(reader, &attribute->args, read_attribute_arg) &&
           detail::read_srcloc(reader, &attribute->loc) &&
           read_enum(reader, &attribute->syntax) &&
           read_enum(reader, &attribute->kind);
}

void write_attribute_list(ByteWriter& writer,
                          const AttributeList& attributes) {
    detail::write_vector(writer, attributes.attrs, write_parsed_attribute);
}

bool read_attribute_list(ByteReader& reader, AttributeList* attributes) {
    return detail::read_vector(reader, &attributes->attrs,
                               read_parsed_attribute);
}

void write_template_info(ByteWriter& writer, const Session::TemplateInfo& info);
bool read_template_info(ByteReader& reader, Session::TemplateInfo* info);

void write_template_parameter(ByteWriter& writer,
                              const Session::TemplateParameter& parameter) {
    detail::write_string(writer, parameter.name);
    write_enum(writer, parameter.kind);
    write_enum(writer, parameter.template_template_parameter_kind);
    writer.u32(parameter.depth);
    writer.u32(parameter.index);
    write_bool(writer, parameter.is_parameter_pack);
    detail::write_id(writer, parameter.entity);
    detail::write_id(writer, parameter.type_param_type);
    detail::write_id(writer, parameter.non_type_type);
    write_bool(writer, parameter.nested_head != nullptr);
    if (parameter.nested_head != nullptr) {
        write_template_info(writer, *parameter.nested_head);
    }
    write_optional(writer, parameter.default_argument, write_argument);
    write_bool(writer, parameter.requires_complete_class_default_replay);
    write_size(writer, parameter.default_argument_token_begin);
    write_size(writer, parameter.default_argument_token_end);
    detail::write_id(writer, parameter.default_argument_context);
    writer.u64(parameter.default_argument_lookup_generation);
    detail::write_srcloc(writer, parameter.loc);
}

bool read_template_parameter(ByteReader& reader,
                             Session::TemplateParameter* parameter) {
    if (!detail::read_string(reader, &parameter->name) ||
        !read_enum(reader, &parameter->kind) ||
        !read_enum(reader, &parameter->template_template_parameter_kind) ||
        !detail::read_u32(reader, &parameter->depth) ||
        !detail::read_u32(reader, &parameter->index) ||
        !read_bool(reader, &parameter->is_parameter_pack) ||
        !detail::read_id(reader, &parameter->entity) ||
        !detail::read_id(reader, &parameter->type_param_type) ||
        !detail::read_id(reader, &parameter->non_type_type)) {
        return false;
    }
    bool has_nested_head = false;
    if (!read_bool(reader, &has_nested_head)) {
        return false;
    }
    if (has_nested_head) {
        auto nested = std::make_shared<Session::TemplateInfo>();
        if (!read_template_info(reader, nested.get())) {
            return false;
        }
        parameter->nested_head = std::move(nested);
    } else {
        parameter->nested_head.reset();
    }
    return read_optional(reader, &parameter->default_argument,
                         read_argument) &&
           read_bool(reader,
                     &parameter->requires_complete_class_default_replay) &&
           read_size(reader, &parameter->default_argument_token_begin) &&
           read_size(reader, &parameter->default_argument_token_end) &&
           detail::read_id(reader, &parameter->default_argument_context) &&
           detail::read_u64(reader,
                            &parameter->default_argument_lookup_generation) &&
           detail::read_srcloc(reader, &parameter->loc);
}

void write_template_parameters(
    ByteWriter& writer,
    const std::vector<Session::TemplateParameter>& parameters) {
    detail::write_vector(writer, parameters, write_template_parameter);
}

bool read_template_parameters(
    ByteReader& reader, std::vector<Session::TemplateParameter>* parameters) {
    return detail::read_vector(reader, parameters, read_template_parameter);
}

void write_argument_binding(ByteWriter& writer,
                            const Session::TemplateArgumentBinding& binding) {
    write_enum(writer, binding.kind);
    write_arguments(writer, binding.arguments);
}

bool read_argument_binding(ByteReader& reader,
                           Session::TemplateArgumentBinding* binding) {
    return read_enum(reader, &binding->kind) &&
           read_arguments(reader, &binding->arguments);
}

void write_parameter_mapping(
    ByteWriter& writer, const Session::ConstraintParameterMapping& mapping) {
    write_enum(writer, mapping.parameter_kind);
    writer.u32(mapping.parameter_depth);
    writer.u32(mapping.parameter_index);
    detail::write_id(writer, mapping.parameter_entity);
    write_enum(writer, mapping.parameter_template_template_kind);
    write_bool(writer, mapping.parameter_is_pack);
    write_argument(writer, mapping.argument);
    write_argument_pack(writer, mapping.argument_pack);
}

bool read_parameter_mapping(ByteReader& reader,
                            Session::ConstraintParameterMapping* mapping) {
    return read_enum(reader, &mapping->parameter_kind) &&
           detail::read_u32(reader, &mapping->parameter_depth) &&
           detail::read_u32(reader, &mapping->parameter_index) &&
           detail::read_id(reader, &mapping->parameter_entity) &&
           read_enum(reader, &mapping->parameter_template_template_kind) &&
           read_bool(reader, &mapping->parameter_is_pack) &&
           read_argument(reader, &mapping->argument) &&
           read_argument_pack(reader, &mapping->argument_pack);
}

void write_parameter_reference(
    ByteWriter& writer,
    const Session::ConstraintParameterReference& reference) {
    write_enum(writer, reference.parameter_kind);
    writer.u32(reference.parameter_depth);
    writer.u32(reference.parameter_index);
    detail::write_id(writer, reference.parameter_entity);
    detail::write_id(writer, reference.parameter_type);
    detail::write_id(writer, reference.owning_template_entity);
}

bool read_parameter_reference(
    ByteReader& reader, Session::ConstraintParameterReference* reference) {
    return read_enum(reader, &reference->parameter_kind) &&
           detail::read_u32(reader, &reference->parameter_depth) &&
           detail::read_u32(reader, &reference->parameter_index) &&
           detail::read_id(reader, &reference->parameter_entity) &&
           detail::read_id(reader, &reference->parameter_type) &&
           detail::read_id(reader, &reference->owning_template_entity);
}

void write_fold_expansion_parameter(
    ByteWriter& writer,
    const Session::ConstraintFoldExpansionParameter& parameter) {
    write_enum(writer, parameter.kind);
    detail::write_string(writer, parameter.name);
    writer.u32(parameter.parameter_depth);
    writer.u32(parameter.parameter_index);
    detail::write_id(writer, parameter.parameter_entity);
    detail::write_id(writer, parameter.owning_template_entity);
    write_enum(writer, parameter.template_template_parameter_kind);
    detail::write_id(writer, parameter.type_parameter_pack_type);
    write_argument(writer, parameter.argument);
    write_argument_pack(writer, parameter.argument_pack);
}

bool read_fold_expansion_parameter(
    ByteReader& reader,
    Session::ConstraintFoldExpansionParameter* parameter) {
    return read_enum(reader, &parameter->kind) &&
           detail::read_string(reader, &parameter->name) &&
           detail::read_u32(reader, &parameter->parameter_depth) &&
           detail::read_u32(reader, &parameter->parameter_index) &&
           detail::read_id(reader, &parameter->parameter_entity) &&
           detail::read_id(reader, &parameter->owning_template_entity) &&
           read_enum(reader,
                     &parameter->template_template_parameter_kind) &&
           detail::read_id(reader, &parameter->type_parameter_pack_type) &&
           read_argument(reader, &parameter->argument) &&
           read_argument_pack(reader, &parameter->argument_pack);
}

void write_atom_identity(ByteWriter& writer,
                         const Session::ConstraintAtomIdentity& atom) {
    detail::write_id(writer, atom.appearance_owner);
    write_size(writer, atom.expression_begin);
    write_size(writer, atom.expression_end);
    detail::write_vector(writer, atom.parameter_mapping,
                         write_parameter_mapping);
    writer.u64(atom.declaration_equivalence_key);
}

bool read_atom_identity(ByteReader& reader,
                        Session::ConstraintAtomIdentity* atom) {
    return detail::read_id(reader, &atom->appearance_owner) &&
           read_size(reader, &atom->expression_begin) &&
           read_size(reader, &atom->expression_end) &&
           detail::read_vector(reader, &atom->parameter_mapping,
                               read_parameter_mapping) &&
           detail::read_u64(reader, &atom->declaration_equivalence_key);
}

void write_constraint_node(ByteWriter& writer,
                           const Session::NormalizedConstraintNode& node) {
    write_enum(writer, node.kind);
    write_atom_identity(writer, node.atom);
    detail::write_id(writer, node.concept_id_entity);
    writer.u32(node.concept_id_template_parameter_index);
    detail::write_type_ref(writer, node.concept_id_dependent_qualifier);
    detail::write_id(writer, node.concept_id_name);
    write_bool(writer, node.concept_id_qualified_name);
    write_size(writer, node.concept_id_argument_list_begin);
    write_size(writer, node.concept_id_argument_list_end);
    write_arguments(writer, node.concept_id_arguments);
    writer.u32(node.lhs);
    writer.u32(node.rhs);
    write_enum(writer, node.fold_operator);
    detail::write_vector(writer, node.fold_expansion_parameters,
                         write_fold_expansion_parameter);
    detail::write_vector(writer, node.fold_pattern_argument_bindings,
                         write_argument_binding);
}

bool read_constraint_node(ByteReader& reader,
                          Session::NormalizedConstraintNode* node) {
    return read_enum(reader, &node->kind) &&
           read_atom_identity(reader, &node->atom) &&
           detail::read_id(reader, &node->concept_id_entity) &&
           detail::read_u32(reader,
                            &node->concept_id_template_parameter_index) &&
           detail::read_type_ref(reader,
                                 &node->concept_id_dependent_qualifier) &&
           detail::read_id(reader, &node->concept_id_name) &&
           read_bool(reader, &node->concept_id_qualified_name) &&
           read_size(reader, &node->concept_id_argument_list_begin) &&
           read_size(reader, &node->concept_id_argument_list_end) &&
           read_arguments(reader, &node->concept_id_arguments) &&
           detail::read_u32(reader, &node->lhs) &&
           detail::read_u32(reader, &node->rhs) &&
           read_enum(reader, &node->fold_operator) &&
           detail::read_vector(reader, &node->fold_expansion_parameters,
                               read_fold_expansion_parameter) &&
           detail::read_vector(reader, &node->fold_pattern_argument_bindings,
                               read_argument_binding);
}

void write_normalized_constraint(
    ByteWriter& writer, const Session::NormalizedConstraint& constraint) {
    writer.u32(constraint.root);
    detail::write_vector(writer, constraint.nodes, write_constraint_node);
    detail::write_value_expression(writer, constraint.value_expression);
    detail::write_vector(writer, constraint.referenced_parameters,
                         write_parameter_reference);
}

bool read_normalized_constraint(ByteReader& reader,
                                Session::NormalizedConstraint* constraint) {
    return detail::read_u32(reader, &constraint->root) &&
           detail::read_vector(reader, &constraint->nodes,
                               read_constraint_node) &&
           detail::read_value_expression(reader,
                                         &constraint->value_expression) &&
           detail::read_vector(reader, &constraint->referenced_parameters,
                               read_parameter_reference);
}

void write_invented_function_parameter(
    ByteWriter& writer,
    const Session::TemplateInfo::InventedFunctionParameter& parameter) {
    writer.u32(parameter.function_parameter_index);
    writer.u32(parameter.placeholder_index);
    writer.u32(parameter.template_parameter_index);
    detail::write_srcloc(writer, parameter.loc);
}

bool read_invented_function_parameter(
    ByteReader& reader,
    Session::TemplateInfo::InventedFunctionParameter* parameter) {
    return detail::read_u32(reader, &parameter->function_parameter_index) &&
           detail::read_u32(reader, &parameter->placeholder_index) &&
           detail::read_u32(reader, &parameter->template_parameter_index) &&
           detail::read_srcloc(reader, &parameter->loc);
}

void write_function_constraint_parameter(
    ByteWriter& writer,
    const Session::TemplateInfo::FunctionConstraintParameter& parameter) {
    detail::write_string(writer, parameter.name);
    detail::write_type_ref(writer, parameter.type);
    detail::write_srcloc(writer, parameter.loc);
    write_bool(writer, parameter.is_parameter_pack);
    detail::write_string(writer, parameter.source_parameter_pack_name);
    write_bool(writer, parameter.is_parameter_pack_expansion_sentinel);
    write_bool(writer, parameter.type_originates_from_template_parameter);
}

bool read_function_constraint_parameter(
    ByteReader& reader,
    Session::TemplateInfo::FunctionConstraintParameter* parameter) {
    return detail::read_string(reader, &parameter->name) &&
           detail::read_type_ref(reader, &parameter->type) &&
           detail::read_srcloc(reader, &parameter->loc) &&
           read_bool(reader, &parameter->is_parameter_pack) &&
           detail::read_string(reader,
                               &parameter->source_parameter_pack_name) &&
           read_bool(reader,
                     &parameter->is_parameter_pack_expansion_sentinel) &&
           read_bool(reader,
                     &parameter->type_originates_from_template_parameter);
}

void write_introduced_constraint(
    ByteWriter& writer,
    const Session::TemplateInfo::IntroducedConstraint& constraint) {
    write_enum(writer, constraint.kind);
    write_size(writer, constraint.begin);
    write_size(writer, constraint.end);
    writer.u32(constraint.constrained_parameter_index);
    detail::write_id(writer, constraint.type_constraint_concept);
    write_arguments(writer, constraint.type_constraint_arguments);
    detail::write_srcloc(writer, constraint.loc);
    write_optional(writer, constraint.normal_form,
                   write_normalized_constraint);
}

bool read_introduced_constraint(
    ByteReader& reader,
    Session::TemplateInfo::IntroducedConstraint* constraint) {
    return read_enum(reader, &constraint->kind) &&
           read_size(reader, &constraint->begin) &&
           read_size(reader, &constraint->end) &&
           detail::read_u32(reader,
                            &constraint->constrained_parameter_index) &&
           detail::read_id(reader, &constraint->type_constraint_concept) &&
           read_arguments(reader, &constraint->type_constraint_arguments) &&
           detail::read_srcloc(reader, &constraint->loc) &&
           read_optional(reader, &constraint->normal_form,
                         read_normalized_constraint);
}

void write_pattern_hole(ByteWriter& writer,
                        const Session::PatternHole& hole) {
    write_size(writer, hole.token_begin);
    write_size(writer, hole.token_end);
    write_size(writer, hole.event_watermark);
    write_enum(writer, hole.kind);
}

bool read_pattern_hole(ByteReader& reader, Session::PatternHole* hole) {
    return read_size(reader, &hole->token_begin) &&
           read_size(reader, &hole->token_end) &&
           read_size(reader, &hole->event_watermark) &&
           read_enum(reader, &hole->kind);
}

void write_pattern_scope_event(ByteWriter& writer,
                               const Session::PatternScopeEvent& event) {
    write_enum(writer, event.kind);
    detail::write_id(writer, event.entity);
    detail::write_id(writer, event.place);
    writer.u64(event.lookup_generation);
}

bool read_pattern_scope_event(ByteReader& reader,
                              Session::PatternScopeEvent* event) {
    return read_enum(reader, &event->kind) &&
           detail::read_id(reader, &event->entity) &&
           detail::read_id(reader, &event->place) &&
           detail::read_u64(reader, &event->lookup_generation);
}

void write_member_pattern(ByteWriter& writer,
                          const Session::MemberPattern& pattern) {
    detail::write_id(writer, pattern.method);
    detail::write_id(writer, pattern.function);
    write_size(writer, pattern.body_token_begin);
    write_size(writer, pattern.body_start_block);
    write_size(writer, pattern.body_block_count);
    writer.u32(pattern.hole_index_base);
    detail::write_vector(writer, pattern.holes, write_pattern_hole);
    detail::write_vector(writer, pattern.events, write_pattern_scope_event);
    write_bool(writer, pattern.usable);
}

bool read_member_pattern(ByteReader& reader,
                         Session::MemberPattern* pattern) {
    return detail::read_id(reader, &pattern->method) &&
           detail::read_id(reader, &pattern->function) &&
           read_size(reader, &pattern->body_token_begin) &&
           read_size(reader, &pattern->body_start_block) &&
           read_size(reader, &pattern->body_block_count) &&
           detail::read_u32(reader, &pattern->hole_index_base) &&
           detail::read_vector(reader, &pattern->holes, read_pattern_hole) &&
           detail::read_vector(reader, &pattern->events,
                               read_pattern_scope_event) &&
           read_bool(reader, &pattern->usable);
}

void write_alias_deduction_projection(
    ByteWriter& writer,
    const Session::TemplateInfo::AliasDeductionProjection& projection) {
    detail::write_id(writer, projection.target_template);
    write_arguments(writer, projection.target_arguments);
}

bool read_alias_deduction_projection(
    ByteReader& reader,
    Session::TemplateInfo::AliasDeductionProjection* projection) {
    return detail::read_id(reader, &projection->target_template) &&
           read_arguments(reader, &projection->target_arguments);
}

void write_instantiation_binding(
    ByteWriter& writer,
    const Session::TemplateInfo::TemplateInstantiationBinding& binding) {
    write_template_parameters(writer, binding.parameters);
    detail::write_vector(writer,
                         binding.argument_bindings,
                         write_argument_binding);
}

bool read_instantiation_binding(
    ByteReader& reader,
    Session::TemplateInfo::TemplateInstantiationBinding* binding) {
    return read_template_parameters(reader, &binding->parameters) &&
           detail::read_vector(reader,
                               &binding->argument_bindings,
                               read_argument_binding);
}

void write_out_of_line_member(
    ByteWriter& writer,
    const Session::TemplateInfo::OutOfLineMember& member) {
    write_size(writer, member.begin);
    write_size(writer, member.end);
    write_bool(writer, member.is_template_declaration);
    write_bool(writer, member.is_static_data_member_definition);
    write_template_parameters(writer, member.head_parameters);
    write_u32_vector(writer, member.head_parameter_owner_slots);
}

bool read_out_of_line_member(
    ByteReader& reader, Session::TemplateInfo::OutOfLineMember* member) {
    return read_size(reader, &member->begin) &&
           read_size(reader, &member->end) &&
           read_bool(reader, &member->is_template_declaration) &&
           read_bool(reader, &member->is_static_data_member_definition) &&
           read_template_parameters(reader, &member->head_parameters) &&
           read_u32_vector(reader, &member->head_parameter_owner_slots);
}

template <typename SpecT>
void write_member_specialization(ByteWriter& writer,
                                 const SpecT& specialization) {
    detail::write_string(writer, specialization.owner_memo_key);
    detail::write_string(writer, specialization.member_name);
    detail::write_type_ref(writer, specialization.member_type);
    detail::write_srcloc(writer, specialization.loc);
}

template <typename SpecT>
bool read_member_specialization(ByteReader& reader, SpecT* specialization) {
    return detail::read_string(reader, &specialization->owner_memo_key) &&
           detail::read_string(reader, &specialization->member_name) &&
           detail::read_type_ref(reader, &specialization->member_type) &&
           detail::read_srcloc(reader, &specialization->loc);
}

void write_partial_specialization(
    ByteWriter& writer,
    const Session::TemplateInfo::PartialSpecialization& partial) {
    detail::write_id(writer, partial.entity);
    write_arguments(writer, partial.arguments);
    detail::write_srcloc(writer, partial.loc);
}

bool read_partial_specialization(
    ByteReader& reader,
    Session::TemplateInfo::PartialSpecialization* partial) {
    return detail::read_id(reader, &partial->entity) &&
           read_arguments(reader, &partial->arguments) &&
           detail::read_srcloc(reader, &partial->loc);
}

void write_deduction_guide(
    ByteWriter& writer, const Session::TemplateInfo::DeductionGuide& guide) {
    detail::write_id(writer, guide.pattern_type);
    detail::write_vector(
        writer,
        guide.parameter_default_argument_flags,
        [](ByteWriter& output, uint8_t flag) { output.u8(flag); });
    write_template_parameters(writer, guide.parameters);
    write_arguments(writer, guide.return_arguments);
    detail::write_vector(writer, guide.introduced_constraints,
                         write_introduced_constraint);
    detail::write_srcloc(writer, guide.loc);
    detail::write_id(writer, guide.declaration_context);
    writer.u64(guide.declaration_generation);
    write_optional(writer, guide.declared_member_access,
                   [](ByteWriter& w, cir::RecordMemberAccess access) {
                       write_enum(w, access);
                   });
    write_bool(writer, guide.is_explicit);
    write_enum(writer, guide.explicit_specifier);
    write_size(writer, guide.explicit_expression_begin);
    write_size(writer, guide.explicit_expression_end);
    detail::write_value_expression(writer, guide.explicit_value_expression);
    detail::write_id(writer, guide.explicit_declaration_context);
    writer.u64(guide.explicit_lookup_generation);
}

bool read_deduction_guide(ByteReader& reader,
                          Session::TemplateInfo::DeductionGuide* guide) {
    return detail::read_id(reader, &guide->pattern_type) &&
           detail::read_vector(
               reader,
               &guide->parameter_default_argument_flags,
               [](ByteReader& input, uint8_t* flag) {
                   return detail::read_u8(input, flag);
               }) &&
           read_template_parameters(reader, &guide->parameters) &&
           read_arguments(reader, &guide->return_arguments) &&
           detail::read_vector(reader, &guide->introduced_constraints,
                               read_introduced_constraint) &&
           detail::read_srcloc(reader, &guide->loc) &&
           detail::read_id(reader, &guide->declaration_context) &&
           detail::read_u64(reader, &guide->declaration_generation) &&
           read_optional(reader, &guide->declared_member_access,
                         [](ByteReader& r, cir::RecordMemberAccess* access) {
                             return read_enum(r, access);
                         }) &&
           read_bool(reader, &guide->is_explicit) &&
           read_enum(reader, &guide->explicit_specifier) &&
           read_size(reader, &guide->explicit_expression_begin) &&
           read_size(reader, &guide->explicit_expression_end) &&
           detail::read_value_expression(reader,
                                         &guide->explicit_value_expression) &&
           detail::read_id(reader, &guide->explicit_declaration_context) &&
           detail::read_u64(reader, &guide->explicit_lookup_generation);
}

void write_template_info(ByteWriter& writer,
                         const Session::TemplateInfo& info) {
    detail::write_id(writer, info.entity);
    detail::write_string(writer, info.name);
    write_operator_function_identity(writer, info.operator_function);
    writer.u32(info.template_parameter_index);
    write_bool(writer, info.is_class_template);
    write_bool(writer, info.is_alias_template);
    write_bool(writer, info.is_variable_template);
    write_bool(writer, info.is_concept);
    write_bool(writer, info.has_internal_linkage);
    write_bool(writer, info.is_template_parameter_pack);
    write_bool(writer, info.is_partial_specialization);
    write_bool(writer, info.is_member_template_specialization_overlay);
    write_bool(writer, info.is_candidate_neutral_argument_recipe);
    write_enum(writer, info.record_kind);
    write_template_parameters(writer, info.parameters);
    detail::write_vector(writer, info.invented_function_parameters,
                         write_invented_function_parameter);
    detail::write_vector(writer, info.function_constraint_parameters,
                         write_function_constraint_parameter);
    write_size(writer, info.complete_class_head_begin);
    write_size(writer, info.complete_class_head_end);
    write_bool(writer, info.has_complete_class_default_recipes);
    detail::write_vector(writer, info.introduced_constraints,
                         write_introduced_constraint);
    write_attribute_list(writer, info.declaration_attrs);
    detail::write_id(writer, info.alias_target_type);
    detail::write_type_ref(writer, info.alias_target_type_ref);
    write_size(writer, info.alias_type_attribute_begin);
    write_size(writer, info.alias_type_attribute_end);
    write_enum(writer, info.alias_type_transform_kind);
    detail::write_u32(writer, info.alias_type_transform_parameter);
    write_optional(writer, info.alias_deduction_projection,
                   write_alias_deduction_projection);
    detail::write_id(writer, info.variable_type);
    detail::write_type_ref(writer, info.variable_type_ref);
    write_bool(writer, info.variable_const_qualification_is_implicit);
    write_decl_semantic_flags(writer, info.variable_decl_flags);
    write_bool(writer, info.variable_is_extern);
    write_bool(writer, info.variable_is_static);
    write_size(writer, info.constraint_begin);
    write_size(writer, info.constraint_end);
    write_optional(writer, info.constraint_normal_form,
                   write_normalized_constraint);
    write_size(writer, info.definition_begin);
    write_size(writer, info.definition_end);
    write_bool(writer, info.has_definition);
    write_bool(writer, info.is_deleted);
    write_bool(writer, info.hidden_friend_definition_is_pattern);
    detail::write_id(writer, info.lexical_context);
    detail::write_id(writer, info.pattern_function);
    detail::write_id(writer, info.pattern_generic);
    write_bool(writer, info.pattern_usable);
    writer.u64(info.definition_generation);
    detail::write_vector(writer, info.pattern_holes, write_pattern_hole);
    detail::write_vector(writer, info.pattern_events,
                         write_pattern_scope_event);
    detail::write_id(writer, info.pattern_record);
    detail::write_vector(writer, info.member_patterns, write_member_pattern);
    detail::write_id(writer, info.pattern_type);
    detail::write_vector(writer, info.param_types,
                         [](ByteWriter& w, cir::TypeId type) {
                             detail::write_id(w, type);
                         });
    detail::write_vector(writer, info.enclosing_instantiation_bindings,
                         write_instantiation_binding);
    detail::write_vector(writer, info.out_of_line_members,
                         write_out_of_line_member);
    detail::write_vector(
        writer, info.explicit_member_function_specializations,
        write_member_specialization<
            Session::TemplateInfo::ExplicitMemberFunctionSpecialization>);
    detail::write_vector(
        writer, info.explicit_static_data_member_specializations,
        write_member_specialization<
            Session::TemplateInfo::ExplicitStaticDataMemberSpecialization>);
    detail::write_vector(writer, info.partial_specializations,
                         write_partial_specialization);
    detail::write_vector(writer, info.deduction_guides,
                         write_deduction_guide);
    write_enum(writer, info.explicit_specifier);
    write_size(writer, info.explicit_expression_begin);
    write_size(writer, info.explicit_expression_end);
    detail::write_value_expression(writer, info.explicit_value_expression);
}

bool read_template_info(ByteReader& reader, Session::TemplateInfo* info) {
    return detail::read_id(reader, &info->entity) &&
           detail::read_string(reader, &info->name) &&
           read_operator_function_identity(reader,
                                           &info->operator_function) &&
           detail::read_u32(reader, &info->template_parameter_index) &&
           read_bool(reader, &info->is_class_template) &&
           read_bool(reader, &info->is_alias_template) &&
           read_bool(reader, &info->is_variable_template) &&
           read_bool(reader, &info->is_concept) &&
           read_bool(reader, &info->has_internal_linkage) &&
           read_bool(reader, &info->is_template_parameter_pack) &&
           read_bool(reader, &info->is_partial_specialization) &&
           read_bool(reader,
                     &info->is_member_template_specialization_overlay) &&
           read_bool(reader, &info->is_candidate_neutral_argument_recipe) &&
           read_enum(reader, &info->record_kind) &&
           read_template_parameters(reader, &info->parameters) &&
           detail::read_vector(reader, &info->invented_function_parameters,
                               read_invented_function_parameter) &&
           detail::read_vector(reader, &info->function_constraint_parameters,
                               read_function_constraint_parameter) &&
           read_size(reader, &info->complete_class_head_begin) &&
           read_size(reader, &info->complete_class_head_end) &&
           read_bool(reader, &info->has_complete_class_default_recipes) &&
           detail::read_vector(reader, &info->introduced_constraints,
                               read_introduced_constraint) &&
           read_attribute_list(reader, &info->declaration_attrs) &&
           detail::read_id(reader, &info->alias_target_type) &&
           detail::read_type_ref(reader, &info->alias_target_type_ref) &&
           read_size(reader, &info->alias_type_attribute_begin) &&
           read_size(reader, &info->alias_type_attribute_end) &&
           read_enum(reader, &info->alias_type_transform_kind) &&
           detail::read_u32(reader,
                            &info->alias_type_transform_parameter) &&
           read_optional(reader, &info->alias_deduction_projection,
                         read_alias_deduction_projection) &&
           detail::read_id(reader, &info->variable_type) &&
           detail::read_type_ref(reader, &info->variable_type_ref) &&
           read_bool(reader,
                     &info->variable_const_qualification_is_implicit) &&
           read_decl_semantic_flags(reader, &info->variable_decl_flags) &&
           read_bool(reader, &info->variable_is_extern) &&
           read_bool(reader, &info->variable_is_static) &&
           read_size(reader, &info->constraint_begin) &&
           read_size(reader, &info->constraint_end) &&
           read_optional(reader, &info->constraint_normal_form,
                         read_normalized_constraint) &&
           read_size(reader, &info->definition_begin) &&
           read_size(reader, &info->definition_end) &&
           read_bool(reader, &info->has_definition) &&
           read_bool(reader, &info->is_deleted) &&
           read_bool(reader, &info->hidden_friend_definition_is_pattern) &&
           detail::read_id(reader, &info->lexical_context) &&
           detail::read_id(reader, &info->pattern_function) &&
           detail::read_id(reader, &info->pattern_generic) &&
           read_bool(reader, &info->pattern_usable) &&
           detail::read_u64(reader, &info->definition_generation) &&
           detail::read_vector(reader, &info->pattern_holes,
                               read_pattern_hole) &&
           detail::read_vector(reader, &info->pattern_events,
                               read_pattern_scope_event) &&
           detail::read_id(reader, &info->pattern_record) &&
           detail::read_vector(reader, &info->member_patterns,
                               read_member_pattern) &&
           detail::read_id(reader, &info->pattern_type) &&
           detail::read_vector(reader, &info->param_types,
                               [](ByteReader& r, cir::TypeId* type) {
                                   return detail::read_id(r, type);
                               }) &&
           detail::read_vector(reader,
                               &info->enclosing_instantiation_bindings,
                               read_instantiation_binding) &&
           detail::read_vector(reader, &info->out_of_line_members,
                               read_out_of_line_member) &&
           detail::read_vector(
               reader, &info->explicit_member_function_specializations,
               read_member_specialization<
                   Session::TemplateInfo::
                       ExplicitMemberFunctionSpecialization>) &&
           detail::read_vector(
               reader, &info->explicit_static_data_member_specializations,
               read_member_specialization<
                   Session::TemplateInfo::
                       ExplicitStaticDataMemberSpecialization>) &&
           detail::read_vector(reader, &info->partial_specializations,
                               read_partial_specialization) &&
           detail::read_vector(reader, &info->deduction_guides,
                               read_deduction_guide) &&
           read_enum(reader, &info->explicit_specifier) &&
           read_size(reader, &info->explicit_expression_begin) &&
           read_size(reader, &info->explicit_expression_end) &&
           detail::read_value_expression(reader,
                                         &info->explicit_value_expression);
}

void write_template_parameter_pattern(
    ByteWriter& writer, const cir::TemplateParameterPattern& pattern) {
    write_enum(writer, pattern.kind);
    write_bool(writer, pattern.is_parameter_pack);
    detail::write_id(writer, pattern.type_param_type);
    detail::write_type_ref(writer, pattern.non_type_type);
    detail::write_vector(writer, pattern.template_parameters,
                         write_template_parameter_pattern);
}

bool read_template_parameter_pattern(ByteReader& reader,
                                     cir::TemplateParameterPattern* pattern) {
    return read_enum(reader, &pattern->kind) &&
           read_bool(reader, &pattern->is_parameter_pack) &&
           detail::read_id(reader, &pattern->type_param_type) &&
           detail::read_type_ref(reader, &pattern->non_type_type) &&
           detail::read_vector(reader, &pattern->template_parameters,
                               read_template_parameter_pattern);
}

void write_class_friend_grant(ByteWriter& writer,
                              const cir::RecordClassFriendGrant& grant) {
    write_enum(writer, grant.kind);
    write_enum(writer, grant.recipe_kind);
    detail::write_id(writer, grant.entity);
    detail::write_type_ref(writer, grant.type_pattern);
    detail::write_id(writer, grant.member_name);
    write_u32_vector(writer, grant.required_type_params);
    write_u32_vector(writer, grant.required_value_params);
    write_u32_vector(writer, grant.required_template_params);
    write_bool(writer, grant.is_pack_expansion);
    detail::write_srcloc(writer, grant.loc);
}

bool read_class_friend_grant(ByteReader& reader,
                             cir::RecordClassFriendGrant* grant) {
    return read_enum(reader, &grant->kind) &&
           read_enum(reader, &grant->recipe_kind) &&
           detail::read_id(reader, &grant->entity) &&
           detail::read_type_ref(reader, &grant->type_pattern) &&
           detail::read_id(reader, &grant->member_name) &&
           read_u32_vector(reader, &grant->required_type_params) &&
           read_u32_vector(reader, &grant->required_value_params) &&
           read_u32_vector(reader, &grant->required_template_params) &&
           read_bool(reader, &grant->is_pack_expansion) &&
           detail::read_srcloc(reader, &grant->loc);
}

void write_function_friend_grant(ByteWriter& writer,
                                 const cir::RecordFunctionFriendGrant& grant) {
    write_enum(writer, grant.kind);
    detail::write_id(writer, grant.entity);
    detail::write_id(writer, grant.context);
    detail::write_id(writer, grant.module_attachment);
    detail::write_id(writer, grant.signature_owner);
    detail::write_id(writer, grant.name);
    detail::write_type_ref(writer, grant.type_pattern);
    write_arguments(writer, grant.arguments);
    detail::write_type_ref(writer, grant.qualifier_pattern);
    detail::write_id(writer, grant.member_name);
    detail::write_vector(writer, grant.member_template_parameters,
                         write_template_parameter_pattern);
    write_u32_vector(writer, grant.required_type_params);
    write_u32_vector(writer, grant.required_value_params);
    write_u32_vector(writer, grant.required_template_params);
    detail::write_srcloc(writer, grant.loc);
}

bool read_function_friend_grant(ByteReader& reader,
                                cir::RecordFunctionFriendGrant* grant) {
    return read_enum(reader, &grant->kind) &&
           detail::read_id(reader, &grant->entity) &&
           detail::read_id(reader, &grant->context) &&
           detail::read_id(reader, &grant->module_attachment) &&
           detail::read_id(reader, &grant->signature_owner) &&
           detail::read_id(reader, &grant->name) &&
           detail::read_type_ref(reader, &grant->type_pattern) &&
           read_arguments(reader, &grant->arguments) &&
           detail::read_type_ref(reader, &grant->qualifier_pattern) &&
           detail::read_id(reader, &grant->member_name) &&
           detail::read_vector(reader, &grant->member_template_parameters,
                               read_template_parameter_pattern) &&
           read_u32_vector(reader, &grant->required_type_params) &&
           read_u32_vector(reader, &grant->required_value_params) &&
           read_u32_vector(reader, &grant->required_template_params) &&
           detail::read_srcloc(reader, &grant->loc);
}

void write_entity_id(ByteWriter& writer, cir::EntityId entity) {
    detail::write_id(writer, entity);
}

bool read_entity_id(ByteReader& reader, cir::EntityId* entity) {
    return detail::read_id(reader, entity);
}

void write_srcloc_value(ByteWriter& writer, SrcLoc loc) {
    detail::write_srcloc(writer, loc);
}

bool read_srcloc_value(ByteReader& reader, SrcLoc* loc) {
    return detail::read_srcloc(reader, loc);
}

void write_class_friend_grants(
    ByteWriter& writer, const std::vector<cir::RecordClassFriendGrant>& grants) {
    detail::write_vector(writer, grants, write_class_friend_grant);
}

bool read_class_friend_grants(ByteReader& reader,
                              std::vector<cir::RecordClassFriendGrant>* grants) {
    return detail::read_vector(reader, grants, read_class_friend_grant);
}

void write_function_friend_grants(
    ByteWriter& writer,
    const std::vector<cir::RecordFunctionFriendGrant>& grants) {
    detail::write_vector(writer, grants, write_function_friend_grant);
}

bool read_function_friend_grants(
    ByteReader& reader, std::vector<cir::RecordFunctionFriendGrant>* grants) {
    return detail::read_vector(reader, grants, read_function_friend_grant);
}

} // namespace

void Session::serialize_template_state(const void* exported_state,
                                       std::string& out) {
    out.clear();
    if (exported_state == nullptr) {
        return;
    }
    const TemplateState& state =
        *static_cast<const TemplateState*>(exported_state);
    ByteWriter writer;
    writer.u32(template_state_magic);
    writer.u64(cir::module_graph_schema_version());
    write_sorted_map(writer, state.templates_, write_u64_key,
                     write_template_info);
    auto write_captured_param = [](ByteWriter& w,
                                   const Session::CapturedMemberParam& p) {
        detail::write_string(w, p.name);
        detail::write_id(w, p.type);
        detail::write_type_ref(w, p.type_ref);
        detail::write_srcloc(w, p.loc);
        write_attribute_list(w, p.attrs);
        write_bool(w, p.has_default_argument);
        write_size(w, p.default_argument_begin);
        write_size(w, p.default_argument_end);
        detail::write_srcloc(w, p.default_argument_loc);
        write_bool(w, p.is_parameter_pack);
        detail::write_string(w, p.source_parameter_pack_name);
        write_bool(w, p.is_parameter_pack_expansion_sentinel);
        write_bool(w, p.type_originates_from_template_parameter);
        detail::write_id(w, p.default_argument_declaration_context);
        w.u64(p.default_argument_lookup_generation);
        write_bool(w, p.default_argument_requires_complete_class_replay);
    };
    write_sorted_map(
        writer, state.captured_member_bodies_, write_u64_key,
        [&](ByteWriter& w, const Session::CapturedMemberBody& body) {
            write_size(w, body.method_index);
            write_size(w, body.body_begin);
            write_size(w, body.body_end);
            write_size(w, body.init_begin);
            write_size(w, body.init_end);
            write_bool(w, body.is_constructor_function_try);
            write_bool(w, body.transferable);
            detail::write_vector(w, body.params, write_captured_param);
        });
    auto write_default_argument =
        [](ByteWriter& w, const ParamInput::DefaultArgument& recipe) {
            write_size(w, recipe.token_begin);
            write_size(w, recipe.token_end);
            detail::write_srcloc(w, recipe.loc);
            detail::write_id(w, recipe.declaration_context);
            w.u64(recipe.lookup_generation);
            write_bool(w, recipe.requires_complete_class_replay);
        };
    write_sorted_map(
        writer, state.exported_default_arguments_, write_u64_key,
        [&](ByteWriter& w,
            const std::vector<ParamInput::DefaultArgument>& recipes) {
            detail::write_vector(w, recipes, write_default_argument);
        });
    write_sorted_map(writer, state.pattern_record_templates_, write_u64_key,
                     write_entity_id);

    write_sorted_map(writer, state.instantiation_cache_, write_string_key,
                     write_entity_id);
    write_sorted_map(writer, state.template_parameter_object_cache_,
                     write_string_key, write_entity_id);
    detail::write_vector(
        writer, state.template_parameter_object_records_,
        [](ByteWriter& w,
           const TemplateState::TemplateParameterObjectRecord& record) {
            detail::write_template_argument(w, record.argument);
            detail::write_id(w, record.object);
        });
    auto write_explicit_instantiation =
        [](ByteWriter& w,
           const TemplateState::ExplicitInstantiationDeclaration&
               declaration) {
            detail::write_id(w, declaration.template_entity);
            write_arguments(w, declaration.arguments);
            detail::write_srcloc(w, declaration.loc);
            write_attribute_list(w, declaration.attrs);
        };
    write_sorted_map(writer, state.explicit_instantiation_declarations_,
                     write_string_key, write_explicit_instantiation);
    write_sorted_map(writer, state.explicit_instantiation_definitions_,
                     write_string_key, write_explicit_instantiation);
    write_sorted_map(writer,
                     state.explicit_entity_instantiation_declarations_,
                     write_u64_key, write_srcloc_value);
    write_sorted_map(writer,
                     state.explicit_entity_instantiation_definitions_,
                     write_u64_key, write_srcloc_value);
    write_sorted_map(writer, state.pending_class_friends_, write_u64_key,
                     write_class_friend_grants);
    write_sorted_map(writer, state.pending_function_friends_, write_u64_key,
                     write_function_friend_grants);
    detail::write_vector(
        writer, state.hidden_friend_class_template_identities_,
        [](ByteWriter& w,
           const TemplateState::FriendClassTemplateIdentity& identity) {
            detail::write_string(w, identity.name);
            detail::write_id(w, identity.context);
            detail::write_id(w, identity.entity);
            write_template_parameters(w, identity.parameters);
        });
    detail::write_vector(
        writer, state.hidden_friend_record_identities_,
        [](ByteWriter& w,
           const TemplateState::HiddenFriendRecordIdentity& identity) {
            detail::write_string(w, identity.name);
            detail::write_id(w, identity.context);
            write_enum(w, identity.kind);
            detail::write_id(w, identity.module_attachment);
            detail::write_id(w, identity.entity);
        });
    detail::write_vector(
        writer, state.hidden_friend_function_template_identities_,
        [](ByteWriter& w,
           const TemplateState::FriendFunctionTemplateIdentity& identity) {
            detail::write_string(w, identity.name);
            detail::write_id(w, identity.context);
            detail::write_id(w, identity.module_attachment);
            detail::write_id(w, identity.signature_owner);
            detail::write_id(w, identity.entity);
            write_template_parameters(w, identity.parameters);
            detail::write_id(w, identity.pattern_type);
        });
    write_function_friend_grants(writer, state.friend_function_identities_);
    out = writer.take();
}

std::shared_ptr<void> Session::deserialize_template_state(
    std::string_view bytes) {
    ByteReader reader(bytes);
    uint32_t magic = 0;
    if (!detail::read_u32(reader, &magic) || magic != template_state_magic) {
        return nullptr;
    }
    uint64_t version = 0;
    if (!detail::read_u64(reader, &version) ||
        version != cir::module_graph_schema_version()) {
        return nullptr;
    }
    auto state = std::make_shared<TemplateState>();
    auto read_explicit_instantiation =
        [](ByteReader& r,
           TemplateState::ExplicitInstantiationDeclaration* declaration) {
            return detail::read_id(r, &declaration->template_entity) &&
                   read_arguments(r, &declaration->arguments) &&
                   detail::read_srcloc(r, &declaration->loc) &&
                   read_attribute_list(r, &declaration->attrs);
        };
    auto read_captured_param = [](ByteReader& r,
                                  Session::CapturedMemberParam* p) {
        return detail::read_string(r, &p->name) &&
               detail::read_id(r, &p->type) &&
               detail::read_type_ref(r, &p->type_ref) &&
               detail::read_srcloc(r, &p->loc) &&
               read_attribute_list(r, &p->attrs) &&
               read_bool(r, &p->has_default_argument) &&
               read_size(r, &p->default_argument_begin) &&
               read_size(r, &p->default_argument_end) &&
               detail::read_srcloc(r, &p->default_argument_loc) &&
               read_bool(r, &p->is_parameter_pack) &&
               detail::read_string(r, &p->source_parameter_pack_name) &&
               read_bool(r, &p->is_parameter_pack_expansion_sentinel) &&
               read_bool(r, &p->type_originates_from_template_parameter) &&
               detail::read_id(r, &p->default_argument_declaration_context) &&
               detail::read_u64(r, &p->default_argument_lookup_generation) &&
               read_bool(
                   r, &p->default_argument_requires_complete_class_replay);
    };
    auto read_captured_body = [&](ByteReader& r,
                                  Session::CapturedMemberBody* body) {
        return read_size(r, &body->method_index) &&
               read_size(r, &body->body_begin) &&
               read_size(r, &body->body_end) &&
               read_size(r, &body->init_begin) &&
               read_size(r, &body->init_end) &&
               read_bool(r, &body->is_constructor_function_try) &&
               read_bool(r, &body->transferable) &&
               detail::read_vector(r, &body->params, read_captured_param);
    };
    if (!read_map(reader, &state->templates_, read_u64_key,
                  read_template_info) ||
        !read_map(reader, &state->captured_member_bodies_, read_u64_key,
                  read_captured_body) ||
        !read_map(reader, &state->exported_default_arguments_, read_u64_key,
                  [&](ByteReader& r,
                      std::vector<ParamInput::DefaultArgument>* recipes) {
                      return detail::read_vector(
                          r, recipes,
                          [](ByteReader& rr,
                             ParamInput::DefaultArgument* recipe) {
                              return read_size(rr, &recipe->token_begin) &&
                                     read_size(rr, &recipe->token_end) &&
                                     detail::read_srcloc(rr, &recipe->loc) &&
                                     detail::read_id(
                                         rr,
                                         &recipe->declaration_context) &&
                                     detail::read_u64(
                                         rr, &recipe->lookup_generation) &&
                                     read_bool(
                                         rr,
                                         &recipe
                                              ->requires_complete_class_replay);
                          });
                  }) ||
        !read_map(reader, &state->pattern_record_templates_, read_u64_key,
                  read_entity_id) ||
        !read_map(reader, &state->instantiation_cache_, read_string_key,
                  read_entity_id) ||
        !read_map(reader, &state->template_parameter_object_cache_,
                  read_string_key, read_entity_id) ||
        !detail::read_vector(
            reader, &state->template_parameter_object_records_,
            [](ByteReader& r,
               TemplateState::TemplateParameterObjectRecord* record) {
                return detail::read_template_argument(r,
                                                      &record->argument) &&
                       detail::read_id(r, &record->object);
            }) ||
        !read_map(reader, &state->explicit_instantiation_declarations_,
                  read_string_key, read_explicit_instantiation) ||
        !read_map(reader, &state->explicit_instantiation_definitions_,
                  read_string_key, read_explicit_instantiation) ||
        !read_map(reader,
                  &state->explicit_entity_instantiation_declarations_,
                  read_u64_key, read_srcloc_value) ||
        !read_map(reader,
                  &state->explicit_entity_instantiation_definitions_,
                  read_u64_key, read_srcloc_value) ||
        !read_map(reader, &state->pending_class_friends_, read_u64_key,
                  read_class_friend_grants) ||
        !read_map(reader, &state->pending_function_friends_, read_u64_key,
                  read_function_friend_grants)) {
        return nullptr;
    }
    if (!detail::read_vector(
            reader, &state->hidden_friend_class_template_identities_,
            [](ByteReader& r,
               TemplateState::FriendClassTemplateIdentity* identity) {
                return detail::read_string(r, &identity->name) &&
                       detail::read_id(r, &identity->context) &&
                       detail::read_id(r, &identity->entity) &&
                       read_template_parameters(r, &identity->parameters);
            }) ||
        !detail::read_vector(
            reader, &state->hidden_friend_record_identities_,
            [](ByteReader& r,
               TemplateState::HiddenFriendRecordIdentity* identity) {
                return detail::read_string(r, &identity->name) &&
                       detail::read_id(r, &identity->context) &&
                       read_enum(r, &identity->kind) &&
                       detail::read_id(r, &identity->module_attachment) &&
                       detail::read_id(r, &identity->entity);
            }) ||
        !detail::read_vector(
            reader, &state->hidden_friend_function_template_identities_,
            [](ByteReader& r,
               TemplateState::FriendFunctionTemplateIdentity* identity) {
                return detail::read_string(r, &identity->name) &&
                       detail::read_id(r, &identity->context) &&
                       detail::read_id(r, &identity->module_attachment) &&
                       detail::read_id(r, &identity->signature_owner) &&
                       detail::read_id(r, &identity->entity) &&
                       read_template_parameters(r, &identity->parameters) &&
                       detail::read_id(r, &identity->pattern_type);
            }) ||
        !read_function_friend_grants(reader,
                                     &state->friend_function_identities_)) {
        return nullptr;
    }

    if (!reader.at_end()) {
        return nullptr;
    }
    return state;
}

} // namespace aburi::collect
