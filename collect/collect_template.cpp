#include "collect.h"
#include "collect_template_state.h"

#include "../numeric/floating_cir.h"
#include "../cir/layout.h"
#include "../constexpr/consteval_engine.h"
#include "../perf_stats.h"

#include <algorithm>
#include <cassert>
#include <cstring>
#include <functional>
#include <optional>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace aburi::collect {

namespace detail {
bool deduce_exception_spec_for_partial_ordering(
    const cir::FunctionExceptionSpec& pattern,
    const cir::FunctionExceptionSpec& argument,
    Session::PatternBindings& bindings,
    const Session& session);
} // namespace detail

const std::vector<Session::TemplateParameter>&
Session::TemplateParameter::nested_parameters() const {
    static const std::vector<TemplateParameter> empty;
    return nested_head ? nested_head->parameters : empty;
}

namespace {

void bump_template_counter(PerfCounter counter) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(counter);
    }
}

void record_template_counter_max(PerfCounter counter, uint64_t value) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->set_counter_max(counter, value);
    }
}

AttributeTarget explicit_instantiation_attribute_target(
    const cir::Entity& entity) {
    if (entity.kind == cir::EntityKind::Record) {
        return AttributeTarget::Type;
    }
    if (entity.kind == cir::EntityKind::Variable) {
        return AttributeTarget::Variable;
    }
    return AttributeTarget::Function;
}

bool template_argument_is_type(const Session::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Type;
}

bool template_argument_is_value(const Session::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Value;
}

bool template_argument_has_dependent_value_name(
    const Session::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Value &&
           argument.dependent_value_qualifier.type.valid() &&
           argument.dependent_value_name.valid();
}

bool template_argument_has_dependent_value_expr(
    const Session::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Value &&
           argument.dependent_value_expr.valid();
}

bool template_argument_has_dependent_template_name(
    const Session::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Template &&
           argument.dependent_template_qualifier.type.valid() &&
           argument.template_name.valid();
}

std::optional<cir::TemplateValueExpression>
extract_template_value_subexpression(
    const cir::TemplateValueExpression& source,
    uint32_t root) {
    if (root == cir::TemplateValueExprNoNode ||
        root >= source.nodes.size()) {
        return std::nullopt;
    }
    cir::TemplateValueExpression extracted;
    extracted.loc = source.loc;
    extracted.definition_context = source.definition_context;
    extracted.definition_lookup_generation =
        source.definition_lookup_generation;
    std::vector<uint32_t> remap(
        source.nodes.size(), cir::TemplateValueExprNoNode);
    std::vector<bool> visiting(source.nodes.size(), false);
    std::function<std::optional<uint32_t>(uint32_t)> clone;
    clone = [&](uint32_t index) -> std::optional<uint32_t> {
        if (index == cir::TemplateValueExprNoNode) {
            return cir::TemplateValueExprNoNode;
        }
        if (index >= source.nodes.size() || visiting[index]) {
            return std::nullopt;
        }
        if (remap[index] != cir::TemplateValueExprNoNode) {
            return remap[index];
        }
        visiting[index] = true;
        cir::TemplateValueExprNode node = source.nodes[index];
        auto clone_child = [&](uint32_t& child) {
            std::optional<uint32_t> mapped = clone(child);
            if (!mapped.has_value()) {
                return false;
            }
            child = *mapped;
            return true;
        };
        if (!clone_child(node.lhs) || !clone_child(node.rhs) ||
            !clone_child(node.third)) {
            visiting[index] = false;
            return std::nullopt;
        }
        for (uint32_t& operand : node.operands) {
            if (!clone_child(operand)) {
                visiting[index] = false;
                return std::nullopt;
            }
        }
        uint32_t mapped =
            static_cast<uint32_t>(extracted.nodes.size());
        extracted.nodes.push_back(std::move(node));
        remap[index] = mapped;
        visiting[index] = false;
        return mapped;
    };
    std::optional<uint32_t> mapped_root = clone(root);
    if (!mapped_root.has_value()) {
        return std::nullopt;
    }
    extracted.root = *mapped_root;
    return extracted;
}

std::vector<Session::ConstraintParameterMapping>
constraint_identity_parameter_mapping(Session& session,
                                      const Session::TemplateInfo& info) {
    std::vector<Session::ConstraintParameterMapping> mappings;
    mappings.reserve(info.parameters.size());
    for (const Session::TemplateParameter& parameter : info.parameters) {
        Session::ConstraintParameterMapping mapping;
        mapping.parameter_kind = parameter.kind;
        mapping.parameter_depth = parameter.depth;
        mapping.parameter_index = parameter.index;
        mapping.parameter_entity = parameter.entity;
        mapping.parameter_is_pack = parameter.is_parameter_pack;
        switch (parameter.kind) {
            case Session::TemplateParameterKind::Type:
                mapping.argument.kind = cir::TemplateArgumentKind::Type;
                mapping.argument.type =
                    session.type_ref(parameter.type_param_type);
                mapping.argument.is_dependent = true;
                break;
            case Session::TemplateParameterKind::NonType:
                mapping.argument.kind = cir::TemplateArgumentKind::Value;
                mapping.argument.value_type =
                    session.type_ref(parameter.non_type_type);
                mapping.argument.value_param_index = parameter.index;
                mapping.argument.value_spelling = parameter.name;
                mapping.argument.is_dependent = true;
                break;
            case Session::TemplateParameterKind::Template:
                mapping.argument.kind = cir::TemplateArgumentKind::Template;
                mapping.parameter_template_template_kind =
                    parameter.template_template_parameter_kind;
                mapping.argument.template_entity = parameter.entity;
                mapping.argument.template_param_index = parameter.index;
                mapping.argument.template_name =
                    parameter.name.empty()
                        ? cir::NameId{}
                        : session.file().intern_name(parameter.name);
                mapping.argument.is_dependent = true;
                break;
        }
        mappings.push_back(std::move(mapping));
    }
    return mappings;
}

void stamp_constraint_normal_form_owner(
    Session::NormalizedConstraint& form,
    Session& session,
    const Session::TemplateInfo& info,
    cir::EntityId owner) {
    for (Session::NormalizedConstraintNode& node : form.nodes) {
        if ((node.kind == Session::NormalizedConstraintKind::Atomic ||
             node.kind ==
                 Session::NormalizedConstraintKind::ConceptDependent) &&
            !node.atom.appearance_owner.valid()) {
            node.atom.appearance_owner = owner;
            if (node.atom.parameter_mapping.empty()) {
                node.atom.parameter_mapping =
                    constraint_identity_parameter_mapping(session, info);
            }
        }
    }
}

cir::TypeId template_argument_type_id(const Session::TemplateArgument& argument) {
    return argument.type.type;
}

cir::TypeId template_argument_value_type_id(
    const Session::TemplateArgument& argument) {
    return argument.value_type.type;
}

void append_key_word(std::string& key, uint64_t value) {
    char bytes[sizeof(value)];
    std::memcpy(bytes, &value, sizeof(value));
    key.append(bytes, sizeof(bytes));
}

void append_key_string(std::string& key, std::string_view value) {
    append_key_word(key, value.size());
    key.append(value);
}

enum class MemoKeyFamily : uint64_t {
    TemplateReplay = 0,
    DefaultCompletion = 1,
    ArgumentListParsing = 2,
};

void append_template_value_expr_key(std::string& key,
                                    const cir::TemplateValueExpression& expr) {
    if (!expr.valid()) {
        append_key_word(key, 0);
        return;
    }
    append_key_word(key, 1);
    append_key_word(key, expr.root);
    append_key_word(key, expr.nodes.size());
    for (const cir::TemplateValueExprNode& node : expr.nodes) {
        append_key_word(key, static_cast<uint64_t>(node.kind));
        append_key_word(key, static_cast<uint64_t>(node.op));
        append_key_word(key, static_cast<uint64_t>(node.trait_kind));
        append_key_word(key, static_cast<uint64_t>(node.fold_kind));
        append_key_word(key, static_cast<uint64_t>(node.value));
        append_key_word(key, node.integer_value.low_bits);
        append_key_word(key, node.integer_value.high_bits);
        append_key_word(key, node.integer_value.bit_width);
        append_key_word(key, node.integer_value.is_unsigned);
        append_key_word(key, node.parameter_index);
        append_key_word(key, node.lhs);
        append_key_word(key, node.rhs);
        append_key_word(key, node.third);
        append_key_word(key, node.operands.size());
        for (uint32_t operand : node.operands) {
            append_key_word(key, operand);
        }
        append_key_word(key, node.expands_parameter_pack);
        append_key_word(key, node.pack_references.size());
        for (const cir::TemplateValuePackReference& reference :
             node.pack_references) {
            append_key_word(key, static_cast<uint64_t>(reference.kind));
            append_key_word(key, reference.declaration.index);
            append_key_word(key, reference.declaration.generation);
            append_key_word(key, reference.owner.index);
            append_key_word(key, reference.owner.generation);
            append_key_word(key, reference.depth);
            append_key_word(key, reference.index);
            append_key_word(key, reference.parameter_type.index);
            append_key_word(key, reference.parameter_type.generation);
            append_key_word(key, reference.name.index);
            append_key_word(key, reference.name.generation);
        }
        append_key_word(key, node.type.index);
        append_key_word(key, node.result_type.type.index);
        append_key_word(key, node.result_type.qualifiers);
        append_key_word(key,
                        static_cast<uint64_t>(node.result_type.memory_space));
        append_key_word(key, node.entity.index);
        append_key_word(key, node.entity.generation);
        append_key_word(key, node.name.index);
        append_key_word(key, node.name.generation);
        append_key_word(key, node.qualifier_type.type.index);
        append_key_word(key, node.qualifier_type.qualifiers);
        append_key_word(key,
                        static_cast<uint64_t>(node.qualifier_type.memory_space));
        append_key_string(key, node.semantic_key);
    }
}

std::string template_value_expr_op_spelling(cir::TemplateValueExprOp op) {
    switch (op) {
        case cir::TemplateValueExprOp::Add: return " + ";
        case cir::TemplateValueExprOp::Sub: return " - ";
        case cir::TemplateValueExprOp::Mul: return " * ";
        case cir::TemplateValueExprOp::Div: return " / ";
        case cir::TemplateValueExprOp::Mod: return " % ";
        case cir::TemplateValueExprOp::Shl: return " << ";
        case cir::TemplateValueExprOp::Shr: return " >> ";
        case cir::TemplateValueExprOp::BitAnd: return " & ";
        case cir::TemplateValueExprOp::BitOr: return " | ";
        case cir::TemplateValueExprOp::BitXor: return " ^ ";
        case cir::TemplateValueExprOp::Less: return " < ";
        case cir::TemplateValueExprOp::LessEqual: return " <= ";
        case cir::TemplateValueExprOp::Greater: return " > ";
        case cir::TemplateValueExprOp::GreaterEqual: return " >= ";
        case cir::TemplateValueExprOp::Equal: return " == ";
        case cir::TemplateValueExprOp::NotEqual: return " != ";
        case cir::TemplateValueExprOp::ThreeWay: return " <=> ";
        case cir::TemplateValueExprOp::LogicalAnd: return " && ";
        case cir::TemplateValueExprOp::LogicalOr: return " || ";
        case cir::TemplateValueExprOp::Comma: return ", ";
        case cir::TemplateValueExprOp::MemberPointerDot: return " .* ";
        case cir::TemplateValueExprOp::MemberPointerArrow: return " ->* ";
        case cir::TemplateValueExprOp::UnaryPlus:
        case cir::TemplateValueExprOp::UnaryMinus:
        case cir::TemplateValueExprOp::LogicalNot:
        case cir::TemplateValueExprOp::BitwiseNot:
        case cir::TemplateValueExprOp::Dereference:
        case cir::TemplateValueExprOp::Delete:
        case cir::TemplateValueExprOp::DeleteArray:
        case cir::TemplateValueExprOp::AddressOf:
        case cir::TemplateValueExprOp::None: return " ? ";
    }
    return " ? ";
}

std::string template_value_expr_display(const cir::TemplateValueExpression& expr,
                                        uint32_t index) {
    if (index == cir::TemplateValueExprNoNode || index >= expr.nodes.size()) {
        return "<value-expr>";
    }
    const cir::TemplateValueExprNode& node = expr.nodes[index];
    switch (node.kind) {
        case cir::TemplateValueExprKind::Integer:
            return node.integer_value.decimal();
        case cir::TemplateValueExprKind::Parameter:
            return "$" + std::to_string(node.parameter_index);
        case cir::TemplateValueExprKind::PackSize:
            return "sizeof...($" + std::to_string(node.parameter_index) + ")";
        case cir::TemplateValueExprKind::PackIndex:
            return "$" + std::to_string(node.parameter_index) + "...[" +
                   template_value_expr_display(expr, node.lhs) + "]";
        case cir::TemplateValueExprKind::Entity:
            return node.name.valid()
                ? "@" + std::to_string(node.name.index)
                : "@entity" + std::to_string(node.entity.index);
        case cir::TemplateValueExprKind::Unary: {
            const char* spelling = "?";
            switch (node.op) {
                case cir::TemplateValueExprOp::UnaryPlus: spelling = "+"; break;
                case cir::TemplateValueExprOp::UnaryMinus: spelling = "-"; break;
                case cir::TemplateValueExprOp::LogicalNot: spelling = "!"; break;
                case cir::TemplateValueExprOp::BitwiseNot: spelling = "~"; break;
                case cir::TemplateValueExprOp::Dereference: spelling = "*"; break;
                case cir::TemplateValueExprOp::AddressOf: spelling = "&"; break;
                case cir::TemplateValueExprOp::Delete:
                    spelling = "delete ";
                    break;
                case cir::TemplateValueExprOp::DeleteArray:
                    spelling = "delete[] ";
                    break;
                default: break;
            }
            return "(" + std::string(spelling) +
                   template_value_expr_display(expr, node.lhs) + ")";
        }
        case cir::TemplateValueExprKind::Binary:
            return "(" + template_value_expr_display(expr, node.lhs) +
                   template_value_expr_op_spelling(node.op) +
                   template_value_expr_display(expr, node.rhs) + ")";
        case cir::TemplateValueExprKind::Conditional:
            return "(" + template_value_expr_display(expr, node.lhs) +
                   " ? " + template_value_expr_display(expr, node.rhs) +
                   " : " + template_value_expr_display(expr, node.third) +
                   ")";
        case cir::TemplateValueExprKind::Cast:
            return "cast(" + template_value_expr_display(expr, node.lhs) +
                   ")";
        case cir::TemplateValueExprKind::SizeofType:
            return "sizeof(@" + std::to_string(node.type.index) + ")";
        case cir::TemplateValueExprKind::AlignofType:
            return "alignof(@" + std::to_string(node.type.index) + ")";
        case cir::TemplateValueExprKind::TypeTrait: {
            std::string result = node.semantic_key + "(";
            for (size_t i = 0; i < node.operands.size(); ++i) {
                if (i != 0) {
                    result += ", ";
                }
                result += template_value_expr_display(expr,
                                                      node.operands[i]);
            }
            return result + ")";
        }
        case cir::TemplateValueExprKind::TypeOperand:
            return "type(" + node.semantic_key + ")";
        case cir::TemplateValueExprKind::Callee: {
            if (node.lhs != cir::TemplateValueExprNoNode) {
                return "callee(" +
                    template_value_expr_display(expr, node.lhs) + ")";
            }
            std::string target = node.semantic_key.empty()
                ? std::string("<named-callee>")
                : node.semantic_key;
            if (node.rhs != cir::TemplateValueExprNoNode) {
                bool arrow =
                    (static_cast<uint64_t>(node.value) &
                     static_cast<uint32_t>(
                         cir::TemplateCalleeFlag::MemberArrow)) != 0;
                return "callee(" +
                    template_value_expr_display(expr, node.rhs) +
                    (arrow ? "->" : ".") + target + ")";
            }
            return "callee(" + target + ")";
        }
        case cir::TemplateValueExprKind::Call:
            return "call(" +
                template_value_expr_display(expr, node.third) + ")";
        case cir::TemplateValueExprKind::Noexcept:
            return "noexcept(" +
                   template_value_expr_display(expr, node.lhs) + ")";
        case cir::TemplateValueExprKind::ConceptId:
            return "concept-id(" +
                (node.semantic_key.empty()
                     ? std::string("<concept>")
                     : node.semantic_key) +
                ")";
        case cir::TemplateValueExprKind::Fold: {
            const char* form = "fold";
            switch (node.fold_kind) {
                case cir::TemplateValueFoldKind::UnaryLeft:
                    form = "fold-unary-left";
                    break;
                case cir::TemplateValueFoldKind::UnaryRight:
                    form = "fold-unary-right";
                    break;
                case cir::TemplateValueFoldKind::BinaryLeft:
                    form = "fold-binary-left";
                    break;
                case cir::TemplateValueFoldKind::BinaryRight:
                    form = "fold-binary-right";
                    break;
                case cir::TemplateValueFoldKind::None:
                    break;
            }
            std::string result = std::string(form) + "(" +
                template_value_expr_display(expr, node.lhs);
            if (node.rhs != cir::TemplateValueExprNoNode) {
                result += ", " +
                    template_value_expr_display(expr, node.rhs);
            }
            return result + ")";
        }
        case cir::TemplateValueExprKind::None:
            return "<value-expr>";
    }
    return "<value-expr>";
}

std::string template_value_expr_display(const cir::TemplateValueExpression& expr) {
    return template_value_expr_display(expr, expr.root);
}

bool template_parameter_is_type(const Session::TemplateParameter& parameter) {
    return parameter.kind == Session::TemplateParameterKind::Type;
}

bool template_parameter_is_value(const Session::TemplateParameter& parameter) {
    return parameter.kind == Session::TemplateParameterKind::NonType;
}

const Session::TemplateArgumentBinding* substitution_binding(
    const Session::TemplateArgumentBindings& bindings,
    uint32_t parameter_index) {
    if (parameter_index >= bindings.size()) {
        return nullptr;
    }
    return &bindings[parameter_index];
}

const Session::TemplateArgumentBinding* exact_or_positional_binding(
    const Session::TemplateArgumentBindings& bindings,
    uint32_t parameter_index,
    cir::EntityId parameter_entity,
    const std::unordered_map<uint32_t, Session::TemplateArgumentBinding>&
        exact_bindings) {
    if (parameter_entity.valid()) {
        auto exact = exact_bindings.find(
            static_cast<uint32_t>(parameter_entity.index));
        if (exact != exact_bindings.end()) {
            return &exact->second;
        }

    }
    return substitution_binding(bindings, parameter_index);
}

const Session::TemplateArgumentBinding* pack_reference_binding(
    const Session::TemplateArgumentBindings& bindings,
    const Session::PatternInstantiationCallbacks& callbacks,
    const cir::TemplateValuePackReference& reference) {
    if (reference.kind == cir::TemplateValuePackKind::Type &&
        reference.parameter_type.valid()) {
        auto exact = callbacks.exact_type_parameter_bindings.find(
            static_cast<uint32_t>(reference.parameter_type.index));
        if (exact != callbacks.exact_type_parameter_bindings.end()) {
            return &exact->second;
        }
    } else if (reference.kind == cir::TemplateValuePackKind::Value &&
               reference.declaration.valid()) {
        auto exact = callbacks.exact_value_parameter_bindings.find(
            static_cast<uint32_t>(reference.declaration.index));
        if (exact != callbacks.exact_value_parameter_bindings.end()) {
            return &exact->second;
        }
    } else if (reference.kind == cir::TemplateValuePackKind::Template &&
               reference.declaration.valid()) {
        auto exact = callbacks.exact_template_parameter_bindings.find(
            static_cast<uint32_t>(reference.declaration.index));
        if (exact != callbacks.exact_template_parameter_bindings.end()) {
            return &exact->second;
        }
    }
    return substitution_binding(bindings, reference.index);
}

bool template_argument_has_symbolic_cardinality(
    const Session::TemplateArgument& argument) {
    return argument.expands_parameter_pack ||
        argument.expands_pack_pattern ||
        argument.generated_pack_kind !=
            cir::TemplateGeneratedPackKind::None;
}

enum class CoordinatedPackCardinalityStatus : uint8_t {
    Concrete,
    StillDependent,
    LengthMismatch,
    Failure,
};

struct CoordinatedPackCardinality {
    CoordinatedPackCardinalityStatus status =
        CoordinatedPackCardinalityStatus::Failure;
    size_t width = 0;
};

CoordinatedPackCardinality resolve_coordinated_pack_cardinality(
    const std::vector<cir::TemplateValuePackReference>& references,
    const Session::TemplateArgumentBindings& bindings,
    const Session::PatternInstantiationCallbacks& callbacks) {
    if (references.empty()) {
        return {};
    }
    std::optional<size_t> width;
    bool still_dependent = false;
    for (const cir::TemplateValuePackReference& reference : references) {
        const Session::TemplateArgumentBinding* binding =
            pack_reference_binding(bindings, callbacks, reference);
        if (!binding || binding->is_unbound()) {
            still_dependent = true;
            continue;
        }
        if (!binding->is_pack()) {
            return {CoordinatedPackCardinalityStatus::Failure, 0};
        }
        if (std::any_of(binding->arguments.begin(),
                        binding->arguments.end(),
                        template_argument_has_symbolic_cardinality)) {
            still_dependent = true;
            continue;
        }
        if (width.has_value() && *width != binding->arguments.size()) {
            return {
                CoordinatedPackCardinalityStatus::LengthMismatch, 0};
        }
        width = binding->arguments.size();
    }
    if (still_dependent) {
        return {CoordinatedPackCardinalityStatus::StillDependent, 0};
    }
    return {CoordinatedPackCardinalityStatus::Concrete,
            width.value_or(0)};
}

const Session::TemplateArgument* single_argument_from_binding(
    const Session::TemplateArgumentBinding* binding,
    bool allow_pack_element = false) {
    if (!binding || binding->arguments.size() != 1 ||
        (!binding->is_single() &&
         !(allow_pack_element && binding->is_pack()))) {
        return nullptr;
    }
    return &binding->arguments.front();
}

const Session::TemplateArgument* single_substitution_argument(
    const Session::TemplateArgumentBindings& bindings,
    uint32_t parameter_index,
    bool allow_pack_element = false) {
    const Session::TemplateArgumentBinding* binding =
        substitution_binding(bindings, parameter_index);
    return single_argument_from_binding(binding, allow_pack_element);
}

std::optional<int64_t> template_value_argument_integer(
    const Session::TemplateArgument& argument) {
    if (argument.kind != cir::TemplateArgumentKind::Value) {
        return std::nullopt;
    }
    if (argument.value_kind == cir::TemplateValueKind::Integer ||
        argument.value_kind == cir::TemplateValueKind::Boolean) {
        return argument.integer_value.try_as_int64();
    }
    return std::nullopt;
}

std::optional<int64_t> evaluate_template_value_expr_node(
    Session& session,
    const cir::TemplateValueExpression& expr,
    uint32_t index,
    const Session::TemplateArgumentBindings& argument_bindings,
    Session::PatternInstantiationCallbacks& callbacks,
    bool* invalid,
    std::string* error_out) {
    if (index == cir::TemplateValueExprNoNode || index >= expr.nodes.size()) {
        return std::nullopt;
    }
    const cir::TemplateValueExprNode& node = expr.nodes[index];
    switch (node.kind) {
        case cir::TemplateValueExprKind::Integer:
            return node.integer_value.try_as_int64();
        case cir::TemplateValueExprKind::Parameter:
            if (const Session::TemplateArgument* argument =
                    single_argument_from_binding(
                        exact_or_positional_binding(argument_bindings,
                                                    node.parameter_index,
                                                    node.entity,
                                                    callbacks
                                                        .exact_value_parameter_bindings),
                        callbacks
                            .allow_parameter_pack_element_substitution)) {
                return template_value_argument_integer(*argument);
            } else {
                return std::nullopt;
            }
        case cir::TemplateValueExprKind::PackSize: {
            if (!node.pack_references.empty()) {
                CoordinatedPackCardinality cardinality =
                    resolve_coordinated_pack_cardinality(
                        node.pack_references,
                        argument_bindings,
                        callbacks);
                return cardinality.status ==
                        CoordinatedPackCardinalityStatus::Concrete
                    ? std::optional<int64_t>(
                          static_cast<int64_t>(cardinality.width))
                    : std::nullopt;
            }
            const Session::TemplateArgumentBinding* binding =
                exact_or_positional_binding(argument_bindings,
                                            node.parameter_index,
                                            node.entity,
                                            callbacks
                                                .exact_value_parameter_bindings);
            if (!binding || !binding->is_pack()) {
                return std::nullopt;
            }
            if (std::any_of(
                    binding->arguments.begin(),
                    binding->arguments.end(),
                    [](const Session::TemplateArgument& argument) {
                        return argument.expands_parameter_pack ||
                            argument.expands_pack_pattern ||
                            argument.generated_pack_kind !=
                                cir::TemplateGeneratedPackKind::None;
                    })) {

                return std::nullopt;
            }
            return static_cast<int64_t>(binding->arguments.size());
        }
        case cir::TemplateValueExprKind::PackIndex: {
            std::optional<int64_t> selected =
                evaluate_template_value_expr_node(session,
                                                  expr,
                                                  node.lhs,
                                                  argument_bindings,
                                                  callbacks,
                                                  invalid,
                                                  error_out);
            const Session::TemplateArgumentBinding* binding =
                exact_or_positional_binding(argument_bindings,
                                            node.parameter_index,
                                            node.entity,
                                            callbacks
                                                .exact_value_parameter_bindings);
            if (!selected.has_value() || *selected < 0 || !binding ||
                !binding->is_pack() ||
                static_cast<size_t>(*selected) >= binding->arguments.size()) {
                return std::nullopt;
            }
            return template_value_argument_integer(
                binding->arguments[static_cast<size_t>(*selected)]);
        }
        case cir::TemplateValueExprKind::Entity:

            return std::nullopt;
        case cir::TemplateValueExprKind::Unary: {
            std::optional<int64_t> operand =
                evaluate_template_value_expr_node(session,
                                                  expr,
                                                  node.lhs,
                                                  argument_bindings,
                                                  callbacks,
                                                  invalid,
                                                  error_out);
            if (!operand.has_value()) {
                return std::nullopt;
            }
            switch (node.op) {
                case cir::TemplateValueExprOp::UnaryPlus: return *operand;
                case cir::TemplateValueExprOp::UnaryMinus: return -*operand;
                case cir::TemplateValueExprOp::LogicalNot:
                    return *operand == 0;
                case cir::TemplateValueExprOp::BitwiseNot: return ~*operand;
                case cir::TemplateValueExprOp::Dereference:
                case cir::TemplateValueExprOp::Delete:
                case cir::TemplateValueExprOp::DeleteArray:
                case cir::TemplateValueExprOp::AddressOf:
                default: return std::nullopt;
            }
        }
        case cir::TemplateValueExprKind::Binary: {
            std::optional<int64_t> lhs =
                evaluate_template_value_expr_node(session,
                                                  expr,
                                                  node.lhs,
                                                  argument_bindings,
                                                  callbacks,
                                                  invalid,
                                                  error_out);
            if (!lhs.has_value()) {
                return std::nullopt;
            }
            if (node.op == cir::TemplateValueExprOp::LogicalAnd &&
                *lhs == 0) {
                return 0;
            }
            if (node.op == cir::TemplateValueExprOp::LogicalOr &&
                *lhs != 0) {
                return 1;
            }
            std::optional<int64_t> rhs =
                evaluate_template_value_expr_node(session,
                                                  expr,
                                                  node.rhs,
                                                  argument_bindings,
                                                  callbacks,
                                                  invalid,
                                                  error_out);
            if (!rhs.has_value()) {
                return std::nullopt;
            }
            switch (node.op) {
                case cir::TemplateValueExprOp::Add: return *lhs + *rhs;
                case cir::TemplateValueExprOp::Sub: return *lhs - *rhs;
                case cir::TemplateValueExprOp::Mul: return *lhs * *rhs;
                case cir::TemplateValueExprOp::Div:
                    return *rhs == 0 ? std::nullopt
                                     : std::optional<int64_t>(*lhs / *rhs);
                case cir::TemplateValueExprOp::Mod:
                    return *rhs == 0 ? std::nullopt
                                     : std::optional<int64_t>(*lhs % *rhs);
                case cir::TemplateValueExprOp::Shl:
                    return (*rhs < 0 || *rhs >= 63)
                        ? std::nullopt
                        : std::optional<int64_t>(*lhs << *rhs);
                case cir::TemplateValueExprOp::Shr:
                    return (*rhs < 0 || *rhs >= 63)
                        ? std::nullopt
                        : std::optional<int64_t>(*lhs >> *rhs);
                case cir::TemplateValueExprOp::BitAnd: return *lhs & *rhs;
                case cir::TemplateValueExprOp::BitOr: return *lhs | *rhs;
                case cir::TemplateValueExprOp::BitXor: return *lhs ^ *rhs;
                case cir::TemplateValueExprOp::Less: return *lhs < *rhs;
                case cir::TemplateValueExprOp::LessEqual: return *lhs <= *rhs;
                case cir::TemplateValueExprOp::Greater: return *lhs > *rhs;
                case cir::TemplateValueExprOp::GreaterEqual:
                    return *lhs >= *rhs;
                case cir::TemplateValueExprOp::Equal: return *lhs == *rhs;
                case cir::TemplateValueExprOp::NotEqual: return *lhs != *rhs;
                case cir::TemplateValueExprOp::ThreeWay:
                    return *lhs < *rhs ? -1 : (*lhs > *rhs ? 1 : 0);
                case cir::TemplateValueExprOp::LogicalAnd:
                    return *lhs != 0 && *rhs != 0;
                case cir::TemplateValueExprOp::LogicalOr:
                    return *lhs != 0 || *rhs != 0;
                case cir::TemplateValueExprOp::Comma: return *rhs;
                case cir::TemplateValueExprOp::MemberPointerDot:
                case cir::TemplateValueExprOp::MemberPointerArrow:
                case cir::TemplateValueExprOp::UnaryPlus:
                case cir::TemplateValueExprOp::UnaryMinus:
                case cir::TemplateValueExprOp::LogicalNot:
                case cir::TemplateValueExprOp::BitwiseNot:
                case cir::TemplateValueExprOp::Dereference:
                case cir::TemplateValueExprOp::Delete:
                case cir::TemplateValueExprOp::DeleteArray:
                case cir::TemplateValueExprOp::AddressOf:
                case cir::TemplateValueExprOp::None:
                    return std::nullopt;
            }
            return std::nullopt;
        }
        case cir::TemplateValueExprKind::Conditional: {
            std::optional<int64_t> condition =
                evaluate_template_value_expr_node(session,
                                                  expr,
                                                  node.lhs,
                                                  argument_bindings,
                                                  callbacks,
                                                  invalid,
                                                  error_out);
            if (!condition.has_value()) {
                return std::nullopt;
            }
            return evaluate_template_value_expr_node(
                session,
                expr,
                *condition != 0 ? node.rhs : node.third,
                argument_bindings,
                callbacks,
                invalid,
                error_out);
        }
        case cir::TemplateValueExprKind::Cast:
            return evaluate_template_value_expr_node(session,
                                                     expr,
                                                     node.lhs,
                                                     argument_bindings,
                                                     callbacks,
                                                     invalid,
                                                     error_out);
        case cir::TemplateValueExprKind::SizeofType:
        case cir::TemplateValueExprKind::AlignofType:
        case cir::TemplateValueExprKind::TypeTrait:
        case cir::TemplateValueExprKind::TypeOperand:
        case cir::TemplateValueExprKind::Callee:
        case cir::TemplateValueExprKind::Call:
        case cir::TemplateValueExprKind::Noexcept:
        case cir::TemplateValueExprKind::Fold:

            return std::nullopt;
        case cir::TemplateValueExprKind::ConceptId: {
            cir::EntityId concept_entity = node.entity;
            const bool target_is_parameter =
                (concept_entity.valid() &&
                 session.file().valid(concept_entity) &&
                 session.file().entity(concept_entity).kind ==
                     cir::EntityKind::TemplateParam) ||
                node.parameter_index !=
                    cir::ArrayTypePayload::no_extent_param;
            if (target_is_parameter) {
                Session::TemplateArgument target;
                target.kind = cir::TemplateArgumentKind::Template;
                target.template_entity = concept_entity;
                target.template_param_index = node.parameter_index;
                target.template_name = node.name;
                target.dependent_template_qualifier =
                    node.qualifier_type;
                target.is_dependent = true;
                if (!session.substitute_template_template_argument(
                        target,
                        argument_bindings,
                        callbacks,
                        error_out)) {
                    if (invalid) {
                        *invalid = true;
                    }
                    return std::nullopt;
                }
                concept_entity = target.template_entity;
            }
            if (!concept_entity.valid() ||
                !session.file().valid(concept_entity)) {
                if (target_is_parameter) {
                    return std::nullopt;
                }
                if (invalid) {
                    *invalid = true;
                }
                if (error_out) {
                    *error_out =
                        "dependent concept-id target is unavailable";
                }
                return std::nullopt;
            }
            if (session.file().entity(concept_entity).kind ==
                cir::EntityKind::TemplateParam) {
                return std::nullopt;
            }

            std::vector<Session::TemplateArgument> arguments;
            arguments.reserve(node.template_arguments.size());
            for (const Session::TemplateArgument& argument :
                 node.template_arguments.values()) {
                if (!session.append_substituted_template_argument(
                        argument,
                        argument_bindings,
                        callbacks,
                        arguments,
                        /*reject_unresolved_template_parameter=*/false,
                        error_out)) {
                    if (invalid) {
                        *invalid = true;
                    }
                    return std::nullopt;
                }
            }
            const bool still_dependent = std::any_of(
                arguments.begin(),
                arguments.end(),
                [&](const Session::TemplateArgument& argument) {
                    if (argument.is_dependent ||
                        argument.expands_parameter_pack ||
                        argument.expands_pack_pattern ||
                        argument.generated_pack_kind !=
                            cir::TemplateGeneratedPackKind::None) {
                        return true;
                    }
                    switch (argument.kind) {
                        case cir::TemplateArgumentKind::Type:
                            return argument.type.type.valid() &&
                                session.is_dependent_type(
                                    argument.type.type);
                        case cir::TemplateArgumentKind::Value:
                            return argument.dependent_value_expr.valid() ||
                                argument.dependent_value_qualifier.type
                                    .valid() ||
                                argument.value_param_index !=
                                    cir::ArrayTypePayload::no_extent_param;
                        case cir::TemplateArgumentKind::Template:
                            return !argument.template_entity.valid() ||
                                (session.file().valid(
                                     argument.template_entity) &&
                                 session.file()
                                         .entity(argument.template_entity)
                                         .kind ==
                                     cir::EntityKind::TemplateParam) ||
                                argument.template_param_index !=
                                    cir::ArrayTypePayload::no_extent_param ||
                                argument.dependent_template_qualifier.type
                                    .valid();
                    }
                    return true;
                });
            if (still_dependent || !callbacks.evaluate_concept_id) {
                return std::nullopt;
            }

            switch (callbacks.evaluate_concept_id(
                concept_entity,
                std::move(arguments),
                expr.definition_lookup_generation)) {
                case Session::ConceptValueEvaluationStatus::Satisfied:
                    return 1;
                case Session::ConceptValueEvaluationStatus::Unsatisfied:
                    return 0;
                case Session::ConceptValueEvaluationStatus::StillDependent:
                    return std::nullopt;
                case Session::ConceptValueEvaluationStatus::Invalid:
                    if (invalid) {
                        *invalid = true;
                    }
                    if (error_out) {
                        *error_out =
                            "dependent concept-id could not be evaluated";
                    }
                    return std::nullopt;
            }
            return std::nullopt;
        }
        case cir::TemplateValueExprKind::None:
            return std::nullopt;
    }
    return std::nullopt;
}

std::optional<int64_t> evaluate_template_value_expr(
    Session& session,
    const cir::TemplateValueExpression& expr,
    const Session::TemplateArgumentBindings& argument_bindings,
    Session::PatternInstantiationCallbacks& callbacks,
    bool* invalid,
    std::string* error_out) {
    if (!expr.valid()) {
        return std::nullopt;
    }
    return evaluate_template_value_expr_node(session,
                                             expr,
                                             expr.root,
                                             argument_bindings,
                                             callbacks,
                                             invalid,
                                             error_out);
}

std::optional<cir::TemplateValuePackReference>
direct_symbolic_pack_reference(
    Session& session,
    const Session::TemplateArgument& argument) {
    if (!argument.expands_parameter_pack || argument.expands_pack_pattern) {
        return std::nullopt;
    }

    cir::TemplateValuePackReference reference;
    switch (argument.kind) {
        case cir::TemplateArgumentKind::Type: {
            std::optional<uint32_t> index =
                session.type_parameter_pack_index(argument.type.type);
            if (!index.has_value()) {
                return std::nullopt;
            }
            reference.kind = cir::TemplateValuePackKind::Type;
            reference.index = *index;
            reference.parameter_type = argument.type.type;
            cir::File& file = session.file();
            cir::TypeId resolved = file.resolved_type(argument.type.type);
            if (file.valid(resolved) &&
                file.type(resolved).kind == cir::TypeKind::TypeParam) {
                const auto& parameter =
                    std::get<cir::TypeParamTypePayload>(
                        file.type_payload(resolved));
                reference.declaration = parameter.entity;
                reference.depth = parameter.depth;
                reference.name = parameter.name;
            }
            return reference;
        }
        case cir::TemplateArgumentKind::Value:
            if (argument.value_param_index ==
                cir::ArrayTypePayload::no_extent_param) {
                return std::nullopt;
            }
            reference.kind = cir::TemplateValuePackKind::Value;
            reference.index = argument.value_param_index;
            reference.declaration = argument.value_entity;
            reference.name = argument.dependent_value_name;
            return reference;
        case cir::TemplateArgumentKind::Template:
            if (argument.template_param_index ==
                cir::ArrayTypePayload::no_extent_param) {
                return std::nullopt;
            }
            reference.kind = cir::TemplateValuePackKind::Template;
            reference.index = argument.template_param_index;
            reference.declaration = argument.template_entity;
            reference.name = argument.template_name;
            return reference;
    }
    return std::nullopt;
}

std::optional<cir::TemplateValueExpression> substitute_template_value_expr(
    Session& session,
    const cir::TemplateValueExpression& expr,
    const Session::TemplateArgumentBindings& argument_bindings,
    Session::PatternInstantiationCallbacks& callbacks,
    std::string* error_out) {
    if (!expr.valid()) {
        return std::nullopt;
    }

    cir::TemplateValueExpression result;
    result.loc = expr.loc;
    result.definition_context = expr.definition_context;
    result.definition_lookup_generation = expr.definition_lookup_generation;
    auto append_node = [&](cir::TemplateValueExprNode node) {
        result.nodes.push_back(std::move(node));
        return static_cast<uint32_t>(result.nodes.size() - 1);
    };
    std::function<std::optional<uint32_t>(
        const cir::TemplateValueExpression&, uint32_t)> append_raw;
    append_raw = [&](const cir::TemplateValueExpression& source,
                     uint32_t index) -> std::optional<uint32_t> {
        if (index == cir::TemplateValueExprNoNode ||
            index >= source.nodes.size()) {
            return std::nullopt;
        }
        cir::TemplateValueExprNode node = source.nodes[index];
        if (node.lhs != cir::TemplateValueExprNoNode) {
            std::optional<uint32_t> lhs = append_raw(source, node.lhs);
            if (!lhs.has_value()) {
                return std::nullopt;
            }
            node.lhs = *lhs;
        }
        if (node.rhs != cir::TemplateValueExprNoNode) {
            std::optional<uint32_t> rhs = append_raw(source, node.rhs);
            if (!rhs.has_value()) {
                return std::nullopt;
            }
            node.rhs = *rhs;
        }
        if (node.third != cir::TemplateValueExprNoNode) {
            std::optional<uint32_t> third = append_raw(source, node.third);
            if (!third.has_value()) {
                return std::nullopt;
            }
            node.third = *third;
        }
        for (uint32_t& operand : node.operands) {
            std::optional<uint32_t> substituted = append_raw(source, operand);
            if (!substituted.has_value()) {
                return std::nullopt;
            }
            operand = *substituted;
        }
        return append_node(std::move(node));
    };

    std::function<std::optional<uint32_t>(uint32_t)> append_substituted;
    append_substituted = [&](uint32_t index) -> std::optional<uint32_t> {
        if (index == cir::TemplateValueExprNoNode ||
            index >= expr.nodes.size()) {
            return std::nullopt;
        }
        const cir::TemplateValueExprNode& source = expr.nodes[index];
        if (source.kind == cir::TemplateValueExprKind::Parameter) {
            const Session::TemplateArgument* argument =
                single_argument_from_binding(
                    exact_or_positional_binding(argument_bindings,
                                                source.parameter_index,
                                                source.entity,
                                                callbacks
                                                    .exact_value_parameter_bindings),
                    callbacks
                        .allow_parameter_pack_element_substitution);
            if (!argument ||
                argument->kind != cir::TemplateArgumentKind::Value) {
                return std::nullopt;
            }
            if (argument->value_kind == cir::TemplateValueKind::Integer ||
                argument->value_kind == cir::TemplateValueKind::Boolean) {
                cir::TypeRef result_type = argument->value_type.type.valid()
                    ? argument->value_type
                    : source.result_type;
                cir::TemplateValueExprNode integer =
                    session.file().template_integer_expression_node(
                        argument->integer_value, result_type);
                return append_node(std::move(integer));
            }
            if (argument->dependent_value_expr.valid()) {

                return append_raw(argument->dependent_value_expr,
                                  argument->dependent_value_expr.root);
            }
            if (argument->dependent_value_qualifier.type.valid() &&
                argument->dependent_value_name.valid()) {

                cir::TemplateValueExprNode qualified_constant;
                qualified_constant.kind =
                    cir::TemplateValueExprKind::TypeOperand;
                qualified_constant.value =
                    static_cast<int64_t>(ValueCategory::Dependent);
                qualified_constant.result_type =
                    argument->value_type.type.valid()
                        ? argument->value_type
                        : source.result_type;
                qualified_constant.name =
                    argument->dependent_value_name;
                qualified_constant.qualifier_type =
                    argument->dependent_value_qualifier;
                qualified_constant.semantic_key = std::string(
                    session.file().name(argument->dependent_value_name));
                return append_node(std::move(qualified_constant));
            }
            if (argument->value_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
                cir::TemplateValueExprNode parameter;
                parameter.kind = cir::TemplateValueExprKind::Parameter;
                parameter.parameter_index = argument->value_param_index;
                parameter.result_type = argument->value_type.type.valid()
                    ? argument->value_type
                    : source.result_type;
                return append_node(std::move(parameter));
            }
            return std::nullopt;
        }
        if (source.kind == cir::TemplateValueExprKind::PackSize) {
            if (!source.pack_references.empty()) {
                CoordinatedPackCardinality cardinality =
                    resolve_coordinated_pack_cardinality(
                        source.pack_references,
                        argument_bindings,
                        callbacks);
                if (cardinality.status ==
                    CoordinatedPackCardinalityStatus::LengthMismatch) {
                    if (error_out && error_out->empty()) {
                        *error_out =
                            "pack expansion contains packs with different "
                            "lengths";
                    }
                    return std::nullopt;
                }
                if (cardinality.status ==
                    CoordinatedPackCardinalityStatus::Concrete) {
                    cir::TemplateValueExprNode integer =
                        session.file().template_integer_expression_node(
                            cir::IntegerValue::from_unsigned(
                                cardinality.width, 64),
                            source.result_type);
                    return append_node(std::move(integer));
                }
                if (cardinality.status ==
                    CoordinatedPackCardinalityStatus::Failure) {
                    return std::nullopt;
                }
            }

            const Session::TemplateArgumentBinding* binding =
                !source.pack_references.empty()
                ? pack_reference_binding(argument_bindings,
                                         callbacks,
                                         source.pack_references.front())
                : exact_or_positional_binding(
                      argument_bindings,
                      source.parameter_index,
                      source.entity,
                      callbacks.exact_value_parameter_bindings);
            if ((!binding || binding->is_unbound()) &&
                !source.pack_references.empty()) {

                return append_node(source);
            }
            if (!binding || !binding->is_pack()) {
                return std::nullopt;
            }

            int64_t concrete_count = 0;
            std::vector<uint32_t> symbolic_counts;
            for (const Session::TemplateArgument& argument :
                 binding->arguments) {
                if (argument.generated_pack_kind !=
                    cir::TemplateGeneratedPackKind::None) {
                    if (!argument.generated_pack_count_expr.valid()) {
                        return std::nullopt;
                    }
                    std::optional<uint32_t> count = append_raw(
                        argument.generated_pack_count_expr,
                        argument.generated_pack_count_expr.root);
                    if (!count.has_value()) {
                        return std::nullopt;
                    }
                    symbolic_counts.push_back(*count);
                    continue;
                }
                if (argument.expands_pack_pattern) {
                    std::vector<cir::TemplateValuePackReference> references;
                    Session::PackPatternExpansionStatus status =
                        session.expand_template_argument_pack_pattern(
                            argument,
                            argument_bindings,
                            callbacks,
                            nullptr,
                            &references);
                    if (status ==
                        Session::PackPatternExpansionStatus::LengthMismatch) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                "pack expansion contains packs with different "
                                "lengths";
                        }
                        return std::nullopt;
                    }
                    if (references.empty() ||
                        status ==
                            Session::PackPatternExpansionStatus::Failure ||
                        status ==
                            Session::PackPatternExpansionStatus::NoPacks) {
                        return std::nullopt;
                    }
                    cir::TemplateValueExprNode pack_size;
                    pack_size.kind = cir::TemplateValueExprKind::PackSize;
                    pack_size.parameter_index = references.front().index;
                    pack_size.result_type = source.result_type;
                    pack_size.entity = references.front().declaration;
                    pack_size.pack_references = std::move(references);
                    symbolic_counts.push_back(
                        append_node(std::move(pack_size)));
                    continue;
                }
                if (argument.expands_parameter_pack) {
                    std::optional<cir::TemplateValuePackReference> reference =
                        direct_symbolic_pack_reference(session, argument);
                    if (!reference.has_value()) {
                        return std::nullopt;
                    }
                    cir::TemplateValueExprNode pack_size;
                    pack_size.kind = cir::TemplateValueExprKind::PackSize;
                    pack_size.parameter_index = reference->index;
                    pack_size.result_type = source.result_type;
                    pack_size.entity = reference->declaration;
                    symbolic_counts.push_back(
                        append_node(std::move(pack_size)));
                    continue;
                }
                ++concrete_count;
            }

            std::optional<uint32_t> total;
            if (concrete_count != 0 || symbolic_counts.empty()) {
                cir::TemplateValueExprNode integer =
                    session.file().template_integer_expression_node(
                        cir::IntegerValue::from_signed(concrete_count, 64),
                        source.result_type);
                total = append_node(std::move(integer));
            }
            for (uint32_t count : symbolic_counts) {
                if (!total.has_value()) {
                    total = count;
                    continue;
                }
                cir::TemplateValueExprNode add;
                add.kind = cir::TemplateValueExprKind::Binary;
                add.op = cir::TemplateValueExprOp::Add;
                add.lhs = *total;
                add.rhs = count;
                add.result_type = source.result_type;
                total = append_node(std::move(add));
            }
            return total;
        }
        if (source.kind == cir::TemplateValueExprKind::ConceptId) {
            cir::TemplateValueExprNode node = source;
            const bool target_is_parameter =
                (node.entity.valid() &&
                 session.file().valid(node.entity) &&
                 session.file().entity(node.entity).kind ==
                     cir::EntityKind::TemplateParam) ||
                node.parameter_index !=
                    cir::ArrayTypePayload::no_extent_param;
            if (target_is_parameter) {
                Session::TemplateArgument target;
                target.kind = cir::TemplateArgumentKind::Template;
                target.template_entity = node.entity;
                target.template_param_index = node.parameter_index;
                target.template_name = node.name;
                target.dependent_template_qualifier =
                    node.qualifier_type;
                target.is_dependent = true;
                if (!session.substitute_template_template_argument(
                        target,
                        argument_bindings,
                        callbacks,
                        error_out)) {
                    return std::nullopt;
                }
                node.entity = target.template_entity;
                node.parameter_index = target.template_param_index;
                node.name = target.template_name;
                node.qualifier_type =
                    target.dependent_template_qualifier;
            }

            std::vector<Session::TemplateArgument> arguments;
            arguments.reserve(source.template_arguments.size());
            for (const Session::TemplateArgument& argument :
                 source.template_arguments.values()) {
                if (!session.append_substituted_template_argument(
                        argument,
                        argument_bindings,
                        callbacks,
                        arguments,
                        /*reject_unresolved_template_parameter=*/false,
                        error_out)) {
                    return std::nullopt;
                }
            }
            node.template_arguments =
                cir::TemplateArgumentList(std::move(arguments));
            return append_node(std::move(node));
        }

        cir::TemplateValueExprNode node = source;
        if (!source.template_arguments.empty()) {
            std::vector<Session::TemplateArgument> arguments;
            arguments.reserve(source.template_arguments.size());
            for (const Session::TemplateArgument& argument :
                 source.template_arguments.values()) {
                if (!session.append_substituted_template_argument(
                        argument,
                        argument_bindings,
                        callbacks,
                        arguments,
                        /*reject_unresolved_template_parameter=*/false,
                        error_out)) {
                    return std::nullopt;
                }
            }
            node.template_arguments =
                cir::TemplateArgumentList(std::move(arguments));
        }
        if (source.lhs != cir::TemplateValueExprNoNode) {
            std::optional<uint32_t> lhs = append_substituted(source.lhs);
            if (!lhs.has_value()) {
                return std::nullopt;
            }
            node.lhs = *lhs;
        }
        if (source.rhs != cir::TemplateValueExprNoNode) {
            std::optional<uint32_t> rhs = append_substituted(source.rhs);
            if (!rhs.has_value()) {
                return std::nullopt;
            }
            node.rhs = *rhs;
        }
        if (source.third != cir::TemplateValueExprNoNode) {
            std::optional<uint32_t> third =
                append_substituted(source.third);
            if (!third.has_value()) {
                return std::nullopt;
            }
            node.third = *third;
        }
        for (uint32_t& operand : node.operands) {
            std::optional<uint32_t> substituted =
                append_substituted(operand);
            if (!substituted.has_value()) {
                return std::nullopt;
            }
            operand = *substituted;
        }
        return append_node(std::move(node));
    };

    std::optional<uint32_t> root = append_substituted(expr.root);
    if (!root.has_value()) {
        return std::nullopt;
    }
    result.root = *root;
    return result;
}

bool template_value_type_is_null_pointer_target(const Session& session,
                                                cir::TypeId type) {
    return session.file().template_null_kind_for_type(type) ==
        cir::TemplateNullKind::Pointer;
}

bool template_value_type_is_member_pointer_target(
    const Session& session,
    cir::TypeId type) {
    return session.file().template_null_kind_for_type(type) ==
        cir::TemplateNullKind::MemberPointer;
}

bool template_value_type_is_bool(const Session& session,
                                 cir::TypeId type) {
    return session.file().template_value_kind_for_type(type) ==
        cir::TemplateValueKind::Boolean;
}

bool template_value_type_is_nullptr_t(const Session& session,
                                      cir::TypeId type) {
    return session.file().template_null_kind_for_type(type) ==
        cir::TemplateNullKind::Nullptr;
}

cir::TemplateNullKind null_kind_for_value_kind(const cir::File& file,
                                               cir::TypeId type,
                                               cir::TemplateValueKind kind) {
    return kind == cir::TemplateValueKind::Null
        ? file.template_null_kind_for_type(type)
        : cir::TemplateNullKind::None;
}

void set_template_binding_error(std::string* error_out,
                                std::string message) {
    if (error_out) {
        *error_out = std::move(message);
    }
}

Session::TemplateArgumentBindingFailure* set_template_binding_failure(
    Session::TemplateArgumentBindingFailure* failure_out,
    Session::TemplateArgumentBindingFailureKind kind,
    Session::TemplateArgumentBindingFailureReason reason =
        Session::TemplateArgumentBindingFailureReason::None,
    std::string detail = {}) {
    if (!failure_out) {
        return nullptr;
    }
    *failure_out = Session::TemplateArgumentBindingFailure{};
    failure_out->kind = kind;
    failure_out->reason = reason;
    if (!detail.empty()) {
        failure_out->detail =
            std::make_shared<const std::string>(std::move(detail));
    }
    return failure_out;
}

uint32_t minimum_template_argument_count(
    const std::vector<Session::TemplateParameter>& parameters) {
    uint32_t count = 0;
    for (const Session::TemplateParameter& parameter : parameters) {
        if (!parameter.is_parameter_pack &&
            !parameter.default_argument.has_value()) {
            ++count;
        }
    }
    return count;
}

uint32_t supplied_template_argument_count(
    const Session::TemplateArgumentBindings& bindings) {
    uint32_t count = 0;
    for (const Session::TemplateArgumentBinding& binding : bindings) {
        for (const Session::TemplateArgument& argument : binding.arguments) {
            if (!argument.is_defaulted) {
                ++count;
            }
        }
    }
    return count;
}

bool template_value_exprs_equivalent(
    const cir::TemplateValueExpression& lhs,
    const cir::TemplateValueExpression& rhs,
    const cir::File* file = nullptr);

bool template_argument_recipe_equivalent(
    const cir::TemplateArgument& lhs,
    const cir::TemplateArgument& rhs,
    const cir::File* file);

bool template_argument_recipes_equivalent(
    const cir::File& file,
    const std::vector<cir::TemplateArgument>& lhs,
    const std::vector<cir::TemplateArgument>& rhs) {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.size(); ++i) {
        if (!template_argument_recipe_equivalent(lhs[i], rhs[i], &file)) {
            return false;
        }
    }
    return true;
}

bool template_argument_bindings_equivalent(
    const cir::File& file,
    const cir::TemplateArgumentBindings& lhs,
    const cir::TemplateArgumentBindings& rhs) {

    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.size(); ++i) {
        if (lhs[i].kind != rhs[i].kind ||
            !template_argument_recipes_equivalent(
                file, lhs[i].arguments, rhs[i].arguments)) {
            return false;
        }
    }
    return true;
}

bool template_type_refs_equivalent(const cir::File& file,
                                   cir::TypeRef lhs,
                                   cir::TypeRef rhs) {
    if (lhs.qualifiers != rhs.qualifiers ||
        lhs.memory_space != rhs.memory_space) {
        return false;
    }
    cir::TypeId l = file.resolved_type(lhs.type);
    cir::TypeId r = file.resolved_type(rhs.type);
    if (l == r) {
        return true;
    }

    if (!file.valid(l) || !file.valid(r)) {
        return false;
    }
    const cir::Type& lhs_node = file.type(l);
    const cir::Type& rhs_node = file.type(r);
    if (lhs_node.kind != rhs_node.kind) {
        return false;
    }
    switch (lhs_node.kind) {
        case cir::TypeKind::TypeParam: {
            const auto* lhs_param =
                std::get_if<cir::TypeParamTypePayload>(&file.type_payload(l));
            const auto* rhs_param =
                std::get_if<cir::TypeParamTypePayload>(&file.type_payload(r));
            return lhs_param && rhs_param &&
                   lhs_param->depth == rhs_param->depth &&
                   lhs_param->index == rhs_param->index &&
                   lhs_param->is_parameter_pack == rhs_param->is_parameter_pack;
        }
        case cir::TypeKind::Pointer: {
            const auto* lhs_pointer =
                std::get_if<cir::PointerTypePayload>(&file.type_payload(l));
            const auto* rhs_pointer =
                std::get_if<cir::PointerTypePayload>(&file.type_payload(r));
            return lhs_pointer && rhs_pointer &&
                   template_type_refs_equivalent(file,
                                                 lhs_pointer->pointee,
                                                 rhs_pointer->pointee);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return template_type_refs_equivalent(
                file,
                file.reference_referred_ref(l),
                file.reference_referred_ref(r));
        case cir::TypeKind::Record: {

            const cir::TemplateSpecializationFact* lhs_specialization =
                file.template_specialization(file.record_entity(l));
            const cir::TemplateSpecializationFact* rhs_specialization =
                file.template_specialization(file.record_entity(r));
            if (!lhs_specialization || !rhs_specialization ||
                lhs_specialization->template_entity !=
                    rhs_specialization->template_entity ||
                lhs_specialization->template_param_index !=
                    rhs_specialization->template_param_index) {
                return false;
            }
            if (!lhs_specialization->argument_bindings.empty() ||
                !rhs_specialization->argument_bindings.empty()) {
                return template_argument_bindings_equivalent(
                    file,
                    lhs_specialization->argument_bindings,
                    rhs_specialization->argument_bindings);
            }
            return template_argument_recipes_equivalent(
                file,
                lhs_specialization->dependent_arguments,
                rhs_specialization->dependent_arguments);
        }
        case cir::TypeKind::TemplateSpecialization: {
            const auto* lhs_specialization =
                std::get_if<cir::TemplateSpecializationTypePayload>(
                    &file.type_payload(l));
            const auto* rhs_specialization =
                std::get_if<cir::TemplateSpecializationTypePayload>(
                    &file.type_payload(r));
            return lhs_specialization && rhs_specialization &&
                   lhs_specialization->template_name ==
                       rhs_specialization->template_name &&
                   lhs_specialization->primary_template ==
                       rhs_specialization->primary_template &&
                   lhs_specialization->is_dependent ==
                       rhs_specialization->is_dependent &&
                   lhs_specialization->is_class_template_placeholder ==
                       rhs_specialization->is_class_template_placeholder &&
                   template_argument_recipes_equivalent(
                       file,
                       lhs_specialization->arguments,
                       rhs_specialization->arguments) &&
                   template_value_exprs_equivalent(
                       lhs_specialization->splice_operand,
                       rhs_specialization->splice_operand,
                       &file);
        }
        case cir::TypeKind::AliasSpecialization: {
            const auto* lhs_specialization =
                std::get_if<cir::AliasSpecializationTypePayload>(
                    &file.type_payload(l));
            const auto* rhs_specialization =
                std::get_if<cir::AliasSpecializationTypePayload>(
                    &file.type_payload(r));
            return lhs_specialization && rhs_specialization &&
                   lhs_specialization->template_name ==
                       rhs_specialization->template_name &&
                   lhs_specialization->alias_template ==
                       rhs_specialization->alias_template &&
                   template_argument_recipes_equivalent(
                       file,
                       lhs_specialization->arguments,
                       rhs_specialization->arguments) &&
                   template_type_refs_equivalent(
                       file,
                       lhs_specialization->associated_type,
                       rhs_specialization->associated_type);
        }
        case cir::TypeKind::DependentName: {
            const auto* lhs_name =
                std::get_if<cir::DependentNameTypePayload>(
                    &file.type_payload(l));
            const auto* rhs_name =
                std::get_if<cir::DependentNameTypePayload>(
                    &file.type_payload(r));
            return lhs_name && rhs_name &&
                   lhs_name->member_name == rhs_name->member_name &&
                   lhs_name->is_current_instantiation ==
                       rhs_name->is_current_instantiation &&
                   template_type_refs_equivalent(file,
                                                 lhs_name->qualifier_type,
                                                 rhs_name->qualifier_type) &&
                   template_argument_recipes_equivalent(
                       file,
                       lhs_name->template_arguments,
                       rhs_name->template_arguments);
        }
        case cir::TypeKind::BuiltinTransform: {
            const auto* lhs_transform =
                std::get_if<cir::BuiltinTypeTransformTypePayload>(
                    &file.type_payload(l));
            const auto* rhs_transform =
                std::get_if<cir::BuiltinTypeTransformTypePayload>(
                    &file.type_payload(r));
            return lhs_transform && rhs_transform &&
                   lhs_transform->transform_kind ==
                       rhs_transform->transform_kind &&
                   template_type_refs_equivalent(file,
                                                 lhs_transform->operand_type,
                                                 rhs_transform->operand_type);
        }
        case cir::TypeKind::PackIndex: {
            const auto* lhs_pack = std::get_if<cir::PackIndexTypePayload>(
                &file.type_payload(l));
            const auto* rhs_pack = std::get_if<cir::PackIndexTypePayload>(
                &file.type_payload(r));
            if (!lhs_pack || !rhs_pack ||
                lhs_pack->fully_substituted != rhs_pack->fully_substituted ||
                lhs_pack->expansions.size() != rhs_pack->expansions.size() ||
                !template_type_refs_equivalent(file,
                                               lhs_pack->pack_type,
                                               rhs_pack->pack_type) ||
                !template_value_exprs_equivalent(
                    lhs_pack->index_expression,
                    rhs_pack->index_expression,
                    &file)) {
                return false;
            }
            for (size_t i = 0; i < lhs_pack->expansions.size(); ++i) {
                if (!template_type_refs_equivalent(
                        file,
                        lhs_pack->expansions[i],
                        rhs_pack->expansions[i])) {
                    return false;
                }
            }
            return true;
        }
        default:
            return false;
    }
}

bool template_value_expr_nodes_equivalent(
    const cir::TemplateValueExprNode& lhs,
    const cir::TemplateValueExprNode& rhs,
    const cir::File* file = nullptr) {
    auto refs_equal = [&](cir::TypeRef left, cir::TypeRef right) {
        return file ? template_type_refs_equivalent(*file, left, right)
                    : left == right;
    };
    auto types_equal = [&](cir::TypeId left, cir::TypeId right) {
        return refs_equal(cir::TypeRef{left}, cir::TypeRef{right});
    };

    bool entities_equal = lhs.kind == cir::TemplateValueExprKind::Parameter
        ? true
        : lhs.entity == rhs.entity;
    if (lhs.pack_references.size() != rhs.pack_references.size() ||
        lhs.template_arguments.size() != rhs.template_arguments.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.pack_references.size(); ++i) {
        const cir::TemplateValuePackReference& left =
            lhs.pack_references[i];
        const cir::TemplateValuePackReference& right =
            rhs.pack_references[i];

        if (left.kind != right.kind || left.depth != right.depth ||
            left.index != right.index ||
            !types_equal(left.parameter_type, right.parameter_type)) {
            return false;
        }
    }
    for (size_t i = 0; i < lhs.template_arguments.size(); ++i) {
        if (!template_argument_recipe_equivalent(
                lhs.template_arguments.values()[i],
                rhs.template_arguments.values()[i],
                file)) {
            return false;
        }
    }
    return lhs.kind == rhs.kind &&
           lhs.op == rhs.op &&
           lhs.trait_kind == rhs.trait_kind &&
           lhs.fold_kind == rhs.fold_kind &&
           lhs.value == rhs.value &&
           lhs.integer_value == rhs.integer_value &&
           lhs.parameter_index == rhs.parameter_index &&
           lhs.lhs == rhs.lhs &&
           lhs.rhs == rhs.rhs &&
           lhs.third == rhs.third &&
           lhs.operands == rhs.operands &&
           lhs.expands_parameter_pack == rhs.expands_parameter_pack &&
           types_equal(lhs.type, rhs.type) &&
           refs_equal(lhs.result_type, rhs.result_type) &&
           entities_equal &&
           lhs.name == rhs.name &&
           refs_equal(lhs.qualifier_type, rhs.qualifier_type) &&
           lhs.semantic_key == rhs.semantic_key;
}

bool template_value_exprs_equivalent(
    const cir::TemplateValueExpression& lhs,
    const cir::TemplateValueExpression& rhs,
    const cir::File* file) {
    if (lhs.root != rhs.root || lhs.nodes.size() != rhs.nodes.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.nodes.size(); ++i) {
        if (!template_value_expr_nodes_equivalent(lhs.nodes[i],
                                                  rhs.nodes[i],
                                                  file)) {
            return false;
        }
    }
    return true;
}

bool template_argument_recipe_equivalent(
    const cir::TemplateArgument& lhs,
    const cir::TemplateArgument& rhs,
    const cir::File* file) {
    auto refs_equal = [&](cir::TypeRef left, cir::TypeRef right) {
        return file ? template_type_refs_equivalent(*file, left, right)
                    : left == right;
    };
    if (lhs.kind != rhs.kind ||
        lhs.expands_parameter_pack != rhs.expands_parameter_pack ||
        lhs.expands_pack_pattern != rhs.expands_pack_pattern ||
        lhs.generated_pack_kind != rhs.generated_pack_kind ||
        !refs_equal(lhs.generated_pack_count_type,
                    rhs.generated_pack_count_type) ||
        !template_value_exprs_equivalent(
            lhs.generated_pack_count_expr,
            rhs.generated_pack_count_expr,
            file)) {
        return false;
    }

    switch (lhs.kind) {
        case cir::TemplateArgumentKind::Type:
            return lhs.value_param_index == rhs.value_param_index &&
                refs_equal(lhs.type, rhs.type);
        case cir::TemplateArgumentKind::Value: {
            const bool parameter_value =
                lhs.value_param_index !=
                    cir::ArrayTypePayload::no_extent_param &&
                rhs.value_param_index !=
                    cir::ArrayTypePayload::no_extent_param;
            if (!refs_equal(lhs.type, rhs.type) ||
                !refs_equal(lhs.value_type, rhs.value_type) ||
                lhs.value_kind != rhs.value_kind ||
                lhs.null_kind != rhs.null_kind ||
                lhs.meta_kind != rhs.meta_kind ||
                lhs.integer_value != rhs.integer_value ||
                (!parameter_value &&
                 lhs.value_entity != rhs.value_entity) ||
                lhs.closure_identity != rhs.closure_identity ||
                lhs.value_byte_offset != rhs.value_byte_offset ||
                lhs.value_param_index != rhs.value_param_index ||
                lhs.dependent_value_name !=
                    rhs.dependent_value_name ||
                !refs_equal(lhs.dependent_value_qualifier,
                            rhs.dependent_value_qualifier) ||
                !template_value_exprs_equivalent(
                    lhs.dependent_value_expr,
                    rhs.dependent_value_expr,
                    file) ||
                lhs.value_elements.size() !=
                    rhs.value_elements.size()) {
                return false;
            }
            if (lhs.value_kind == cir::TemplateValueKind::Floating &&
                lhs.floating_value != rhs.floating_value) {
                return false;
            }
            for (size_t i = 0; i < lhs.value_elements.size(); ++i) {
                if (!template_argument_recipe_equivalent(
                        lhs.value_elements[i],
                        rhs.value_elements[i],
                        file)) {
                    return false;
                }
            }
            return true;
        }
        case cir::TemplateArgumentKind::Template: {
            const bool parameter_template =
                lhs.template_param_index !=
                    cir::ArrayTypePayload::no_extent_param &&
                rhs.template_param_index !=
                    cir::ArrayTypePayload::no_extent_param;
            return lhs.template_param_index ==
                       rhs.template_param_index &&
                (parameter_template ||
                 lhs.template_entity == rhs.template_entity) &&
                (parameter_template ||
                 lhs.template_name == rhs.template_name) &&
                refs_equal(lhs.dependent_template_qualifier,
                           rhs.dependent_template_qualifier);
        }
    }
    return false;
}

bool function_exception_specs_structurally_equivalent(
    const cir::File& file,
    cir::TypeId lhs,
    cir::TypeId rhs) {
    lhs = file.resolved_type(lhs);
    rhs = file.resolved_type(rhs);
    const auto* left = file.valid(lhs)
        ? std::get_if<cir::FunctionTypePayload>(&file.type_payload(lhs))
        : nullptr;
    const auto* right = file.valid(rhs)
        ? std::get_if<cir::FunctionTypePayload>(&file.type_payload(rhs))
        : nullptr;
    return left && right &&
        left->exception_spec.kind == right->exception_spec.kind &&
        template_value_exprs_equivalent(left->exception_spec.predicate,
                                        right->exception_spec.predicate,
                                        &file);
}

bool template_parameter_accepts_argument(
    const Session& session,
    const Session::TemplateParameter& parameter,
    const Session::TemplateArgument& argument,
    Session::TemplateArgumentBindingFailureReason* reason_out) {
    using Parameter = Session::TemplateParameter;
    using ParameterList = std::vector<Parameter>;
    using Reason = Session::TemplateArgumentBindingFailureReason;
    if (reason_out) {
        *reason_out = Reason::None;
    }
    auto reject = [reason_out](Reason reason) {
        if (reason_out) {
            *reason_out = reason;
        }
        return false;
    };

    std::function<bool(const Parameter&, const Parameter&)>
        parameter_forms_match;
    std::function<bool(const ParameterList&, const ParameterList&)>
        parameter_lists_match;

    parameter_forms_match =
        [&](const Parameter& expected_parameter,
            const Parameter& actual_parameter) -> bool {
        if (expected_parameter.kind != actual_parameter.kind) {
            return false;
        }
        if (expected_parameter.kind == Session::TemplateParameterKind::NonType &&
            session.file().resolved_type(expected_parameter.non_type_type) !=
                session.file().resolved_type(actual_parameter.non_type_type)) {

            if (!session.contains_auto_type(expected_parameter.non_type_type) &&
                !session.contains_auto_type(actual_parameter.non_type_type)) {
                return false;
            }
        }
        if (expected_parameter.kind == Session::TemplateParameterKind::Template &&
            expected_parameter.template_template_parameter_kind !=
                actual_parameter.template_template_parameter_kind) {
            return false;
        }
        if (expected_parameter.kind == Session::TemplateParameterKind::Template &&
            !parameter_lists_match(expected_parameter.nested_parameters(),
                                   actual_parameter.nested_parameters())) {
            return false;
        }
        return true;
    };

    parameter_lists_match =
        [&](const ParameterList& expected,
            const ParameterList& actual) -> bool {
        size_t actual_index = 0;
        for (size_t expected_index = 0;
             expected_index < expected.size();
             ++expected_index) {
            const Parameter& expected_parameter = expected[expected_index];
            if (expected_parameter.is_parameter_pack) {
                while (actual_index < actual.size()) {
                    if (!parameter_forms_match(expected_parameter,
                                               actual[actual_index])) {
                        return false;
                    }
                    ++actual_index;
                }
                return true;
            }
            if (actual_index >= actual.size()) {
                return false;
            }
            if (!parameter_forms_match(expected_parameter,
                                       actual[actual_index])) {
                return false;
            }
            ++actual_index;
        }
        for (; actual_index < actual.size(); ++actual_index) {
            const Parameter& trailing = actual[actual_index];
            if (!trailing.is_parameter_pack &&
                !trailing.default_argument.has_value()) {
                return false;
            }
        }
        return true;
    };

    switch (parameter.kind) {
        case Session::TemplateParameterKind::Type:
            if (argument.kind == cir::TemplateArgumentKind::Type) {
                return true;
            }
            return reject(Reason::TypeParameterRequiresTypeArgument);
        case Session::TemplateParameterKind::NonType: {
            if (argument.kind != cir::TemplateArgumentKind::Value) {
                return reject(Reason::NonTypeParameterRequiresValueArgument);
            }

            if (!argument.is_dependent &&
                (argument.value_kind == cir::TemplateValueKind::Integer ||
                 argument.value_kind == cir::TemplateValueKind::Boolean) &&
                parameter.non_type_type.valid()) {
                cir::TypeId resolved =
                    session.file().resolved_type(parameter.non_type_type);
                if (session.file().valid(resolved) &&
                    cir::is_integer_like_type(session.file(), resolved)) {
                    cir::IntegerTypeShape shape =
                        cir::integer_shape_for_type(session.file(), resolved);
                    ConstIntValue source = argument.integer_value;
                    if (!const_int_value_representable(source,
                                                       shape.bit_width,
                                                       shape.is_unsigned)) {
                        return reject(Reason::NonTypeArgumentNarrowing);
                    }
                }
            }
            return true;
        }
        case Session::TemplateParameterKind::Template:
            if (argument.kind != cir::TemplateArgumentKind::Template) {
                return reject(
                    Reason::TemplateParameterRequiresTemplateArgument);
            }
            if (template_argument_has_dependent_template_name(argument)) {
                return true;
            }
            if (argument.template_param_index !=
                    cir::ArrayTypePayload::no_extent_param &&
                argument.is_dependent &&
                argument.template_entity.valid() &&
                session.file().valid(argument.template_entity) &&
                session.file().entity(argument.template_entity).kind ==
                    cir::EntityKind::TemplateParam) {
                return true;
            }
            if (!argument.template_entity.valid()) {
                return reject(Reason::TemplateArgumentMustNameTemplate);
            }
            const Session::TemplateInfo* argument_info =
                session.template_info(argument.template_entity);
            if (!argument_info) {
                return reject(Reason::TemplateArgumentMustNameTemplate);
            }
            bool expects_concept =
                parameter.template_template_parameter_kind ==
                    Session::TemplateTemplateParameterKind::Concept;
            bool expects_variable =
                parameter.template_template_parameter_kind ==
                    Session::TemplateTemplateParameterKind::Variable;
            if (expects_concept && !argument_info->is_concept) {
                return reject(
                    Reason::TemplateArgumentMustNameConceptTemplate);
            }
            if (expects_variable && !argument_info->is_variable_template) {
                return reject(Reason::TemplateArgumentMustNameTemplate);
            }
            if (!expects_concept && !expects_variable &&
                !argument_info->is_class_template &&
                !argument_info->is_alias_template) {
                return reject(
                    Reason::TemplateArgumentMustNameClassOrAliasTemplate);
            }
            if (!parameter_lists_match(parameter.nested_parameters(),
                                       argument_info->parameters)) {
                return reject(
                    Reason::TemplateTemplateParameterListMismatch);
            }
            return true;
    }
    return false;
}

} // namespace

bool Session::function_exception_specs_equivalent(cir::TypeId lhs,
                                                  cir::TypeId rhs) const {
    return function_exception_specs_structurally_equivalent(file_, lhs, rhs);
}

Session::InstantiationScope::InstantiationScope() = default;
Session::InstantiationScope::InstantiationScope(InstantiationScope&&) noexcept =
    default;
Session::InstantiationScope& Session::InstantiationScope::operator=(
    InstantiationScope&&) noexcept = default;
Session::InstantiationScope::~InstantiationScope() = default;

bool Session::form_class_template_value_argument(
    cir::TypeId declared_type,
    ExprResult source,
    TemplateArgument& argument,
    SrcLoc loc,
    std::string_view constant_expression_diagnostic,
    std::string* error_out,
    bool diagnose_deduction) {
    cir::TypeId value_type = declared_type;
    if (const TemplateInfo* placeholder =
            class_template_placeholder_info(declared_type)) {
        if (!tstate().class_template_placeholder_deduction_callback_) {
            set_template_binding_error(
                error_out,
                "class template argument deduction is unavailable");
            return false;
        }
        value_type =
            tstate().class_template_placeholder_deduction_callback_(
                *placeholder, source, loc, diagnose_deduction);
        if (!value_type.valid()) {
            return false;
        }
        if (!require_complete_class_type(
                value_type,
                loc,
                cir::InstantiationDemandKind::CompleteClass)) {
            return false;
        }
        if (!constant_template_parameter_type_is_supported(value_type)) {
            set_template_binding_error(
                error_out,
                "deduced constant template parameter type is not structural");
            return false;
        }
    }

    cir::TypeId resolved = file_.resolved_type(value_type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Record) {
        set_template_binding_error(
            error_out,
            "class template argument did not produce a class type");
        return false;
    }
    if (!source.type.valid() ||
        file_.resolved_type(source.type) != resolved) {
        source = convert_to(std::move(source),
                            value_type,
                            UseContext::Init,
                            loc);
        if (source.has_error) {
            return false;
        }
    }

    TemplateValueConstant constant;
    if (!evaluate_template_value_constant(
            std::move(source),
            value_type,
            constant,
            loc,
            constant_expression_diagnostic)) {
        return false;
    }
    return build_template_value_argument(value_type,
                                         constant,
                                         argument,
                                         error_out);
}

bool Session::build_template_value_argument(
    cir::TypeId expected_type,
    const TemplateValueConstant& constant,
    TemplateArgument& argument,
    std::string* error_out) const {
    cir::TypeId value_type = expected_type.valid()
        ? expected_type
        : file_.builtin_type(cir::BuiltinTypeKind::Int);
    argument = TemplateArgument{};
    argument.kind = cir::TemplateArgumentKind::Value;
    argument.value_type = type_ref(value_type);
    if (template_value_type_is_member_pointer_target(*this, value_type)) {
        if (constant.kind == cir::TemplateValueKind::MemberPointer) {
            argument.value_kind = cir::TemplateValueKind::MemberPointer;
            argument.value_entity = constant.entity;
            argument.value_byte_offset = constant.byte_offset;
            return true;
        }
        if (constant.kind == cir::TemplateValueKind::Null &&
            (constant.null_kind == cir::TemplateNullKind::MemberPointer ||
             constant.null_kind == cir::TemplateNullKind::Nullptr)) {
            argument.value_kind = cir::TemplateValueKind::Null;
            argument.null_kind = cir::TemplateNullKind::MemberPointer;
            return true;
        }
        set_template_binding_error(
            error_out,
            "expected a member pointer template argument");
        return false;
    }
    if (template_value_type_is_null_pointer_target(*this, value_type)) {
        if (constant.kind == cir::TemplateValueKind::Address) {
            argument.value_kind = cir::TemplateValueKind::Address;
            argument.value_entity = constant.entity;
            argument.value_byte_offset = constant.byte_offset;
            return true;
        }
        if (constant.kind != cir::TemplateValueKind::Null ||
            (constant.null_kind != cir::TemplateNullKind::Pointer &&
             constant.null_kind != cir::TemplateNullKind::Nullptr)) {
            set_template_binding_error(
                error_out,
                "expected a null pointer template argument");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::Null;
        argument.null_kind = cir::TemplateNullKind::Pointer;
        return true;
    }
    cir::TypeId resolved = file_.resolved_type(value_type);
    bool expects_reference = file_.valid(resolved) &&
        (file_.type(resolved).kind == cir::TypeKind::LValueReference ||
         file_.type(resolved).kind == cir::TypeKind::RValueReference);
    if (expects_reference) {
        if (constant.kind != cir::TemplateValueKind::Address) {
            set_template_binding_error(
                error_out,
                "expected a reference template argument");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::Address;
        argument.value_entity = constant.entity;
        argument.value_byte_offset = constant.byte_offset;
        return true;
    }
    if (constant.kind == cir::TemplateValueKind::Closure) {
        if (!file_.valid(constant.closure_identity)) {
            set_template_binding_error(
                error_out,
                "closure template argument has no canonical identity");
            return false;
        }
        const cir::ClosureIdentityFact& identity =
            file_.closure_identity(constant.closure_identity);
        if (!identity.is_structural || !identity.type.type.valid()) {
            set_template_binding_error(
                error_out,
                "capturing lambda closure type is not structural");
            return false;
        }
        if (contains_auto_type(value_type)) {
            value_type = identity.type.type;
            argument.value_type = identity.type;
        }
        const cir::RecordFacts* facts = file_.record_facts_for_type(value_type);
        if (file_.template_value_kind_for_type(value_type) !=
                cir::TemplateValueKind::Closure ||
            !facts || facts->lambda_has_capture ||
            facts->closure_identity != constant.closure_identity) {
            set_template_binding_error(
                error_out,
                "closure template argument does not match its closure type");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::Closure;
        argument.closure_identity = constant.closure_identity;
        return true;
    }
    if (constant.kind == cir::TemplateValueKind::StructuralObject) {
        if (file_.template_value_kind_for_type(value_type) !=
            cir::TemplateValueKind::StructuralObject) {
            set_template_binding_error(
                error_out,
                "expected a structural object template argument");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::StructuralObject;
        argument.value_elements = constant.elements;
        argument.value_entity = constant.entity;
        return true;
    }
    if (file_.template_value_kind_for_type(value_type) ==
        cir::TemplateValueKind::MetaInfo) {
        if (constant.kind != cir::TemplateValueKind::MetaInfo) {
            set_template_binding_error(
                error_out, "expected a reflection template argument");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::MetaInfo;
        argument.meta_kind = constant.meta_kind;
        argument.type = constant.meta_type;
        argument.value_entity = constant.entity;
        return true;
    }
    if (template_value_type_is_bool(*this, value_type)) {
        if (constant.kind != cir::TemplateValueKind::Boolean &&
            constant.kind != cir::TemplateValueKind::Integer) {
            set_template_binding_error(error_out,
                                       "expected a bool template argument");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::Boolean;
        argument.integer_value = cir::IntegerValue::from_unsigned(
            constant.integer_value.is_zero() ? 0 : 1, 1);
        return true;
    }
    if (cir::is_floating_type(file_, resolved)) {
        if (constant.kind != cir::TemplateValueKind::Floating) {
            set_template_binding_error(error_out,
                                       "expected a floating template argument");
            return false;
        }
        cir::FloatingSemantics semantics =
            floating::semantics_for_type(file_, resolved);
        floating::FloatResult converted =
            floating::convert(constant.floating_value, semantics);
        if (!converted || !converted->canonical()) {
            set_template_binding_error(
                error_out,
                "floating template argument does not match the target type");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::Floating;
        argument.floating_value = *converted;
        argument.value_spelling = floating::display(*converted);
        return true;
    }
    if (template_value_type_is_nullptr_t(*this, value_type)) {
        if (constant.kind != cir::TemplateValueKind::Null ||
            constant.null_kind != cir::TemplateNullKind::Nullptr) {
            set_template_binding_error(error_out,
                                       "expected a nullptr template argument");
            return false;
        }
        argument.value_kind = cir::TemplateValueKind::Null;
        argument.null_kind = cir::TemplateNullKind::Nullptr;
        return true;
    }
    if (constant.kind == cir::TemplateValueKind::Null ||
        constant.kind == cir::TemplateValueKind::Address ||
        constant.kind == cir::TemplateValueKind::MemberPointer ||
        constant.kind == cir::TemplateValueKind::Closure ||
        constant.kind == cir::TemplateValueKind::StructuralObject) {
        set_template_binding_error(error_out,
                                   "expected an integer template argument");
        return false;
    }
    if (cir::is_integer_like_type(file_, resolved)) {
        cir::IntegerTypeShape shape =
            cir::integer_shape_for_type(file_, resolved);
        ConstIntValue source = constant.integer_value;
        if (!const_int_value_representable(source,
                                           shape.bit_width,
                                           shape.is_unsigned)) {
            set_template_binding_error(
                error_out,
                "non-type template argument conversion is narrowing");
            return false;
        }
        ConstIntValue converted =
            source.cast(shape.bit_width, shape.is_unsigned);
        argument.value_kind = cir::TemplateValueKind::Integer;
        argument.integer_value = converted;
        return true;
    }
    argument.value_kind = cir::TemplateValueKind::Integer;
    argument.integer_value = constant.integer_value;
    return true;
}

bool Session::template_value_constant_from_entity(
    cir::EntityId entity_id,
    TemplateValueConstant& constant) const {
    if (!entity_id.valid() || !file_.valid(entity_id)) {
        return false;
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if (!entity.has_constant_value) {
        return false;
    }

    constant = TemplateValueConstant{};
    constant.kind = entity.constant_value_kind;
    constant.null_kind = entity.constant_null_kind;
    constant.integer_value = entity.constant_integer_value;
    constant.floating_value = entity.constant_floating_value;
    constant.entity = entity.constant_entity;
    constant.closure_identity = entity.constant_closure_identity;
    constant.byte_offset = entity.constant_byte_offset;
    constant.elements = entity.constant_value_elements;
    constant.meta_kind = entity.constant_meta_kind;
    constant.meta_type = entity.constant_meta_type;

    cir::TypeId resolved = file_.resolved_type(entity.type);
    if ((constant.kind == cir::TemplateValueKind::Integer ||
         constant.kind == cir::TemplateValueKind::Boolean) &&
        file_.valid(resolved) &&
        cir::is_integer_like_type(file_, resolved)) {
        cir::IntegerTypeShape shape =
            cir::integer_shape_for_type(file_, resolved);
        constant.integer_value = constant.integer_value.cast(
            shape.bit_width, shape.is_unsigned);
    }
    return true;
}

namespace {

constexpr uint64_t generated_integer_pack_limit = 65536;

bool generated_integer_pack_count(
    const Session::TemplateArgument& argument,
    uint64_t& count,
    std::string* error_out) {
    if (argument.kind != cir::TemplateArgumentKind::Value ||
        (argument.value_kind != cir::TemplateValueKind::Integer &&
         argument.value_kind != cir::TemplateValueKind::Boolean)) {
        set_template_binding_error(
            error_out,
            "generated integer pack count is not an integral constant expression");
        return false;
    }
    if (argument.integer_value.is_negative()) {
        set_template_binding_error(
            error_out, "generated integer pack count must not be negative");
        return false;
    }
    std::optional<uint64_t> exact_count =
        argument.integer_value.try_as_uint64();
    if (!exact_count.has_value()) {
        set_template_binding_error(
            error_out, "generated integer pack count is too large");
        return false;
    }
    count = *exact_count;
    if (count > generated_integer_pack_limit) {
        set_template_binding_error(
            error_out,
            "generated integer pack count exceeds the implementation limit of " +
                std::to_string(generated_integer_pack_limit));
        return false;
    }
    return true;
}

bool append_generated_integer_arguments(
    Session& session,
    cir::TypeId value_type,
    const Session::TemplateArgument& count_argument,
    std::vector<Session::TemplateArgument>& destination,
    std::string* error_out) {
    cir::TypeId resolved = session.file().resolved_type(value_type);
    if (!resolved.valid() || !session.file().valid(resolved) ||
        !cir::is_integer_like_type(session.file(), resolved)) {
        set_template_binding_error(
            error_out, "generated integer pack element type must be integral");
        return false;
    }
    uint64_t count = 0;
    if (!generated_integer_pack_count(count_argument, count, error_out)) {
        return false;
    }
    destination.reserve(destination.size() + static_cast<size_t>(count));
    for (uint64_t index = 0; index < count; ++index) {
        Session::TemplateValueConstant constant;
        constant.kind = cir::TemplateValueKind::Integer;
        constant.integer_value = cir::IntegerValue::from_unsigned(index, 64);
        Session::TemplateArgument element;
        if (!session.build_template_value_argument(
                value_type, constant, element, error_out)) {
            return false;
        }
        destination.push_back(std::move(element));
    }
    return true;
}

cir::TemplateValueExpression concrete_generated_pack_count_expression(
    const cir::File& file,
    const Session::TemplateArgument& count) {
    cir::TemplateValueExpression expression;
    expression.nodes.push_back(file.template_integer_expression_node(
        count.integer_value, count.value_type));
    expression.root = 0;
    return expression;
}

} // namespace

bool Session::build_generated_integer_pack(
    cir::TypeId value_type,
    ExprResult count,
    TemplateArgument& dependent_pack,
    std::vector<TemplateArgument>& concrete_arguments,
    SrcLoc loc,
    std::string* error_out) {
    dependent_pack = TemplateArgument{};
    concrete_arguments.clear();
    cir::TypeId count_type = count.type;
    cir::TypeId resolved_count = file_.resolved_type(count_type);
    if (!count_type.valid() || !file_.valid(resolved_count) ||
        (!cir::is_integer_like_type(file_, resolved_count) &&
         !is_dependent_type(resolved_count))) {
        set_template_binding_error(
            error_out, "generated integer pack count must have integral type");
        return false;
    }
    cir::TypeId resolved_value = file_.resolved_type(value_type);
    if (!value_type.valid() || !file_.valid(resolved_value) ||
        (!cir::is_integer_like_type(file_, resolved_value) &&
         !is_dependent_type(resolved_value))) {
        set_template_binding_error(
            error_out, "generated integer pack element type must be integral");
        return false;
    }
    if (expr_is_value_dependent(count)) {
        if (!count.template_value_expr.valid()) {
            set_template_binding_error(
                error_out,
                "dependent generated integer pack count has no substitution recipe");
            return false;
        }
        dependent_pack.kind = cir::TemplateArgumentKind::Value;
        dependent_pack.value_type = type_ref(value_type);
        dependent_pack.generated_pack_kind =
            cir::TemplateGeneratedPackKind::IntegerSequence;
        dependent_pack.generated_pack_count_type = type_ref(count_type);
        dependent_pack.generated_pack_count_expr =
            std::move(count.template_value_expr);
        dependent_pack.is_dependent = true;
        file_.canonicalize_template_value_expression(
            dependent_pack.generated_pack_count_expr);
        return true;
    }

    TemplateValueConstant constant;
    if (!evaluate_template_value_constant(
            std::move(count), count_type, constant, loc,
            "generated integer pack count is not an integral constant expression")) {
        return false;
    }
    TemplateArgument count_argument;
    if (!build_template_value_argument(
            count_type, constant, count_argument, error_out)) {
        return false;
    }
    return append_generated_integer_arguments(
        *this, value_type, count_argument, concrete_arguments, error_out);
}

bool Session::append_substituted_generated_pack(
    const TemplateArgument& generated_pack,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks,
    std::vector<TemplateArgument>& destination,
    bool reject_unresolved_template_parameter,
    std::string* error_out) {
    if (generated_pack.generated_pack_kind !=
            cir::TemplateGeneratedPackKind::IntegerSequence ||
        generated_pack.kind != cir::TemplateArgumentKind::Value ||
        !generated_pack.generated_pack_count_expr.valid()) {
        set_template_binding_error(error_out,
                                   "invalid generated template pack recipe");
        return false;
    }

    TemplateArgument substituted_pack = generated_pack;
    if (substituted_pack.value_type.type.valid() &&
        type_contains_type_param(substituted_pack.value_type.type)) {
        cir::TypeRef substituted = substitute_pattern_type_ref(
            substituted_pack.value_type, argument_bindings, callbacks);
        if (!substituted.valid()) {
            set_template_binding_error(
                error_out,
                "generated integer pack element type could not be substituted");
            return false;
        }
        substituted_pack.value_type = substituted;
    }

    TemplateArgument count_argument;
    count_argument.kind = cir::TemplateArgumentKind::Value;
    count_argument.value_type = substituted_pack.generated_pack_count_type;
    count_argument.dependent_value_expr =
        substituted_pack.generated_pack_count_expr;
    count_argument.is_dependent = true;
    if (!substitute_template_value_argument(
            count_argument, argument_bindings, callbacks, error_out)) {
        return false;
    }
    substituted_pack.generated_pack_count_type = count_argument.value_type;
    if (count_argument.is_dependent ||
        is_dependent_type(substituted_pack.value_type.type)) {
        if (reject_unresolved_template_parameter) {
            set_template_binding_error(
                error_out, "generated integer pack remains dependent");
            return false;
        }
        substituted_pack.generated_pack_count_expr =
            count_argument.is_dependent
                ? std::move(count_argument.dependent_value_expr)
                : concrete_generated_pack_count_expression(file_,
                                                           count_argument);
        file_.canonicalize_template_value_expression(
            substituted_pack.generated_pack_count_expr);
        substituted_pack.is_dependent = true;
        destination.push_back(std::move(substituted_pack));
        return true;
    }
    return append_generated_integer_arguments(
        *this,
        substituted_pack.value_type.type,
        count_argument,
        destination,
        error_out);
}
// todo: this function is bigger than the land ambitions (Greater ...) of the average Balkan ultranationalist
bool Session::substitute_template_value_argument(
    TemplateArgument& argument,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks,
    std::string* error_out,
    const std::unordered_set<uint32_t>* already_substituted_nodes) {
    if (argument.kind != cir::TemplateArgumentKind::Value) {
        return true;
    }
    if (argument.value_type.type.valid() &&
        type_contains_type_param(argument.value_type.type)) {
        cir::TypeId substituted =
            substitute_pattern_type(argument.value_type.type,
                                    argument_bindings,
                                    callbacks);
        if (!substituted.valid()) {
            set_template_binding_error(
                error_out,
                "dependent template value argument type could not be substituted");
            return false;
        }
        argument.value_type =
            type_ref(substituted,
                     argument.value_type.qualifiers,
                     argument.value_type.memory_space);
    }
    if (argument.dependent_value_expr.valid()) {

        std::vector<bool> visiting_calls(
            argument.dependent_value_expr.nodes.size(), false);
        std::vector<bool> collected_unselected_nodes(
            argument.dependent_value_expr.nodes.size(), false);
        std::vector<uint32_t> unselected_calls;
        std::function<void(uint32_t)> collect_unselected_calls;
        collect_unselected_calls = [&](uint32_t index) {
            if (index == cir::TemplateValueExprNoNode ||
                index >= argument.dependent_value_expr.nodes.size() ||
                collected_unselected_nodes[index]) {
                return;
            }
            collected_unselected_nodes[index] = true;
            const cir::TemplateValueExprNode& node =
                argument.dependent_value_expr.nodes[index];
            if (node.kind == cir::TemplateValueExprKind::Call) {
                unselected_calls.push_back(index);
                return;
            }
            collect_unselected_calls(node.lhs);
            collect_unselected_calls(node.rhs);
            collect_unselected_calls(node.third);
            for (uint32_t operand : node.operands) {
                collect_unselected_calls(operand);
            }
        };
        std::function<bool(uint32_t)> contains_evaluated_call;
        contains_evaluated_call = [&](uint32_t index) {
            if (index == cir::TemplateValueExprNoNode ||
                index >= argument.dependent_value_expr.nodes.size() ||
                visiting_calls[index]) {
                return false;
            }
            visiting_calls[index] = true;
            const cir::TemplateValueExprNode& node =
                argument.dependent_value_expr.nodes[index];
            if (node.kind == cir::TemplateValueExprKind::Call) {
                visiting_calls[index] = false;
                return true;
            }
            bool contains_call = contains_evaluated_call(node.lhs);
            if (node.kind == cir::TemplateValueExprKind::Binary &&
                (node.op == cir::TemplateValueExprOp::LogicalAnd ||
                 node.op == cir::TemplateValueExprOp::LogicalOr)) {
                bool invalid = false;
                std::string ignored_error;
                std::optional<int64_t> lhs =
                    evaluate_template_value_expr_node(
                        *this,
                        argument.dependent_value_expr,
                        node.lhs,
                        argument_bindings,
                        callbacks,
                        &invalid,
                        &ignored_error);
                bool short_circuited = lhs.has_value() &&
                    ((node.op == cir::TemplateValueExprOp::LogicalAnd &&
                      *lhs == 0) ||
                     (node.op == cir::TemplateValueExprOp::LogicalOr &&
                      *lhs != 0));
                if (short_circuited) {
                    collect_unselected_calls(node.rhs);
                    visiting_calls[index] = false;
                    return contains_call;
                }
            }
            if (node.kind == cir::TemplateValueExprKind::Conditional) {
                bool invalid = false;
                std::string ignored_error;
                std::optional<int64_t> condition =
                    evaluate_template_value_expr_node(
                        *this,
                        argument.dependent_value_expr,
                        node.lhs,
                        argument_bindings,
                        callbacks,
                        &invalid,
                        &ignored_error);
                if (condition.has_value()) {
                    uint32_t selected =
                        *condition != 0 ? node.rhs : node.third;
                    uint32_t unselected =
                        *condition != 0 ? node.third : node.rhs;
                    collect_unselected_calls(unselected);
                    bool result = contains_call ||
                        contains_evaluated_call(selected);
                    visiting_calls[index] = false;
                    return result;
                }
            }
            contains_call = contains_call ||
                contains_evaluated_call(node.rhs) ||
                contains_evaluated_call(node.third);
            contains_call = contains_call || std::any_of(
                node.operands.begin(), node.operands.end(),
                [&](uint32_t operand) {
                    return contains_evaluated_call(operand);
                });
            visiting_calls[index] = false;
            return contains_call;
        };
        bool contains_call = contains_evaluated_call(
            argument.dependent_value_expr.root);
        if (!callbacks.preserve_opaque_dependent_call_types) {
            for (uint32_t call : unselected_calls) {
                std::optional<cir::TemplateValueExpression> extracted =
                    extract_template_value_subexpression(
                        argument.dependent_value_expr, call);
                if (!extracted.has_value()) {
                    set_template_binding_error(
                        error_out,
                        "unselected dependent call expression is malformed");
                    return false;
                }
                UnevaluatedCallResolution resolution =
                    resolve_unevaluated_call_expression(
                        std::move(*extracted),
                        argument_bindings,
                        callbacks);
                if (resolution.status ==
                        UnevaluatedCallResolutionStatus::SubstitutionFailure) {
                    set_template_binding_error(
                        error_out,
                        "unselected dependent call expression substitution failed");
                    return false;
                }
                if (resolution.status ==
                        UnevaluatedCallResolutionStatus::HardError) {
                    set_template_binding_error(
                        error_out,
                        "unselected dependent call expression resolution produced an instantiation error");
                    return false;
                }
            }
        }
        if (contains_call &&
            !callbacks.preserve_opaque_dependent_call_types) {
            SpeculativeParseGuard transaction = speculative_parse();
            size_t diagnostic_watermark = file_.errors().size();
            UnevaluatedCallResolution resolution =
                resolve_unevaluated_call_expression(
                    argument.dependent_value_expr,
                    argument_bindings,
                    callbacks);
            if (resolution.status ==
                UnevaluatedCallResolutionStatus::StillDependent) {
                argument.dependent_value_expr =
                    std::move(resolution.expression);
                argument.value_param_index =
                    cir::ArrayTypePayload::no_extent_param;
                argument.value_kind = cir::TemplateValueKind::None;
                argument.is_dependent = true;
                file_.canonicalize_template_value_expression(
                    argument.dependent_value_expr);
                transaction.commit();
                return true;
            }
            if (resolution.status ==
                UnevaluatedCallResolutionStatus::SubstitutionFailure) {
                set_template_binding_error(
                    error_out,
                    "dependent call expression substitution failed");
                return false;
            }
            if (resolution.status ==
                UnevaluatedCallResolutionStatus::HardError) {
                set_template_binding_error(
                    error_out,
                    "dependent call expression resolution produced an instantiation error");
                transaction.commit();
                return false;
            }

            std::string materialization_error;
            std::optional<ExprResult> materialized =
                materialize_resolved_template_value_expression(
                    resolution, &materialization_error);
            if (!materialized.has_value()) {
                if (materialization_error.empty() &&
                    file_.errors().size() > diagnostic_watermark) {
                    materialization_error =
                        file_.errors()[diagnostic_watermark].second;
                }
                set_template_binding_error(
                    error_out,
                    materialization_error.empty()
                        ? "resolved dependent call expression could not be materialized"
                        : std::move(materialization_error));
                if (callbacks.argument_completion_mode ==
                    TemplateArgumentCompletionMode::Required) {
                    transaction.commit();
                }
                return false;
            }

            cir::TypeId expected_type = argument.value_type.type.valid()
                ? argument.value_type.type
                : builder_.int_type();
            TemplateValueConstant constant;
            if (!evaluate_template_value_constant(
                    std::move(*materialized),
                    expected_type,
                    constant,
                    argument.dependent_value_expr.loc,
                    "dependent call is not a converted constant expression")) {
                std::string evaluation_error;
                if (file_.errors().size() > diagnostic_watermark) {
                    evaluation_error =
                        file_.errors()[diagnostic_watermark].second;
                }
                set_template_binding_error(
                    error_out,
                    evaluation_error.empty()
                        ? "dependent call is not a converted constant expression"
                        : std::move(evaluation_error));
                if (callbacks.argument_completion_mode ==
                    TemplateArgumentCompletionMode::Required) {
                    transaction.commit();
                }
                return false;
            }

            TemplateArgument concrete;
            if (!build_template_value_argument(expected_type,
                                               constant,
                                               concrete,
                                               error_out)) {
                if (callbacks.argument_completion_mode ==
                    TemplateArgumentCompletionMode::Required) {
                    transaction.commit();
                }
                return false;
            }
            concrete.is_defaulted = argument.is_defaulted;
            argument = std::move(concrete);
            transaction.commit();
            return true;
        }

        enum class FoldExpansionStatus : uint8_t {
            Expanded,
            StillDependent,
            Failure,
        };

        auto append_value_expression = [](
            cir::TemplateValueExpression& destination,
            const cir::TemplateValueExpression& source) -> uint32_t {
            if (!source.valid()) {
                return cir::TemplateValueExprNoNode;
            }
            uint32_t offset =
                static_cast<uint32_t>(destination.nodes.size());
            for (cir::TemplateValueExprNode node : source.nodes) {
                auto shift = [&](uint32_t& child) {
                    if (child != cir::TemplateValueExprNoNode) {
                        child += offset;
                    }
                };
                shift(node.lhs);
                shift(node.rhs);
                shift(node.third);
                for (uint32_t& operand : node.operands) {
                    shift(operand);
                }
                destination.nodes.push_back(std::move(node));
            }
            return source.root + offset;
        };

        auto binding_for_fold_reference = [&](
            const cir::TemplateValuePackReference& reference)
            -> const TemplateArgumentBinding* {
            if (reference.declaration.valid()) {
                const auto* exact = [&]()
                    -> const std::unordered_map<
                        uint32_t, TemplateArgumentBinding>* {
                    switch (reference.kind) {
                        case cir::TemplateValuePackKind::Function:
                        case cir::TemplateValuePackKind::Type:
                            return &callbacks.exact_type_parameter_bindings;
                        case cir::TemplateValuePackKind::Value:
                            return &callbacks.exact_value_parameter_bindings;
                        case cir::TemplateValuePackKind::Template:
                            return &callbacks
                                .exact_template_parameter_bindings;
                    }
                    return nullptr;
                }();
                if (exact) {
                    auto found = exact->find(static_cast<uint32_t>(
                        reference.declaration.index));
                    if (found != exact->end()) {
                        return &found->second;
                    }
                }
            }
            return substitution_binding(argument_bindings,
                                        reference.index);
        };

        auto fold_expansion_width = [&](
            const std::vector<cir::TemplateValuePackReference>& references,
            size_t& width) -> FoldExpansionStatus {
            if (references.empty()) {
                set_template_binding_error(
                    error_out,
                    "dependent fold expression has no parameter pack");
                return FoldExpansionStatus::Failure;
            }
            std::optional<size_t> common_width;
            for (const cir::TemplateValuePackReference& reference :
                 references) {
                const TemplateArgumentBinding* binding =
                    binding_for_fold_reference(reference);
                if (!binding || binding->is_unbound()) {
                    return FoldExpansionStatus::StillDependent;
                }
                if (!binding->is_pack()) {
                    set_template_binding_error(
                        error_out,
                        "dependent fold expression does not name a template argument pack");
                    return FoldExpansionStatus::Failure;
                }
                if (std::any_of(
                        binding->arguments.begin(),
                        binding->arguments.end(),
                        [](const TemplateArgument& element) {
                            return element.expands_parameter_pack ||
                                element.expands_pack_pattern ||
                                element.generated_pack_kind !=
                                    cir::TemplateGeneratedPackKind::None;
                        })) {

                    return FoldExpansionStatus::StillDependent;
                }
                if (common_width.has_value() &&
                    *common_width != binding->arguments.size()) {
                    set_template_binding_error(
                        error_out,
                        "parameter packs in fold expression have different lengths");
                    return FoldExpansionStatus::Failure;
                }
                common_width = binding->arguments.size();
                cir::TemplateArgumentKind expected =
                    reference.kind == cir::TemplateValuePackKind::Value
                        ? cir::TemplateArgumentKind::Value
                        : reference.kind ==
                                  cir::TemplateValuePackKind::Template
                              ? cir::TemplateArgumentKind::Template
                              : cir::TemplateArgumentKind::Type;
                if (std::any_of(
                        binding->arguments.begin(),
                        binding->arguments.end(),
                        [&](const TemplateArgument& element) {
                            return element.kind != expected;
                        })) {
                    set_template_binding_error(
                        error_out,
                        "parameter pack element kind does not match fold expression");
                    return FoldExpansionStatus::Failure;
                }
            }
            width = common_width.value_or(0);
            return FoldExpansionStatus::Expanded;
        };

        std::function<cir::TypeId(cir::TypeId, uint32_t)>
            fold_pack_parameter_type;
        fold_pack_parameter_type = [&](cir::TypeId type,
                                       uint32_t parameter_index)
            -> cir::TypeId {
            cir::TypeId resolved = file_.resolved_type(type);
            if (!file_.valid(resolved)) {
                return {};
            }
            const cir::TypePayload& payload = file_.type_payload(resolved);
            switch (file_.type(resolved).kind) {
                case cir::TypeKind::TypeParam: {
                    const auto* parameter =
                        std::get_if<cir::TypeParamTypePayload>(&payload);
                    return parameter &&
                            parameter->index == parameter_index
                        ? resolved
                        : cir::TypeId{};
                }
                case cir::TypeKind::Pointer:
                    return fold_pack_parameter_type(
                        std::get<cir::PointerTypePayload>(payload)
                            .pointee.type,
                        parameter_index);
                case cir::TypeKind::LValueReference:
                case cir::TypeKind::RValueReference:
                    return fold_pack_parameter_type(
                        std::get<cir::ReferenceTypePayload>(payload)
                            .referred_type.type,
                        parameter_index);
                case cir::TypeKind::Array:
                    return fold_pack_parameter_type(
                        std::get<cir::ArrayTypePayload>(payload)
                            .element_type.type,
                        parameter_index);
                case cir::TypeKind::MemberPointer: {
                    const auto& member =
                        std::get<cir::MemberPointerTypePayload>(payload);
                    cir::TypeId found = fold_pack_parameter_type(
                        member.member_type.type, parameter_index);
                    return found.valid()
                        ? found
                        : fold_pack_parameter_type(
                              member.class_type.type, parameter_index);
                }
                default:
                    return {};
            }
        };

        auto project_fold_element = [&](
            const std::vector<cir::TemplateValuePackReference>& references,
            size_t element,
            TemplateArgumentBindings& projected_bindings,
            PatternInstantiationCallbacks& projected_callbacks) {
            projected_bindings = argument_bindings;
            projected_callbacks = callbacks;
            projected_callbacks.allow_parameter_pack_element_substitution =
                true;
            for (const cir::TemplateValuePackReference& reference :
                 references) {
                const TemplateArgumentBinding* source =
                    binding_for_fold_reference(reference);
                if (!source || !source->is_pack() ||
                    element >= source->arguments.size()) {
                    return false;
                }
                TemplateArgumentBinding projected;
                projected.kind = TemplateArgumentBindingKind::Single;
                projected.arguments = {source->arguments[element]};
                if (reference.index < projected_bindings.size()) {
                    projected_bindings[reference.index] = projected;
                }
                if (reference.kind ==
                        cir::TemplateValuePackKind::Type ||
                    reference.kind ==
                        cir::TemplateValuePackKind::Function) {
                    cir::TypeId parameter_type{};
                    if (reference.parameter_type.valid()) {
                        parameter_type = fold_pack_parameter_type(
                            reference.parameter_type, reference.index);
                    }
                    if (!parameter_type.valid() &&
                        reference.declaration.valid() &&
                        file_.valid(reference.declaration)) {
                        parameter_type = fold_pack_parameter_type(
                            file_.entity(reference.declaration).type,
                            reference.index);
                    }
                    if (parameter_type.valid()) {
                        projected_callbacks
                            .exact_type_parameter_bindings[
                                static_cast<uint32_t>(
                                    parameter_type.index)] = projected;
                    }
                } else if (reference.kind ==
                               cir::TemplateValuePackKind::Value &&
                           reference.declaration.valid()) {
                    projected_callbacks
                        .exact_value_parameter_bindings[
                            static_cast<uint32_t>(
                                reference.declaration.index)] = projected;
                } else if (reference.kind ==
                               cir::TemplateValuePackKind::Template &&
                           reference.declaration.valid()) {
                    projected_callbacks
                        .exact_template_parameter_bindings[
                            static_cast<uint32_t>(
                                reference.declaration.index)] = projected;
                }
            }
            return true;
        };

        auto expression_for_substituted_argument = [&]
            (const TemplateArgument& substituted,
             cir::TypeRef fallback_type)
            -> std::optional<cir::TemplateValueExpression> {
            if (substituted.dependent_value_expr.valid()) {
                return substituted.dependent_value_expr;
            }
            if (substituted.value_kind !=
                    cir::TemplateValueKind::Integer &&
                substituted.value_kind !=
                    cir::TemplateValueKind::Boolean) {
                return std::nullopt;
            }
            cir::TemplateValueExpression expression;
            cir::TypeRef result_type = substituted.value_type.type.valid()
                ? substituted.value_type
                : fallback_type;
            cir::TemplateValueExprNode integer =
                file_.template_integer_expression_node(
                    substituted.integer_value, result_type);
            expression.nodes.push_back(std::move(integer));
            expression.root = 0;
            return expression;
        };

        cir::TemplateValueExpression source_expression =
            argument.dependent_value_expr;
        cir::TemplateValueExpression expanded_expression;
        expanded_expression.loc = source_expression.loc;
        expanded_expression.definition_context =
            source_expression.definition_context;
        expanded_expression.definition_lookup_generation =
            source_expression.definition_lookup_generation;

        std::unordered_set<uint32_t> projected_fold_nodes;
        std::vector<bool> expanding(source_expression.nodes.size(), false);
        std::function<std::optional<uint32_t>(uint32_t)> expand_node;
        expand_node = [&](uint32_t index) -> std::optional<uint32_t> {
            if (index == cir::TemplateValueExprNoNode) {
                return cir::TemplateValueExprNoNode;
            }
            if (index >= source_expression.nodes.size() ||
                expanding[index]) {
                return std::nullopt;
            }
            expanding[index] = true;
            const cir::TemplateValueExprNode& source =
                source_expression.nodes[index];
            if (source.kind == cir::TemplateValueExprKind::Fold) {
                const size_t projected_begin =
                    expanded_expression.nodes.size();
                auto finish_projected_fold = [&](uint32_t root) {
                    for (size_t projected = projected_begin;
                         projected < expanded_expression.nodes.size();
                         ++projected) {
                        projected_fold_nodes.insert(
                            static_cast<uint32_t>(projected));
                    }
                    expanding[index] = false;
                    return std::optional<uint32_t>(root);
                };
                size_t width = 0;
                FoldExpansionStatus width_status = fold_expansion_width(
                    source.pack_references, width);
                if (width_status == FoldExpansionStatus::Failure) {
                    expanding[index] = false;
                    return std::nullopt;
                }
                if (width_status == FoldExpansionStatus::Expanded) {
                    std::optional<cir::TemplateValueExpression> pattern =
                        extract_template_value_subexpression(
                            source_expression, source.lhs);
                    if (!pattern.has_value()) {
                        set_template_binding_error(
                            error_out,
                            "dependent fold expression pattern is invalid");
                        expanding[index] = false;
                        return std::nullopt;
                    }
                    std::vector<uint32_t> elements;
                    elements.reserve(width);
                    for (size_t element = 0; element < width; ++element) {
                        TemplateArgumentBindings projected_bindings;
                        PatternInstantiationCallbacks projected_callbacks;
                        if (!project_fold_element(source.pack_references,
                                                  element,
                                                  projected_bindings,
                                                  projected_callbacks)) {
                            set_template_binding_error(
                                error_out,
                                "fold expression pack element could not be projected");
                            expanding[index] = false;
                            return std::nullopt;
                        }
                        TemplateArgument pattern_argument;
                        pattern_argument.kind =
                            cir::TemplateArgumentKind::Value;
                        pattern_argument.value_type = argument.value_type;
                        pattern_argument.dependent_value_expr = *pattern;
                        pattern_argument.is_dependent = true;
                        if (!substitute_template_value_argument(
                                pattern_argument,
                                projected_bindings,
                                projected_callbacks,
                                error_out)) {
                            expanding[index] = false;
                            return std::nullopt;
                        }
                        std::optional<cir::TemplateValueExpression>
                            element_expression =
                                expression_for_substituted_argument(
                                    pattern_argument,
                                    source.result_type);
                        if (!element_expression.has_value()) {
                            set_template_binding_error(
                                error_out,
                                "fold expression element is not an integral constant expression");
                            expanding[index] = false;
                            return std::nullopt;
                        }
                        elements.push_back(append_value_expression(
                            expanded_expression, *element_expression));
                    }

                    std::optional<uint32_t> initializer;
                    if (source.rhs != cir::TemplateValueExprNoNode) {
                        std::optional<cir::TemplateValueExpression>
                            initializer_expression =
                                extract_template_value_subexpression(
                                    source_expression, source.rhs);
                        if (!initializer_expression.has_value()) {
                            set_template_binding_error(
                                error_out,
                                "dependent binary fold initializer is invalid");
                            expanding[index] = false;
                            return std::nullopt;
                        }
                        TemplateArgument initializer_argument;
                        initializer_argument.kind =
                            cir::TemplateArgumentKind::Value;
                        initializer_argument.value_type =
                            argument.value_type;
                        initializer_argument.dependent_value_expr =
                            std::move(*initializer_expression);
                        initializer_argument.is_dependent = true;
                        PatternInstantiationCallbacks
                            initializer_callbacks = callbacks;
                        if (!substitute_template_value_argument(
                                initializer_argument,
                                argument_bindings,
                                initializer_callbacks,
                                error_out)) {
                            expanding[index] = false;
                            return std::nullopt;
                        }
                        std::optional<cir::TemplateValueExpression>
                            substituted_initializer =
                                expression_for_substituted_argument(
                                    initializer_argument,
                                    source.result_type);
                        if (!substituted_initializer.has_value()) {
                            set_template_binding_error(
                                error_out,
                                "binary fold initializer is not an integral constant expression");
                            expanding[index] = false;
                            return std::nullopt;
                        }
                        initializer = append_value_expression(
                            expanded_expression,
                            *substituted_initializer);
                    }

                    if (elements.empty() && !initializer.has_value()) {
                        if (source.op !=
                                cir::TemplateValueExprOp::LogicalAnd &&
                            source.op !=
                                cir::TemplateValueExprOp::LogicalOr) {
                            set_template_binding_error(
                                error_out,
                                "empty unary fold has no integral identity for this operator");
                            expanding[index] = false;
                            return std::nullopt;
                        }
                        bool identity_value = source.op ==
                            cir::TemplateValueExprOp::LogicalAnd;
                        cir::TemplateValueExprNode identity =
                            file_.template_integer_expression_node(
                                cir::IntegerValue::from_unsigned(
                                    identity_value ? 1 : 0, 1),
                                argument.value_type);
                        expanded_expression.nodes.push_back(
                            std::move(identity));
                        uint32_t result = static_cast<uint32_t>(
                            expanded_expression.nodes.size() - 1);
                        return finish_projected_fold(result);
                    }

                    auto append_binary = [&](uint32_t lhs,
                                             uint32_t rhs) {
                        cir::TemplateValueExprNode binary;
                        binary.kind =
                            cir::TemplateValueExprKind::Binary;
                        binary.op = source.op;
                        binary.lhs = lhs;
                        binary.rhs = rhs;

                        binary.result_type = argument.value_type;
                        expanded_expression.nodes.push_back(
                            std::move(binary));
                        return static_cast<uint32_t>(
                            expanded_expression.nodes.size() - 1);
                    };

                    uint32_t result = cir::TemplateValueExprNoNode;
                    if (source.fold_kind ==
                            cir::TemplateValueFoldKind::UnaryLeft ||
                        source.fold_kind ==
                            cir::TemplateValueFoldKind::BinaryLeft) {
                        size_t first_element = 0;
                        if (initializer.has_value()) {
                            result = *initializer;
                        } else if (!elements.empty()) {
                            result = elements.front();
                            first_element = 1;
                        }
                        for (size_t element = first_element;
                             element < elements.size(); ++element) {
                            result = append_binary(result,
                                                   elements[element]);
                        }
                    } else if (source.fold_kind ==
                                   cir::TemplateValueFoldKind::UnaryRight ||
                               source.fold_kind ==
                                   cir::TemplateValueFoldKind::BinaryRight) {
                        size_t remaining = elements.size();
                        if (initializer.has_value()) {
                            result = *initializer;
                        } else if (remaining != 0) {
                            result = elements[--remaining];
                        }
                        while (remaining != 0) {
                            result = append_binary(
                                elements[--remaining], result);
                        }
                    } else {
                        set_template_binding_error(
                            error_out,
                            "dependent fold expression has an invalid form");
                        expanding[index] = false;
                        return std::nullopt;
                    }
                    return finish_projected_fold(result);
                }
            }

            cir::TemplateValueExprNode node = source;
            auto expand_child = [&](uint32_t& child) {
                std::optional<uint32_t> expanded = expand_node(child);
                if (!expanded.has_value()) {
                    return false;
                }
                child = *expanded;
                return true;
            };
            if (!expand_child(node.lhs) || !expand_child(node.rhs) ||
                !expand_child(node.third)) {
                expanding[index] = false;
                return std::nullopt;
            }
            for (uint32_t& operand : node.operands) {
                if (!expand_child(operand)) {
                    expanding[index] = false;
                    return std::nullopt;
                }
            }
            expanded_expression.nodes.push_back(std::move(node));
            uint32_t result = static_cast<uint32_t>(
                expanded_expression.nodes.size() - 1);
            expanding[index] = false;
            return result;
        };

        std::optional<uint32_t> expanded_root =
            expand_node(source_expression.root);
        if (!expanded_root.has_value()) {
            if (!error_out || error_out->empty()) {
                set_template_binding_error(
                    error_out,
                    "dependent fold expression could not be expanded");
            }
            return false;
        }
        expanded_expression.root = *expanded_root;
        argument.dependent_value_expr = std::move(expanded_expression);

        std::vector<bool> deferred_fold_nodes(
            argument.dependent_value_expr.nodes.size(), false);
        std::function<bool(uint32_t)> mark_deferred_fold_subgraph;
        mark_deferred_fold_subgraph = [&](uint32_t index) {
            if (index == cir::TemplateValueExprNoNode) {
                return true;
            }
            if (index >= argument.dependent_value_expr.nodes.size()) {
                return false;
            }
            if (deferred_fold_nodes[index]) {
                return true;
            }
            deferred_fold_nodes[index] = true;
            const cir::TemplateValueExprNode& node =
                argument.dependent_value_expr.nodes[index];
            if (!mark_deferred_fold_subgraph(node.lhs) ||
                !mark_deferred_fold_subgraph(node.rhs) ||
                !mark_deferred_fold_subgraph(node.third)) {
                return false;
            }
            return std::all_of(
                node.operands.begin(),
                node.operands.end(),
                [&](uint32_t operand) {
                    return mark_deferred_fold_subgraph(operand);
                });
        };
        for (uint32_t index = 0;
             index < argument.dependent_value_expr.nodes.size(); ++index) {
            const cir::TemplateValueExprNode& node =
                argument.dependent_value_expr.nodes[index];
            if (node.kind != cir::TemplateValueExprKind::Fold) {
                continue;
            }
            size_t ignored_width = 0;
            if (fold_expansion_width(node.pack_references,
                                     ignored_width) ==
                    FoldExpansionStatus::StillDependent &&
                !mark_deferred_fold_subgraph(index)) {
                set_template_binding_error(
                    error_out,
                    "dependent fold expression graph is invalid");
                return false;
            }
        }

        argument.dependent_value_expr.canonical_id = {};

        std::unordered_set<uint32_t> address_operand_nodes;
        for (const cir::TemplateValueExprNode& node :
             argument.dependent_value_expr.nodes) {
            if (node.kind == cir::TemplateValueExprKind::Unary &&
                node.op == cir::TemplateValueExprOp::AddressOf &&
                node.lhs != cir::TemplateValueExprNoNode) {
                address_operand_nodes.insert(node.lhs);
            }
        }

        auto node_is_potentially_evaluated = [&](uint32_t target) {
            std::vector<bool> visiting(
                argument.dependent_value_expr.nodes.size(), false);
            std::function<bool(uint32_t)> visit;
            visit = [&](uint32_t index) {
                if (index == cir::TemplateValueExprNoNode ||
                    index >= argument.dependent_value_expr.nodes.size() ||
                    visiting[index]) {
                    return false;
                }
                if (index == target) {
                    return true;
                }
                visiting[index] = true;
                const cir::TemplateValueExprNode& node =
                    argument.dependent_value_expr.nodes[index];
                if (visit(node.lhs)) {
                    visiting[index] = false;
                    return true;
                }
                if (node.kind == cir::TemplateValueExprKind::Binary &&
                    (node.op == cir::TemplateValueExprOp::LogicalAnd ||
                     node.op == cir::TemplateValueExprOp::LogicalOr)) {
                    bool invalid = false;
                    std::string ignored_error;
                    std::optional<int64_t> lhs =
                        evaluate_template_value_expr_node(
                            *this,
                            argument.dependent_value_expr,
                            node.lhs,
                            argument_bindings,
                            callbacks,
                            &invalid,
                            &ignored_error);
                    bool short_circuited = lhs.has_value() &&
                        ((node.op ==
                              cir::TemplateValueExprOp::LogicalAnd &&
                          *lhs == 0) ||
                         (node.op ==
                              cir::TemplateValueExprOp::LogicalOr &&
                          *lhs != 0));
                    if (short_circuited) {
                        visiting[index] = false;
                        return false;
                    }
                }
                if (node.kind == cir::TemplateValueExprKind::Conditional) {
                    bool invalid = false;
                    std::string ignored_error;
                    std::optional<int64_t> condition =
                        evaluate_template_value_expr_node(
                            *this,
                            argument.dependent_value_expr,
                            node.lhs,
                            argument_bindings,
                            callbacks,
                            &invalid,
                            &ignored_error);
                    if (condition.has_value()) {
                        bool result = visit(*condition != 0
                                                ? node.rhs
                                                : node.third);
                        visiting[index] = false;
                        return result;
                    }
                }
                if (visit(node.rhs) || visit(node.third)) {
                    visiting[index] = false;
                    return true;
                }
                bool result = std::any_of(
                    node.operands.begin(),
                    node.operands.end(),
                    [&](uint32_t operand) { return visit(operand); });
                visiting[index] = false;
                return result;
            };
            return visit(argument.dependent_value_expr.root);
        };
        for (size_t node_index = 0;
             node_index < argument.dependent_value_expr.nodes.size();
             ++node_index) {
            if (already_substituted_nodes &&
                already_substituted_nodes->contains(
                    static_cast<uint32_t>(node_index))) {
                continue;
            }
            cir::TemplateValueExprNode& node =
                argument.dependent_value_expr.nodes[node_index];
            // Callee nodes are lookup descriptors. Older serialized recipes
            // can carry the parser's transient overload-designator type here;
            // it is not the selected callable type and must not instantiate a
            // discarded candidate during structural substitution.
            if (node.kind == cir::TemplateValueExprKind::Callee) {
                node.result_type = {};
            }
            if (projected_fold_nodes.contains(
                    static_cast<uint32_t>(node_index))) {
                continue;
            }
            if (deferred_fold_nodes[node_index]) {
                continue;
            }
            if (!node_is_potentially_evaluated(
                    static_cast<uint32_t>(node_index))) {
                continue;
            }
            auto substitute_node_ref = [&](cir::TypeRef& ref,
                                           const char* description,
                                           bool allow_opaque_dependent = false,
                                           bool require_definition = false) {
                if (!ref.type.valid() ||
                    !type_contains_type_param(ref.type)) {
                    return true;
                }
                const bool saved_materialization =
                    callbacks.materialize_type_template_definition;
                if (require_definition) {

                    callbacks.materialize_type_template_definition = true;
                }
                cir::TypeRef substituted = substitute_pattern_type_ref(
                    ref, argument_bindings, callbacks);
                callbacks.materialize_type_template_definition =
                    saved_materialization;
                if (!substituted.valid()) {
                    cir::TypeId resolved = file_.resolved_type(ref.type);
                    if ((allow_opaque_dependent ||
                         callbacks.preserve_opaque_dependent_call_types) &&
                        file_.valid(resolved) &&
                        file_.type(resolved).kind ==
                            cir::TypeKind::Dependent) {
                        return true;
                    }
                    set_template_binding_error(error_out, description);
                    return false;
                }
                ref = substituted;
                return true;
            };
            bool deferred_pack_operand =
                node.kind == cir::TemplateValueExprKind::TypeOperand &&
                node.expands_parameter_pack &&
                !callbacks.allow_parameter_pack_element_substitution;
            bool retained_member_access =
                node.kind == cir::TemplateValueExprKind::TypeOperand &&
                (static_cast<uint64_t>(node.value) &
                 static_cast<uint32_t>(
                     cir::TemplateCalleeFlag::MemberAccess)) != 0;
            bool result_resolves_from_expression =
                node.kind == cir::TemplateValueExprKind::Binary ||
                node.kind == cir::TemplateValueExprKind::Unary ||
                node.kind == cir::TemplateValueExprKind::Conditional ||
                retained_member_access ||
                (node.kind == cir::TemplateValueExprKind::TypeOperand &&
                 node.name.valid() && node.qualifier_type.type.valid());
            bool template_descriptor_was_rebound = false;
            if (node.kind == cir::TemplateValueExprKind::TypeOperand &&
                node.value == static_cast<int64_t>(
                    cir::TemplateArgumentKind::Template) &&
                node.entity.valid() && file_.valid(node.entity) &&
                file_.entity(node.entity).kind ==
                    cir::EntityKind::TemplateParam) {
                TemplateArgument template_argument;
                template_argument.kind =
                    cir::TemplateArgumentKind::Template;
                template_argument.template_entity = node.entity;
                template_argument.template_param_index =
                    node.parameter_index;
                template_argument.template_name = node.name;
                template_argument.dependent_template_qualifier =
                    node.qualifier_type;
                template_argument.is_dependent = true;
                if (!substitute_template_template_argument(
                        template_argument,
                        argument_bindings,
                        callbacks,
                        error_out)) {
                    return false;
                }
                node.entity = template_argument.template_entity;
                node.parameter_index =
                    template_argument.template_param_index;
                node.name = template_argument.template_name;
                node.qualifier_type =
                    template_argument.dependent_template_qualifier;

                template_descriptor_was_rebound = true;
            }
            if ((!deferred_pack_operand &&
                 !template_descriptor_was_rebound &&
                 !substitute_node_ref(
                     node.result_type,
                     "dependent value expression result type could not be substituted",
                     result_resolves_from_expression)) ||
                (!deferred_pack_operand &&
                 !template_descriptor_was_rebound &&
                 !substitute_node_ref(
                    node.qualifier_type,
                    "dependent value expression qualifier could not be substituted",
                    /*allow_opaque_dependent=*/false,
                    node.kind == cir::TemplateValueExprKind::TypeOperand &&
                        node.name.valid()))) {
                return false;
            }
            if (node.kind == cir::TemplateValueExprKind::Entity &&
                node.entity.valid() && file_.valid(node.entity) &&
                (callbacks.instantiate_value ||
                 callbacks.instantiate_value_entity)) {
                const cir::TemplateSpecializationFact* specialization =
                    file_.template_specialization(node.entity);
                if (specialization &&
                    specialization->template_entity.valid()) {
                    std::vector<TemplateArgument> source_arguments =
                        specialization->template_arguments();
                    std::vector<TemplateArgument> entity_arguments;
                    entity_arguments.reserve(source_arguments.size());
                    bool substituted_arguments = true;
                    for (const TemplateArgument& entity_argument :
                         source_arguments) {
                        if (!append_substituted_template_argument(
                                entity_argument,
                                argument_bindings,
                                callbacks,
                                entity_arguments,
                                /*reject_unresolved_template_parameter=*/false,
                                error_out)) {
                            substituted_arguments = false;
                            break;
                        }
                    }
                    bool arguments_still_dependent = std::any_of(
                        entity_arguments.begin(),
                        entity_arguments.end(),
                        [](const TemplateArgument& entity_argument) {
                            return entity_argument.is_dependent;
                        });
                    cir::EntityId template_entity =
                        specialization->template_entity;
                    if (specialization->template_param_index !=
                        cir::ArrayTypePayload::no_extent_param) {
                        const TemplateArgument* substituted_template = nullptr;
                        auto exact =
                            callbacks.exact_template_parameter_bindings.find(
                                static_cast<uint32_t>(
                                    template_entity.index));
                        if (exact !=
                                callbacks
                                    .exact_template_parameter_bindings.end() &&
                            exact->second.is_single() &&
                            exact->second.arguments.size() == 1) {
                            substituted_template =
                                &exact->second.arguments.front();
                        } else {
                            substituted_template =
                                single_substitution_argument(
                                    argument_bindings,
                                    specialization->template_param_index);
                        }
                        if (!substituted_template ||
                            substituted_template->kind !=
                                cir::TemplateArgumentKind::Template) {
                            substituted_arguments = false;
                        } else {
                            template_entity =
                                substituted_template->template_entity;
                        }
                    }
                    bool template_still_dependent =
                        template_entity.valid() &&
                        file_.valid(template_entity) &&
                        file_.entity(template_entity).kind ==
                            cir::EntityKind::TemplateParam;
                    if (substituted_arguments &&
                        !arguments_still_dependent &&
                        !template_still_dependent) {
                        if (callbacks.instantiate_value) {
                            std::optional<TemplateArgument> value =
                                callbacks.instantiate_value(
                                    template_entity,
                                    std::move(entity_arguments));
                            if (value.has_value() &&
                                (value->value_kind ==
                                     cir::TemplateValueKind::Integer ||
                                 value->value_kind ==
                                     cir::TemplateValueKind::Boolean)) {
                                node = file_
                                    .template_integer_expression_node(
                                        value->integer_value,
                                        value->value_type);
                            }
                        } else {
                            cir::EntityId concrete =
                                callbacks.instantiate_value_entity(
                                    template_entity,
                                    std::move(entity_arguments));
                            if (concrete.valid() && file_.valid(concrete)) {
                                const cir::Entity& value =
                                    file_.entity(concrete);
                                if (value.has_constant_value &&
                                    (value.constant_value_kind ==
                                         cir::TemplateValueKind::Integer ||
                                     value.constant_value_kind ==
                                         cir::TemplateValueKind::Boolean)) {
                                    cir::TypeRef result_type =
                                        value.type.valid()
                                            ? type_ref(value.type)
                                            : node.result_type;
                                    node = file_
                                        .template_integer_expression_node(
                                            value.constant_integer_value,
                                            result_type);
                                }
                            }
                        }
                    }
                }
            }
            if (!deferred_pack_operand && node.type.valid() &&
                type_contains_type_param(node.type)) {
                cir::TypeId substituted =
                    substitute_pattern_type(node.type,
                                            argument_bindings,
                                            callbacks);
                if (!substituted.valid()) {
                    cir::TypeId resolved = file_.resolved_type(node.type);
                    if (callbacks.preserve_opaque_dependent_call_types &&
                        file_.valid(resolved) &&
                        file_.type(resolved).kind ==
                            cir::TypeKind::Dependent) {
                        continue;
                    }
                    set_template_binding_error(
                        error_out,
                        "dependent value expression operand type could not be substituted");
                    return false;
                }
                node.type = substituted;
            }
            if (node.kind == cir::TemplateValueExprKind::TypeOperand &&
                !retained_member_access &&
                node.qualifier_type.type.valid() && node.name.valid() &&
                !is_dependent_type(node.qualifier_type.type)) {

                if (address_operand_nodes.contains(
                        static_cast<uint32_t>(node_index))) {
                    continue;
                }
                cir::TypeId qualifier =
                    file_.resolved_type(node.qualifier_type.type);
                if (!file_.valid(qualifier) ||
                    file_.type(qualifier).kind != cir::TypeKind::Record) {
                    set_template_binding_error(
                        error_out,
                        "dependent qualified constant has a non-class qualifier after substitution");
                    return false;
                }
                MemberLookupResult lookup = lookup_member_name(
                    qualifier, file_.name(node.name));
                cir::EntityId constant_entity{};
                if (lookup.found_name && !lookup.ambiguous) {
                    for (const MemberLookupDeclaration& declaration :
                         lookup.declarations) {
                        if (!declaration.entity.valid() ||
                            !file_.valid(declaration.entity)) {
                            continue;
                        }
                        if (!static_data_member_fact(declaration.entity)) {
                            continue;
                        }
                        if (constant_entity.valid() &&
                            constant_entity != declaration.entity) {
                            constant_entity = {};
                            break;
                        }
                        constant_entity = declaration.entity;
                    }
                }
                if (!constant_entity.valid()) {
                    set_template_binding_error(
                        error_out,
                        "dependent qualified constant could not be resolved after substitution");
                    return false;
                }
                if (request_class_member_instantiation(
                        constant_entity,
                        cir::InstantiationDemandKind::ConstantEvaluation,
                        SrcLoc()) !=
                    InstantiationDemandResult::Satisfied) {
                    set_template_binding_error(
                        error_out,
                        "dependent qualified constant initializer could not "
                        "be materialized after substitution");
                    return false;
                }
                ExprResult constant_expr = make_entity_reference(
                    constant_entity, file_.name(node.name), SrcLoc(), true);
                TemplateValueConstant constant;
                cir::TypeId constant_type = constant_expr.type;
                if (!evaluate_template_value_constant(
                        std::move(constant_expr),
                        constant_type,
                        constant,
                        SrcLoc()) ||
                    (constant.kind != cir::TemplateValueKind::Integer &&
                     constant.kind != cir::TemplateValueKind::Boolean)) {
                    set_template_binding_error(
                        error_out,
                        "dependent qualified constant is not an integral constant expression");
                    return false;
                }
                node = file_.template_integer_expression_node(
                    constant.integer_value, type_ref(constant_type));
            }
            if (node.kind == cir::TemplateValueExprKind::TypeTrait) {
                std::optional<BuiltinKind> builtin_kind =
                    builtin_kind_for_type_trait(node.trait_kind);
                if (!builtin_kind.has_value() || node.operands.empty()) {
                    set_template_binding_error(
                        error_out,
                        "dependent builtin type trait recipe is invalid");
                    return false;
                }
                std::vector<cir::TypeRef> trait_operands;
                trait_operands.reserve(node.operands.size());
                bool operands_still_dependent = false;
                for (uint32_t operand_index : node.operands) {
                    if (operand_index >=
                        argument.dependent_value_expr.nodes.size()) {
                        set_template_binding_error(
                            error_out,
                            "dependent builtin type trait operand is invalid");
                        return false;
                    }
                    const cir::TemplateValueExprNode& operand =
                        argument.dependent_value_expr.nodes[operand_index];
                    if (operand.kind !=
                            cir::TemplateValueExprKind::TypeOperand ||
                        !operand.result_type.type.valid()) {
                        set_template_binding_error(
                            error_out,
                            "dependent builtin type trait operand is not a type");
                        return false;
                    }
                    if (operand.expands_parameter_pack) {
                        const TemplateArgumentBinding* binding =
                            substitution_binding(argument_bindings,
                                                 operand.parameter_index);
                        if (!binding || binding->is_unbound()) {
                            operands_still_dependent = true;
                            continue;
                        }
                        if (!binding->is_pack()) {
                            set_template_binding_error(
                                error_out,
                                "dependent builtin type trait expansion does "
                                "not name a type argument pack");
                            return false;
                        }
                        std::optional<std::vector<cir::TypeRef>> expanded =
                            substitute_pattern_function_parameter_pack(
                                operand.result_type, argument_bindings,
                                callbacks);
                        if (!expanded.has_value()) {
                            set_template_binding_error(
                                error_out,
                                "dependent builtin type trait pack operand "
                                "could not be expanded");
                            return false;
                        }
                        for (cir::TypeRef element : *expanded) {
                            trait_operands.push_back(element);
                            operands_still_dependent =
                                operands_still_dependent ||
                                is_dependent_type(element.type);
                        }
                        continue;
                    }
                    trait_operands.push_back(operand.result_type);
                    operands_still_dependent =
                        operands_still_dependent ||
                        is_dependent_type(operand.result_type.type);
                }
                if (operands_still_dependent) {
                    continue;
                }
                std::optional<bool> value = evaluate_builtin_type_trait(
                    *builtin_kind, trait_operands,
                    argument.dependent_value_expr.loc);
                if (!value.has_value()) {
                    set_template_binding_error(
                        error_out,
                        "dependent builtin type trait could not be evaluated");
                    return false;
                }
                node = file_.template_integer_expression_node(
                    cir::IntegerValue::from_unsigned(*value ? 1 : 0, 1),
                    node.result_type);
                continue;
            }
            if (node.kind != cir::TemplateValueExprKind::SizeofType &&
                node.kind != cir::TemplateValueExprKind::AlignofType) {
                continue;
            }
            if (node.type.valid() && !is_dependent_type(node.type)) {
                cir::TypeId query_type = file_.resolved_type(node.type);
                if (file_.valid(query_type) &&
                    (file_.type(query_type).kind ==
                         cir::TypeKind::LValueReference ||
                     file_.type(query_type).kind ==
                         cir::TypeKind::RValueReference)) {
                    query_type =
                        file_.reference_referred_ref(query_type).type;
                }
                std::optional<size_t> folded =
                    node.kind == cir::TemplateValueExprKind::SizeofType
                        ? cir::size_of_type(file_, query_type)
                        : cir::align_of_type(file_, query_type);
                if (!folded.has_value()) {
                    set_template_binding_error(
                        error_out,
                        "sizeof operand is incomplete after substitution");
                    return false;
                }
                node = file_.template_integer_expression_node(
                    cir::IntegerValue::from_unsigned(*folded, 64),
                    node.result_type);
            }
        }
        bool evaluation_invalid = false;
        std::optional<int64_t> evaluated =
            evaluate_template_value_expr(*this,
                                         argument.dependent_value_expr,
                                         argument_bindings,
                                         callbacks,
                                         &evaluation_invalid,
                                         error_out);
        if (evaluation_invalid) {
            return false;
        }
        if (!evaluated.has_value()) {
            std::optional<cir::TemplateValueExpression> substituted =
                substitute_template_value_expr(*this,
                                               argument.dependent_value_expr,
                                               argument_bindings,
                                               callbacks,
                                               error_out);
            if (!substituted.has_value()) {
                set_template_binding_error(
                    error_out,
                    "dependent template value expression could not be substituted");
                return false;
            }
            argument.dependent_value_expr = std::move(*substituted);
            file_.canonicalize_template_value_expression(
                argument.dependent_value_expr);
            argument.value_param_index =
                cir::ArrayTypePayload::no_extent_param;
            argument.value_kind = cir::TemplateValueKind::None;
            argument.is_dependent = true;
            return true;
        }
        cir::TypeId expected_type = argument.value_type.type.valid()
            ? argument.value_type.type
            : builder_.int_type();
        TemplateValueConstant constant;
        constant.kind = cir::TemplateValueKind::Integer;
        constant.integer_value = cir::IntegerValue::from_signed(
            *evaluated, 64);
        TemplateArgument concrete;
        if (!build_template_value_argument(expected_type,
                                           constant,
                                           concrete,
                                           error_out)) {
            return false;
        }
        concrete.is_defaulted = argument.is_defaulted;
        argument = std::move(concrete);
        return true;
    }
    if (argument.value_param_index !=
        cir::ArrayTypePayload::no_extent_param) {
        uint32_t index = argument.value_param_index;
        const TemplateArgument* substitution = single_argument_from_binding(
            exact_or_positional_binding(
                argument_bindings,
                index,
                argument.value_entity,
                callbacks.exact_value_parameter_bindings),
            callbacks.allow_parameter_pack_element_substitution);
        if (!substitution ||
            substitution->kind != cir::TemplateArgumentKind::Value) {
            set_template_binding_error(
                error_out,
                "dependent template value argument could not be substituted");
            return false;
        }
        cir::TypeRef target_type = argument.value_type;
        argument = *substitution;
        if (target_type.type.valid()) {
            bool target_contains_placeholder =
                contains_auto_type(target_type.type);
            if (argument.value_type.type.valid() &&
                !target_contains_placeholder &&
                file_.resolved_type(target_type.type) !=
                    file_.resolved_type(argument.value_type.type)) {
                set_template_binding_error(
                    error_out,
                    "dependent template value argument conversion is not supported yet");
                return false;
            }

            if (!target_contains_placeholder) {
                argument.value_type = target_type;
            }
            if (argument.value_kind == cir::TemplateValueKind::None) {
                argument.value_kind =
                    file_.template_value_kind_for_type(
                        argument.value_type.type);
                argument.null_kind =
                    null_kind_for_value_kind(file_,
                                             argument.value_type.type,
                                             argument.value_kind);
            }
        }

        return true;
    }
    if (!argument.dependent_value_qualifier.type.valid() ||
        !argument.dependent_value_name.valid()) {

        if (argument.value_kind != cir::TemplateValueKind::None &&
            !argument.expands_pack_pattern &&
            (!argument.value_type.type.valid() ||
             !is_dependent_type(argument.value_type.type))) {
            argument.is_dependent = false;
        }
        return true;
    }
    const bool saved_materialization =
        callbacks.materialize_type_template_definition;

    callbacks.materialize_type_template_definition = true;
    cir::TypeId qualifier =
        substitute_pattern_type(argument.dependent_value_qualifier.type,
                                argument_bindings,
                                callbacks);
    callbacks.materialize_type_template_definition =
        saved_materialization;
    if (!qualifier.valid()) {
        set_template_binding_error(
            error_out,
            "dependent qualified template value argument could not be substituted");
        return false;
    }
    argument.dependent_value_qualifier =
        type_ref(qualifier,
                 argument.dependent_value_qualifier.qualifiers,
                 argument.dependent_value_qualifier.memory_space);
    if (is_dependent_type(qualifier)) {
        argument.is_dependent = true;
        return true;
    }

    cir::TypeId resolved_qualifier = file_.resolved_type(qualifier);
    if (!file_.valid(resolved_qualifier) ||
        file_.type(resolved_qualifier).kind != cir::TypeKind::Record) {
        set_template_binding_error(
            error_out,
            "dependent qualified template value argument qualifier is not a record");
        return false;
    }
    const cir::RecordFacts* qualifier_facts =
        file_.record_facts_for_type(resolved_qualifier);
    if ((!qualifier_facts || qualifier_facts->is_incomplete) &&
        !require_complete_class_type(
            resolved_qualifier,
            callbacks.access_loc,
            cir::InstantiationDemandKind::BaseMemberList)) {
        set_template_binding_error(
            error_out,
            "dependent qualified template value argument scope could not be completed");
        return false;
    }
    cir::EntityId record = file_.record_entity(resolved_qualifier);
    if (!record.valid() || !file_.valid(record) ||
        !file_.entity(record).semantic_context.valid()) {
        set_template_binding_error(
            error_out,
            "dependent qualified template value argument scope is unavailable");
        return false;
    }
    ExprResult expr = lookup_qualified_name(
        file_.entity(record).semantic_context,
        file_.name(argument.dependent_value_name),
        SrcLoc());
    if (expr.has_error) {
        set_template_binding_error(
            error_out,
            "dependent qualified template value argument lookup failed");
        return false;
    }
    if (expr.entity.valid() && file_.valid(expr.entity) &&
        static_data_member_fact(expr.entity) &&
        request_class_member_instantiation(
            expr.entity,
            cir::InstantiationDemandKind::ConstantEvaluation,
            callbacks.access_loc) != InstantiationDemandResult::Satisfied) {
        set_template_binding_error(
            error_out,
            "dependent qualified template value argument initializer could "
            "not be materialized");
        return false;
    }
    cir::TypeId expected_type = argument.value_type.type;
    if (contains_auto_type(expected_type, cir::AutoTypeFlavor::Cxx)) {
        expected_type = deduce_auto_type(expected_type, expr, SrcLoc());
        if (!expected_type.valid()) {
            set_template_binding_error(
                error_out,
                "cannot deduce auto template parameter type");
            return false;
        }
    }
    TemplateValueConstant constant;
    if (!evaluate_template_value_constant(std::move(expr),
                                          expected_type,
                                          constant,
                                          SrcLoc())) {
        set_template_binding_error(
            error_out,
            "template argument is not a constant expression");
        return false;
    }
    TemplateArgument concrete;
    if (!build_template_value_argument(expected_type, constant, concrete,
                                       error_out)) {
        return false;
    }
    concrete.is_defaulted = argument.is_defaulted;
    argument = std::move(concrete);
    return true;
}

std::optional<bool> Session::evaluate_dependent_boolean_expression(
    cir::TemplateValueExpression expression,
    const TemplateArgumentBindings& bindings,
    std::string* error_out) {
    if (!expression.valid()) {
        return std::nullopt;
    }
    TemplateArgument argument;
    argument.kind = cir::TemplateArgumentKind::Value;
    argument.value_type = type_ref(builder_.bool_type());
    argument.dependent_value_expr = std::move(expression);
    argument.is_dependent = true;
    PatternInstantiationCallbacks callbacks;
    if (!substitute_template_value_argument(argument,
                                            bindings,
                                            callbacks,
                                            error_out) ||
        argument.is_dependent ||
        argument.kind != cir::TemplateArgumentKind::Value) {
        return std::nullopt;
    }
    if (argument.value_kind != cir::TemplateValueKind::Integer &&
        argument.value_kind != cir::TemplateValueKind::Boolean) {
        return std::nullopt;
    }
    return !argument.integer_value.is_zero();
}

bool Session::substitute_template_template_argument(
    TemplateArgument& argument,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks,
    std::string* error_out) {
    if (argument.kind != cir::TemplateArgumentKind::Template) {
        return true;
    }
    uint32_t parameter_index = argument.template_param_index;
    if (parameter_index == cir::ArrayTypePayload::no_extent_param &&
        argument.template_entity.valid() &&
        file_.valid(argument.template_entity) &&
        file_.entity(argument.template_entity).kind ==
            cir::EntityKind::TemplateParam) {
        if (const TemplateInfo* parameter =
                template_info(argument.template_entity)) {
            parameter_index = parameter->template_parameter_index;
        }
    }
    if (parameter_index !=
        cir::ArrayTypePayload::no_extent_param) {
        const TemplateArgument* substitution = single_argument_from_binding(
            exact_or_positional_binding(
                argument_bindings,
                parameter_index,
                argument.template_entity,
                callbacks.exact_template_parameter_bindings),
            callbacks.allow_parameter_pack_element_substitution);
        if (!substitution ||
            substitution->kind != cir::TemplateArgumentKind::Template) {
            set_template_binding_error(
                error_out,
                "dependent template template argument could not be substituted");
            return false;
        }
        argument = *substitution;
        return true;
    }
    if (!template_argument_has_dependent_template_name(argument)) {
        return true;
    }

    cir::TypeId qualifier =
        substitute_pattern_type(argument.dependent_template_qualifier.type,
                                argument_bindings,
                                callbacks);
    if (!qualifier.valid()) {
        set_template_binding_error(
            error_out,
            "dependent qualified template template argument qualifier could not be substituted");
        return false;
    }
    argument.dependent_template_qualifier =
        type_ref(qualifier,
                 argument.dependent_template_qualifier.qualifiers,
                 argument.dependent_template_qualifier.memory_space);
    if (is_dependent_type(qualifier)) {
        argument.is_dependent = true;
        return true;
    }

    cir::TypeId resolved_qualifier = file_.resolved_type(qualifier);
    if (!file_.valid(resolved_qualifier) ||
        file_.type(resolved_qualifier).kind != cir::TypeKind::Record) {
        set_template_binding_error(
            error_out,
            "dependent qualified template template argument qualifier is not a record");
        return false;
    }
    cir::EntityId record = file_.record_entity(resolved_qualifier);
    if (!record.valid() || !file_.valid(record) ||
        !file_.entity(record).semantic_context.valid()) {
        set_template_binding_error(
            error_out,
            "dependent qualified template template argument scope is unavailable");
        return false;
    }
    const TemplateInfo* info =
        template_info_in_context(file_.entity(record).semantic_context,
                                 file_.name(argument.template_name),
                                 /*include_parents=*/false);
    if (!info || (!info->is_class_template && !info->is_alias_template)) {
        set_template_binding_error(
            error_out,
            "dependent qualified template template argument lookup failed");
        return false;
    }
    argument.template_entity = info->entity;
    argument.template_param_index =
        info->entity.valid() && file_.valid(info->entity) &&
                file_.entity(info->entity).kind == cir::EntityKind::TemplateParam
            ? info->template_parameter_index
            : cir::ArrayTypePayload::no_extent_param;
    argument.dependent_template_qualifier = {};
    argument.is_dependent =
        argument.template_param_index != cir::ArrayTypePayload::no_extent_param;
    return true;
}

bool Session::compose_constraint_parameter_mappings(
    NormalizedConstraint& form,
    uint32_t root,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks,
    std::string* error_out) {
    uint32_t root_to_visit =
        root == NormalizedConstraint::no_node ? form.root : root;
    if (!form.valid_node(root_to_visit)) {
        set_template_binding_error(
            error_out,
            "constraint normal form root is unavailable");
        return false;
    }

    auto substitute_mapping_argument = [&](TemplateArgument& argument) -> bool {
        switch (argument.kind) {
            case cir::TemplateArgumentKind::Type: {
                cir::TypeId direct_type =
                    file_.resolved_type(argument.type.type);
                if (file_.valid(direct_type) &&
                    file_.type(direct_type).kind == cir::TypeKind::TypeParam) {
                    const auto* parameter =
                        std::get_if<cir::TypeParamTypePayload>(
                            &file_.type_payload(direct_type));
                    const TemplateArgumentBinding* direct_binding = parameter
                        ? substitution_binding(argument_bindings,
                                               parameter->index)
                        : nullptr;
                    if (direct_binding && direct_binding->is_single() &&
                        direct_binding->arguments.size() == 1 &&
                        direct_binding->arguments.front().kind ==
                            cir::TemplateArgumentKind::Type &&
                        direct_binding->arguments.front().value_param_index !=
                            cir::ArrayTypePayload::no_extent_param) {
                        const TemplateArgument& marker =
                            direct_binding->arguments.front();
                        argument.type.type = marker.type.type;
                        argument.value_param_index =
                            marker.value_param_index;
                        argument.is_dependent = true;
                    }
                }
                if (argument.value_param_index !=
                    cir::ArrayTypePayload::no_extent_param) {
                    const TemplateArgumentBinding* binding =
                        substitution_binding(argument_bindings,
                                             argument.value_param_index);
                    if (binding && binding->is_single() &&
                        binding->arguments.size() == 1 &&
                        binding->arguments.front().kind ==
                            cir::TemplateArgumentKind::Value &&
                        binding->arguments.front().value_type.valid()) {
                        argument.type =
                            binding->arguments.front().value_type;
                        argument.value_param_index =
                            cir::ArrayTypePayload::no_extent_param;
                        argument.is_dependent =
                            is_dependent_type(argument.type.type);
                        return true;
                    }

                }
                if (!argument.type.type.valid()) {
                    return true;
                }
                cir::TypeId substituted =
                    substitute_pattern_type(argument.type.type,
                                            argument_bindings,
                                            callbacks);
                if (!substituted.valid()) {
                    set_template_binding_error(
                        error_out,
                        "constraint type parameter mapping could not be substituted");
                    return false;
                }
                argument.type =
                    type_ref(substituted,
                             argument.type.qualifiers,
                             argument.type.memory_space);
                argument.is_dependent = is_dependent_type(substituted);
                return true;
            }
            case cir::TemplateArgumentKind::Value:
                return substitute_template_value_argument(argument,
                                                          argument_bindings,
                                                          callbacks,
                                                          error_out);
            case cir::TemplateArgumentKind::Template:
                return substitute_template_template_argument(
                    argument,
                    argument_bindings,
                    callbacks,
                    error_out);
        }
        return true;
    };
    auto mapping_argument_names_mapped_pack =
        [&](const ConstraintParameterMapping& mapping) {
        if (!mapping.parameter_is_pack) {
            return false;
        }
        switch (mapping.parameter_kind) {
            case TemplateParameterKind::Type:
                return mapping.argument.kind ==
                           cir::TemplateArgumentKind::Type &&
                       mapping.argument.type.type.valid() &&
                       type_parameter_pack_index(
                           mapping.argument.type.type) ==
                           mapping.parameter_index;
            case TemplateParameterKind::NonType:
                return mapping.argument.kind ==
                           cir::TemplateArgumentKind::Value &&
                       mapping.argument.value_param_index ==
                           mapping.parameter_index;
            case TemplateParameterKind::Template:
                return mapping.argument.kind ==
                           cir::TemplateArgumentKind::Template &&
                       mapping.argument.template_param_index ==
                           mapping.parameter_index;
        }
        return false;
    };
    auto compose_mapping = [&](ConstraintParameterMapping& mapping) -> bool {
        if (mapping.argument_pack.has_value()) {

            std::vector<TemplateArgument> composed_arguments;
            for (const TemplateArgument& argument :
                 *mapping.argument_pack) {
                if (!append_substituted_template_argument(
                        argument,
                        argument_bindings,
                        callbacks,
                        composed_arguments,
                        /*reject_unresolved_template_parameter=*/false,
                        error_out)) {
                    return false;
                }
            }
            mapping.argument_pack = std::move(composed_arguments);
            return true;
        }
        if (mapping_argument_names_mapped_pack(mapping)) {
            const TemplateArgumentBinding* binding =
                substitution_binding(argument_bindings,
                                     mapping.parameter_index);
            if (!binding || !binding->is_pack()) {
                set_template_binding_error(
                    error_out,
                    "constraint parameter pack mapping has no arguments");
                return false;
            }
            mapping.argument_pack = binding->arguments;
            for (const TemplateArgument& argument :
                 *mapping.argument_pack) {
                if (argument.kind != mapping.argument.kind) {
                    set_template_binding_error(
                        error_out,
                        "constraint parameter pack mapping has mixed argument kinds");
                    return false;
                }
            }
            return true;
        }
        return substitute_mapping_argument(mapping.argument);
    };
    auto fold_argument_matches_parameter =
        [](const ConstraintFoldExpansionParameter& parameter,
           const TemplateArgument& argument) {
        switch (parameter.kind) {
            case ConstraintFoldExpansionParameterKind::Function:
                return false;
            case ConstraintFoldExpansionParameterKind::Type:
                return argument.kind == cir::TemplateArgumentKind::Type;
            case ConstraintFoldExpansionParameterKind::Value:
                return argument.kind == cir::TemplateArgumentKind::Value;
            case ConstraintFoldExpansionParameterKind::Template:
                return argument.kind == cir::TemplateArgumentKind::Template;
        }
        return false;
    };
    auto fold_argument_pack_index =
        [&](const TemplateArgument& argument) -> std::optional<uint32_t> {
        switch (argument.kind) {
            case cir::TemplateArgumentKind::Type:
                if (!argument.type.type.valid()) {
                    return std::nullopt;
                }
                return type_parameter_pack_index(argument.type.type);
            case cir::TemplateArgumentKind::Value:
                if (argument.value_param_index ==
                    cir::ArrayTypePayload::no_extent_param) {
                    return std::nullopt;
                }
                return argument.value_param_index;
            case cir::TemplateArgumentKind::Template:
                if (argument.template_param_index ==
                    cir::ArrayTypePayload::no_extent_param) {
                    return std::nullopt;
                }
                return argument.template_param_index;
        }
        return std::nullopt;
    };
    auto compose_fold_argument_pack =
        [&](const ConstraintFoldExpansionParameter& parameter,
            const TemplateArgument& marker,
            std::optional<std::vector<TemplateArgument>>& argument_pack)
        -> bool {
        if (!fold_argument_matches_parameter(parameter, marker)) {
            return false;
        }
        std::optional<uint32_t> pack_index =
            fold_argument_pack_index(marker);
        if (!pack_index.has_value()) {
            return false;
        }
        const TemplateArgumentBinding* binding =
            substitution_binding(argument_bindings, *pack_index);
        if (!binding || !binding->is_pack()) {
            set_template_binding_error(
                error_out,
                "constraint fold parameter pack mapping has no arguments");
            return true;
        }
        argument_pack = binding->arguments;
        for (const TemplateArgument& argument : *argument_pack) {
            if (!fold_argument_matches_parameter(parameter, argument)) {
                set_template_binding_error(
                    error_out,
                    "constraint fold parameter pack mapping has mixed argument kinds");
                return true;
            }
        }
        return true;
    };
    auto compose_fold_expansion_parameter =
        [&](ConstraintFoldExpansionParameter& parameter) -> bool {
        if (parameter.kind ==
            ConstraintFoldExpansionParameterKind::Function) {
            return true;
        }
        if (parameter.argument_pack.has_value()) {
            if (parameter.argument_pack->size() == 1) {
                std::optional<std::vector<TemplateArgument>> composed_pack;
                if (compose_fold_argument_pack(parameter,
                                               (*parameter.argument_pack)[0],
                                               composed_pack)) {
                    if (!composed_pack.has_value()) {
                        return false;
                    }
                    parameter.argument_pack = std::move(composed_pack);
                    return true;
                }
            }
            for (TemplateArgument& argument : *parameter.argument_pack) {
                if (!substitute_mapping_argument(argument)) {
                    return false;
                }
            }
            return true;
        }
        std::optional<std::vector<TemplateArgument>> composed_pack;
        if (compose_fold_argument_pack(parameter,
                                       parameter.argument,
                                       composed_pack)) {
            if (!composed_pack.has_value()) {
                return false;
            }
            parameter.argument_pack = std::move(composed_pack);
            return true;
        }
        return substitute_mapping_argument(parameter.argument);
    };

    std::vector<uint8_t> visited(form.nodes.size(), 0);
    std::function<bool(uint32_t)> visit = [&](uint32_t index) -> bool {
        if (!form.valid_node(index)) {
            return false;
        }
        if (visited[index]) {
            return true;
        }
        visited[index] = 1;

        NormalizedConstraintNode& node = form.nodes[index];
        switch (node.kind) {
            case NormalizedConstraintKind::Atomic:
            case NormalizedConstraintKind::ConceptDependent:
                for (ConstraintParameterMapping& mapping :
                     node.atom.parameter_mapping) {
                    if (!compose_mapping(mapping)) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                "constraint parameter mapping could not be substituted";
                        }
                        return false;
                    }
                }
                for (TemplateArgument& argument :
                     node.concept_id_arguments) {
                    if (!substitute_mapping_argument(argument)) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                "constraint concept-id argument could not be substituted";
                        }
                        return false;
                    }
                }
                return true;
            case NormalizedConstraintKind::Conjunction:
            case NormalizedConstraintKind::Disjunction:
                return visit(node.lhs) && visit(node.rhs);
            case NormalizedConstraintKind::FoldExpanded:
            {
                bool expands_concept_template_pack = false;
                for (ConstraintFoldExpansionParameter& parameter :
                     node.fold_expansion_parameters) {
                    if (!compose_fold_expansion_parameter(parameter)) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                "constraint fold expansion parameter could not be substituted";
                        }
                        return false;
                    }
                    expands_concept_template_pack =
                        expands_concept_template_pack ||
                        (parameter.kind ==
                             ConstraintFoldExpansionParameterKind::Template &&
                         parameter.template_template_parameter_kind ==
                             TemplateTemplateParameterKind::Concept);
                }
                node.fold_pattern_argument_bindings = argument_bindings;
                if (expands_concept_template_pack) {
                    return visit(node.lhs);
                }
                return true;
            }
        }
        return true;
    };
    if (!visit(root_to_visit)) {
        return false;
    }
    if (root_to_visit == form.root && form.value_expression.valid()) {
        TemplateArgument expression_argument;
        expression_argument.kind = cir::TemplateArgumentKind::Value;
        expression_argument.value_type = type_ref(builder_.bool_type());
        expression_argument.dependent_value_expr = form.value_expression;
        expression_argument.is_dependent = true;
        std::string graph_error;
        if (substitute_template_value_argument(expression_argument,
                                               argument_bindings,
                                               callbacks,
                                               &graph_error)) {
            if (expression_argument.dependent_value_expr.valid()) {
                form.value_expression =
                    std::move(expression_argument.dependent_value_expr);
            } else if (!expression_argument.is_dependent) {
                cir::TemplateValueExpression concrete;
                concrete.loc = form.value_expression.loc;
                concrete.definition_context =
                    form.value_expression.definition_context;
                concrete.definition_lookup_generation =
                    form.value_expression.definition_lookup_generation;
                cir::TemplateValueExprNode node =
                    file_.template_integer_expression_node(
                        cir::IntegerValue::from_unsigned(
                            expression_argument.integer_value.is_zero()
                                ? 0
                                : 1,
                            1),
                        type_ref(builder_.bool_type()));
                concrete.nodes.push_back(node);
                concrete.root = 0;
                file_.canonicalize_template_value_expression(concrete);
                form.value_expression = std::move(concrete);
            }
        }
    }
    return true;
}

bool Session::template_arguments_equivalent(
    const TemplateArgument& lhs,
    const TemplateArgument& rhs) const {
    if (lhs.kind != rhs.kind ||
        lhs.expands_parameter_pack != rhs.expands_parameter_pack) {
        return false;
    }

    switch (lhs.kind) {
        case cir::TemplateArgumentKind::Type:
            return lhs.value_param_index == rhs.value_param_index &&
                   template_type_refs_equivalent(file_, lhs.type, rhs.type);
        case cir::TemplateArgumentKind::Value:
            return template_value_arguments_equivalent(lhs, rhs);
        case cir::TemplateArgumentKind::Template:
            return lhs.template_entity == rhs.template_entity &&
                   lhs.template_param_index == rhs.template_param_index &&
                   template_type_refs_equivalent(
                       file_,
                       lhs.dependent_template_qualifier,
                       rhs.dependent_template_qualifier) &&
                   lhs.template_name == rhs.template_name;
    }
    return false;
}

bool Session::template_value_arguments_equivalent(
    const TemplateArgument& lhs,
    const TemplateArgument& rhs) const {
    if (lhs.kind != cir::TemplateArgumentKind::Value ||
        rhs.kind != cir::TemplateArgumentKind::Value) {
        return false;
    }
    if (lhs.value_type.type.valid() && rhs.value_type.type.valid() &&
        !template_type_refs_equivalent(file_, lhs.value_type, rhs.value_type)) {
        return false;
    }
    if (lhs.value_kind != rhs.value_kind ||
        lhs.null_kind != rhs.null_kind ||
        lhs.meta_kind != rhs.meta_kind ||
        !template_type_refs_equivalent(file_, lhs.type, rhs.type) ||
        lhs.integer_value != rhs.integer_value ||
        lhs.value_entity != rhs.value_entity ||
        lhs.closure_identity != rhs.closure_identity ||
        lhs.value_byte_offset != rhs.value_byte_offset ||
        lhs.value_param_index != rhs.value_param_index ||
        !template_value_exprs_equivalent(lhs.dependent_value_expr,
                                         rhs.dependent_value_expr,
                                         &file_) ||
        lhs.generated_pack_kind != rhs.generated_pack_kind ||
        !template_type_refs_equivalent(file_,
                                       lhs.generated_pack_count_type,
                                       rhs.generated_pack_count_type) ||
        !template_value_exprs_equivalent(lhs.generated_pack_count_expr,
                                         rhs.generated_pack_count_expr,
                                         &file_) ||
        !template_type_refs_equivalent(file_,
                                       lhs.dependent_value_qualifier,
                                       rhs.dependent_value_qualifier) ||
        lhs.dependent_value_name != rhs.dependent_value_name ||
        lhs.value_elements.size() != rhs.value_elements.size()) {
        return false;
    }
    if (lhs.value_kind == cir::TemplateValueKind::Floating &&
        lhs.floating_value != rhs.floating_value) {
        return false;
    }
    return std::equal(lhs.value_elements.begin(),
                      lhs.value_elements.end(),
                      rhs.value_elements.begin(),
                      [&](const TemplateArgument& left,
                          const TemplateArgument& right) {
                          return template_value_arguments_equivalent(left,
                                                                     right);
                      });
}

bool Session::constraint_atoms_declaration_equivalent(
    const ConstraintAtomIdentity& lhs,
    const ConstraintAtomIdentity& rhs) const {
    if (lhs.declaration_equivalence_key == 0 ||
        lhs.declaration_equivalence_key != rhs.declaration_equivalence_key ||
        lhs.parameter_mapping.size() != rhs.parameter_mapping.size()) {
        return false;
    }

    ConstraintAtomIdentity lhs_keyed = lhs;
    ConstraintAtomIdentity rhs_keyed = rhs;
    lhs_keyed.appearance_owner = {};
    rhs_keyed.appearance_owner = {};
    lhs_keyed.expression_begin = 0;
    rhs_keyed.expression_begin = 0;
    lhs_keyed.expression_end = 0;
    rhs_keyed.expression_end = 0;
    return constraint_atoms_identical(lhs_keyed, rhs_keyed);
}

bool Session::constraint_atoms_identical(
    const ConstraintAtomIdentity& lhs,
    const ConstraintAtomIdentity& rhs) const {
    if (!lhs.same_appearance_as(rhs) ||
        lhs.parameter_mapping.size() != rhs.parameter_mapping.size()) {
        return false;
    }
    auto template_argument_lists_equivalent =
        [&](const std::vector<TemplateArgument>& lhs_arguments,
            const std::vector<TemplateArgument>& rhs_arguments) -> bool {
        if (lhs_arguments.size() != rhs_arguments.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs_arguments.size(); ++i) {
            if (!template_arguments_equivalent(lhs_arguments[i],
                                               rhs_arguments[i])) {
                return false;
            }
        }
        return true;
    };

    std::vector<uint8_t> matched(rhs.parameter_mapping.size(), 0);
    for (const ConstraintParameterMapping& lhs_mapping :
         lhs.parameter_mapping) {
        bool found = false;
        for (size_t i = 0; i < rhs.parameter_mapping.size(); ++i) {
            if (matched[i]) {
                continue;
            }
            const ConstraintParameterMapping& rhs_mapping =
                rhs.parameter_mapping[i];
            if (!lhs_mapping.same_parameter_as(rhs_mapping)) {
                continue;
            }
            if (!template_arguments_equivalent(lhs_mapping.argument,
                                               rhs_mapping.argument)) {
                return false;
            }
            if (lhs_mapping.argument_pack.has_value() !=
                rhs_mapping.argument_pack.has_value()) {
                return false;
            }
            if (lhs_mapping.argument_pack.has_value() &&
                !template_argument_lists_equivalent(
                    *lhs_mapping.argument_pack,
                    *rhs_mapping.argument_pack)) {
                return false;
            }
            matched[i] = 1;
            found = true;
            break;
        }
        if (!found) {
            return false;
        }
    }
    return true;
}

bool Session::constraint_concept_pack_fold_argument_lengths_match(
    const NormalizedConstraint& form,
    uint32_t root,
    std::string* error_out) const {
    uint32_t root_to_visit =
        root == NormalizedConstraint::no_node ? form.root : root;
    if (!form.valid_node(root_to_visit)) {
        set_template_binding_error(
            error_out,
            "constraint normal form root is unavailable");
        return false;
    }

    std::optional<size_t> expected_count;
    std::vector<uint8_t> visited(form.nodes.size(), 0);
    std::function<bool(uint32_t)> visit = [&](uint32_t index) -> bool {
        if (!form.valid_node(index)) {
            return false;
        }
        if (visited[index]) {
            return true;
        }
        visited[index] = 1;

        const NormalizedConstraintNode& node = form.nodes[index];
        switch (node.kind) {
            case NormalizedConstraintKind::Atomic:
            case NormalizedConstraintKind::ConceptDependent:
                for (const ConstraintParameterMapping& mapping :
                     node.atom.parameter_mapping) {
                    if (mapping.parameter_kind !=
                            TemplateParameterKind::Template ||
                        mapping.parameter_template_template_kind !=
                            TemplateTemplateParameterKind::Concept ||
                        !mapping.parameter_is_pack ||
                        !mapping.argument_pack.has_value()) {
                        continue;
                    }
                    size_t count = mapping.argument_pack->size();
                    if (expected_count.has_value() &&
                        *expected_count != count) {
                        set_template_binding_error(
                            error_out,
                            "concept template parameter packs in constraint fold must have the same number of arguments");
                        return false;
                    }
                    expected_count = count;
                }
                return true;
            case NormalizedConstraintKind::Conjunction:
            case NormalizedConstraintKind::Disjunction:
                return visit(node.lhs) && visit(node.rhs);
            case NormalizedConstraintKind::FoldExpanded:
                return visit(node.lhs);
        }
        return true;
    };
    return visit(root_to_visit);
}

bool Session::normalized_constraints_equivalent(
    const NormalizedConstraint& lhs,
    const NormalizedConstraint& rhs,
    uint32_t lhs_root,
    uint32_t rhs_root,
    bool declaration_equivalence) const {
    uint32_t lhs_index =
        lhs_root == NormalizedConstraint::no_node ? lhs.root : lhs_root;
    uint32_t rhs_index =
        rhs_root == NormalizedConstraint::no_node ? rhs.root : rhs_root;
    if (!lhs.valid_node(lhs_index) || !rhs.valid_node(rhs_index)) {
        return false;
    }

    const NormalizedConstraintNode& lhs_node = lhs.nodes[lhs_index];
    const NormalizedConstraintNode& rhs_node = rhs.nodes[rhs_index];
    if (lhs_node.kind != rhs_node.kind) {
        return false;
    }
    auto template_argument_lists_equivalent =
        [&](const std::vector<TemplateArgument>& lhs_arguments,
            const std::vector<TemplateArgument>& rhs_arguments) -> bool {
        if (lhs_arguments.size() != rhs_arguments.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs_arguments.size(); ++i) {
            if (!template_arguments_equivalent(lhs_arguments[i],
                                               rhs_arguments[i])) {
                return false;
            }
        }
        return true;
    };
    auto fold_expansion_parameters_equivalent =
        [](const std::vector<ConstraintFoldExpansionParameter>& lhs_parameters,
           const std::vector<ConstraintFoldExpansionParameter>& rhs_parameters)
        -> bool {
        if (lhs_parameters.size() != rhs_parameters.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs_parameters.size(); ++i) {
            const ConstraintFoldExpansionParameter& lhs = lhs_parameters[i];
            const ConstraintFoldExpansionParameter& rhs = rhs_parameters[i];
            if (lhs.kind != rhs.kind) {
                return false;
            }
            if (lhs.kind ==
                    ConstraintFoldExpansionParameterKind::Template &&
                lhs.template_template_parameter_kind !=
                    rhs.template_template_parameter_kind) {
                return false;
            }
            bool lhs_has_slot =
                lhs.parameter_index != cir::ArrayTypePayload::no_extent_param;
            bool rhs_has_slot =
                rhs.parameter_index != cir::ArrayTypePayload::no_extent_param;
            if (lhs_has_slot || rhs_has_slot) {
                if (!lhs_has_slot || !rhs_has_slot ||
                    lhs.parameter_depth != rhs.parameter_depth ||
                    lhs.parameter_index != rhs.parameter_index) {
                    return false;
                }
                continue;
            }
            if (lhs.parameter_entity.valid() ||
                rhs.parameter_entity.valid()) {
                if (lhs.parameter_entity != rhs.parameter_entity) {
                    return false;
                }
                continue;
            }
            if (lhs.owning_template_entity.valid() ||
                rhs.owning_template_entity.valid()) {
                if (lhs.owning_template_entity !=
                    rhs.owning_template_entity) {
                    return false;
                }
                continue;
            }
            if (lhs.name != rhs.name) {
                return false;
            }
        }
        return true;
    };

    switch (lhs_node.kind) {
        case NormalizedConstraintKind::Atomic:
        case NormalizedConstraintKind::ConceptDependent:
            if (lhs_node.concept_id_template_parameter_index !=
                    rhs_node.concept_id_template_parameter_index ||
                (lhs_node.concept_id_template_parameter_index ==
                     cir::ArrayTypePayload::no_extent_param &&
                 lhs_node.concept_id_entity != rhs_node.concept_id_entity) ||
                !template_type_refs_equivalent(
                    file_,
                    lhs_node.concept_id_dependent_qualifier,
                    rhs_node.concept_id_dependent_qualifier) ||
                (lhs_node.concept_id_template_parameter_index ==
                     cir::ArrayTypePayload::no_extent_param &&
                 lhs_node.concept_id_name != rhs_node.concept_id_name) ||
                lhs_node.concept_id_qualified_name !=
                    rhs_node.concept_id_qualified_name ||
                !template_argument_lists_equivalent(
                    lhs_node.concept_id_arguments,
                    rhs_node.concept_id_arguments)) {
                return false;
            }
            if (lhs_node.kind == NormalizedConstraintKind::ConceptDependent) {

                return true;
            }
            return constraint_atoms_identical(lhs_node.atom, rhs_node.atom) ||
                   (declaration_equivalence &&
                    constraint_atoms_declaration_equivalent(lhs_node.atom,
                                                            rhs_node.atom));
        case NormalizedConstraintKind::Conjunction:
        case NormalizedConstraintKind::Disjunction:
            return normalized_constraints_equivalent(lhs,
                                                     rhs,
                                                     lhs_node.lhs,
                                                     rhs_node.lhs,
                                                     declaration_equivalence) &&
                   normalized_constraints_equivalent(lhs,
                                                     rhs,
                                                     lhs_node.rhs,
                                                     rhs_node.rhs,
                                                     declaration_equivalence);
        case NormalizedConstraintKind::FoldExpanded: {
            const TemplateArgumentBindings& lhs_bindings =
                lhs_node.fold_pattern_argument_bindings;
            const TemplateArgumentBindings& rhs_bindings =
                rhs_node.fold_pattern_argument_bindings;
            if (lhs_bindings.size() != rhs_bindings.size()) {
                return false;
            }
            for (size_t i = 0; i < lhs_bindings.size(); ++i) {
                if (lhs_bindings[i].kind != rhs_bindings[i].kind ||
                    !template_argument_lists_equivalent(
                        lhs_bindings[i].arguments,
                        rhs_bindings[i].arguments)) {
                    return false;
                }
            }
            return lhs_node.fold_operator == rhs_node.fold_operator &&
                   fold_expansion_parameters_equivalent(
                       lhs_node.fold_expansion_parameters,
                       rhs_node.fold_expansion_parameters) &&
                   normalized_constraints_equivalent(lhs,
                                                     rhs,
                                                     lhs_node.lhs,
                                                     rhs_node.lhs,
                                                     declaration_equivalence);
        }
    }
    return false;
}

bool Session::normalized_constraint_contains_concept_dependent(
    const NormalizedConstraint& form,
    uint32_t root) const {
    uint32_t index = root == NormalizedConstraint::no_node ? form.root
                                                           : root;
    if (!form.valid_node(index)) {
        return false;
    }

    const NormalizedConstraintNode& node = form.nodes[index];
    switch (node.kind) {
        case NormalizedConstraintKind::ConceptDependent:
            return true;
        case NormalizedConstraintKind::Conjunction:
        case NormalizedConstraintKind::Disjunction:
            return normalized_constraint_contains_concept_dependent(
                       form,
                       node.lhs) ||
                   normalized_constraint_contains_concept_dependent(
                       form,
                       node.rhs);
        case NormalizedConstraintKind::FoldExpanded:
            return normalized_constraint_contains_concept_dependent(
                form,
                node.lhs);
        case NormalizedConstraintKind::Atomic:
            return false;
    }
    return false;
}

bool Session::normalized_constraint_subsumes(
    const NormalizedConstraint& lhs,
    const NormalizedConstraint& rhs,
    uint32_t lhs_root,
    uint32_t rhs_root) const {
    uint32_t lhs_index =
        lhs_root == NormalizedConstraint::no_node ? lhs.root : lhs_root;
    uint32_t rhs_index =
        rhs_root == NormalizedConstraint::no_node ? rhs.root : rhs_root;
    if (!lhs.valid_node(lhs_index) || !rhs.valid_node(rhs_index)) {
        return false;
    }

    using Clause = std::vector<uint32_t>;
    auto combine_clauses = [](const std::vector<Clause>& left,
                              const std::vector<Clause>& right) {
        std::vector<Clause> combined;
        combined.reserve(left.size() * right.size());
        for (const Clause& lhs_clause : left) {
            for (const Clause& rhs_clause : right) {
                Clause merged = lhs_clause;
                merged.insert(merged.end(),
                              rhs_clause.begin(),
                              rhs_clause.end());
                combined.push_back(std::move(merged));
            }
        }
        return combined;
    };

    std::function<std::optional<std::vector<Clause>>(
        const NormalizedConstraint&,
        uint32_t)> dnf =
        [&](const NormalizedConstraint& form,
            uint32_t index) -> std::optional<std::vector<Clause>> {
        if (!form.valid_node(index)) {
            return std::nullopt;
        }
        const NormalizedConstraintNode& node = form.nodes[index];
        switch (node.kind) {
            case NormalizedConstraintKind::Atomic:
            case NormalizedConstraintKind::FoldExpanded:
                return std::vector<Clause>{Clause{index}};
            case NormalizedConstraintKind::ConceptDependent:
                return std::nullopt;
            case NormalizedConstraintKind::Conjunction: {
                auto lhs_clauses = dnf(form, node.lhs);
                auto rhs_clauses = dnf(form, node.rhs);
                if (!lhs_clauses.has_value() || !rhs_clauses.has_value()) {
                    return std::nullopt;
                }
                return combine_clauses(*lhs_clauses, *rhs_clauses);
            }
            case NormalizedConstraintKind::Disjunction: {
                auto lhs_clauses = dnf(form, node.lhs);
                auto rhs_clauses = dnf(form, node.rhs);
                if (!lhs_clauses.has_value() || !rhs_clauses.has_value()) {
                    return std::nullopt;
                }
                lhs_clauses->insert(lhs_clauses->end(),
                                    rhs_clauses->begin(),
                                    rhs_clauses->end());
                return lhs_clauses;
            }
        }
        return std::nullopt;
    };

    std::function<std::optional<std::vector<Clause>>(
        const NormalizedConstraint&,
        uint32_t)> cnf =
        [&](const NormalizedConstraint& form,
            uint32_t index) -> std::optional<std::vector<Clause>> {
        if (!form.valid_node(index)) {
            return std::nullopt;
        }
        const NormalizedConstraintNode& node = form.nodes[index];
        switch (node.kind) {
            case NormalizedConstraintKind::Atomic:
            case NormalizedConstraintKind::FoldExpanded:
                return std::vector<Clause>{Clause{index}};
            case NormalizedConstraintKind::ConceptDependent:
                return std::nullopt;
            case NormalizedConstraintKind::Conjunction: {
                auto lhs_clauses = cnf(form, node.lhs);
                auto rhs_clauses = cnf(form, node.rhs);
                if (!lhs_clauses.has_value() || !rhs_clauses.has_value()) {
                    return std::nullopt;
                }
                lhs_clauses->insert(lhs_clauses->end(),
                                    rhs_clauses->begin(),
                                    rhs_clauses->end());
                return lhs_clauses;
            }
            case NormalizedConstraintKind::Disjunction: {
                auto lhs_clauses = cnf(form, node.lhs);
                auto rhs_clauses = cnf(form, node.rhs);
                if (!lhs_clauses.has_value() || !rhs_clauses.has_value()) {
                    return std::nullopt;
                }
                return combine_clauses(*lhs_clauses, *rhs_clauses);
            }
        }
        return std::nullopt;
    };

    auto fold_expansion_parameters_compatible =
        [](const std::vector<ConstraintFoldExpansionParameter>& lhs_parameters,
           const std::vector<ConstraintFoldExpansionParameter>& rhs_parameters) {
        if (lhs_parameters.size() != rhs_parameters.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs_parameters.size(); ++i) {
            const ConstraintFoldExpansionParameter& lhs = lhs_parameters[i];
            const ConstraintFoldExpansionParameter& rhs = rhs_parameters[i];
            if (lhs.kind != rhs.kind) {
                return false;
            }
            if (lhs.kind ==
                    ConstraintFoldExpansionParameterKind::Template &&
                lhs.template_template_parameter_kind !=
                    rhs.template_template_parameter_kind) {
                return false;
            }
            bool lhs_has_slot =
                lhs.parameter_index != cir::ArrayTypePayload::no_extent_param;
            bool rhs_has_slot =
                rhs.parameter_index != cir::ArrayTypePayload::no_extent_param;
            if (lhs_has_slot || rhs_has_slot) {
                if (!lhs_has_slot || !rhs_has_slot ||
                    lhs.parameter_depth != rhs.parameter_depth ||
                    lhs.parameter_index != rhs.parameter_index) {
                    return false;
                }
                continue;
            }
            if (lhs.parameter_entity.valid() ||
                rhs.parameter_entity.valid()) {
                if (lhs.parameter_entity != rhs.parameter_entity) {
                    return false;
                }
                continue;
            }
            if (lhs.owning_template_entity.valid() ||
                rhs.owning_template_entity.valid()) {
                if (lhs.owning_template_entity !=
                    rhs.owning_template_entity) {
                    return false;
                }
                continue;
            }
            if (lhs.name != rhs.name) {
                return false;
            }
        }
        return true;
    };

    auto leaf_subsumes = [&](uint32_t lhs_leaf,
                             uint32_t rhs_leaf) -> bool {
        if (!lhs.valid_node(lhs_leaf) || !rhs.valid_node(rhs_leaf)) {
            return false;
        }
        const NormalizedConstraintNode& lhs_node = lhs.nodes[lhs_leaf];
        const NormalizedConstraintNode& rhs_node = rhs.nodes[rhs_leaf];
        if (lhs_node.kind == NormalizedConstraintKind::Atomic &&
            rhs_node.kind == NormalizedConstraintKind::Atomic) {
            return normalized_constraints_equivalent(lhs,
                                                     rhs,
                                                     lhs_leaf,
                                                     rhs_leaf);
        }
        if (lhs_node.kind == NormalizedConstraintKind::FoldExpanded &&
            rhs_node.kind == NormalizedConstraintKind::FoldExpanded) {
            return lhs_node.fold_operator == rhs_node.fold_operator &&
                   fold_expansion_parameters_compatible(
                       lhs_node.fold_expansion_parameters,
                       rhs_node.fold_expansion_parameters) &&
                   normalized_constraint_subsumes(lhs,
                                                  rhs,
                                                  lhs_node.lhs,
                                                  rhs_node.lhs);
        }
        return false;
    };

    auto lhs_dnf = dnf(lhs, lhs_index);
    auto rhs_cnf = cnf(rhs, rhs_index);
    if (!lhs_dnf.has_value() || !rhs_cnf.has_value()) {
        return false;
    }

    for (const Clause& disjunctive_clause : *lhs_dnf) {
        for (const Clause& conjunctive_clause : *rhs_cnf) {
            bool clause_subsumed = false;
            for (uint32_t lhs_leaf : disjunctive_clause) {
                for (uint32_t rhs_leaf : conjunctive_clause) {
                    if (leaf_subsumes(lhs_leaf, rhs_leaf)) {
                        clause_subsumed = true;
                        break;
                    }
                }
                if (clause_subsumed) {
                    break;
                }
            }
            if (!clause_subsumed) {
                return false;
            }
        }
    }
    return true;
}

bool Session::build_associated_constraint_normal_form(
    const std::vector<TemplateInfo::IntroducedConstraint>& constraints,
    std::optional<NormalizedConstraint>& form) const {
    form.reset();
    if (constraints.empty()) {
        return true;
    }

    std::vector<const TemplateInfo::IntroducedConstraint*> ordered;
    ordered.reserve(constraints.size());
    for (const TemplateInfo::IntroducedConstraint& constraint : constraints) {
        ordered.push_back(&constraint);
    }
    std::stable_sort(
        ordered.begin(),
        ordered.end(),
        [](const TemplateInfo::IntroducedConstraint* lhs,
           const TemplateInfo::IntroducedConstraint* rhs) {
            return TemplateInfo::associated_constraint_order_less(*lhs, *rhs);
        });

    NormalizedConstraint associated_form;
    uint32_t root = NormalizedConstraint::no_node;
    for (const TemplateInfo::IntroducedConstraint* constraint : ordered) {
        if (!constraint->normal_form.has_value()) {
            return false;
        }
        uint32_t copied_root =
            associated_form.append_copy_of(*constraint->normal_form);
        if (!associated_form.valid_node(copied_root)) {
            return false;
        }
        if (root == NormalizedConstraint::no_node) {
            root = copied_root;
        } else {
            root = associated_form.add_conjunction(root, copied_root);
        }
    }
    associated_form.root = root;
    form = std::move(associated_form);
    return true;
}

bool Session::associated_constraints_equivalent(
    const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
    const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const {
    std::optional<NormalizedConstraint> lhs_form;
    std::optional<NormalizedConstraint> rhs_form;
    if (!build_associated_constraint_normal_form(lhs, lhs_form) ||
        !build_associated_constraint_normal_form(rhs, rhs_form)) {
        return false;
    }
    if (lhs_form.has_value() != rhs_form.has_value()) {
        return false;
    }
    if (!lhs_form.has_value()) {
        return true;
    }
    if (!normalized_constraints_equivalent(*lhs_form,
                                           *rhs_form,
                                           NormalizedConstraint::no_node,
                                           NormalizedConstraint::no_node,
                                           /*declaration_equivalence=*/true)) {
        return false;
    }
    return true;
}

bool Session::associated_constraints_eligible_for_subsumption(
    const std::vector<TemplateInfo::IntroducedConstraint>& constraints) const {
    std::optional<NormalizedConstraint> form;
    if (!build_associated_constraint_normal_form(constraints, form)) {
        return false;
    }
    if (!form.has_value()) {
        return true;
    }
    return !normalized_constraint_contains_concept_dependent(*form);
}

bool Session::associated_constraints_subsume(
    const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
    const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const {
    std::optional<NormalizedConstraint> lhs_form;
    std::optional<NormalizedConstraint> rhs_form;
    if (!build_associated_constraint_normal_form(lhs, lhs_form) ||
        !build_associated_constraint_normal_form(rhs, rhs_form)) {
        return false;
    }
    if (!lhs_form.has_value() || !rhs_form.has_value()) {
        return false;
    }
    return normalized_constraint_subsumes(*lhs_form, *rhs_form);
}

bool Session::declaration_at_least_as_constrained(
    const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
    const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const {
    std::optional<NormalizedConstraint> lhs_form;
    std::optional<NormalizedConstraint> rhs_form;
    if (!build_associated_constraint_normal_form(lhs, lhs_form) ||
        !build_associated_constraint_normal_form(rhs, rhs_form)) {
        return false;
    }
    if (!rhs_form.has_value()) {
        return true;
    }
    if (!lhs_form.has_value()) {
        return false;
    }
    return !normalized_constraint_contains_concept_dependent(*lhs_form) &&
           normalized_constraint_subsumes(*lhs_form, *rhs_form);
}

bool Session::declaration_more_constrained(
    const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
    const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const {
    return declaration_at_least_as_constrained(lhs, rhs) &&
           !declaration_at_least_as_constrained(rhs, lhs);
}

uint64_t Session::normalized_constraint_fingerprint(
    const NormalizedConstraint& form) const {

    uint64_t hash = 1469598103934665603ull;
    auto mix = [&](uint64_t value) {
        hash ^= value;
        hash *= 1099511628211ull;
    };
    auto mix_entity = [&](cir::EntityId entity) {
        mix(entity.valid() ? static_cast<uint64_t>(entity.index) + 1 : 0);
        mix(entity.valid() ? entity.generation : 0);
    };
    auto mix_type = [&](cir::TypeRef type) {
        cir::TypeId resolved = file_.resolved_type(type.type);
        mix(resolved.valid() ? static_cast<uint64_t>(resolved.index) + 1 : 0);
        mix(resolved.valid() ? resolved.generation : 0);
        mix(type.qualifiers);
        mix(static_cast<uint64_t>(type.memory_space));
    };
    auto mix_argument = [&](const cir::TemplateArgument& argument) {
        mix(static_cast<uint64_t>(argument.kind));
        mix_type(argument.type);
        mix_type(argument.value_type);
        mix(argument.integer_value.low_bits);
        mix(argument.integer_value.high_bits);
        mix(argument.integer_value.bit_width);
        mix(argument.integer_value.is_unsigned);
        mix(static_cast<uint64_t>(argument.value_kind));
        mix(argument.value_param_index);
        mix_entity(argument.template_entity);
    };

    mix(form.root);
    mix(form.nodes.size());
    for (const NormalizedConstraintNode& node : form.nodes) {
        mix(static_cast<uint64_t>(node.kind));
        mix(node.lhs);
        mix(node.rhs);
        mix_entity(node.atom.appearance_owner);
        mix(node.atom.expression_begin);
        mix(node.atom.expression_end);
        mix(node.atom.parameter_mapping.size());
        for (const ConstraintParameterMapping& mapping :
             node.atom.parameter_mapping) {
            mix(static_cast<uint64_t>(mapping.parameter_kind));
            mix(mapping.parameter_depth);
            mix(mapping.parameter_index);
            mix_entity(mapping.parameter_entity);
            mix(static_cast<uint64_t>(
                mapping.parameter_template_template_kind));
            mix(mapping.parameter_is_pack);
            mix_argument(mapping.argument);
            if (mapping.argument_pack.has_value()) {
                mix(mapping.argument_pack->size() + 1);
                for (const cir::TemplateArgument& argument :
                     *mapping.argument_pack) {
                    mix_argument(argument);
                }
            } else {
                mix(0);
            }
        }
        mix_entity(node.concept_id_entity);
        mix(node.concept_id_template_parameter_index);
        mix_type(node.concept_id_dependent_qualifier);
        mix(node.concept_id_name.valid()
                ? static_cast<uint64_t>(node.concept_id_name.index) + 1
                : 0);
        mix(node.concept_id_qualified_name);
        mix(node.concept_id_arguments.size());
        for (const cir::TemplateArgument& argument :
             node.concept_id_arguments) {
            mix_argument(argument);
        }
        mix(static_cast<uint64_t>(node.fold_operator));
    }
    return hash == 0 ? 1 : hash;
}

bool Session::template_parameter_lists_match(
    const std::vector<TemplateParameter>& lhs,
    const std::vector<TemplateParameter>& rhs) const {
    PatternBindings empty_outer_bindings;
    std::function<bool(
        const std::vector<TemplateParameter>&,
        const std::vector<TemplateParameter>&,
        std::vector<std::pair<cir::TypeId, cir::TypeId>>)> match =
        [&](const std::vector<TemplateParameter>& left,
            const std::vector<TemplateParameter>& right,
            std::vector<std::pair<cir::TypeId, cir::TypeId>> type_map) {
            if (left.size() != right.size()) {
                return false;
            }
            for (size_t i = 0; i < left.size(); ++i) {
                const TemplateParameter& a = left[i];
                const TemplateParameter& b = right[i];
                if (a.kind != b.kind ||
                    a.is_parameter_pack != b.is_parameter_pack) {
                    return false;
                }
                if (a.kind == TemplateParameterKind::Type) {
                    if (!a.type_param_type.valid() ||
                        !b.type_param_type.valid()) {
                        return false;
                    }
                    type_map.push_back(
                        {a.type_param_type, b.type_param_type});
                    continue;
                }
                if (a.kind == TemplateParameterKind::NonType) {
                    std::vector<std::pair<cir::TypeId, cir::TypeId>> reverse;
                    reverse.reserve(type_map.size());
                    for (const auto& [from, to] : type_map) {
                        reverse.push_back({to, from});
                    }
                    if (!dependent_member_friend_template_type_corresponds(
                            a.non_type_type,
                            b.non_type_type,
                            empty_outer_bindings,
                            type_map,
                            DependentTypeCorrespondenceMode::
                                CompareDeclarations) ||
                        !dependent_member_friend_template_type_corresponds(
                            b.non_type_type,
                            a.non_type_type,
                            empty_outer_bindings,
                            reverse,
                            DependentTypeCorrespondenceMode::
                                CompareDeclarations)) {
                        return false;
                    }
                    continue;
                }
                if (a.template_template_parameter_kind !=
                    b.template_template_parameter_kind) {
                    return false;
                }
                if (!match(a.nested_parameters(),
                           b.nested_parameters(),
                           type_map)) {
                    return false;
                }
                if (a.nested_head && b.nested_head &&
                    !associated_constraints_equivalent(
                        a.nested_head->introduced_constraints,
                        b.nested_head->introduced_constraints)) {
                    return false;
                }
            }
            return true;
        };
    return match(lhs, rhs, {});
}

bool Session::template_heads_equivalent(const TemplateInfo& lhs,
                                        const TemplateInfo& rhs) const {
    return template_parameter_lists_match(lhs.parameters, rhs.parameters) &&
           associated_constraints_equivalent(lhs.introduced_constraints,
                                             rhs.introduced_constraints);
}

std::vector<size_t>
Session::inherit_prior_class_template_defaults_for_validation(
    TemplateInfo& info) const {
    std::vector<size_t> inherited;
    if (!info.is_class_template || info.is_partial_specialization ||
        info.name.empty()) {
        return inherited;
    }

    cir::DeclContextId context = info.lexical_context.valid()
        ? info.lexical_context
        : current_decl_context();
    const TemplateInfo* previous = nullptr;
    const cir::Binding* binding = file_.lookup_template_name_binding(
        context, info.name, /*include_parents=*/false);
    if (binding) {
        for (auto it = binding->entities.rbegin();
             it != binding->entities.rend();
             ++it) {
            const TemplateInfo* candidate = template_info(*it);
            if (!candidate || !candidate->is_class_template ||
                candidate->is_partial_specialization ||
                !template_heads_equivalent(*candidate, info)) {
                continue;
            }
            previous = candidate;
            break;
        }
    }
    if (!previous) {
        cir::EntityId hidden = hidden_friend_class_template_entity(
            info.name,
            info.parameters,
            info.introduced_constraints,
            context);
        previous = hidden.valid() ? template_info(hidden) : nullptr;
    }
    if (!previous) {
        return inherited;
    }

    size_t count = std::min(info.parameters.size(),
                            previous->parameters.size());
    for (size_t i = 0; i < count; ++i) {
        if (info.parameters[i].default_argument.has_value() ||
            !previous->parameters[i].default_argument.has_value()) {
            continue;
        }
        info.parameters[i].default_argument =
            previous->parameters[i].default_argument;
        inherited.push_back(i);
    }
    return inherited;
}

bool Session::function_template_declarations_correspond(
    const TemplateInfo& lhs,
    const TemplateInfo& rhs) const {
    if (!template_heads_equivalent(lhs, rhs) ||
        !lhs.pattern_type.valid() || !rhs.pattern_type.valid()) {
        return false;
    }
    if (lhs.operator_function.kind != rhs.operator_function.kind ||
        lhs.operator_function.spelling != rhs.operator_function.spelling ||
        lhs.operator_function.literal_suffix !=
            rhs.operator_function.literal_suffix) {
        return false;
    }

    return function_template_declarations_correspond(
        lhs.parameters,
        lhs.pattern_type,
        rhs.parameters,
        rhs.pattern_type);
}

bool Session::function_template_declarations_correspond(
    const std::vector<TemplateParameter>& lhs_parameters,
    cir::TypeId lhs_pattern_type,
    const std::vector<TemplateParameter>& rhs_parameters,
    cir::TypeId rhs_pattern_type) const {
    if (!template_parameter_lists_match(lhs_parameters, rhs_parameters) ||
        !lhs_pattern_type.valid() || !rhs_pattern_type.valid()) {
        return false;
    }
    std::vector<std::pair<cir::TypeId, cir::TypeId>> lhs_to_rhs_type_params;
    std::vector<std::pair<cir::TypeId, cir::TypeId>> rhs_to_lhs_type_params;
    lhs_to_rhs_type_params.reserve(lhs_parameters.size());
    rhs_to_lhs_type_params.reserve(rhs_parameters.size());
    for (size_t i = 0; i < lhs_parameters.size(); ++i) {
        const TemplateParameter& lhs_parameter = lhs_parameters[i];
        const TemplateParameter& rhs_parameter = rhs_parameters[i];
        if (lhs_parameter.kind != TemplateParameterKind::Type) {
            continue;
        }
        if (!lhs_parameter.type_param_type.valid() ||
            !rhs_parameter.type_param_type.valid()) {
            return false;
        }
        lhs_to_rhs_type_params.push_back({lhs_parameter.type_param_type,
                                          rhs_parameter.type_param_type});
        rhs_to_lhs_type_params.push_back({rhs_parameter.type_param_type,
                                          lhs_parameter.type_param_type});
    }

    auto corresponds = [&](cir::TypeId pattern_type,
                           cir::TypeId actual_type,
                           const std::vector<
                               std::pair<cir::TypeId, cir::TypeId>>& type_map) {
        cir::TypeId pattern = file_.resolved_type(pattern_type);
        cir::TypeId actual = file_.resolved_type(actual_type);
        if (!file_.valid(pattern) || !file_.valid(actual) ||
            file_.type(pattern).kind != cir::TypeKind::Function ||
            file_.type(actual).kind != cir::TypeKind::Function) {
            return false;
        }
        const auto* pattern_function =
            std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(pattern));
        const auto* actual_function =
            std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(actual));
        if (!pattern_function || !actual_function ||
            pattern_function->parameters.size() !=
                actual_function->parameters.size() ||
            pattern_function->is_variadic != actual_function->is_variadic ||
            pattern_function->has_prototype !=
                actual_function->has_prototype ||
            pattern_function->member_ref_qualifier !=
                actual_function->member_ref_qualifier ||
            pattern_function->member_is_const !=
                actual_function->member_is_const ||
            pattern_function->member_is_volatile !=
                actual_function->member_is_volatile ||
            pattern_function->calling_convention !=
                actual_function->calling_convention) {
            return false;
        }
        PatternBindings empty_outer_bindings;
        auto refs_correspond = [&](cir::TypeRef pattern_ref,
                                   cir::TypeRef actual_ref) {
            return pattern_ref.qualifiers == actual_ref.qualifiers &&
                   pattern_ref.memory_space == actual_ref.memory_space &&
                   dependent_member_friend_template_type_corresponds(
                       pattern_ref.type,
                       actual_ref.type,
                       empty_outer_bindings,
                       type_map,
                       DependentTypeCorrespondenceMode::
                           CompareDeclarations);
        };
        if (!refs_correspond(pattern_function->return_type,
                             actual_function->return_type)) {
            return false;
        }
        for (size_t i = 0; i < pattern_function->parameters.size(); ++i) {
            if (!refs_correspond(pattern_function->parameters[i],
                                 actual_function->parameters[i])) {
                return false;
            }
        }
        return true;
    };
    return corresponds(lhs_pattern_type,
                       rhs_pattern_type,
                       lhs_to_rhs_type_params) &&
           corresponds(rhs_pattern_type,
                       lhs_pattern_type,
                       rhs_to_lhs_type_params);
}

cir::EntityId Session::hidden_friend_class_template_entity(
    std::string_view name,
    const std::vector<TemplateParameter>& parameters,
    const std::vector<TemplateInfo::IntroducedConstraint>&
        introduced_constraints,
    cir::DeclContextId context) const {
    if (name.empty() || !context.valid()) {
        return {};
    }
    for (const TemplateState::FriendClassTemplateIdentity& identity :
         tstate().hidden_friend_class_template_identities_) {
        auto found = tstate().templates_.find(static_cast<uint64_t>(
            identity.entity.index));
        if (identity.context == context && identity.name == name &&
            identity.entity.valid() && file_.valid(identity.entity) &&
            found != tstate().templates_.end() &&
            template_parameter_lists_match(found->second.parameters,
                                           parameters) &&
            associated_constraints_equivalent(
                found->second.introduced_constraints,
                introduced_constraints)) {
            return identity.entity;
        }
    }
    return {};
}

cir::EntityId Session::hidden_friend_function_template_entity(
    std::string_view name,
    const std::vector<TemplateParameter>& parameters,
    cir::TypeId pattern_type,
    const std::vector<TemplateInfo::IntroducedConstraint>&
        introduced_constraints,
    cir::DeclContextId context,
    cir::ModuleAttachmentId module_attachment,
    cir::EntityId signature_owner) const {
    if (name.empty() || !pattern_type.valid() || !context.valid()) {
        return {};
    }
    for (const TemplateState::FriendFunctionTemplateIdentity& identity :
         tstate().hidden_friend_function_template_identities_) {
        if (identity.context != context || identity.name != name ||
            identity.module_attachment != module_attachment ||
            identity.signature_owner != signature_owner ||
            !identity.entity.valid() || !file_.valid(identity.entity)) {
            continue;
        }
        auto found = tstate().templates_.find(static_cast<uint64_t>(
            identity.entity.index));
        if (found != tstate().templates_.end() &&
            function_template_declarations_correspond(
                found->second.parameters,
                found->second.pattern_type,
                parameters,
                pattern_type) &&
            associated_constraints_equivalent(
                found->second.introduced_constraints,
                introduced_constraints)) {
            return identity.entity;
        }
    }
    return {};
}

cir::EntityId Session::declare_hidden_friend_class_template(
    TemplateInfo info,
    cir::DeclContextId context,
    SrcLoc loc) {
    if (info.name.empty() || !context.valid()) {
        return {};
    }
    info.is_class_template = true;
    info.is_alias_template = false;
    info.is_variable_template = false;
    info.is_partial_specialization = false;
    info.has_definition = false;
    if (cir::EntityId existing = hidden_friend_class_template_entity(
            info.name,
            info.parameters,
            info.introduced_constraints,
            context);
        existing.valid()) {
        return existing;
    }

    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Record,
                                               info.name,
                                               {},
                                               {},
                                               loc);
    file_.entity_mut(entity).is_definition = false;
    file_.entity_mut(entity).lexical_context = context;
    file_.entity_mut(entity).semantic_context = context;
    info.entity = entity;
    info.lexical_context = context;

    uint64_t key = static_cast<uint64_t>(entity.index);
    auto inserted = tstate().templates_.emplace(key, info);
    if (!inserted.second) {
        return inserted.first->second.entity;
    }
    TemplateState::FriendClassTemplateIdentity identity;
    identity.name = info.name;
    identity.context = context;
    identity.entity = entity;
    identity.parameters = info.parameters;
    tstate().hidden_friend_class_template_identities_.push_back(std::move(identity));
    note_constraint_environment_change();
    track_speculative_rollback([this, key, entity] {
        erase_template_info(key);
        auto found = std::find_if(
            tstate().hidden_friend_class_template_identities_.begin(),
            tstate().hidden_friend_class_template_identities_.end(),
            [entity](const TemplateState::FriendClassTemplateIdentity& identity) {
                return identity.entity == entity;
            });
        if (found != tstate().hidden_friend_class_template_identities_.end()) {
            tstate().hidden_friend_class_template_identities_.erase(found);
        }
    });
    return entity;
}

cir::EntityId Session::declare_hidden_friend_function_template(
    TemplateInfo info,
    cir::DeclContextId context,
    SrcLoc loc,
    const std::vector<ParamInput>* params,
    cir::EntityId granting_record,
    cir::EntityId signature_owner) {
    if (info.name.empty() || !info.pattern_type.valid() || !context.valid()) {
        return {};
    }
    cir::OperatorFunctionIdentity operator_function =
        info.operator_function;
    info.is_class_template = false;
    info.is_alias_template = false;
    info.is_variable_template = false;
    info.hidden_friend_definition_is_pattern =
        info.has_definition && collecting_pattern_;
    cir::ModuleAttachmentId module_attachment{};
    if (granting_record.valid() && file_.valid(granting_record)) {
        module_attachment = file_.entity(granting_record).module_attachment;
        cir::DeclContextId record_context =
            file_.entity(granting_record).semantic_context;
        if (record_context.valid()) {

            info.lexical_context = record_context;
        }
    }
    if (!info.lexical_context.valid()) {
        info.lexical_context = context;
    }
    if (cir::EntityId existing = hidden_friend_function_template_entity(
            info.name,
            info.parameters,
            info.pattern_type,
            info.introduced_constraints,
            context,
            module_attachment,
            signature_owner);
        existing.valid()) {
        auto found = tstate().templates_.find(static_cast<uint64_t>(existing.index));
        if (found != tstate().templates_.end() && info.has_definition) {
            if (found->second.has_definition) {
                if (found->second.hidden_friend_definition_is_pattern &&
                    !info.hidden_friend_definition_is_pattern) {

                    uint64_t key = static_cast<uint64_t>(existing.index);
                    TemplateInfo previous_snapshot = found->second;
                    track_speculative_rollback(
                        [this, key, previous_snapshot] {
                            restore_template_info(key, previous_snapshot);
                        });
                    cir::EntityId entity = found->second.entity;
                    cir::TypeId pattern_type =
                        found->second.pattern_type.valid()
                            ? found->second.pattern_type
                            : info.pattern_type;
                    info.entity = entity;
                    info.pattern_type = pattern_type;
                    found->second = std::move(info);
                    note_constraint_environment_change();
                } else {
                    report_error("redefinition of template '" + info.name +
                                     "'",
                                 loc);
                }
            } else {
                uint64_t key = static_cast<uint64_t>(existing.index);
                TemplateInfo previous_snapshot = found->second;
                track_speculative_rollback(
                    [this, key, previous_snapshot] {
                        restore_template_info(key, previous_snapshot);
                    });
                cir::EntityId entity = found->second.entity;
                cir::TypeId pattern_type = found->second.pattern_type.valid()
                    ? found->second.pattern_type
                    : info.pattern_type;
                info.entity = entity;
                info.pattern_type = pattern_type;
                found->second = std::move(info);
                note_constraint_environment_change();
            }
        }
        if (params) {
            register_function_default_arguments(existing, *params, nullptr,
                                                loc);
        }
        if (operator_function.valid()) {
            file_.entity_mut(existing).operator_function =
                operator_function;
        }
        return existing;
    }

    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Function,
                                               info.name,
                                               {},
                                               {},
                                               loc);
    file_.entity_mut(entity).operator_function = operator_function;
    file_.entity_mut(entity).is_definition = false;
    file_.entity_mut(entity).lexical_context = info.lexical_context;
    file_.entity_mut(entity).semantic_context = context;
    file_.entity_mut(entity).module_attachment = module_attachment;
    info.entity = entity;

    uint64_t key = static_cast<uint64_t>(entity.index);
    auto inserted = tstate().templates_.emplace(key, info);
    if (!inserted.second) {
        return inserted.first->second.entity;
    }
    if (params) {
        register_function_default_arguments(entity, *params, nullptr, loc);
    }
    TemplateState::FriendFunctionTemplateIdentity identity;
    identity.name = info.name;
    identity.context = context;
    identity.module_attachment = module_attachment;
    identity.signature_owner = signature_owner;
    identity.entity = entity;
    identity.parameters = info.parameters;
    identity.pattern_type = info.pattern_type;
    tstate().hidden_friend_function_template_identities_.push_back(
        std::move(identity));
    note_constraint_environment_change();
    track_speculative_rollback([this, key, entity] {
        erase_template_info(key);
        auto found = std::find_if(
            tstate().hidden_friend_function_template_identities_.begin(),
            tstate().hidden_friend_function_template_identities_.end(),
            [entity](const TemplateState::FriendFunctionTemplateIdentity& identity) {
                return identity.entity == entity;
            });
        if (found != tstate().hidden_friend_function_template_identities_.end()) {
            tstate().hidden_friend_function_template_identities_.erase(found);
        }
    });
    return entity;
}

bool Session::is_hidden_friend_function_template(cir::EntityId entity) const {
    if (!entity.valid()) {
        return false;
    }
    return std::any_of(
        tstate().hidden_friend_function_template_identities_.begin(),
        tstate().hidden_friend_function_template_identities_.end(),
        [entity](const TemplateState::FriendFunctionTemplateIdentity& identity) {
            return identity.entity == entity;
        });
}

void Session::populate_enclosing_instantiation_bindings(TemplateInfo& info) {
    if (info.enclosing_instantiation_bindings.empty()) {
        for (const TemplateState::CurrentInstantiationFrame& frame :
             tstate().current_instantiation_frames_) {
            if (!frame.info || frame.memo_key.empty()) {
                continue;
            }
            info.enclosing_instantiation_bindings.insert(
                info.enclosing_instantiation_bindings.end(),
                frame.info->enclosing_instantiation_bindings.begin(),
                frame.info->enclosing_instantiation_bindings.end());
            if (!frame.info->parameters.empty()) {
                info.enclosing_instantiation_bindings.push_back(
                    TemplateInfo::TemplateInstantiationBinding{
                        frame.info->parameters,
                        frame.argument_bindings});
            }
        }
    }
}

cir::EntityId Session::declare_template(TemplateInfo info, SrcLoc loc) {
    info.lexical_context = current_decl_context();
    populate_enclosing_instantiation_bindings(info);
    if (info.is_variable_template && !info.variable_type_ref.valid() &&
        info.variable_type.valid()) {
        info.variable_type_ref = type_ref(info.variable_type);
    }
    for (const TemplateParameter& parameter : info.parameters) {
        if (!parameter.name.empty() && parameter.name == info.name) {
            SrcLoc diagnostic_loc = parameter.loc.isInvalid()
                ? loc
                : parameter.loc;
            report_error("template declaration name shadows template parameter",
                         diagnostic_loc);
            break;
        }
    }

    auto validate_parameter_pack_position =
        [&](const TemplateInfo& candidate) {
        bool is_function_template =
            !candidate.is_class_template &&
            !candidate.is_variable_template &&
            !candidate.is_alias_template &&
            !candidate.is_concept && candidate.pattern_type.valid() &&
            file_.valid(file_.resolved_type(candidate.pattern_type)) &&
            file_.type(file_.resolved_type(candidate.pattern_type)).kind ==
                cir::TypeKind::Function;
        for (size_t i = 0; i < candidate.parameters.size(); ++i) {
            const TemplateParameter& pack = candidate.parameters[i];
            if (!pack.is_parameter_pack ||
                i + 1 == candidate.parameters.size()) {
                continue;
            }
            if (!is_function_template) {

                if (candidate.is_partial_specialization) {
                    continue;
                }
                report_error(
                    "template parameter pack must be the last template parameter",
                    pack.loc.isInvalid() ? loc : pack.loc);
                return;
            }
            for (size_t j = i + 1; j < candidate.parameters.size(); ++j) {
                const TemplateParameter& trailing = candidate.parameters[j];
                if (trailing.default_argument.has_value() ||
                    template_parameter_is_deducible_from_function_parameter_types(
                        trailing,
                        candidate.pattern_type)) {
                    continue;
                }
                report_error(
                    "template parameter following a function template parameter pack must be deducible from the function parameter-type-list or have a default argument",
                    trailing.loc.isInvalid() ? loc : trailing.loc);
                return;
            }
        }
    };
    auto parameters_match =
        [&](const TemplateInfo& lhs, const TemplateInfo& rhs) {
            return template_heads_equivalent(lhs, rhs);
        };

    auto merge_default_arguments =
        [&](TemplateInfo& target, const TemplateInfo& previous) {
        size_t count = std::min(target.parameters.size(),
                                previous.parameters.size());
        for (size_t i = 0; i < count; ++i) {
            bool has_current =
                target.parameters[i].default_argument.has_value();
            bool has_previous =
                previous.parameters[i].default_argument.has_value();
            if (has_current && has_previous) {
                SrcLoc default_loc = target.parameters[i].loc.isInvalid()
                    ? loc
                    : target.parameters[i].loc;
                report_error("repeated default template argument",
                             default_loc);
            } else if (!has_current && has_previous) {
                target.parameters[i].default_argument =
                    previous.parameters[i].default_argument;
            }
        }
    };

    auto validate_primary_default_order = [&](const TemplateInfo& candidate) {
        if (!candidate.is_class_template &&
            !candidate.is_variable_template &&
            !candidate.is_alias_template &&
            !candidate.is_concept) {
            return;
        }
        bool saw_default = false;
        for (const TemplateParameter& parameter : candidate.parameters) {
            if (parameter.is_parameter_pack) {
                continue;
            }
            if (parameter.default_argument.has_value()) {
                saw_default = true;
                continue;
            }
            if (saw_default) {
                SrcLoc diagnostic_loc = parameter.loc.isInvalid()
                    ? loc
                    : parameter.loc;
                report_error(
                    "template parameter without a default argument follows "
                    "a parameter with a default template argument",
                    diagnostic_loc);
                return;
            }
        }
    };

    auto primary_redeclarations_merge = [](const TemplateInfo& candidate) {
        return candidate.is_class_template || candidate.is_variable_template ||
               candidate.is_concept;
    };
    auto same_primary_family = [](const TemplateInfo& lhs,
                                  const TemplateInfo& rhs) {
        return lhs.is_class_template == rhs.is_class_template &&
               lhs.is_variable_template == rhs.is_variable_template &&
               lhs.is_alias_template == rhs.is_alias_template &&
               lhs.is_concept == rhs.is_concept;
    };

    if (primary_redeclarations_merge(info)) {
        TemplateInfo* previous = nullptr;
        TemplateInfo* conflicting_constraints_previous = nullptr;
        TemplateInfo* incompatible_previous = nullptr;
        bool previous_was_hidden_friend = false;
        const cir::Binding* binding = file_.lookup_template_name_binding(
            current_decl_context(),
            info.name,
            /*include_parents=*/false);
        if (binding) {
            for (auto it = binding->entities.rbegin();
                 it != binding->entities.rend();
                 ++it) {
                auto found =
                    tstate().templates_.find(static_cast<uint64_t>(it->index));
                if (found == tstate().templates_.end() ||
                    !primary_redeclarations_merge(found->second) ||
                    !same_primary_family(found->second, info)) {
                    continue;
                }
                if (parameters_match(found->second, info)) {
                    previous = &found->second;
                    break;
                }
                if (template_parameter_lists_match(found->second.parameters,
                                                   info.parameters) &&
                    !associated_constraints_equivalent(
                        found->second.introduced_constraints,
                        info.introduced_constraints)) {
                    if (!conflicting_constraints_previous) {
                        conflicting_constraints_previous = &found->second;
                    }
                } else if ((info.is_variable_template || info.is_concept) &&
                           !incompatible_previous) {
                    incompatible_previous = &found->second;
                }
            }
        }
        if (!previous && info.is_class_template &&
            !info.is_partial_specialization) {
            cir::EntityId hidden = hidden_friend_class_template_entity(
                info.name,
                info.parameters,
                info.introduced_constraints,
                current_decl_context());
            if (hidden.valid()) {
                auto found =
                    tstate().templates_.find(static_cast<uint64_t>(hidden.index));
                if (found != tstate().templates_.end() &&
                    found->second.is_class_template &&
                    !found->second.is_partial_specialization) {
                    previous = &found->second;
                    previous_was_hidden_friend = true;
                }
            }
        }
        if (!previous && conflicting_constraints_previous) {
            report_error("conflicting associated constraints for template '" +
                             info.name + "'",
                         loc);
            return conflicting_constraints_previous->entity;
        }
        if (!previous && incompatible_previous) {
            report_error("conflicting template parameter list for " +
                             std::string(info.is_concept ? "concept '"
                                                         : "variable template '") +
                             info.name + "'",
                         loc);
            return incompatible_previous->entity;
        }
        if (previous) {
            uint64_t key = static_cast<uint64_t>(previous->entity.index);
            TemplateInfo previous_snapshot = *previous;
            track_speculative_rollback(
                [this, key, previous_snapshot] {
                    restore_template_info(key, previous_snapshot);
                });

            merge_default_arguments(info, *previous);
            validate_parameter_pack_position(info);
            validate_primary_default_order(info);

            if (info.is_variable_template &&
                !types_compatible(previous->variable_type_ref,
                                  info.variable_type_ref)) {
                report_error("conflicting type for variable template '" +
                                 info.name + "'",
                             loc);
                return previous->entity;
            }

            bool replacing_inherited =
                info.is_member_template_specialization_overlay &&
                !previous->is_member_template_specialization_overlay;
            if (replacing_inherited) {
                SrcLoc first_required =
                    first_implicit_template_specialization(previous->entity);
                if (!first_required.isInvalid()) {
                    report_error(
                        "explicit specialization of member template after implicit instantiation",
                        loc);
                    report_error("implicit instantiation first required here",
                                 first_required);
                    return previous->entity;
                }
            }

            if (previous->has_definition && info.has_definition &&
                !replacing_inherited) {
                report_error("redefinition of template '" + info.name + "'",
                             loc);
                return previous->entity;
            }

            if (previous->is_member_template_specialization_overlay &&
                previous->has_definition && !info.has_definition) {
                return previous->entity;
            }

            if (info.has_definition || replacing_inherited) {
                cir::EntityId entity = previous->entity;
                cir::DeclContextId lexical_context =
                    previous->lexical_context;
                std::vector<TemplateInfo::OutOfLineMember> out_of_line_members =
                    replacing_inherited
                        ? std::vector<TemplateInfo::OutOfLineMember>{}
                        : previous->out_of_line_members;
                std::vector<TemplateInfo::DeductionGuide> deduction_guides =
                    replacing_inherited
                        ? std::vector<TemplateInfo::DeductionGuide>{}
                        : previous->deduction_guides;
                std::vector<TemplateInfo::PartialSpecialization>
                    partial_specializations;
                for (const TemplateInfo::PartialSpecialization& entry :
                     previous->partial_specializations) {
                    const TemplateInfo* partial = template_info(entry.entity);
                    if (!replacing_inherited ||
                        (partial &&
                         partial->is_member_template_specialization_overlay)) {
                        partial_specializations.push_back(entry);
                    }
                }
                std::vector<TemplateInfo::TemplateInstantiationBinding>
                    enclosing_bindings =
                        previous->enclosing_instantiation_bindings;
                info.entity = entity;
                info.lexical_context = lexical_context;
                if (info.enclosing_instantiation_bindings.empty()) {
                    info.enclosing_instantiation_bindings =
                        std::move(enclosing_bindings);
                }
                if (!out_of_line_members.empty()) {
                    info.out_of_line_members.insert(
                        info.out_of_line_members.begin(),
                        out_of_line_members.begin(),
                        out_of_line_members.end());
                }
                if (!deduction_guides.empty()) {
                    info.deduction_guides.insert(
                        info.deduction_guides.begin(),
                        deduction_guides.begin(),
                        deduction_guides.end());
                }
                if (!partial_specializations.empty()) {
                    info.partial_specializations.insert(
                        info.partial_specializations.begin(),
                        partial_specializations.begin(),
                        partial_specializations.end());
                }
                erase_template_pattern_record(*previous);
                *previous = std::move(info);
                index_template_pattern_record(*previous);
                if (previous_was_hidden_friend) {
                    bind_entity(previous->name,
                                cir::LookupNamespace::Ordinary,
                                previous->entity,
                                {},
                                false,
                                /*is_template_name=*/true,
                                previous->has_definition,
                                {},
                                loc);
                }
                note_constraint_environment_change();
                return entity;
            }

            previous->parameters = std::move(info.parameters);
            previous->param_types = std::move(info.param_types);
            if (previous_was_hidden_friend) {
                previous->has_definition = previous->has_definition ||
                    info.has_definition;
                bind_entity(previous->name,
                            cir::LookupNamespace::Ordinary,
                            previous->entity,
                            {},
                            false,
                            /*is_template_name=*/true,
                            previous->has_definition,
                            {},
                            loc);
            }
            note_constraint_environment_change();
            return previous->entity;
        }
    }

    if (!info.is_class_template && !info.is_alias_template &&
        !info.is_variable_template && !info.is_concept &&
        info.pattern_type.valid()) {
        cir::EntityId hidden = hidden_friend_function_template_entity(
            info.name,
            info.parameters,
            info.pattern_type,
            info.introduced_constraints,
            current_decl_context());
        if (hidden.valid()) {
            auto found = tstate().templates_.find(static_cast<uint64_t>(hidden.index));
            if (found != tstate().templates_.end() &&
                !found->second.is_class_template &&
                !found->second.is_alias_template &&
                !found->second.is_variable_template &&
                !found->second.is_concept) {
                TemplateInfo& previous = found->second;
                if (!function_exception_specs_structurally_equivalent(
                        file_, previous.pattern_type, info.pattern_type)) {
                    report_error(
                        "exception specification of function template '" +
                            info.name +
                            "' does not match the previous declaration",
                        loc);
                    return previous.entity;
                }
                uint64_t key = static_cast<uint64_t>(previous.entity.index);
                TemplateInfo previous_snapshot = previous;
                track_speculative_rollback(
                    [this, key, previous_snapshot] {
                        restore_template_info(key, previous_snapshot);
                    });

                merge_default_arguments(info, previous);
                validate_parameter_pack_position(info);
                AttributeList written_declaration_attrs =
                    info.declaration_attrs;
                if (info.is_deleted) {
                    report_error("deleted definition of function template '" +
                                     info.name +
                                     "' must be the first declaration",
                                 loc);
                    report_note("previous declaration is here",
                                file_.entity(previous.entity).loc);
                    return previous.entity;
                }
                if (previous.has_definition && info.has_definition) {
                    report_error("redefinition of template '" + info.name + "'",
                                 loc);
                    return previous.entity;
                }

                cir::EntityId entity = previous.entity;
                apply_attributes(entity,
                                 AttributeTarget::Function,
                                 written_declaration_attrs,
                                 loc);
                cir::DeclContextId lexical_context =
                    previous.lexical_context.valid()
                        ? previous.lexical_context
                        : current_decl_context();
                if (info.has_definition) {
                    AttributeList merged_attrs =
                        previous.declaration_attrs;
                    merged_attrs.append(std::move(info.declaration_attrs));
                    info.declaration_attrs = std::move(merged_attrs);
                    info.entity = entity;
                    info.lexical_context = lexical_context;
                    info.pattern_type = previous.pattern_type.valid()
                        ? previous.pattern_type
                        : info.pattern_type;
                    previous = std::move(info);
                } else {
                    previous.declaration_attrs.append(
                        std::move(info.declaration_attrs));
                    previous.parameters = std::move(info.parameters);
                    previous.param_types = std::move(info.param_types);
                    previous.has_definition = previous.has_definition ||
                        info.has_definition;
                }
                note_constraint_environment_change();
                if (const cir::Binding* binding =
                        file_.lookup_callable_binding(current_decl_context(),
                                                      previous.name,
                                                      /*include_parents=*/false);
                    binding) {
                    bool already_bound = std::find(binding->entities.begin(),
                                                   binding->entities.end(),
                                                   entity) !=
                        binding->entities.end();
                    if (already_bound) {
                        refresh_callable_binding(previous.name,
                                                 entity,
                                                 {},
                                                 previous.has_definition,
                                                 loc);
                    } else {
                        bind_callable(previous.name,
                                      entity,
                                      {},
                                      previous.has_definition,
                                      loc);
                    }
                } else {
                    bind_callable(previous.name,
                                  entity,
                                  {},
                                  previous.has_definition,
                                  loc);
                }
                return entity;
            }
        }
    }

    if (!info.is_class_template && !info.is_alias_template &&
        !info.is_variable_template && !info.is_concept &&
        info.pattern_type.valid()) {
        TemplateInfo* previous = nullptr;
        const cir::Binding* binding = file_.lookup_callable_binding(
            current_decl_context(),
            info.name,
            /*include_parents=*/false);
        if (binding) {
            for (auto it = binding->entities.rbegin();
                 it != binding->entities.rend();
                 ++it) {
                auto found =
                    tstate().templates_.find(static_cast<uint64_t>(it->index));
                if (found == tstate().templates_.end() ||
                    found->second.is_class_template ||
                    found->second.is_alias_template ||
                    found->second.is_variable_template ||
                    found->second.is_concept) {
                    continue;
                }
                if (function_template_declarations_correspond(found->second,
                                                              info)) {
                    previous = &found->second;
                    break;
                }
            }
        }
        if (previous) {
            if (!function_exception_specs_structurally_equivalent(
                    file_, previous->pattern_type, info.pattern_type)) {
                report_error(
                    "exception specification of function template '" +
                        info.name +
                        "' does not match the previous declaration",
                    loc);
                return previous->entity;
            }
            uint64_t key = static_cast<uint64_t>(previous->entity.index);
            TemplateInfo previous_snapshot = *previous;
            track_speculative_rollback(
                [this, key, previous_snapshot] {
                    restore_template_info(key, previous_snapshot);
                });

            merge_default_arguments(info, *previous);
            validate_parameter_pack_position(info);
            AttributeList written_declaration_attrs =
                info.declaration_attrs;
            if (info.is_deleted) {
                report_error("deleted definition of function template '" +
                                 info.name +
                                 "' must be the first declaration",
                             loc);
                report_note("previous declaration is here",
                            file_.entity(previous->entity).loc);
                return previous->entity;
            }
            if (previous->has_definition && info.has_definition) {
                report_error("redefinition of template '" + info.name + "'",
                             loc);
                return previous->entity;
            }

            cir::EntityId entity = previous->entity;
            apply_attributes(entity,
                             AttributeTarget::Function,
                             written_declaration_attrs,
                             loc);
            cir::DeclContextId lexical_context =
                previous->lexical_context.valid()
                    ? previous->lexical_context
                    : current_decl_context();
            cir::TypeId pattern_type = previous->pattern_type.valid()
                ? previous->pattern_type
                : info.pattern_type;
            if (info.has_definition) {
                AttributeList merged_attrs =
                    previous->declaration_attrs;
                merged_attrs.append(std::move(info.declaration_attrs));
                info.declaration_attrs = std::move(merged_attrs);
                info.entity = entity;
                info.lexical_context = lexical_context;
                info.pattern_type = pattern_type;
                if (info.pattern_function.valid() &&
                    !info.pattern_generic.valid()) {

                    info.pattern_generic = file_.add_generic(
                        cir::Generic{entity, loc, {}, info.pattern_function});
                }
                *previous = std::move(info);
            } else {
                previous->declaration_attrs.append(
                    std::move(info.declaration_attrs));
                previous->parameters = std::move(info.parameters);
                previous->param_types = std::move(info.param_types);
                previous->introduced_constraints =
                    std::move(info.introduced_constraints);
                previous->pattern_type = pattern_type;
            }
            note_constraint_environment_change();
            refresh_callable_binding(previous->name,
                                     entity,
                                     {},
                                     previous->has_definition,
                                     loc);
            return entity;
        }
    }

    bool is_function_template =
        !info.is_class_template && !info.is_alias_template &&
        !info.is_variable_template && !info.is_concept;
    bool is_type_template = info.is_class_template || info.is_alias_template;
    if (const cir::Binding* binding =
            file_.lookup_ordinary_binding(current_decl_context(),
                                          info.name,
                                          /*include_parents=*/false)) {
        for (cir::EntityId existing : binding->entities) {
            if (!existing.valid() || !file_.valid(existing) ||
                template_info(existing) != nullptr) {
                continue;
            }
            cir::EntityKind existing_kind = file_.entity(existing).kind;
            bool existing_is_function =
                existing_kind == cir::EntityKind::Function ||
                existing_kind == cir::EntityKind::Method;
            bool existing_is_type =
                existing_kind == cir::EntityKind::Record ||
                existing_kind == cir::EntityKind::Enum ||
                existing_kind == cir::EntityKind::TypeAlias;
            bool allowed_function_and_type_pair =
                (is_function_template && existing_is_type) ||
                (is_type_template && existing_is_function);
            bool allowed_function_overload =
                is_function_template && existing_is_function;
            if (allowed_function_and_type_pair || allowed_function_overload) {
                continue;
            }
            report_error("template '" + info.name +
                             "' conflicts with a previous declaration",
                         loc);
            return existing;
        }
    }

    validate_parameter_pack_position(info);
    validate_primary_default_order(info);

    cir::EntityKind entity_kind = info.is_class_template
        ? cir::EntityKind::Record
        : (info.is_alias_template
               ? cir::EntityKind::TypeAlias
               : (info.is_variable_template
                      ? cir::EntityKind::Variable
                      : (info.is_concept ? cir::EntityKind::Concept
                                         : cir::EntityKind::Function)));
    cir::TypeRef placeholder_ref = info.is_alias_template
        ? (info.alias_target_type_ref.valid()
               ? info.alias_target_type_ref
               : type_ref(info.alias_target_type))
        : cir::TypeRef{};
    cir::TypeId placeholder_type = info.is_alias_template
        ? placeholder_ref.type
        : (info.is_variable_template
               ? info.variable_type_ref.type
               : (info.is_concept ? builder_.bool_type() : cir::TypeId{}));
    cir::EntityId entity = builder_.add_entity(
        entity_kind,
        info.name,
        placeholder_type,
        {},
        loc);
    file_.entity_mut(entity).operator_function = info.operator_function;

    file_.entity_mut(entity).is_definition = false;
    file_.entity_mut(entity).is_deleted = false;
    if (is_function_template && info.is_deleted) {
        file_.entity_mut(entity).decl_flags.is_inline = true;
    }
    if (info.is_alias_template) {
        file_.entity_mut(entity).qualifiers = placeholder_ref.qualifiers;
        file_.entity_mut(entity).memory_space = placeholder_ref.memory_space;
    }
    if (info.has_internal_linkage) {
        file_.entity_mut(entity).linkage = cir::LinkageKind::Internal;
    }
    if (info.is_concept) {
        apply_attributes(entity,
                         AttributeTarget::Concept,
                         info.declaration_attrs,
                         loc);
    } else if (is_function_template) {

        apply_attributes(entity,
                         AttributeTarget::Function,
                         info.declaration_attrs,
                         loc);
    }
    info.entity = entity;
    if (info.is_concept && info.constraint_normal_form.has_value()) {
        stamp_constraint_normal_form_owner(*info.constraint_normal_form,
                                           *this,
                                           info,
                                           entity);
    }

    if (info.is_class_template || info.is_alias_template ||
        info.is_variable_template || info.is_concept) {
        bind_entity(info.name,
                    cir::LookupNamespace::Ordinary,
                    entity,
                    placeholder_type,
                    false,
                    /*is_template_name=*/true,
                    info.has_definition,
                    {},
                    loc);
        if (info.is_alias_template) {
            if (cir::Binding* binding = file_.mutable_ordinary_binding(
                    current_decl_context(), info.name)) {
                binding->type = placeholder_ref;
            }
        }
    } else {

        bind_callable(info.name, entity, {}, info.has_definition, loc);
    }
    if (info.pattern_function.valid()) {

        info.pattern_generic = file_.add_generic(
            cir::Generic{entity, loc, {}, info.pattern_function});
    }
    uint64_t key = static_cast<uint64_t>(entity.index);
    auto inserted = tstate().templates_.emplace(key, std::move(info));
    index_template_pattern_record(inserted.first->second);
    note_constraint_environment_change();
    track_speculative_rollback([this, key] { erase_template_info(key); });
    return entity;
}

bool Session::add_deduction_guide(cir::EntityId primary_entity,
                                  TemplateInfo::DeductionGuide guide,
                                  SrcLoc loc) {
    if (!primary_entity.valid()) {
        report_error("deduction guide requires a class template primary", loc);
        return false;
    }
    auto found = tstate().templates_.find(static_cast<uint64_t>(primary_entity.index));
    if (found == tstate().templates_.end() ||
        !found->second.is_class_template ||
        found->second.is_partial_specialization) {
        report_error("deduction guide requires a class template primary", loc);
        return false;
    }

    auto function_payload = [&](cir::TypeId type)
        -> const cir::FunctionTypePayload* {
        cir::TypeId resolved = file_.resolved_type(type);
        if (!file_.valid(resolved)) {
            return nullptr;
        }
        return std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(resolved));
    };
    auto prepare_bindings =
        [](const std::vector<TemplateParameter>& parameters) {
        PatternBindings bindings;
        bindings.types.resize(parameters.size());
        bindings.values.resize(parameters.size());
        bindings.templates.resize(parameters.size());
        bindings.explicit_types.resize(parameters.size(), false);
        bindings.explicit_values.resize(parameters.size(), false);
        bindings.explicit_templates.resize(parameters.size(), false);
        return bindings;
    };
    auto parameter_clauses_equivalent =
        [&](const TemplateInfo::DeductionGuide& lhs,
            const TemplateInfo::DeductionGuide& rhs) {
        const cir::FunctionTypePayload* left = function_payload(lhs.pattern_type);
        const cir::FunctionTypePayload* right =
            function_payload(rhs.pattern_type);
        if (!left || !right ||
            left->parameters.size() != right->parameters.size() ||
            left->is_variadic != right->is_variadic ||
            left->parameter_pack_flags != right->parameter_pack_flags ||
            lhs.parameter_default_argument_flags !=
                rhs.parameter_default_argument_flags) {
            return false;
        }

        PatternBindings left_to_right = prepare_bindings(lhs.parameters);
        PatternBindings right_to_left = prepare_bindings(rhs.parameters);
        for (size_t i = 0; i < left->parameters.size(); ++i) {
            if (!unify_type_pattern(left->parameters[i].type,
                                    right->parameters[i].type,
                                    left_to_right) ||
                !unify_type_pattern(right->parameters[i].type,
                                    left->parameters[i].type,
                                    right_to_left)) {
                return false;
            }
        }
        return true;
    };
    for (const TemplateInfo::DeductionGuide& existing :
         found->second.deduction_guides) {
        if (parameter_clauses_equivalent(existing, guide)) {
            report_error(
                "deduction guide redeclared with equivalent parameter list",
                loc);
            return false;
        }
    }

    uint64_t key = static_cast<uint64_t>(primary_entity.index);
    TemplateInfo previous = found->second;
    track_speculative_rollback(
        [this, key, previous] { restore_template_info(key, previous); });
    found->second.deduction_guides.push_back(std::move(guide));
    note_constraint_environment_change();
    return true;
}

cir::EntityId Session::register_template_partial_specialization(
    const TemplateInfo& primary,
    TemplateInfo partial,
    std::vector<TemplateArgument> arguments,
    SrcLoc loc) {
    if (!primary.entity.valid() ||
        (!primary.is_class_template && !primary.is_variable_template)) {
        report_error(
            "partial specialization requires a class or variable template primary",
            loc);
        return {};
    }
    auto primary_found =
        tstate().templates_.find(static_cast<uint64_t>(primary.entity.index));
    if (primary_found == tstate().templates_.end()) {
        report_error("partial specialization primary is not registered", loc);
        return {};
    }
    const std::string specialization_kind = primary.is_variable_template
        ? "variable template"
        : "class template";
    for (const TemplateParameter& parameter : partial.parameters) {
        if (!parameter.default_argument.has_value()) {
            continue;
        }
        report_error("default template arguments are not allowed in " +
                         specialization_kind + " partial specializations",
                     parameter.loc.isInvalid() ? loc : parameter.loc);
        return {};
    }

    auto all_parameters_deduced =
        [&](const TemplateInfo& pattern,
            const PatternBindings& bindings) {
        for (const TemplateParameter& parameter : pattern.parameters) {
            switch (parameter.kind) {
                case TemplateParameterKind::Type:
                    if (parameter.is_parameter_pack &&
                        parameter.index < bindings.pack_arguments.size() &&
                        bindings.pack_arguments[parameter.index].has_value()) {
                        break;
                    }
                    if (parameter.index >= bindings.types.size() ||
                        !bindings.types[parameter.index].valid()) {
                        return false;
                    }
                    break;
                case TemplateParameterKind::NonType:
                    if (parameter.is_parameter_pack &&
                        parameter.index < bindings.pack_arguments.size() &&
                        bindings.pack_arguments[parameter.index].has_value()) {
                        break;
                    }
                    if (parameter.index >= bindings.values.size() ||
                        !bindings.values[parameter.index].bound) {
                        return false;
                    }
                    break;
                case TemplateParameterKind::Template:
                    if (parameter.is_parameter_pack &&
                        parameter.index < bindings.pack_arguments.size() &&
                        bindings.pack_arguments[parameter.index].has_value()) {
                        break;
                    }
                    if (parameter.index >= bindings.templates.size() ||
                        !bindings.templates[parameter.index].bound) {
                        return false;
                    }
                    break;
            }
        }
        return true;
    };
    auto pattern_matches =
        [&](const TemplateInfo& pattern,
            const std::vector<TemplateArgument>& pattern_arguments,
            const TemplateInfo& actual_owner,
            const std::vector<TemplateArgument>& actual_arguments,
            bool deduce_through_alias_associated_type) {
        PatternBindings bindings;
        bindings.deduce_through_alias_associated_type =
            deduce_through_alias_associated_type;
        if (deduce_template_argument_list(
                pattern.parameters,
                pattern_arguments,
                actual_arguments,
                bindings,
                TemplateArgumentListDeductionMode::Ordinary,
                &actual_owner.parameters) !=
            TemplateArgumentListDeductionResult::Match) {
            return false;
        }
        if (!reconcile_deduced_value_parameter_types(pattern, bindings)) {
            return false;
        }
        return all_parameters_deduced(pattern, bindings);
    };
    auto type_pattern_qualifiers_equal =
        [&](auto&& self, cir::TypeRef lhs, cir::TypeRef rhs) -> bool {

        if (lhs.qualifiers != rhs.qualifiers ||
            lhs.memory_space != rhs.memory_space) {
            return false;
        }
        cir::TypeId left = file_.resolved_type(lhs.type);
        cir::TypeId right = file_.resolved_type(rhs.type);
        if (!file_.valid(left) || !file_.valid(right) ||
            file_.type(left).kind != file_.type(right).kind) {
            return false;
        }
        switch (file_.type(left).kind) {
            case cir::TypeKind::Pointer:
                return self(self,
                            file_.pointer_pointee_ref(left),
                            file_.pointer_pointee_ref(right));
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference:
                return self(self,
                            file_.reference_referred_ref(left),
                            file_.reference_referred_ref(right));
            case cir::TypeKind::Array: {
                const auto& left_array =
                    std::get<cir::ArrayTypePayload>(file_.type_payload(left));
                const auto& right_array =
                    std::get<cir::ArrayTypePayload>(file_.type_payload(right));
                return self(self,
                            left_array.element_type,
                            right_array.element_type);
            }
            case cir::TypeKind::MemberPointer: {
                const auto& left_member = std::get<cir::MemberPointerTypePayload>(
                    file_.type_payload(left));
                const auto& right_member =
                    std::get<cir::MemberPointerTypePayload>(
                        file_.type_payload(right));
                return self(self,
                            left_member.class_type,
                            right_member.class_type) &&
                       self(self,
                            left_member.member_type,
                            right_member.member_type);
            }
            default:
                return true;
        }
    };
    auto argument_pattern_qualifiers_equal =
        [&](const std::vector<TemplateArgument>& lhs,
            const std::vector<TemplateArgument>& rhs) {
        if (lhs.size() != rhs.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs.size(); ++i) {
            if (lhs[i].kind != rhs[i].kind) {
                return false;
            }
            if (lhs[i].kind == cir::TemplateArgumentKind::Type &&
                !type_pattern_qualifiers_equal(type_pattern_qualifiers_equal,
                                               lhs[i].type,
                                               rhs[i].type)) {
                return false;
            }
            if (lhs[i].kind == cir::TemplateArgumentKind::Value &&
                !type_pattern_qualifiers_equal(type_pattern_qualifiers_equal,
                                               lhs[i].value_type,
                                               rhs[i].value_type)) {
                return false;
            }
        }
        return true;
    };

    for (size_t i = 0; i < arguments.size(); ++i) {
        if (arguments[i].expands_parameter_pack &&
            i + 1 != arguments.size()) {
            report_error("a pack expansion in a " + specialization_kind +
                             " partial specialization shall be the last template argument",
                         loc);
            return {};
        }
    }

    if (!pattern_matches(partial,
                         arguments,
                         partial,
                         arguments,
                         /*deduce_through_alias_associated_type=*/true)) {
        report_error("template parameters of a " + specialization_kind +
                         " partial specialization shall be deducible from its argument list",
                     loc);
        return {};
    }
    TemplateArgumentBindings primary_argument_bindings;
    (void)bind_template_arguments_to_parameters(primary.parameters,
                                                arguments,
                                                primary_argument_bindings);
    for (size_t i = 0; i < arguments.size(); ++i) {
        const TemplateArgument& argument = arguments[i];
        if (i >= primary.parameters.size() ||
            argument.kind != cir::TemplateArgumentKind::Value ||
            argument.value_param_index !=
                cir::ArrayTypePayload::no_extent_param ||
            primary.parameters[i].kind != TemplateParameterKind::NonType) {
            continue;
        }
        cir::TypeId argument_type = primary.parameters[i].non_type_type;
        if (type_contains_type_param(argument_type)) {
            PatternInstantiationCallbacks callbacks;
            cir::TypeId substituted = substitute_pattern_type(
                argument_type,
                primary_argument_bindings,
                callbacks);
            if (substituted.valid()) {
                argument_type = substituted;
            }
        }
        if (type_contains_type_param(argument_type)) {
            report_error(
                "the type of a specialized constant template argument shall not depend on a partial specialization parameter",
                loc);
            return {};
        }
    }

    std::vector<TemplateArgument> primary_arguments =
        self_template_arguments(primary);
    FunctionTemplateOrderingCandidate partial_candidate =
        partial_specialization_ordering_candidate(primary,
                                                  partial,
                                                  arguments);
    FunctionTemplateOrderingCandidate primary_candidate =
        partial_specialization_ordering_candidate(primary,
                                                  primary,
                                                  primary_arguments);
    FunctionTemplatePartialOrdering primary_ordering =
        function_template_partial_ordering(
            partial_candidate,
            primary_candidate,
            FunctionTemplateOrderingContext::declaration());
    bool partial_has_nondeduced_type_pattern =
        std::any_of(arguments.begin(),
                    arguments.end(),
                    [&](const TemplateArgument& argument) {
                        return argument.kind ==
                                   cir::TemplateArgumentKind::Type &&
                               type_contains_nondeduced_context(
                                   argument.type.type);
                    });
    bool more_specialized =
        primary_ordering.lhs_at_least_as_specialized &&
        (!primary_ordering.rhs_at_least_as_specialized ||
         partial_has_nondeduced_type_pattern ||
         declaration_more_constrained(partial.introduced_constraints,
                                      primary.introduced_constraints));
    if (!more_specialized) {
        report_error(specialization_kind +
                         " partial specialization is not more specialized than the primary template",
                     loc);
        return {};
    }

    uint64_t primary_key = static_cast<uint64_t>(primary.entity.index);
    std::string display = template_display_name(primary, arguments);

    if (partial.is_member_template_specialization_overlay) {
        SrcLoc first_affected{};
        for (const auto& [memo_key, specialization] :
             tstate().instantiation_cache_) {
            (void)memo_key;
            if (!specialization.valid() || !file_.valid(specialization) ||
                file_.entity(specialization)
                    .is_explicit_template_specialization) {
                continue;
            }
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(specialization);
            if (!fact || fact->template_entity != primary.entity ||
                !pattern_matches(partial,
                                 arguments,
                                 primary,
                                 fact->template_arguments(),
                                 /*deduce_through_alias_associated_type=*/
                                     false)) {
                continue;
            }
            SrcLoc candidate = fact->point_of_instantiation.isInvalid()
                ? file_.entity(specialization).loc
                : fact->point_of_instantiation;
            if (!candidate.isInvalid() &&
                (first_affected.isInvalid() ||
                 candidate.offset < first_affected.offset)) {
                first_affected = candidate;
            }
        }
        if (!first_affected.isInvalid()) {
            report_error(
                "explicit specialization of member template partial specialization after implicit instantiation",
                loc);
            report_error("implicit instantiation first required here",
                         first_affected);
            return {};
        }
    }

    for (TemplateInfo::PartialSpecialization& existing :
         primary_found->second.partial_specializations) {
        if (!existing.entity.valid() || !file_.valid(existing.entity)) {
            continue;
        }

        uint64_t existing_key = static_cast<uint64_t>(existing.entity.index);
        auto existing_info = tstate().templates_.find(existing_key);
        if (existing_info == tstate().templates_.end()) {
            return existing.entity;
        }
        if (!template_parameter_lists_match(existing_info->second.parameters,
                                            partial.parameters) ||
            !associated_constraints_equivalent(
                existing_info->second.introduced_constraints,
                partial.introduced_constraints)) {
            continue;
        }
        if (!pattern_matches(existing_info->second,
                             existing.arguments,
                             partial,
                             arguments,
                             /*deduce_through_alias_associated_type=*/false) ||
            !pattern_matches(partial,
                             arguments,
                             existing_info->second,
                             existing.arguments,
                             /*deduce_through_alias_associated_type=*/false) ||
            !argument_pattern_qualifiers_equal(existing.arguments,
                                               arguments)) {
            continue;
        }
        if (primary.is_variable_template) {
            PatternBindings existing_to_new;
            PatternBindings new_to_existing;
            bool same_declared_type =
                unify_type_ref_pattern(existing_info->second.variable_type_ref,
                                       partial.variable_type_ref,
                                       existing_to_new) &&
                unify_type_ref_pattern(partial.variable_type_ref,
                                       existing_info->second.variable_type_ref,
                                       new_to_existing);
            if (!same_declared_type) {
                report_error(
                    "conflicting type for variable template partial specialization '" +
                        primary.name + "'",
                    loc);
                return existing.entity;
            }
            if (existing_info->second.variable_decl_flags.is_thread_local !=
                partial.variable_decl_flags.is_thread_local) {
                report_error(
                    "thread_local must appear on all declarations of variable template partial specialization '" +
                        primary.name + "'",
                    loc);
                return existing.entity;
            }
        }
        bool replacing_inherited =
            partial.is_member_template_specialization_overlay &&
            !existing_info->second
                 .is_member_template_specialization_overlay;
        if (existing_info->second.has_definition && partial.has_definition &&
            !replacing_inherited) {
            report_error("redefinition of " + specialization_kind +
                             " partial specialization",
                         loc);
            return existing.entity;
        }
        if (existing_info->second
                .is_member_template_specialization_overlay &&
            existing_info->second.has_definition &&
            !partial.has_definition) {
            return existing.entity;
        }
        if (replacing_inherited || partial.has_definition ||
            !existing_info->second.has_definition) {
            TemplateInfo previous_info = existing_info->second;
            TemplateInfo::PartialSpecialization previous_entry = existing;
            std::vector<TemplateInfo::OutOfLineMember> out_of_line_members =
                replacing_inherited
                    ? std::vector<TemplateInfo::OutOfLineMember>{}
                    : existing_info->second.out_of_line_members;
            track_speculative_rollback(
                [this, primary_key, existing_key, previous_info,
                 previous_entry] {
                restore_template_info(existing_key, previous_info);
                auto found = tstate().templates_.find(primary_key);
                if (found == tstate().templates_.end()) {
                    return;
                }
                for (TemplateInfo::PartialSpecialization& entry :
                     found->second.partial_specializations) {
                    if (entry.entity == previous_entry.entity) {
                        entry = previous_entry;
                        return;
                    }
                }
            });

            partial.entity = existing.entity;
            partial.name = primary.name;
            partial.is_class_template = primary.is_class_template;
            partial.is_variable_template = primary.is_variable_template;
            partial.is_partial_specialization = true;
            partial.lexical_context = primary.lexical_context.valid()
                ? primary.lexical_context
                : current_decl_context();
            if (partial.enclosing_instantiation_bindings.empty()) {
                partial.enclosing_instantiation_bindings =
                    existing_info->second.enclosing_instantiation_bindings;
            }
            partial.has_internal_linkage =
                partial.has_internal_linkage ||
                primary.has_internal_linkage ||
                existing_info->second.has_internal_linkage;
            AttributeList merged_attrs =
                existing_info->second.declaration_attrs;
            merged_attrs.append(partial.declaration_attrs);
            partial.declaration_attrs = std::move(merged_attrs);
            erase_template_pattern_record(existing_info->second);
            existing_info->second = std::move(partial);
            index_template_pattern_record(existing_info->second);
            if (primary.is_variable_template) {
                cir::Entity& partial_entity =
                    file_.entity_mut(existing.entity);
                partial_entity.type = existing_info->second.variable_type;
                partial_entity.decl_flags =
                    existing_info->second.variable_decl_flags;
                partial_entity.linkage =
                    existing_info->second.has_internal_linkage
                        ? cir::LinkageKind::Internal
                        : cir::LinkageKind::External;
            }
            if (!out_of_line_members.empty()) {
                existing_info->second.out_of_line_members.insert(
                    existing_info->second.out_of_line_members.begin(),
                    out_of_line_members.begin(),
                    out_of_line_members.end());
            }
            existing.arguments = std::move(arguments);
            existing.loc = loc;
            note_constraint_environment_change();
        }
        return existing.entity;
    }

    cir::EntityId entity = builder_.add_entity(
        primary.is_class_template ? cir::EntityKind::Record
                                  : cir::EntityKind::Variable,
        display,
        {},
        {},
        loc);
    file_.entity_mut(entity).is_definition = false;

    partial.entity = entity;
    partial.name = primary.name;
    partial.is_class_template = primary.is_class_template;
    partial.is_variable_template = primary.is_variable_template;
    partial.is_partial_specialization = true;
    partial.lexical_context = primary.lexical_context.valid()
        ? primary.lexical_context
        : current_decl_context();
    partial.has_internal_linkage =
        partial.has_internal_linkage || primary.has_internal_linkage;
    if (primary.is_variable_template) {
        cir::Entity& partial_entity = file_.entity_mut(entity);
        partial_entity.type = partial.variable_type;
        partial_entity.decl_flags = partial.variable_decl_flags;
        partial_entity.linkage = partial.has_internal_linkage
            ? cir::LinkageKind::Internal
            : cir::LinkageKind::External;
    }

    uint64_t partial_key = static_cast<uint64_t>(entity.index);
    auto inserted_partial = tstate().templates_.emplace(partial_key, std::move(partial));
    index_template_pattern_record(inserted_partial.first->second);
    primary_found->second.partial_specializations.push_back(
        TemplateInfo::PartialSpecialization{
            entity,
            std::move(arguments),
            loc});
    note_constraint_environment_change();

    track_speculative_rollback([this, primary_key, partial_key] {
        erase_template_info(partial_key);
        auto found = tstate().templates_.find(primary_key);
        if (found != tstate().templates_.end() &&
            !found->second.partial_specializations.empty()) {
            found->second.partial_specializations.pop_back();
        }
    });
    return entity;
}

cir::EntityId Session::register_template_entity(TemplateInfo info,
                                                cir::EntityId entity,
                                                SrcLoc loc) {
    if (!entity.valid() || !file_.valid(entity)) {
        report_error("template declaration has no entity to attach to", loc);
        return {};
    }
    if (template_info(entity)) {
        report_error("redefinition of template '" + info.name + "'", loc);
        return entity;
    }
    for (const TemplateParameter& parameter : info.parameters) {
        if (!parameter.name.empty() && parameter.name == info.name) {
            SrcLoc diagnostic_loc = parameter.loc.isInvalid()
                ? loc
                : parameter.loc;
            report_error("template declaration name shadows template parameter",
                         diagnostic_loc);
            break;
        }
    }

    const cir::Entity& target = file_.entity(entity);
    info.entity = entity;
    info.lexical_context = target.lexical_context.valid()
        ? target.lexical_context
        : current_decl_context();
    if (!info.pattern_type.valid() &&
        file_.valid(target.type) &&
        file_.type(file_.resolved_type(target.type)).kind ==
            cir::TypeKind::Function) {
        info.pattern_type = target.type;
    }
    populate_enclosing_instantiation_bindings(info);

    uint64_t key = static_cast<uint64_t>(entity.index);
    auto inserted = tstate().templates_.emplace(key, std::move(info));
    index_template_pattern_record(inserted.first->second);
    note_constraint_environment_change();
    track_speculative_rollback([this, key] { erase_template_info(key); });
    return entity;
}

bool Session::define_member_template_entity(TemplateInfo info,
                                            cir::EntityId entity,
                                            SrcLoc loc) {
    if (!entity.valid() || !file_.valid(entity)) {
        report_error("member template definition has no entity to attach to",
                     loc);
        return false;
    }
    const cir::Entity& target = file_.entity(entity);
    bool is_static_member_function =
        target.kind == cir::EntityKind::Function &&
        target.semantic_context.valid() &&
        file_.valid(target.semantic_context) &&
        file_.decl_context(target.semantic_context).kind ==
            cir::DeclContextKind::Record;
    if (target.kind != cir::EntityKind::Method &&
        target.kind != cir::EntityKind::Constructor &&
        target.kind != cir::EntityKind::Destructor &&
        !is_static_member_function) {
        report_error("member template definition does not name a member function",
                     loc);
        return false;
    }

    uint64_t key = static_cast<uint64_t>(entity.index);
    auto found = tstate().templates_.find(key);
    if (found == tstate().templates_.end()) {
        report_error("out-of-line member function template definition has no matching declaration",
                     loc);
        return false;
    }

    auto parameter_lists_match =
        [&](auto& self,
            const std::vector<TemplateParameter>& lhs,
            const std::vector<TemplateParameter>& rhs) -> bool {
        if (lhs.size() != rhs.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs.size(); ++i) {
            const TemplateParameter& a = lhs[i];
            const TemplateParameter& b = rhs[i];
            if (a.kind != b.kind ||
                a.is_parameter_pack != b.is_parameter_pack) {
                return false;
            }
            if (a.kind == TemplateParameterKind::NonType &&
                file_.resolved_type(a.non_type_type) !=
                    file_.resolved_type(b.non_type_type)) {
                return false;
            }
            if (a.kind == TemplateParameterKind::Template &&
                a.template_template_parameter_kind !=
                    b.template_template_parameter_kind) {
                return false;
            }
            if (a.kind == TemplateParameterKind::Template &&
                !self(self, a.nested_parameters(), b.nested_parameters())) {
                return false;
            }
        }
        return true;
    };

    TemplateInfo& previous = found->second;
    if (!parameter_lists_match(parameter_lists_match,
                               previous.parameters,
                               info.parameters)) {
        report_error(
            "out-of-line member function template definition has incompatible template parameter list",
            loc);
        return false;
    }
    if (!associated_constraints_equivalent(
            previous.introduced_constraints,
            info.introduced_constraints)) {
        report_error(
            "out-of-line member function template definition has conflicting associated constraints",
            loc);
        return false;
    }
    bool replacing_inherited =
        info.is_member_template_specialization_overlay &&
        !previous.is_member_template_specialization_overlay;
    if (replacing_inherited) {
        SrcLoc first_required =
            first_implicit_template_specialization(previous.entity);
        if (!first_required.isInvalid()) {
            report_error(
                "explicit specialization of member template after implicit instantiation",
                loc);
            report_error("implicit instantiation first required here",
                         first_required);
            return false;
        }
    }
    if (previous.has_definition && info.has_definition &&
        !replacing_inherited) {
        report_error("redefinition of template '" + previous.name + "'", loc);
        return false;
    }
    if (previous.is_member_template_specialization_overlay &&
        previous.has_definition && !info.has_definition) {
        return true;
    }

    TemplateInfo previous_snapshot = previous;
    track_speculative_rollback(
        [this, key, previous_snapshot] {
            restore_template_info(key, previous_snapshot);
        });

    size_t count = std::min(info.parameters.size(),
                            previous.parameters.size());
    for (size_t i = 0; i < count; ++i) {
        if (!info.parameters[i].default_argument.has_value() &&
            previous.parameters[i].default_argument.has_value()) {
            info.parameters[i].default_argument =
                previous.parameters[i].default_argument;
        }
    }

    info.entity = entity;
    if (info.name.empty()) {
        info.name = previous.name;
    }
    info.lexical_context = target.lexical_context.valid()
        ? target.lexical_context
        : previous.lexical_context;
    if (!info.lexical_context.valid()) {
        info.lexical_context = current_decl_context();
    }
    if (!info.pattern_type.valid()) {
        info.pattern_type = previous.pattern_type.valid()
            ? previous.pattern_type
            : target.type;
    }
    if (info.enclosing_instantiation_bindings.empty()) {
        info.enclosing_instantiation_bindings =
            previous.enclosing_instantiation_bindings;
    }
    erase_template_pattern_record(previous);
    previous = std::move(info);
    index_template_pattern_record(previous);
    note_constraint_environment_change();
    return true;
}

bool Session::define_member_class_template_entity(TemplateInfo info,
                                                  cir::EntityId entity,
                                                  SrcLoc loc) {
    if (!entity.valid() || !file_.valid(entity)) {
        report_error("member class template definition has no entity to attach to",
                     loc);
        return false;
    }
    const cir::Entity& target = file_.entity(entity);
    if (target.kind != cir::EntityKind::Record) {
        report_error("member class template definition does not name a class",
                     loc);
        return false;
    }

    uint64_t key = static_cast<uint64_t>(entity.index);
    auto found = tstate().templates_.find(key);
    if (found == tstate().templates_.end() || !found->second.is_class_template) {
        report_error("out-of-class member class template definition has no matching declaration",
                     loc);
        return false;
    }

    auto parameter_lists_match =
        [&](auto& self,
            const std::vector<TemplateParameter>& lhs,
            const std::vector<TemplateParameter>& rhs) -> bool {
        if (lhs.size() != rhs.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs.size(); ++i) {
            const TemplateParameter& a = lhs[i];
            const TemplateParameter& b = rhs[i];
            if (a.kind != b.kind ||
                a.is_parameter_pack != b.is_parameter_pack) {
                return false;
            }
            if (a.kind == TemplateParameterKind::NonType &&
                file_.resolved_type(a.non_type_type) !=
                    file_.resolved_type(b.non_type_type)) {
                return false;
            }
            if (a.kind == TemplateParameterKind::Template &&
                a.template_template_parameter_kind !=
                    b.template_template_parameter_kind) {
                return false;
            }
            if (a.kind == TemplateParameterKind::Template &&
                !self(self, a.nested_parameters(), b.nested_parameters())) {
                return false;
            }
        }
        return true;
    };

    TemplateInfo& previous = found->second;
    if (!parameter_lists_match(parameter_lists_match,
                               previous.parameters,
                               info.parameters)) {
        report_error(
            "out-of-class member class template definition has incompatible template parameter list",
            loc);
        return false;
    }
    if (!associated_constraints_equivalent(
            previous.introduced_constraints,
            info.introduced_constraints)) {
        report_error(
            "out-of-class member class template definition has conflicting associated constraints",
            loc);
        return false;
    }
    bool replacing_inherited =
        info.is_member_template_specialization_overlay &&
        !previous.is_member_template_specialization_overlay;
    if (replacing_inherited) {
        SrcLoc first_required =
            first_implicit_template_specialization(previous.entity);
        if (!first_required.isInvalid()) {
            report_error(
                "explicit specialization of member template after implicit instantiation",
                loc);
            report_error("implicit instantiation first required here",
                         first_required);
            return false;
        }
    }
    if (previous.has_definition && info.has_definition &&
        !replacing_inherited) {
        report_error("redefinition of template '" + previous.name + "'", loc);
        return false;
    }
    if (previous.is_member_template_specialization_overlay &&
        previous.has_definition && !info.has_definition) {
        return true;
    }

    TemplateInfo previous_snapshot = previous;
    track_speculative_rollback(
        [this, key, previous_snapshot] {
            restore_template_info(key, previous_snapshot);
        });

    size_t count = std::min(info.parameters.size(),
                            previous.parameters.size());
    for (size_t i = 0; i < count; ++i) {
        if (!info.parameters[i].default_argument.has_value() &&
            previous.parameters[i].default_argument.has_value()) {
            info.parameters[i].default_argument =
                previous.parameters[i].default_argument;
        }
    }

    std::vector<TemplateInfo::OutOfLineMember> out_of_line_members =
        replacing_inherited
            ? std::vector<TemplateInfo::OutOfLineMember>{}
            : previous.out_of_line_members;
    std::vector<TemplateInfo::ExplicitMemberFunctionSpecialization>
        explicit_member_function_specializations =
            replacing_inherited
                ? std::vector<TemplateInfo::ExplicitMemberFunctionSpecialization>{}
                : previous.explicit_member_function_specializations;
    std::vector<TemplateInfo::ExplicitStaticDataMemberSpecialization>
        explicit_static_data_member_specializations =
            replacing_inherited
                ? std::vector<TemplateInfo::ExplicitStaticDataMemberSpecialization>{}
                : previous.explicit_static_data_member_specializations;
    std::vector<TemplateInfo::PartialSpecialization>
        partial_specializations;
    for (const TemplateInfo::PartialSpecialization& partial_entry :
         previous.partial_specializations) {
        const TemplateInfo* partial = template_info(partial_entry.entity);
        if (!replacing_inherited ||
            (partial &&
             partial->is_member_template_specialization_overlay)) {
            partial_specializations.push_back(partial_entry);
        }
    }
    std::vector<TemplateInfo::DeductionGuide> deduction_guides =
        replacing_inherited
            ? std::vector<TemplateInfo::DeductionGuide>{}
            : previous.deduction_guides;

    info.entity = entity;
    if (info.name.empty()) {
        info.name = previous.name;
    }
    info.lexical_context = previous.lexical_context.valid()
        ? previous.lexical_context
        : target.lexical_context;
    if (!info.lexical_context.valid()) {
        info.lexical_context = current_decl_context();
    }
    if (info.enclosing_instantiation_bindings.empty()) {
        info.enclosing_instantiation_bindings =
            previous.enclosing_instantiation_bindings;
    }
    if (!out_of_line_members.empty()) {
        info.out_of_line_members.insert(info.out_of_line_members.begin(),
                                        out_of_line_members.begin(),
                                        out_of_line_members.end());
    }
    if (!explicit_member_function_specializations.empty()) {
        info.explicit_member_function_specializations.insert(
            info.explicit_member_function_specializations.begin(),
            explicit_member_function_specializations.begin(),
            explicit_member_function_specializations.end());
    }
    if (!explicit_static_data_member_specializations.empty()) {
        info.explicit_static_data_member_specializations.insert(
            info.explicit_static_data_member_specializations.begin(),
            explicit_static_data_member_specializations.begin(),
            explicit_static_data_member_specializations.end());
    }
    if (!partial_specializations.empty()) {
        info.partial_specializations.insert(
            info.partial_specializations.begin(),
            partial_specializations.begin(),
            partial_specializations.end());
    }
    if (!deduction_guides.empty()) {
        info.deduction_guides.insert(info.deduction_guides.begin(),
                                     deduction_guides.begin(),
                                     deduction_guides.end());
    }

    erase_template_pattern_record(previous);
    previous = std::move(info);
    index_template_pattern_record(previous);
    return true;
}

SrcLoc Session::first_implicit_template_specialization(
    cir::EntityId template_entity) const {
    if (!template_entity.valid()) {
        return {};
    }
    SrcLoc first{};
    for (const auto& [memo_key, specialization] :
         tstate().instantiation_cache_) {
        (void)memo_key;
        if (!specialization.valid() || !file_.valid(specialization) ||
            file_.entity(specialization).is_explicit_template_specialization) {
            continue;
        }
        const cir::TemplateSpecializationFact* fact =
            file_.template_specialization(specialization);
        if (!fact || fact->template_entity != template_entity) {
            continue;
        }
        SrcLoc candidate = fact->point_of_instantiation.isInvalid()
            ? file_.entity(specialization).loc
            : fact->point_of_instantiation;
        if (!candidate.isInvalid() &&
            (first.isInvalid() || candidate.offset < first.offset)) {
            first = candidate;
        }
    }
    return first;
}

void Session::index_template_pattern_record(const TemplateInfo& info) {
    if (!info.is_class_template || !info.entity.valid() ||
        !info.pattern_record.valid()) {
        return;
    }
    tstate().pattern_record_templates_[static_cast<uint64_t>(
        info.pattern_record.index)] = info.entity;
}

void Session::erase_template_pattern_record(const TemplateInfo& info) {
    if (!info.is_class_template || !info.entity.valid() ||
        !info.pattern_record.valid()) {
        return;
    }
    uint64_t key = static_cast<uint64_t>(info.pattern_record.index);
    auto found = tstate().pattern_record_templates_.find(key);
    if (found != tstate().pattern_record_templates_.end() &&
        found->second == info.entity) {
        tstate().pattern_record_templates_.erase(found);
    }
}

void Session::restore_template_info(uint64_t key, TemplateInfo info) {
    auto current = tstate().templates_.find(key);
    if (current != tstate().templates_.end()) {
        erase_template_pattern_record(current->second);
    }
    tstate().templates_[key] = std::move(info);
    index_template_pattern_record(tstate().templates_[key]);
}

void Session::erase_template_info(uint64_t key) {
    auto found = tstate().templates_.find(key);
    if (found == tstate().templates_.end()) {
        return;
    }
    erase_template_pattern_record(found->second);
    tstate().templates_.erase(found);
}

const Session::TemplateInfo* Session::template_info(cir::EntityId entity) const {
    auto found = tstate().templates_.find(static_cast<uint64_t>(entity.index));
    return found == tstate().templates_.end() ? nullptr : &found->second;
}

std::vector<Session::TemplateInfo>
Session::complete_class_template_default_recipes(
    cir::EntityId record) const {
    std::vector<TemplateInfo> recipes;
    for (const auto& [_, info] : tstate().templates_) {
        if (!info.has_complete_class_default_recipes) {
            continue;
        }
        cir::EntityId owner = info.entity.valid() && file_.valid(info.entity)
            ? file_.entity(info.entity).parent
            : cir::EntityId{};
        if (owner != record &&
            enclosing_record_for_context(info.lexical_context) != record) {
            continue;
        }
        recipes.push_back(info);
    }
    return recipes;
}

bool Session::resolve_complete_class_template_defaults(
    cir::EntityId template_entity,
    const std::vector<TemplateParameter>& parameters) {
    uint64_t key = static_cast<uint64_t>(template_entity.index);
    auto found = tstate().templates_.find(key);
    if (found == tstate().templates_.end() ||
        found->second.parameters.size() != parameters.size()) {
        return false;
    }
    TemplateInfo previous = found->second;
    track_speculative_rollback(
        [this, key, previous] { restore_template_info(key, previous); });
    for (size_t i = 0; i < parameters.size(); ++i) {
        if (!found->second.parameters[i]
                 .requires_complete_class_default_replay) {
            continue;
        }
        found->second.parameters[i].default_argument =
            parameters[i].default_argument;
        found->second.parameters[i]
            .requires_complete_class_default_replay = false;
    }
    found->second.has_complete_class_default_recipes = false;
    return true;
}

const Session::TemplateInfo*
Session::template_info_for_pattern_record(cir::EntityId record) const {
    if (!record.valid()) {
        return nullptr;
    }
    auto found = tstate().pattern_record_templates_.find(
        static_cast<uint64_t>(record.index));
    if (found == tstate().pattern_record_templates_.end()) {
        return nullptr;
    }
    return template_info(found->second);
}

cir::EntityId Session::class_template_entity_for_record(
    cir::EntityId record) const {
    if (!record.valid() || !file_.valid(record)) {
        return {};
    }
    if (const cir::TemplateSpecializationFact* fact =
            file_.template_specialization(record);
        fact && fact->template_entity.valid()) {
        return fact->template_entity;
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (frame->record != record || !frame->info ||
            !frame->info->is_class_template) {
            continue;
        }
        if (frame->template_entity.valid()) {
            return frame->template_entity;
        }
        if (frame->info->entity.valid()) {
            return frame->info->entity;
        }
    }
    if (const TemplateInfo* info = template_info_for_pattern_record(record);
        info && info->is_class_template && info->entity.valid()) {
        return info->entity;
    }
    if (const TemplateInfo* info = template_info(record);
        info && info->is_class_template && info->entity.valid()) {
        return info->entity;
    }
    return {};
}

cir::EntityId Session::enclosing_injected_class_record(
    cir::DeclContextId context,
    std::string_view name) const {
    for (; context.valid() && file_.valid(context);
         context = file_.decl_context(context).parent) {
        const cir::DeclContext& declaration = file_.decl_context(context);
        if (declaration.kind != cir::DeclContextKind::Record ||
            !declaration.owner.valid() ||
            !file_.valid(declaration.owner)) {
            continue;
        }
        cir::EntityId record = declaration.owner;
        const cir::Entity& entity = file_.entity(record);
        if (entity.name.valid() && file_.name(entity.name) == name) {
            return record;
        }
        cir::EntityId template_entity =
            class_template_entity_for_record(record);
        const TemplateInfo* info = template_info(template_entity);
        if (info && info->is_class_template && info->name == name) {
            return record;
        }
    }
    return {};
}

std::vector<Session::TemplateArgument> Session::self_template_arguments(
    const TemplateInfo& info) const {
    std::vector<TemplateArgument> arguments;
    arguments.reserve(info.parameters.size());
    for (const TemplateParameter& parameter : info.parameters) {
        TemplateArgument argument;
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                argument.kind = cir::TemplateArgumentKind::Type;
                argument.type = cir::TypeRef{
                    parameter.type_param_type,
                    cir::QualNone,
                    cir::MemorySpace::Default};
                break;
            case TemplateParameterKind::NonType:
                argument.kind = cir::TemplateArgumentKind::Value;
                argument.value_type = cir::TypeRef{
                    parameter.non_type_type,
                    cir::QualNone,
                    cir::MemorySpace::Default};
                argument.value_param_index = parameter.index;
                argument.is_dependent = true;
                break;
            case TemplateParameterKind::Template:
                argument.kind = cir::TemplateArgumentKind::Template;
                argument.template_param_index = parameter.index;
                argument.is_dependent = true;
                break;
        }
        argument.expands_parameter_pack = parameter.is_parameter_pack;
        arguments.push_back(std::move(argument));
    }
    return arguments;
}

bool Session::class_template_arguments_for_record(
    cir::EntityId record,
    cir::EntityId* template_entity_out,
    std::vector<TemplateArgument>* arguments_out) const {
    if (!record.valid() || !file_.valid(record)) {
        return false;
    }
    if (const cir::TemplateSpecializationFact* fact =
            file_.template_specialization(record);
        fact && fact->template_entity.valid()) {
        if (template_entity_out) {
            *template_entity_out = fact->template_entity;
        }
        if (arguments_out) {
            *arguments_out = fact->template_arguments();
        }
        return true;
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (frame->record != record || !frame->info ||
            !frame->info->is_class_template) {
            continue;
        }
        if (template_entity_out) {
            *template_entity_out = frame->template_entity.valid()
                ? frame->template_entity
                : frame->info->entity;
        }
        if (arguments_out) {
            *arguments_out = frame->memo_key.empty()
                ? self_template_arguments(*frame->info)
                : frame->arguments;
        }
        return true;
    }
    if (const TemplateInfo* info = template_info_for_pattern_record(record);
        info && info->is_class_template && info->entity.valid()) {
        if (template_entity_out) {
            *template_entity_out = info->entity;
        }
        if (arguments_out) {
            *arguments_out = self_template_arguments(*info);
        }
        return true;
    }
    return false;
}

bool Session::constant_parameter_declared_type_pattern_matches(
    cir::TypeRef pattern,
    cir::TypeRef argument,
    PatternBindings& bindings) const {
    cir::TypeId pattern_type = file_.resolved_type(pattern.type);
    cir::TypeId argument_type = file_.resolved_type(argument.type);
    if (!file_.valid(pattern_type) || !file_.valid(argument_type)) {
        return true;
    }
    if (!contains_auto_type(pattern_type)) {
        return unify_type_ref_pattern(pattern, argument, bindings);
    }
    if ((pattern.qualifiers &
         static_cast<uint8_t>(~argument.qualifiers)) != 0 ||
        (pattern.memory_space != cir::MemorySpace::Default &&
         pattern.memory_space != argument.memory_space)) {
        return false;
    }
    cir::TypeKind pattern_kind = file_.type(pattern_type).kind;
    if (pattern_kind == cir::TypeKind::Auto) {
        return true;
    }
    if (pattern_kind != file_.type(argument_type).kind) {
        return false;
    }

    PatternBindings trial = bindings;
    bool matched = false;
    switch (pattern_kind) {
        case cir::TypeKind::Pointer:
            matched = constant_parameter_declared_type_pattern_matches(
                file_.pointer_pointee_ref(pattern_type),
                file_.pointer_pointee_ref(argument_type),
                trial);
            break;
        case cir::TypeKind::BlockPointer: {
            const auto& pattern_pointer =
                std::get<cir::BlockPointerTypePayload>(
                    file_.type_payload(pattern_type));
            const auto& argument_pointer =
                std::get<cir::BlockPointerTypePayload>(
                    file_.type_payload(argument_type));
            matched = constant_parameter_declared_type_pattern_matches(
                pattern_pointer.pointee,
                argument_pointer.pointee,
                trial);
            break;
        }
        case cir::TypeKind::MemberPointer: {
            const auto& pattern_member =
                std::get<cir::MemberPointerTypePayload>(
                    file_.type_payload(pattern_type));
            const auto& argument_member =
                std::get<cir::MemberPointerTypePayload>(
                    file_.type_payload(argument_type));
            matched = constant_parameter_declared_type_pattern_matches(
                          pattern_member.class_type,
                          argument_member.class_type,
                          trial) &&
                      constant_parameter_declared_type_pattern_matches(
                          pattern_member.member_type,
                          argument_member.member_type,
                          trial);
            break;
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            matched = constant_parameter_declared_type_pattern_matches(
                file_.reference_referred_ref(pattern_type),
                file_.reference_referred_ref(argument_type),
                trial);
            break;
        case cir::TypeKind::Array: {
            const auto& pattern_array = std::get<cir::ArrayTypePayload>(
                file_.type_payload(pattern_type));
            const auto& argument_array = std::get<cir::ArrayTypePayload>(
                file_.type_payload(argument_type));
            constexpr uint32_t no_extent =
                cir::ArrayTypePayload::no_extent_param;
            if (pattern_array.extent_param != no_extent) {
                TemplateArgument extent;
                extent.kind = cir::TemplateArgumentKind::Value;
                if (argument_array.extent_param != no_extent) {
                    extent.value_param_index = argument_array.extent_param;
                    extent.is_dependent = true;
                } else if (argument_array.size.has_value()) {
                    extent.value_kind = cir::TemplateValueKind::Integer;
                    extent.integer_value = cir::IntegerValue::from_unsigned(
                        *argument_array.size, 64);
                } else {
                    return false;
                }
                if (pattern_array.extent_param >= trial.values.size()) {
                    trial.values.resize(pattern_array.extent_param + 1);
                }
                PatternBindings::ValueBinding& extent_binding =
                    trial.values[pattern_array.extent_param];
                if (extent_binding.bound &&
                    !template_value_arguments_equivalent(
                        extent_binding.argument,
                        extent)) {
                    return false;
                }
                if (!extent_binding.bound) {
                    extent_binding.bound = true;
                    extent_binding.argument = extent;
                }
                extent_binding.deduced_from_array_bound = true;
            } else if (!pattern_array.dependent_size_expr.valid() &&
                       !pattern_array.size_expr_is_dependent &&
                       (pattern_array.size_kind != argument_array.size_kind ||
                        argument_array.extent_param != no_extent ||
                        pattern_array.size != argument_array.size)) {
                return false;
            }
            matched = constant_parameter_declared_type_pattern_matches(
                pattern_array.element_type,
                argument_array.element_type,
                trial);
            break;
        }
        case cir::TypeKind::Function: {
            const auto& pattern_function =
                std::get<cir::FunctionTypePayload>(
                    file_.type_payload(pattern_type));
            const auto& argument_function =
                std::get<cir::FunctionTypePayload>(
                    file_.type_payload(argument_type));
            if (pattern_function.parameters.size() !=
                    argument_function.parameters.size() ||
                pattern_function.is_variadic !=
                    argument_function.is_variadic ||
                pattern_function.has_prototype !=
                    argument_function.has_prototype ||
                pattern_function.member_ref_qualifier !=
                    argument_function.member_ref_qualifier ||
                pattern_function.member_is_const !=
                    argument_function.member_is_const ||
                pattern_function.member_is_volatile !=
                    argument_function.member_is_volatile ||
                pattern_function.calling_convention !=
                    argument_function.calling_convention ||
                pattern_function.parameter_pack_flags !=
                    argument_function.parameter_pack_flags) {
                return false;
            }
            matched = constant_parameter_declared_type_pattern_matches(
                pattern_function.return_type,
                argument_function.return_type,
                trial);
            for (size_t i = 0;
                 matched && i < pattern_function.parameters.size();
                 ++i) {
                matched = constant_parameter_declared_type_pattern_matches(
                    pattern_function.parameters[i],
                    argument_function.parameters[i],
                    trial);
            }
            if (matched) {
                matched =
                    detail::deduce_exception_spec_for_partial_ordering(
                        pattern_function.exception_spec,
                        argument_function.exception_spec,
                        trial,
                        *this);
            }
            break;
        }
        case cir::TypeKind::Complex: {
            const auto& pattern_complex =
                std::get<cir::ComplexTypePayload>(
                    file_.type_payload(pattern_type));
            const auto& argument_complex =
                std::get<cir::ComplexTypePayload>(
                    file_.type_payload(argument_type));
            matched = constant_parameter_declared_type_pattern_matches(
                pattern_complex.element_type,
                argument_complex.element_type,
                trial);
            break;
        }
        default:
            matched = false;
            break;
    }
    if (matched) {
        bindings = std::move(trial);
    }
    return matched;
}

bool Session::template_argument_patterns_match(
    const std::vector<TemplateArgument>& pattern_arguments,
    const std::vector<TemplateArgument>& actual_arguments,
    PatternBindings& bindings,
    const std::vector<TemplateParameter>* pattern_parameters,
    const std::vector<TemplateParameter>* actual_parameters) const {
    if (pattern_arguments.size() != actual_arguments.size()) {
        return false;
    }
    for (size_t i = 0; i < pattern_arguments.size(); ++i) {
        const TemplateArgument& pattern_argument = pattern_arguments[i];
        const TemplateArgument& actual_argument = actual_arguments[i];
        if (pattern_argument.kind != actual_argument.kind) {
            return false;
        }
        if (pattern_argument.kind == cir::TemplateArgumentKind::Type) {
            if (!unify_type_ref_pattern(pattern_argument.type,
                                        actual_argument.type,
                                        bindings)) {
                return false;
            }
        } else if (pattern_argument.kind == cir::TemplateArgumentKind::Value) {
            if (pattern_argument.value_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
                uint32_t index = pattern_argument.value_param_index;
                if (index >= bindings.values.size()) {
                    bindings.values.resize(index + 1);
                }
                if (bindings.values[index].bound) {
                    const TemplateArgument& bound =
                        bindings.values[index].argument;
                    if (!template_arguments_equivalent(bound,
                                                       actual_argument)) {
                        return false;
                    }
                } else {
                    bindings.values[index].bound = true;
                    bindings.values[index].argument = actual_argument;
                }
                PatternBindings::ValueBinding& binding =
                    bindings.values[index];
                cir::TypeId pattern_declared =
                    pattern_parameters && index < pattern_parameters->size()
                        ? (*pattern_parameters)[index].non_type_type
                        : pattern_argument.value_type.type;
                cir::TypeId actual_declared = actual_argument.value_type.type;
                if (actual_parameters &&
                    actual_argument.value_param_index !=
                        cir::ArrayTypePayload::no_extent_param &&
                    actual_argument.value_param_index <
                        actual_parameters->size()) {
                    cir::TypeId owner_declared =
                        (*actual_parameters)[actual_argument.value_param_index]
                            .non_type_type;
                    if (owner_declared.valid()) {
                        actual_declared = owner_declared;
                    }
                }
                cir::TypeRef deduction_source = actual_argument.value_type;
                if (actual_declared.valid()) {
                    deduction_source = file_.type_ref(actual_declared);
                }
                if (deduction_source.valid()) {
                    if (binding.source_type_requires_exact_match &&
                        binding.deduction_source_type !=
                            deduction_source) {
                        return false;
                    }
                    binding.deduction_source_type = deduction_source;
                    binding.source_type_requires_exact_match = true;
                }
                if (pattern_declared.valid() && actual_declared.valid() &&
                    !constant_parameter_declared_type_pattern_matches(
                        file_.type_ref(pattern_declared),
                        file_.type_ref(actual_declared),
                        bindings)) {
                    return false;
                }
            } else if (!template_arguments_equivalent(pattern_argument,
                                                      actual_argument)) {
                return false;
            }
        } else {
            if (pattern_argument.template_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
                uint32_t index = pattern_argument.template_param_index;
                if (index >= bindings.templates.size()) {
                    bindings.templates.resize(index + 1);
                }
                if (bindings.templates[index].bound) {
                    if (bindings.templates[index].argument.template_entity !=
                        actual_argument.template_entity) {
                        return false;
                    }
                } else {
                    bindings.templates[index].bound = true;
                    bindings.templates[index].argument = actual_argument;
                }
            } else if (pattern_argument.template_entity !=
                       actual_argument.template_entity) {
                return false;
            }
        }
    }
    return true;
}

bool Session::dependent_member_friend_parameters_deduced(
    const std::vector<uint32_t>& required_type_params,
    const std::vector<uint32_t>& required_value_params,
    const std::vector<uint32_t>& required_template_params,
    const PatternBindings& bindings) const {
    for (uint32_t index : required_type_params) {
        if (index >= bindings.types.size() ||
            !bindings.types[index].valid()) {
            return false;
        }
    }
    for (uint32_t index : required_value_params) {
        if (index >= bindings.values.size() ||
            !bindings.values[index].bound) {
            return false;
        }
    }
    for (uint32_t index : required_template_params) {
        if (index >= bindings.templates.size() ||
            !bindings.templates[index].bound) {
            return false;
        }
    }
    return true;
}

bool Session::dependent_member_friend_qualifier_matches(
    cir::EntityId record,
    cir::TypeRef qualifier_pattern,
    PatternBindings& bindings) const {
    if (!record.valid() || !file_.valid(record) ||
        !qualifier_pattern.type.valid()) {
        return false;
    }
    cir::TypeId pattern_type = file_.resolved_type(qualifier_pattern.type);
    if (!file_.valid(pattern_type) ||
        file_.type(pattern_type).kind != cir::TypeKind::Record) {
        return false;
    }
    cir::EntityId pattern_record = file_.record_entity(pattern_type);
    const cir::TemplateSpecializationFact* pattern_fact =
        pattern_record.valid() ? file_.template_specialization(pattern_record)
                               : nullptr;
    if (!pattern_fact || !pattern_fact->template_entity.valid()) {
        return false;
    }

    PatternBindings direct_bindings = bindings;
    bool direct_match = unify_type_pattern(qualifier_pattern.type,
                                           file_.entity(record).type,
                                           direct_bindings);

    cir::EntityId actual_template{};
    std::vector<TemplateArgument> actual_arguments;
    if (!class_template_arguments_for_record(record,
                                             &actual_template,
                                             &actual_arguments) ||
        actual_template != pattern_fact->template_entity) {
        if (direct_match) {
            bindings = std::move(direct_bindings);
            return true;
        }
        return false;
    }
    PatternBindings argument_bindings = bindings;
    if (!template_argument_patterns_match(pattern_fact->template_arguments(),
                                          actual_arguments,
                                          argument_bindings)) {
        if (direct_match) {
            bindings = std::move(direct_bindings);
            return true;
        }
        return false;
    }
    bindings = std::move(argument_bindings);
    return true;
}

bool Session::dependent_member_friend_parameters_deducible_from_qualifier(
    cir::TypeRef qualifier_pattern,
    const std::vector<uint32_t>& required_type_params,
    const std::vector<uint32_t>& required_value_params,
    const std::vector<uint32_t>& required_template_params) const {
    cir::TypeId qualifier = file_.resolved_type(qualifier_pattern.type);
    if (!file_.valid(qualifier) ||
        file_.type(qualifier).kind != cir::TypeKind::Record) {
        return false;
    }
    cir::EntityId qualifier_record = file_.record_entity(qualifier);
    PatternBindings bindings;
    return dependent_member_friend_qualifier_matches(
               qualifier_record,
               qualifier_pattern,
               bindings) &&
           dependent_member_friend_parameters_deduced(
               required_type_params,
               required_value_params,
               required_template_params,
               bindings);
}

bool Session::dependent_member_friend_template_type_corresponds(
    cir::TypeId pattern_type,
    cir::TypeId actual_type,
    const PatternBindings& outer_bindings,
    const std::vector<std::pair<cir::TypeId, cir::TypeId>>&
        inner_type_params,
    DependentTypeCorrespondenceMode mode) const {
    // Declaration equivalence must remove aliases without resolving through
    // a dependent associated type. In particular,
    // `enable_if_t<Condition<T>, int>` desugars to the dependent
    // `enable_if<Condition<T>, int>::type`; resolving it all the way to
    // `int` would erase the condition and merge distinct SFINAE overloads.
    // Pattern matching, in contrast, compares the substituted object types.
    cir::TypeId p =
        mode == DependentTypeCorrespondenceMode::CompareDeclarations
        ? file_.desugared_type(pattern_type)
        : file_.resolved_type(pattern_type);
    cir::TypeId a =
        mode == DependentTypeCorrespondenceMode::CompareDeclarations
        ? file_.desugared_type(actual_type)
        : file_.resolved_type(actual_type);
    if (!file_.valid(p) || !file_.valid(a)) {
        return false;
    }
    for (const auto& [pattern_param, actual_param] : inner_type_params) {
        if (p == file_.resolved_type(pattern_param)) {
            return a == file_.resolved_type(actual_param);
        }
    }
    const cir::Type& pattern_node = file_.type(p);
    if (pattern_node.kind == cir::TypeKind::DependentName &&
        mode == DependentTypeCorrespondenceMode::MatchPattern) {
        return true;
    }
    if (pattern_node.kind == cir::TypeKind::TypeParam) {
        const auto* leaf =
            std::get_if<cir::TypeParamTypePayload>(&file_.type_payload(p));
        if (mode ==
            DependentTypeCorrespondenceMode::CompareDeclarations) {
            const auto* actual_leaf =
                file_.type(a).kind == cir::TypeKind::TypeParam
                ? std::get_if<cir::TypeParamTypePayload>(
                      &file_.type_payload(a))
                : nullptr;
            return leaf && actual_leaf &&
                   leaf->depth == actual_leaf->depth &&
                   leaf->index == actual_leaf->index &&
                   leaf->is_parameter_pack ==
                       actual_leaf->is_parameter_pack;
        }
        if (!leaf || leaf->index >= outer_bindings.types.size()) {
            return false;
        }
        cir::TypeId bound = outer_bindings.types[leaf->index].type;
        return bound.valid() && file_.resolved_type(bound) == a;
    }
    if (pattern_node.kind != file_.type(a).kind) {
        return false;
    }

    auto refs_correspond = [&](cir::TypeRef pattern,
                               cir::TypeRef actual) -> bool {
        return pattern.qualifiers == actual.qualifiers &&
               pattern.memory_space == actual.memory_space &&
               dependent_member_friend_template_type_corresponds(
                   pattern.type,
                   actual.type,
                   outer_bindings,
                   inner_type_params,
                   mode);
    };
    auto optional_refs_correspond = [&](cir::TypeRef pattern,
                                        cir::TypeRef actual) -> bool {
        if (!pattern.type.valid() || !actual.type.valid()) {
            return pattern.type.valid() == actual.type.valid() &&
                   pattern.qualifiers == actual.qualifiers &&
                   pattern.memory_space == actual.memory_space;
        }
        return refs_correspond(pattern, actual);
    };
    std::function<bool(const cir::TemplateArgument&,
                       const cir::TemplateArgument&)>
        value_arguments_correspond =
            [&](const cir::TemplateArgument& pattern,
                const cir::TemplateArgument& actual) -> bool {
        bool value_entities_correspond =
            pattern.value_entity == actual.value_entity;
        if (mode ==
                DependentTypeCorrespondenceMode::CompareDeclarations &&
            pattern.value_param_index !=
                cir::ArrayTypePayload::no_extent_param &&
            actual.value_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
            value_entities_correspond =
                pattern.value_param_index == actual.value_param_index;
        }
        if (pattern.kind != actual.kind ||
            pattern.value_kind != actual.value_kind ||
            pattern.null_kind != actual.null_kind ||
            pattern.meta_kind != actual.meta_kind ||
            pattern.integer_value != actual.integer_value ||
            pattern.floating_value != actual.floating_value ||
            !value_entities_correspond ||
            pattern.closure_identity != actual.closure_identity ||
            pattern.value_byte_offset != actual.value_byte_offset ||
            pattern.value_elements.size() != actual.value_elements.size() ||
            !optional_refs_correspond(pattern.type, actual.type) ||
            !template_value_exprs_equivalent(
                pattern.dependent_value_expr,
                actual.dependent_value_expr,
                &file_) ||
            !optional_refs_correspond(pattern.value_type,
                                      actual.value_type) ||
            pattern.generated_pack_kind != actual.generated_pack_kind ||
            !optional_refs_correspond(pattern.generated_pack_count_type,
                                      actual.generated_pack_count_type) ||
            !template_value_exprs_equivalent(
                pattern.generated_pack_count_expr,
                actual.generated_pack_count_expr,
                &file_) ||
            !optional_refs_correspond(pattern.dependent_value_qualifier,
                                      actual.dependent_value_qualifier) ||
            pattern.dependent_value_name != actual.dependent_value_name ||
            pattern.is_dependent != actual.is_dependent ||
            pattern.expands_parameter_pack !=
                actual.expands_parameter_pack ||
            pattern.expands_pack_pattern != actual.expands_pack_pattern) {
            return false;
        }
        for (size_t i = 0; i < pattern.value_elements.size(); ++i) {
            if (!value_arguments_correspond(pattern.value_elements[i],
                                           actual.value_elements[i])) {
                return false;
            }
        }
        return true;
    };
    auto value_arguments_match = [&](const cir::TemplateArgument& pattern,
                                     const cir::TemplateArgument& actual)
        -> bool {
        if (mode ==
            DependentTypeCorrespondenceMode::CompareDeclarations) {
            return pattern.value_param_index ==
                       actual.value_param_index &&
                   value_arguments_correspond(pattern, actual);
        }
        if (pattern.value_param_index != cir::ArrayTypePayload::no_extent_param) {
            uint32_t index = pattern.value_param_index;
            return index < outer_bindings.values.size() &&
                   outer_bindings.values[index].bound &&
                   value_arguments_correspond(
                       outer_bindings.values[index].argument,
                       actual);
        }
        return value_arguments_correspond(pattern, actual);
    };
    auto template_arguments_match = [&](const cir::TemplateArgument& pattern,
                                        const cir::TemplateArgument& actual)
        -> bool {
        if (mode ==
            DependentTypeCorrespondenceMode::CompareDeclarations) {
            bool pattern_is_parameter =
                pattern.template_param_index !=
                cir::ArrayTypePayload::no_extent_param;
            bool actual_is_parameter =
                actual.template_param_index !=
                cir::ArrayTypePayload::no_extent_param;
            if (pattern_is_parameter || actual_is_parameter) {
                return pattern_is_parameter == actual_is_parameter &&
                       pattern.template_param_index ==
                           actual.template_param_index;
            }
        }
        if (pattern.template_param_index !=
            cir::ArrayTypePayload::no_extent_param) {
            uint32_t index = pattern.template_param_index;
            return index < outer_bindings.templates.size() &&
                   outer_bindings.templates[index].bound &&
                   outer_bindings.templates[index].argument.kind == actual.kind &&
                   outer_bindings.templates[index].argument.template_entity ==
                       actual.template_entity &&
                   outer_bindings.templates[index].argument.template_param_index ==
                       actual.template_param_index;
        }
        return pattern.template_entity == actual.template_entity &&
               pattern.template_param_index == actual.template_param_index;
    };

    switch (pattern_node.kind) {
        case cir::TypeKind::DependentName: {
            const auto* pattern_name =
                std::get_if<cir::DependentNameTypePayload>(
                    &file_.type_payload(p));
            const auto* actual_name =
                std::get_if<cir::DependentNameTypePayload>(
                    &file_.type_payload(a));
            if (!pattern_name || !actual_name ||
                pattern_name->member_name != actual_name->member_name ||
                pattern_name->is_current_instantiation !=
                    actual_name->is_current_instantiation ||
                pattern_name->template_arguments.size() !=
                    actual_name->template_arguments.size() ||
                !refs_correspond(pattern_name->qualifier_type,
                                 actual_name->qualifier_type)) {
                return false;
            }
            for (size_t i = 0;
                 i < pattern_name->template_arguments.size();
                 ++i) {
                const cir::TemplateArgument& pattern_argument =
                    pattern_name->template_arguments[i];
                const cir::TemplateArgument& actual_argument =
                    actual_name->template_arguments[i];
                if (pattern_argument.kind != actual_argument.kind) {
                    return false;
                }
                if (template_argument_is_type(pattern_argument)) {
                    if (!refs_correspond(pattern_argument.type,
                                         actual_argument.type)) {
                        return false;
                    }
                } else if (template_argument_is_value(pattern_argument)) {
                    if (!value_arguments_match(pattern_argument,
                                               actual_argument)) {
                        return false;
                    }
                } else if (!template_arguments_match(pattern_argument,
                                                     actual_argument)) {
                    return false;
                }
            }
            return true;
        }
        case cir::TypeKind::DecltypeExpr: {
            const auto* pattern_decltype =
                std::get_if<cir::DecltypeExprTypePayload>(
                    &file_.type_payload(p));
            const auto* actual_decltype =
                std::get_if<cir::DecltypeExprTypePayload>(
                    &file_.type_payload(a));
            if (!pattern_decltype || !actual_decltype ||
                pattern_decltype->use_declared_type_rule !=
                    actual_decltype->use_declared_type_rule ||
                pattern_decltype->operand_category !=
                    actual_decltype->operand_category ||
                pattern_decltype->dependent_value_name !=
                    actual_decltype->dependent_value_name) {
                return false;
            }
            auto optional_refs_correspond = [&](cir::TypeRef pattern,
                                                cir::TypeRef actual) {
                if (!pattern.type.valid() || !actual.type.valid()) {
                    return pattern.type.valid() == actual.type.valid() &&
                           pattern.qualifiers == actual.qualifiers &&
                           pattern.memory_space == actual.memory_space;
                }
                return refs_correspond(pattern, actual);
            };
            if (!optional_refs_correspond(
                    pattern_decltype->operand_type,
                    actual_decltype->operand_type) ||
                !optional_refs_correspond(
                    pattern_decltype->dependent_value_qualifier,
                    actual_decltype->dependent_value_qualifier) ||
                pattern_decltype->operand_expression.valid() !=
                    actual_decltype->operand_expression.valid()) {
                return false;
            }
            if (pattern_decltype->operand_expression.valid()) {
                return template_value_exprs_equivalent(
                    pattern_decltype->operand_expression,
                    actual_decltype->operand_expression,
                    &file_);
            }

            return p == a;
        }
        case cir::TypeKind::Pointer: {

            const auto* pattern_pointer =
                std::get_if<cir::PointerTypePayload>(&file_.type_payload(p));
            const auto* actual_pointer =
                std::get_if<cir::PointerTypePayload>(&file_.type_payload(a));
            return pattern_pointer && actual_pointer &&
                   refs_correspond(pattern_pointer->pointee,
                                   actual_pointer->pointee);
        }
        case cir::TypeKind::BlockPointer: {
            const auto* pattern_pointer =
                std::get_if<cir::BlockPointerTypePayload>(
                    &file_.type_payload(p));
            const auto* actual_pointer =
                std::get_if<cir::BlockPointerTypePayload>(
                    &file_.type_payload(a));
            return pattern_pointer && actual_pointer &&
                   refs_correspond(pattern_pointer->pointee,
                                   actual_pointer->pointee);
        }
        case cir::TypeKind::MemberPointer: {
            const auto* pattern_member =
                std::get_if<cir::MemberPointerTypePayload>(
                    &file_.type_payload(p));
            const auto* actual_member =
                std::get_if<cir::MemberPointerTypePayload>(
                    &file_.type_payload(a));
            return pattern_member && actual_member &&
                   refs_correspond(pattern_member->class_type,
                                   actual_member->class_type) &&
                   refs_correspond(pattern_member->member_type,
                                   actual_member->member_type);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return refs_correspond(file_.reference_referred_ref(p),
                                   file_.reference_referred_ref(a));
        case cir::TypeKind::Array: {
            const auto* pattern_array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(p));
            const auto* actual_array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(a));
            if (!pattern_array || !actual_array ||
                pattern_array->size_kind != actual_array->size_kind ||
                pattern_array->size != actual_array->size ||
                pattern_array->extent_param != actual_array->extent_param ||
                pattern_array->size_expr_is_dependent !=
                    actual_array->size_expr_is_dependent ||
                !template_value_exprs_equivalent(
                    pattern_array->dependent_size_expr,
                    actual_array->dependent_size_expr,
                    &file_)) {
                return false;
            }
            return refs_correspond(pattern_array->element_type,
                                   actual_array->element_type);
        }
        case cir::TypeKind::PackIndex: {
            const auto* pattern_pack =
                std::get_if<cir::PackIndexTypePayload>(
                    &file_.type_payload(p));
            const auto* actual_pack =
                std::get_if<cir::PackIndexTypePayload>(
                    &file_.type_payload(a));
            if (!pattern_pack || !actual_pack ||
                pattern_pack->fully_substituted !=
                    actual_pack->fully_substituted ||
                pattern_pack->expansions.size() !=
                    actual_pack->expansions.size() ||
                !refs_correspond(pattern_pack->pack_type,
                                 actual_pack->pack_type) ||
                !template_value_exprs_equivalent(
                    pattern_pack->index_expression,
                    actual_pack->index_expression,
                    &file_)) {
                return false;
            }
            for (size_t i = 0; i < pattern_pack->expansions.size(); ++i) {
                if (!refs_correspond(pattern_pack->expansions[i],
                                     actual_pack->expansions[i])) {
                    return false;
                }
            }
            return true;
        }
        case cir::TypeKind::Function: {
            const auto* pattern_function =
                std::get_if<cir::FunctionTypePayload>(&file_.type_payload(p));
            const auto* actual_function =
                std::get_if<cir::FunctionTypePayload>(&file_.type_payload(a));
            if (!pattern_function || !actual_function ||
                pattern_function->parameters.size() !=
                    actual_function->parameters.size() ||
                pattern_function->is_variadic != actual_function->is_variadic ||
                pattern_function->has_prototype !=
                    actual_function->has_prototype ||
                pattern_function->member_ref_qualifier !=
                    actual_function->member_ref_qualifier ||
                pattern_function->member_is_const !=
                    actual_function->member_is_const ||
                pattern_function->member_is_volatile !=
                    actual_function->member_is_volatile ||
                pattern_function->exception_spec.kind !=
                    actual_function->exception_spec.kind ||
                !template_value_exprs_equivalent(
                    pattern_function->exception_spec.predicate,
                    actual_function->exception_spec.predicate,
                    &file_) ||
                pattern_function->calling_convention !=
                    actual_function->calling_convention ||
                !refs_correspond(pattern_function->return_type,
                                  actual_function->return_type)) {
                return false;
            }
            for (size_t i = 0; i < pattern_function->parameters.size(); ++i) {
                if (!refs_correspond(pattern_function->parameters[i],
                                     actual_function->parameters[i])) {
                    return false;
                }
            }
            return true;
        }
        case cir::TypeKind::Record: {
            const cir::TemplateSpecializationFact* pattern_fact =
                file_.template_specialization(file_.record_entity(p));
            const cir::TemplateSpecializationFact* actual_fact =
                file_.template_specialization(file_.record_entity(a));
            if (!pattern_fact || !actual_fact ||
                pattern_fact->template_entity != actual_fact->template_entity) {
                return p == a;
            }
            auto arguments_correspond =
                [&](const std::vector<TemplateArgument>& pattern_arguments,
                    const std::vector<TemplateArgument>& actual_arguments) {
                if (pattern_arguments.size() != actual_arguments.size()) {
                    return false;
                }
                for (size_t i = 0; i < pattern_arguments.size(); ++i) {
                    const cir::TemplateArgument& pattern_argument =
                        pattern_arguments[i];
                    const cir::TemplateArgument& actual_argument =
                        actual_arguments[i];
                    if (pattern_argument.kind != actual_argument.kind) {
                        return false;
                    }
                    if (template_argument_is_type(pattern_argument)) {
                        if (!refs_correspond(pattern_argument.type,
                                             actual_argument.type)) {
                            return false;
                        }
                    } else if (template_argument_is_value(pattern_argument)) {
                        if (!value_arguments_match(pattern_argument,
                                                   actual_argument)) {
                            return false;
                        }
                    } else if (!template_arguments_match(pattern_argument,
                                                         actual_argument)) {
                        return false;
                    }
                }
                return true;
            };
            if (pattern_fact->argument_bindings.empty() ||
                actual_fact->argument_bindings.empty()) {
                return arguments_correspond(pattern_fact->template_arguments(),
                                            actual_fact->template_arguments());
            }
            if (pattern_fact->argument_bindings.size() !=
                actual_fact->argument_bindings.size()) {
                return false;
            }
            for (size_t slot = 0;
                 slot < pattern_fact->argument_bindings.size();
                 ++slot) {
                const TemplateArgumentBinding& pattern_binding =
                    pattern_fact->argument_bindings[slot];
                const TemplateArgumentBinding& actual_binding =
                    actual_fact->argument_bindings[slot];
                if (pattern_binding.kind != actual_binding.kind ||
                    !arguments_correspond(pattern_binding.arguments,
                                          actual_binding.arguments)) {
                    return false;
                }
            }
            return true;
        }
        default:
            return p == a;
    }
}

bool Session::dependent_member_friend_template_parameter_lists_match(
    const std::vector<cir::TemplateParameterPattern>& pattern,
    const std::vector<TemplateParameter>& actual,
    const PatternBindings& outer_bindings) const {
    if (pattern.size() != actual.size()) {
        return false;
    }
    std::vector<std::pair<cir::TypeId, cir::TypeId>> inner_type_params;
    inner_type_params.reserve(pattern.size());
    for (size_t i = 0; i < pattern.size(); ++i) {
        const cir::TemplateParameterPattern& pattern_parameter = pattern[i];
        const TemplateParameter& actual_parameter = actual[i];
        cir::TemplateParameterPatternKind actual_kind =
            cir::TemplateParameterPatternKind::Type;
        switch (actual_parameter.kind) {
            case TemplateParameterKind::Type:
                actual_kind = cir::TemplateParameterPatternKind::Type;
                break;
            case TemplateParameterKind::NonType:
                actual_kind = cir::TemplateParameterPatternKind::NonType;
                break;
            case TemplateParameterKind::Template:
                actual_kind = cir::TemplateParameterPatternKind::Template;
                break;
        }
        if (pattern_parameter.kind != actual_kind ||
            pattern_parameter.is_parameter_pack !=
                actual_parameter.is_parameter_pack) {
            return false;
        }
        if (pattern_parameter.kind ==
            cir::TemplateParameterPatternKind::Type) {
            if (!pattern_parameter.type_param_type.valid() ||
                !actual_parameter.type_param_type.valid()) {
                return false;
            }
            inner_type_params.push_back(
                {pattern_parameter.type_param_type,
                 actual_parameter.type_param_type});
            continue;
        }
        if (pattern_parameter.kind ==
            cir::TemplateParameterPatternKind::NonType) {
            if (!dependent_member_friend_template_type_corresponds(
                    pattern_parameter.non_type_type.type,
                    actual_parameter.non_type_type,
                    outer_bindings,
                    inner_type_params,
                    DependentTypeCorrespondenceMode::MatchPattern)) {
                return false;
            }
            continue;
        }
        if (!dependent_member_friend_template_parameter_lists_match(
                pattern_parameter.template_parameters,
                actual_parameter.nested_parameters(),
                outer_bindings)) {
            return false;
        }
    }
    return true;
}

const Session::TemplateInfo*
Session::template_info_from_declaration(cir::EntityId entity) const {
    if (!entity.valid() || !file_.valid(entity)) {
        return nullptr;
    }
    if (const TemplateInfo* info = template_info(entity)) {
        return info;
    }
    if (const TemplateInfo* info = template_info_for_pattern_record(entity)) {
        return info;
    }
    if (const cir::TemplateSpecializationFact* fact =
            file_.template_specialization(entity);
        fact && fact->template_entity.valid()) {
        if (const TemplateInfo* info =
                template_info(fact->template_entity)) {
            return info;
        }
    }

    const cir::Entity& declaration = file_.entity(entity);
    if (declaration.kind != cir::EntityKind::Method &&
        declaration.kind != cir::EntityKind::Constructor &&
        declaration.kind != cir::EntityKind::Destructor) {
        return nullptr;
    }
    cir::EntityId owner = declaration.parent;
    if (!owner.valid() || !file_.valid(owner)) {
        return nullptr;
    }
    auto record_is_within = [&](cir::EntityId record,
                                cir::EntityId enclosing) {
        while (record.valid() && file_.valid(record)) {
            if (record == enclosing) {
                return true;
            }
            const cir::Entity& current = file_.entity(record);
            if (!current.semantic_context.valid() ||
                !file_.valid(current.semantic_context)) {
                break;
            }
            cir::DeclContextId parent =
                file_.decl_context(current.semantic_context).parent;
            if (!parent.valid() || !file_.valid(parent)) {
                break;
            }
            const cir::DeclContext& parent_context =
                file_.decl_context(parent);
            if (parent_context.kind != cir::DeclContextKind::Record ||
                !parent_context.owner.valid()) {
                break;
            }
            record = parent_context.owner;
        }
        return false;
    };
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (!frame->info || !frame->info->is_class_template ||
            !frame->record.valid() ||
            !record_is_within(owner, frame->record)) {
            continue;
        }
        cir::EntityId pattern =
            class_template_member_pattern_entity(entity, *frame->info);
        if (const TemplateInfo* info = template_info(pattern)) {
            return info;
        }
    }
    return nullptr;
}

cir::DeclContextId Session::current_instantiation_pattern_context(
    cir::DeclContextId context) const {
    if (!context.valid() || !file_.valid(context)) {
        return {};
    }
    std::vector<cir::EntityId> enclosing_records;
    for (cir::DeclContextId walk = context;
         walk.valid() && file_.valid(walk);
         walk = file_.decl_context(walk).parent) {
        const cir::DeclContext& declaration = file_.decl_context(walk);
        if (declaration.kind == cir::DeclContextKind::Record &&
            declaration.owner.valid() &&
            file_.valid(declaration.owner)) {
            enclosing_records.push_back(declaration.owner);
        }
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (!frame->info || !frame->info->is_class_template ||
            !frame->record.valid() ||
            !frame->info->pattern_record.valid() ||
            !file_.valid(frame->info->pattern_record)) {
            continue;
        }
        auto enclosing = std::find(enclosing_records.begin(),
                                   enclosing_records.end(),
                                   frame->record);
        if (enclosing == enclosing_records.end()) {
            continue;
        }
        size_t frame_index = static_cast<size_t>(
            std::distance(enclosing_records.begin(), enclosing));
        cir::EntityId pattern_record = frame->info->pattern_record;

        for (size_t i = frame_index; i-- > 0;) {
            cir::EntityId instance_record = enclosing_records[i];
            const cir::Entity& instance = file_.entity(instance_record);
            if (!instance.name.valid()) {
                pattern_record = {};
                break;
            }
            cir::DeclContextId pattern_context =
                file_.entity(pattern_record).semantic_context;
            const cir::Binding* binding = pattern_context.valid()
                ? file_.lookup_tag_binding(pattern_context,
                                           file_.name(instance.name),
                                           /*include_parents=*/false)
                : nullptr;
            cir::EntityId nested_pattern{};
            if (binding) {
                for (cir::EntityId candidate : binding->entities) {
                    if (!candidate.valid() || !file_.valid(candidate) ||
                        file_.entity(candidate).kind !=
                            cir::EntityKind::Record) {
                        continue;
                    }
                    nested_pattern = candidate;
                    if (file_.entity(candidate).loc.offset ==
                        instance.loc.offset) {
                        break;
                    }
                }
            }
            pattern_record = nested_pattern;
            if (!pattern_record.valid()) {
                break;
            }
        }
        if (pattern_record.valid() && file_.valid(pattern_record)) {
            return file_.entity(pattern_record).semantic_context;
        }
    }
    return {};
}

const Session::TemplateInfo*
Session::template_info_from_related_ordinary_binding(
    cir::DeclContextId context,
    std::string_view name,
    bool include_parents) const {
    const cir::Binding* ordinary = file_.lookup_ordinary_binding(
        context, name, include_parents);
    if (!ordinary) {
        return nullptr;
    }

    if (ordinary->is_type_name && ordinary->type.valid()) {
        cir::TypeId type = file_.resolved_type(ordinary->type.type);
        if (file_.valid(type) &&
            file_.type(type).kind == cir::TypeKind::Record) {
            cir::EntityId record = file_.record_entity(type);
            if (const TemplateInfo* info =
                    template_info_from_declaration(record);
                info && info->name == name) {
                return info;
            }
        }
    }
    for (auto it = ordinary->entities.rbegin();
         it != ordinary->entities.rend();
         ++it) {
        cir::EntityId entity = *it;
        if (!entity.valid() || !file_.valid(entity)) {
            continue;
        }
        if (const TemplateInfo* info =
                template_info_from_declaration(entity)) {
            if (info->name == name) {
                return info;
            }
        }
    }
    return nullptr;
}

Session::FunctionTemplateInstantiationCallback
Session::set_function_template_instantiation_callback(
    FunctionTemplateInstantiationCallback callback) {
    FunctionTemplateInstantiationCallback previous =
        std::move(tstate().function_template_instantiation_callback_);
    tstate().function_template_instantiation_callback_ = std::move(callback);
    return previous;
}

bool Session::has_function_template_instantiation_callback() const {
    return static_cast<bool>(
        tstate().function_template_instantiation_callback_);
}

cir::EntityId Session::form_function_template_specialization_candidate(
    const TemplateInfo& info,
    const TemplateArgumentBindings& argument_bindings,
    SrcLoc loc) {
    if (!tstate().function_template_instantiation_callback_) {
        return {};
    }
    return tstate().function_template_instantiation_callback_(
        info, argument_bindings, loc);
}

Session::PatternInstantiationCallbackConfigurator
Session::set_pattern_instantiation_callback_configurator(
    PatternInstantiationCallbackConfigurator callback) {
    PatternInstantiationCallbackConfigurator previous =
        std::move(tstate().pattern_instantiation_callback_configurator_);
    tstate().pattern_instantiation_callback_configurator_ =
        std::move(callback);
    return previous;
}

Session::ClassTemplatePlaceholderDeductionCallback
Session::set_class_template_placeholder_deduction_callback(
    ClassTemplatePlaceholderDeductionCallback callback) {
    ClassTemplatePlaceholderDeductionCallback previous =
        std::move(tstate().class_template_placeholder_deduction_callback_);
    tstate().class_template_placeholder_deduction_callback_ =
        std::move(callback);
    return previous;
}

Session::ClassInstantiationDemandCallback
Session::set_class_instantiation_demand_callback(
    ClassInstantiationDemandCallback callback) {
    ClassInstantiationDemandCallback previous =
        std::move(tstate().class_instantiation_demand_callback_);
    tstate().class_instantiation_demand_callback_ = std::move(callback);
    return previous;
}

Session::FunctionInstantiationDemandCallback
Session::set_function_instantiation_demand_callback(
    FunctionInstantiationDemandCallback callback) {
    FunctionInstantiationDemandCallback previous =
        std::move(tstate().function_instantiation_demand_callback_);
    tstate().function_instantiation_demand_callback_ = std::move(callback);
    return previous;
}

cir::EntityId Session::set_function_template_materialization_target(
    cir::EntityId target) {
    cir::EntityId previous =
        tstate().function_template_materialization_target_;
    tstate().function_template_materialization_target_ = target;
    return previous;
}

Session::InstantiationDemandResult Session::request_class_instantiation(
    cir::EntityId specialization,
    cir::InstantiationDemandKind kind,
    SrcLoc loc,
    cir::EntityId subject) {
    using Result = InstantiationDemandResult;
    using Status = cir::InstantiationDemandStatus;
    if (!specialization.valid() || !file_.valid(specialization) ||
        file_.entity(specialization).kind != cir::EntityKind::Record) {
        return Result::Failed;
    }
    const cir::TemplateSpecializationFact* stored =
        file_.template_specialization(specialization);
    if (!stored || !stored->template_entity.valid()) {

        return Result::Satisfied;
    }

    auto find_demand = [&](const cir::TemplateSpecializationFact& fact)
        -> const cir::InstantiationDemandFact* {
        for (const cir::InstantiationDemandFact& demand :
             fact.instantiation_demands) {
            if (demand.kind == kind && demand.subject == subject) {
                return &demand;
            }
        }
        return nullptr;
    };
    bool retry_unavailable_demand = false;
    if (const cir::InstantiationDemandFact* existing = find_demand(*stored)) {
        const cir::RecordFacts* facts = file_.record_facts(specialization);
        bool completed_class_satisfies_demand =
            !subject.valid() && facts && !facts->is_incomplete &&
            (kind == cir::InstantiationDemandKind::DeclarationSet ||
             kind == cir::InstantiationDemandKind::CompleteClass ||
             kind == cir::InstantiationDemandKind::BaseMemberList);
        if (completed_class_satisfies_demand &&
            existing->status != Status::Satisfied) {

            cir::TemplateSpecializationFact reconciled = *stored;
            for (cir::InstantiationDemandFact& demand :
                 reconciled.instantiation_demands) {
                if (demand.kind == kind && demand.subject == subject) {
                    demand.status = Status::Satisfied;
                    break;
                }
            }
            file_.set_template_specialization(specialization,
                                            std::move(reconciled));
            return Result::Satisfied;
        }
        switch (existing->status) {
            case Status::Satisfied:
                return Result::Satisfied;
            case Status::Active:

                return Result::Unavailable;
            case Status::Unavailable:

                retry_unavailable_demand = true;
                break;
            case Status::Failed:
                return Result::Failed;
        }
    }

    bool source_order_placeholder_result =
        kind == cir::InstantiationDemandKind::ResultType &&
        subject.valid() && file_.valid(subject) &&
        file_.entity(subject).has_deferred_definition &&
        file_.entity(subject).parent == specialization;
    bool deferred_member_class_during_owner_replay =
        subject.valid() && file_.valid(subject) &&
        file_.entity(subject).kind == cir::EntityKind::Record &&
        std::any_of(
            tstate().current_instantiation_frames_.rbegin(),
            tstate().current_instantiation_frames_.rend(),
            [&](const TemplateState::CurrentInstantiationFrame& frame) {
                return frame.record == specialization;
            });
    bool constexpr_member_during_owner_replay =
        kind == cir::InstantiationDemandKind::ConstantEvaluation &&
        subject.valid() && file_.valid(subject) &&
        (file_.entity(subject).kind == cir::EntityKind::Method ||
         file_.entity(subject).kind == cir::EntityKind::Constructor ||
         file_.entity(subject).kind == cir::EntityKind::Destructor) &&
        file_.entity(subject).has_deferred_definition &&
        file_.entity(subject).parent == specialization &&
        std::any_of(
            tstate().current_instantiation_frames_.rbegin(),
            tstate().current_instantiation_frames_.rend(),
            [&](const TemplateState::CurrentInstantiationFrame& frame) {
                return frame.record == specialization;
            });

    if (kind != cir::InstantiationDemandKind::Identity &&
        kind != cir::InstantiationDemandKind::DeclarationSet &&
        !source_order_placeholder_result &&
        !deferred_member_class_during_owner_replay &&
        !constexpr_member_during_owner_replay) {
        Result declarations = request_class_instantiation(
            specialization,
            cir::InstantiationDemandKind::DeclarationSet,
            loc);
        if (declarations != Result::Satisfied) {
            return declarations;
        }

        stored = file_.template_specialization(specialization);
        if (!stored) {
            return Result::Failed;
        }
        if (const cir::InstantiationDemandFact* existing =
                find_demand(*stored)) {
            switch (existing->status) {
                case Status::Satisfied:
                case Status::Active:
                    return Result::Satisfied;
                case Status::Unavailable:
                    return Result::Unavailable;
                case Status::Failed:
                    return Result::Failed;
            }
        }
        if (((kind == cir::InstantiationDemandKind::CompleteClass ||
              kind == cir::InstantiationDemandKind::BaseMemberList) &&
             !subject.valid()) ||
            (kind == cir::InstantiationDemandKind::DeletionSemantics &&
             !subject.valid()) ||
            ((kind == cir::InstantiationDemandKind::ConstantEvaluation ||
              kind == cir::InstantiationDemandKind::OdrUse) &&
             !subject.valid())) {
            cir::TemplateSpecializationFact completed =
                *file_.template_specialization(specialization);
            completed.instantiation_demands.push_back(
                cir::InstantiationDemandFact{
                    kind,
                    Status::Satisfied,
                    subject,
                    loc,
                    current_point_lookup_generation(),
                    0});
            file_.set_template_specialization(specialization,
                                            std::move(completed));
            return Result::Satisfied;
        }
    }

    stored = file_.template_specialization(specialization);
    if (!stored) {
        return Result::Failed;
    }
    const TemplateInfo* info = template_info(stored->template_entity);
    if (!info) {
        return Result::Failed;
    }
    uint64_t point_generation =
        template_instantiation_point_generation(0);
    uint64_t request_id = record_template_instantiation_request(
        *info,
        stored->template_arguments(),
        loc,
        point_generation,
        TemplateInstantiationRequestKind::ClassInstantiationDemand);
    cir::TemplateSpecializationFact active = *stored;
    if (active.point_of_instantiation.isInvalid()) {
        active.point_of_instantiation = loc;
        active.point_lookup_generation = point_generation;
    }
    if (retry_unavailable_demand) {
        for (cir::InstantiationDemandFact& demand :
             active.instantiation_demands) {
            if (demand.kind != kind || demand.subject != subject) {
                continue;
            }
            demand.status = Status::Active;
            demand.request_id = request_id;
            break;
        }
    } else {
        active.instantiation_demands.push_back(cir::InstantiationDemandFact{
            kind,
            Status::Active,
            subject,
            loc,
            point_generation,
            request_id});
    }
    file_.set_template_specialization(specialization, std::move(active));

    Result result = Result::Failed;
    if (kind == cir::InstantiationDemandKind::Identity) {
        result = Result::Satisfied;
    } else if (tstate().class_instantiation_demand_callback_) {
        result = tstate().class_instantiation_demand_callback_(
            specialization, kind, subject, loc);
    } else {
        report_error("class-template instantiation demand has no materializer",
                     loc);
    }

    stored = file_.template_specialization(specialization);
    if (!stored) {
        return Result::Failed;
    }
    cir::TemplateSpecializationFact finished = *stored;
    for (cir::InstantiationDemandFact& demand :
         finished.instantiation_demands) {
        if (demand.request_id != request_id) {
            continue;
        }
        demand.status = result == Result::Satisfied
            ? Status::Satisfied
            : (result == Result::Unavailable ? Status::Unavailable
                                             : Status::Failed);
        break;
    }
    file_.set_template_specialization(specialization, std::move(finished));
    return result;
}

Session::InstantiationDemandResult
Session::request_class_member_instantiation(
    cir::EntityId subject,
    cir::InstantiationDemandKind kind,
    SrcLoc loc) {
    if (!subject.valid() || !file_.valid(subject)) {
        return InstantiationDemandResult::Failed;
    }
    cir::EntityId specialization{};
    cir::EntityId parent = file_.entity(subject).parent;
    if (parent.valid() && file_.valid(parent) &&
        file_.template_specialization(parent)) {
        specialization = parent;
    }
    cir::DeclContextId context = file_.entity(subject).semantic_context;
    while (!specialization.valid() && context.valid() && file_.valid(context)) {
        const cir::DeclContext& declaration = file_.decl_context(context);
        if (declaration.kind == cir::DeclContextKind::Record &&
            declaration.owner.valid() && declaration.owner != subject &&
            file_.template_specialization(declaration.owner)) {
            specialization = declaration.owner;
            break;
        }
        context = declaration.parent;
    }
    if (!specialization.valid()) {
        return InstantiationDemandResult::Satisfied;
    }
    return request_class_instantiation(specialization, kind, loc, subject);
}

bool Session::require_placeholder_result(
    cir::EntityId function,
    cir::InstantiationDemandKind kind,
    SrcLoc loc) {
    if (!function.valid() || !file_.valid(function)) {
        return false;
    }
    cir::Entity& entity = file_.entity_mut(function);
    cir::PlaceholderResultFactId fact_id = entity.placeholder_result;
    if (!file_.valid(fact_id) &&
        function_has_placeholder_return(entity.type)) {
        fact_id = register_placeholder_result(function, entity.type, nullptr,
                                              entity.loc);
    }
    if (!file_.valid(fact_id)) {
        return true;
    }

    auto adopt_concrete_entity_result = [&]() {
        cir::TypeId resolved = file_.resolved_type(
            file_.entity(function).type);
        const auto* payload = file_.valid(resolved)
            ? std::get_if<cir::FunctionTypePayload>(
                  &file_.type_payload(resolved))
            : nullptr;
        if (!payload || contains_auto_type(payload->return_type.type)) {
            return false;
        }
        publish_placeholder_result(fact_id, payload->return_type, loc,
                                   /*final=*/true);
        return true;
    };

    auto state = [&]() {
        return file_.placeholder_result_fact(fact_id).state;
    };
    if (state() == cir::PlaceholderResultState::Complete) {
        return true;
    }
    if (state() == cir::PlaceholderResultState::Failed) {
        return false;
    }
    if (state() == cir::PlaceholderResultState::Undeduced &&
        adopt_concrete_entity_result()) {
        return true;
    }
    if (state() == cir::PlaceholderResultState::Deducing) {
        const cir::PlaceholderResultFact& fact =
            file_.placeholder_result_fact(fact_id);
        if (fact.candidate.type.valid()) {
            return true;
        }
        report_error("function with a deduced return type cannot be used "
                     "before its return type is deduced",
                     loc);
        return false;
    }

    InstantiationDemandResult member_demand =
        request_class_member_instantiation(function, kind, loc);
    if (member_demand == InstantiationDemandResult::Failed) {
        return false;
    }
    if (member_demand == InstantiationDemandResult::Satisfied &&
        (state() == cir::PlaceholderResultState::Complete ||
         adopt_concrete_entity_result())) {
        return true;
    }

    InstantiationDemandResult demand = request_function_instantiation(
        function, cir::InstantiationDemandKind::ResultType, loc);
    if (demand == InstantiationDemandResult::Satisfied &&
        (state() == cir::PlaceholderResultState::Complete ||
         adopt_concrete_entity_result())) {
        return true;
    }
    if (demand == InstantiationDemandResult::Failed) {
        return false;
    }

    report_error("function with a deduced return type cannot be used before "
                 "its definition",
                 loc);
    (void)kind;
    return false;
}

Session::InstantiationDemandResult Session::request_function_instantiation(
    cir::EntityId specialization,
    cir::InstantiationDemandKind kind,
    SrcLoc loc) {
    using Result = InstantiationDemandResult;
    using Status = cir::InstantiationDemandStatus;
    if (!specialization.valid() || !file_.valid(specialization)) {
        return Result::Failed;
    }
    cir::Entity& entity = file_.entity_mut(specialization);
    if (entity.kind != cir::EntityKind::Function &&
        entity.kind != cir::EntityKind::Method &&
        entity.kind != cir::EntityKind::Constructor &&
        entity.kind != cir::EntityKind::Destructor) {
        return Result::Failed;
    }
    const cir::TemplateSpecializationFact* stored =
        file_.template_specialization(specialization);
    if (!stored || !stored->template_entity.valid()) {
        if (tstate().function_instantiation_demand_callback_ &&
            (!entity.is_definition ||
             entity.result_type_only_definition)) {
            return tstate().function_instantiation_demand_callback_(
                specialization, kind, loc);
        }
        return Result::Satisfied;
    }
    const TemplateInfo* info = template_info(stored->template_entity);
    if (!info) {
        return Result::Failed;
    }

    if (info->is_class_template) {
        return Result::Satisfied;
    }
    // [temp.point]p1: a function specialization referenced from a dependent
    // template-definition context takes its point of instantiation from the
    // enclosing concrete specialization.  Keep the bound pattern shell for
    // validation and replay, but do not publish an ODR demand owned by the
    // generic pattern itself.
    if (kind == cir::InstantiationDemandKind::OdrUse &&
        in_template_definition_ && entity.is_template_pattern) {
        return Result::Satisfied;
    }
    if (entity.is_definition) {
        bool promote_result_only =
            entity.result_type_only_definition &&
            (kind == cir::InstantiationDemandKind::OdrUse ||
             kind == cir::InstantiationDemandKind::ConstantEvaluation);
        if (kind == cir::InstantiationDemandKind::OdrUse ||
            kind == cir::InstantiationDemandKind::ConstantEvaluation) {
            entity.result_type_only_definition = false;
            if (file_.valid(entity.placeholder_result)) {
                file_.placeholder_result_fact_mut(entity.placeholder_result)
                    .result_only_materialization = false;
            }
        }
        if (promote_result_only) {

            std::vector<std::pair<cir::EntityId, SrcLoc>> callees;
            for (cir::FunctionId function_id : file_.function_ids()) {
                const cir::Function& function = file_.function(function_id);
                if (function.entity != specialization) {
                    continue;
                }
                for (cir::BlockId block_id : function.blocks) {
                    const cir::Block& block = file_.block(block_id);
                    for (cir::InstId inst_id : block.instructions) {
                        if (!file_.valid(inst_id) ||
                            file_.inst(inst_id).kind !=
                                cir::InstKind::Call) {
                            continue;
                        }
                        std::vector<cir::Operand> operands =
                            file_.operands(file_.inst(inst_id).operands);
                        if (operands.empty() ||
                            operands.front().kind !=
                                cir::OperandKind::Entity) {
                            continue;
                        }
                        const auto* callee = std::get_if<cir::EntityId>(
                            &operands.front().data);
                        if (!callee || !callee->valid() ||
                            !file_.valid(*callee) ||
                            *callee == specialization ||
                            !file_.template_specialization(*callee)) {
                            continue;
                        }
                        callees.emplace_back(*callee,
                                             file_.inst(inst_id).loc);
                    }
                }
                break;
            }
            for (const auto& [callee, call_loc] : callees) {
                if (request_function_instantiation(
                        callee,
                        cir::InstantiationDemandKind::OdrUse,
                        call_loc.isInvalid() ? loc : call_loc) ==
                    Result::Failed) {
                    return Result::Failed;
                }
            }
        }
        ensure_structor_variants(specialization, loc);
        return Result::Satisfied;
    }
    if (entity.suppressed_by_explicit_instantiation_declaration) {

        return Result::Unavailable;
    }

    auto find_demand = [&](const cir::TemplateSpecializationFact& fact)
        -> const cir::InstantiationDemandFact* {
        for (const cir::InstantiationDemandFact& demand :
             fact.instantiation_demands) {
            if (demand.kind == kind && !demand.subject.valid()) {
                return &demand;
            }
        }
        return nullptr;
    };
    if (const cir::InstantiationDemandFact* demand = find_demand(*stored)) {
        switch (demand->status) {
            case Status::Active:
            case Status::Satisfied:
                return Result::Satisfied;
            case Status::Unavailable:
                return Result::Unavailable;
            case Status::Failed:
                return Result::Failed;
        }
    }

    uint64_t point_generation = stored->point_lookup_generation != 0
        ? stored->point_lookup_generation
        : template_instantiation_point_generation(0);
    uint64_t request_id = record_template_instantiation_request(
        *info,
        stored->template_arguments(),
        loc,
        point_generation,
        TemplateInstantiationRequestKind::FunctionInstantiationDemand);
    cir::TemplateSpecializationFact active = *stored;
    active.instantiation_demands.push_back(cir::InstantiationDemandFact{
        kind,
        Status::Active,
        {},
        loc,
        point_generation,
        request_id});
    file_.set_template_specialization(specialization, std::move(active));

    Result result = Result::Unavailable;
    if (kind == cir::InstantiationDemandKind::Identity) {
        result = Result::Satisfied;
    } else if (tstate().function_instantiation_demand_callback_) {
        result = tstate().function_instantiation_demand_callback_(
            specialization, kind, loc);
    }

    stored = file_.template_specialization(specialization);
    if (!stored) {
        return Result::Failed;
    }
    cir::TemplateSpecializationFact finished = *stored;
    for (cir::InstantiationDemandFact& demand :
         finished.instantiation_demands) {
        if (demand.request_id != request_id) {
            continue;
        }
        demand.status = result == Result::Satisfied
            ? Status::Satisfied
            : (result == Result::Unavailable ? Status::Unavailable
                                             : Status::Failed);
        break;
    }
    file_.set_template_specialization(specialization, std::move(finished));
    if (result == Result::Satisfied &&
        file_.entity(specialization).is_definition) {
        ensure_structor_variants(specialization, loc);
    }
    return result;
}

Session::InstantiationDemandResult
Session::require_complete_class_type_result(
    cir::TypeId type,
    SrcLoc loc,
    cir::InstantiationDemandKind reason) {
    using Result = InstantiationDemandResult;
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Record) {
        return Result::Satisfied;
    }
    cir::EntityId record = file_.record_entity(resolved);
    if (record.valid() && file_.template_specialization(record)) {
        Result demand = request_class_instantiation(record, reason, loc);
        if (demand != Result::Satisfied) {
            return demand;
        }
    } else if (record.valid() && file_.valid(record)) {

        cir::InstantiationDemandKind member_reason =
            reason == cir::InstantiationDemandKind::DeclarationSet
                ? cir::InstantiationDemandKind::CompleteClass
                : reason;
        Result demand =
            request_class_member_instantiation(record, member_reason, loc);
        if (demand != Result::Satisfied) {
            return demand;
        }
    }
    const cir::RecordFacts* facts = file_.record_facts_for_type(resolved);
    return facts && !facts->is_incomplete ? Result::Satisfied
                                          : Result::Unavailable;
}

bool Session::require_complete_class_type(
    cir::TypeId type,
    SrcLoc loc,
    cir::InstantiationDemandKind reason) {
    return require_complete_class_type_result(type, loc, reason) ==
        InstantiationDemandResult::Satisfied;
}

ConstEvalContext Session::make_consteval_context(LangOptions options) const {
    ConstEvalContext context;
    context.file = &file_;
    context.mutable_file = const_cast<cir::File*>(&file_);
    context.lang_options = std::move(options);
    context.demand_function_definition =
        [self = const_cast<Session*>(this)](cir::EntityId function,
                                            SrcLoc loc) {
            if (!function.valid() || !self->file_.valid(function)) {
                return false;
            }

            if (self->file_.entity(function).is_definition) {
                return true;
            }
            cir::EntityKind kind = self->file_.entity(function).kind;
            bool member_kind = kind == cir::EntityKind::Method ||
                               kind == cir::EntityKind::Constructor ||
                               kind == cir::EntityKind::Destructor;
            InstantiationDemandResult result = member_kind
                ? self->request_class_member_instantiation(
                      function,
                      cir::InstantiationDemandKind::ConstantEvaluation,
                      loc)
                : self->request_function_instantiation(
                      function,
                      cir::InstantiationDemandKind::ConstantEvaluation,
                      loc);

            if (member_kind && !self->file_.entity(function).is_definition &&
                self->file_.template_specialization(function)) {
                InstantiationDemandResult recipe =
                    self->request_function_instantiation(
                        function,
                        cir::InstantiationDemandKind::ConstantEvaluation,
                        loc);
                if (result != InstantiationDemandResult::Satisfied ||
                    self->file_.entity(function).is_definition) {
                    result = recipe;
                }
            }
            return result == InstantiationDemandResult::Satisfied &&
                self->file_.entity(function).is_definition;
        };
    return context;
}

Session::DefaultArgumentReplayCallback
Session::set_default_argument_replay_callback(
    DefaultArgumentReplayCallback callback) {
    DefaultArgumentReplayCallback previous =
        std::move(default_argument_replay_callback_);
    default_argument_replay_callback_ = std::move(callback);
    return previous;
}

Session::DefaultMemberInitializerReplayCallback
Session::set_default_member_initializer_replay_callback(
    DefaultMemberInitializerReplayCallback callback) {
    DefaultMemberInitializerReplayCallback previous =
        std::move(default_member_initializer_replay_callback_);
    default_member_initializer_replay_callback_ = std::move(callback);
    return previous;
}

const Session::TemplateInfo* Session::template_info_for_name(
    std::string_view name) const {
    std::string key(name);
    if (in_pack_pattern_capture()) {
        if (const TemplateInfo* pack_info =
                template_parameter_pack_info_for_name(name)) {
            const_cast<Session*>(this)->capture_parameter_pack(
                ParameterPackKind::Template, name);
            return pack_info;
        }
    }
    if (const ParameterPackElement* replay = parameter_pack_replay_element(
            ParameterPackKind::Template, name)) {
        if (const TemplateArgument* argument =
                std::get_if<TemplateArgument>(replay)) {
            return template_info(argument->template_entity);
        }
    }
    auto capture_if_template_pack = [&](const TemplateInfo* info) {
        if (info && info->is_template_parameter_pack &&
            in_pack_pattern_capture()) {
            const_cast<Session*>(this)->capture_parameter_pack(
                ParameterPackKind::Template, name);
        }
        return info;
    };
    auto is_structor_template = [&](const TemplateInfo* info) {
        if (!info || !info->entity.valid() ||
            !file_.valid(info->entity)) {
            return false;
        }

        cir::EntityKind kind = file_.entity(info->entity).kind;
        return kind == cir::EntityKind::Constructor ||
            kind == cir::EntityKind::Destructor;
    };
    auto active_primary_for_partial =
        [&](const TemplateInfo* info) {
        if (!info || !info->is_partial_specialization) {
            return info;
        }
        for (auto frame =
                 tstate().current_instantiation_frames_.rbegin();
             frame != tstate().current_instantiation_frames_.rend();
             ++frame) {
            if (frame->info != info ||
                !frame->template_entity.valid()) {
                continue;
            }
            if (const TemplateInfo* primary =
                    template_info(frame->template_entity)) {
                return primary;
            }
            break;
        }
        return info;
    };

    if (active_template_header_info_) {
        for (auto parameter = active_template_header_info_->parameters.rbegin();
             parameter != active_template_header_info_->parameters.rend();
             ++parameter) {
            if (parameter->kind == TemplateParameterKind::Template &&
                parameter->name == name && parameter->nested_head) {
                return capture_if_template_pack(parameter->nested_head.get());
            }
        }
    }

    if (validating_template_info_ &&
        validating_template_info_->name == name &&
        !is_structor_template(validating_template_info_)) {
        const TemplateInfo* named_template =
            active_primary_for_partial(validating_template_info_);
        return capture_if_template_pack(named_template);
    }
    const cir::Binding* binding =
        lookup_template_name_binding(name, /*include_parents=*/true);
    if (binding && !binding->entities.empty()) {
        if (const TemplateInfo* info =
                template_info_from_declaration(binding->entities.back())) {
            if (!is_structor_template(info)) {
                return capture_if_template_pack(info);
            }
        }
    }

    const cir::Binding* callable = file_.lookup_callable_binding(
        current_decl_context(), name, /*include_parents=*/true);
    if (callable) {
        for (cir::EntityId entity : callable->entities) {
            if (const TemplateInfo* info =
                    template_info_from_declaration(entity)) {
                if (!is_structor_template(info)) {
                    return capture_if_template_pack(info);
                }
            }
        }
    }

    cir::DeclContextId pattern_context =
        current_instantiation_pattern_context(current_decl_context());
    if (pattern_context.valid()) {
        const cir::Binding* pattern_template =
            file_.lookup_template_name_binding(pattern_context,
                                               name,
                                               /*include_parents=*/false);
        if (pattern_template && !pattern_template->entities.empty()) {
            if (const TemplateInfo* info =
                    template_info_from_declaration(
                        pattern_template->entities.back());
                info && !is_structor_template(info)) {
                return capture_if_template_pack(info);
            }
        }
        const cir::Binding* pattern_callable =
            file_.lookup_callable_binding(pattern_context,
                                          name,
                                          /*include_parents=*/false);
        if (pattern_callable) {
            for (cir::EntityId entity : pattern_callable->entities) {
                if (const TemplateInfo* info =
                        template_info_from_declaration(entity);
                    info && !is_structor_template(info)) {
                    return capture_if_template_pack(info);
                }
            }
        }
    }

    bool found_record_type_name = false;
    cir::TypeRef record_type =
        lookup_record_scope_type_before_outer_template_parameters(
            name, &found_record_type_name);
    if (found_record_type_name && record_type.valid()) {
        cir::TypeId resolved = file_.resolved_type(record_type.type);
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Record) {
            cir::EntityId record = file_.record_entity(resolved);
            if (const TemplateInfo* info =
                    template_info_from_declaration(record);
                info && info->name == name &&
                !is_structor_template(info)) {
                return capture_if_template_pack(
                    active_primary_for_partial(info));
            }
        }
    }

    if (const TemplateInfo* related =
            template_info_from_related_ordinary_binding(
                current_decl_context(), name, /*include_parents=*/true)) {
        related = active_primary_for_partial(related);
        if (!is_structor_template(related)) {
            return capture_if_template_pack(related);
        }
    }

    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        const TemplateInfo* named_template =
            frame->template_entity.valid()
            ? template_info(frame->template_entity)
            : frame->info;
        if (named_template && named_template->name == name &&
            named_template->is_class_template &&
            !is_structor_template(named_template)) {
            return capture_if_template_pack(named_template);
        }
    }

    for (auto it = active_instantiations_.rbegin();
         it != active_instantiations_.rend(); ++it) {
        auto found = tstate().templates_.find(it->template_entity_index);
        if (found != tstate().templates_.end() &&
            found->second.name == name &&
            !is_structor_template(&found->second)) {
            return capture_if_template_pack(&found->second);
        }
    }
    return nullptr;
}

const Session::TemplateInfo*
Session::template_parameter_pack_info_for_name(std::string_view name) const {
    auto keep_template_pack = [](const TemplateInfo* info) {
        return info && info->is_template_parameter_pack ? info : nullptr;
    };

    if (validating_template_info_ && validating_template_info_->name == name) {
        if (const TemplateInfo* info =
                keep_template_pack(validating_template_info_)) {
            return info;
        }
    }
    const cir::Binding* binding =
        lookup_template_name_binding(name, /*include_parents=*/true);
    if (binding && !binding->entities.empty()) {
        if (const TemplateInfo* info =
                keep_template_pack(template_info_from_declaration(
                    binding->entities.back()))) {
            return info;
        }
    }
    const cir::Binding* callable = file_.lookup_callable_binding(
        current_decl_context(), name, /*include_parents=*/true);
    if (callable) {
        for (cir::EntityId entity : callable->entities) {
            if (const TemplateInfo* info =
                    keep_template_pack(
                        template_info_from_declaration(entity))) {
                return info;
            }
        }
    }
    if (const TemplateInfo* related =
            keep_template_pack(template_info_from_related_ordinary_binding(
                current_decl_context(), name, /*include_parents=*/true))) {
        return related;
    }
    for (auto it = active_instantiations_.rbegin();
         it != active_instantiations_.rend(); ++it) {
        auto found = tstate().templates_.find(it->template_entity_index);
        if (found != tstate().templates_.end() && found->second.name == name) {
            if (const TemplateInfo* info =
                    keep_template_pack(&found->second)) {
                return info;
            }
        }
    }
    return nullptr;
}

const Session::TemplateInfo* Session::template_info_in_context(
    cir::DeclContextId context,
    std::string_view name,
    bool include_parents) const {
    if (!context.valid()) {
        return nullptr;
    }
    if (validating_template_info_ && validating_template_info_->name == name &&
        validating_template_info_->lexical_context.valid() &&
        namespace_lookup_reaches_context(
            context, validating_template_info_->lexical_context)) {
        return validating_template_info_;
    }
    // Qualified lookup forms one direct declaration set from a namespace and
    // its transitive inline namespace members ([namespace.qual]). Consult that
    // same set before the category indexes below so an enclosing non-template
    // overload cannot hide a template in an inline ABI namespace.
    if (!include_parents) {
        std::optional<cir::Binding> namespace_direct =
            qualified_namespace_direct_binding(context, name);
        if (namespace_direct) {
            for (cir::EntityId entity : namespace_direct->entities) {
                if (const TemplateInfo* info =
                        template_info_from_declaration(entity)) {
                    return info;
                }
            }
        }
    }
    const cir::Binding* binding = file_.lookup_template_name_binding(
        context, name, include_parents);
    if (binding && !binding->entities.empty()) {
        if (const TemplateInfo* info =
                template_info_from_declaration(binding->entities.back())) {
            return info;
        }
    }

    const cir::Binding* callable = file_.lookup_callable_binding(
        context, name, include_parents);
    if (callable) {
        for (cir::EntityId entity : callable->entities) {
            if (const TemplateInfo* info =
                    template_info_from_declaration(entity)) {
                return info;
            }
        }
    }
    cir::DeclContextId pattern_context =
        current_instantiation_pattern_context(context);
    if (pattern_context.valid()) {
        const cir::Binding* pattern_template =
            file_.lookup_template_name_binding(pattern_context,
                                               name,
                                               /*include_parents=*/false);
        if (pattern_template && !pattern_template->entities.empty()) {
            if (const TemplateInfo* info =
                    template_info_from_declaration(
                        pattern_template->entities.back())) {
                return info;
            }
        }
        const cir::Binding* pattern_callable =
            file_.lookup_callable_binding(pattern_context,
                                          name,
                                          /*include_parents=*/false);
        if (pattern_callable) {
            for (cir::EntityId entity : pattern_callable->entities) {
                if (const TemplateInfo* info =
                        template_info_from_declaration(entity)) {
                    return info;
                }
            }
        }
    }
    if (const TemplateInfo* related =
            template_info_from_related_ordinary_binding(context,
                                                        name,
                                                        include_parents)) {
        return related;
    }
    cir::EntityId owner = file_.decl_context(context).owner;
    if (owner.valid() && file_.valid(owner) &&
        file_.entity(owner).kind == cir::EntityKind::Record) {
        MemberLookupResult lookup =
            lookup_member_name(file_.entity(owner).type, name);
        const TemplateInfo* selected = nullptr;
        cir::EntityId selected_primary{};
        for (const MemberLookupDeclaration& declaration :
             lookup.declarations) {
            cir::EntityId entity = declaration.entity;
            const TemplateInfo* info =
                template_info_from_declaration(entity);
            if (!info && entity.valid() && file_.valid(entity) &&
                file_.entity(entity).kind == cir::EntityKind::Record) {
                entity = class_template_entity_for_record(entity);
                info = template_info(entity);
            }
            if (!info) {
                return nullptr;
            }
            cir::EntityId primary = info->entity.valid() ? info->entity
                                                         : entity;
            if (selected_primary.valid() && selected_primary != primary) {
                return nullptr;
            }
            selected_primary = primary;
            selected = info;
        }
        if (selected) {
            return selected;
        }
    }
    return nullptr;
}

std::vector<const Session::TemplateInfo*>
Session::function_template_infos_for_name(cir::DeclContextId context,
                                          std::string_view name,
                                          bool include_parents) const {
    cir::DeclContextId lookup_context =
        context.valid() ? context : current_decl_context();
    const cir::Binding* callable = file_.lookup_callable_binding(
        lookup_context, name, include_parents);
    std::vector<const TemplateInfo*> results;
    auto append_info = [&](const TemplateInfo* info) {
        if (!info || info->is_class_template ||
            info->is_alias_template ||
            info->is_variable_template || info->is_concept) {
            return;
        }
        if (std::find(results.begin(), results.end(), info) ==
            results.end()) {
            results.push_back(info);
        }
    };
    auto append_callable = [&](const cir::Binding* binding) {
        if (!binding) {
            return;
        }
        for (cir::EntityId entity : binding->entities) {
            append_info(template_info_from_declaration(entity));
        }
    };
    if (callable) {
        results.reserve(callable->entities.size());
    }
    append_callable(callable);

    if (include_parents && validating_template_info_ &&
        validating_template_info_->name == name) {
        append_info(validating_template_info_);
        if (validating_template_info_->lexical_context.valid()) {
            append_callable(file_.lookup_callable_binding(
                validating_template_info_->lexical_context,
                name,
                /*include_parents=*/false));
        }
    }
    cir::DeclContextId pattern_context =
        current_instantiation_pattern_context(lookup_context);
    if (pattern_context.valid()) {
        append_callable(file_.lookup_callable_binding(
            pattern_context, name, /*include_parents=*/false));
    }
    return results;
}

const Session::TemplateInfo* Session::peek_qualified_template_info(
    bool global_qualifier,
    const std::vector<std::string_view>& qualifiers,
    std::string_view terminal) const {

    cir::DeclContextId context =
        global_qualifier ? translation_unit_context_ : cir::DeclContextId{};
    for (std::string_view component : qualifiers) {
        const cir::Binding* binding = context.valid()
            ? file_.lookup_namespace_name_binding(context, component,
                                                  /*include_parents=*/false)
            : file_.lookup_namespace_name_binding(current_decl_context(),
                                                  component,
                                                  /*include_parents=*/true);
        if (binding && !binding->entities.empty()) {
            context = file_.entity(binding->entities.back()).semantic_context;
            if (!context.valid()) {
                return nullptr;
            }
            continue;
        }

        cir::TypeId component_type{};
        bool member_record_context = false;
        if (context.valid()) {
            cir::EntityId owner = file_.decl_context(context).owner;
            if (owner.valid() && file_.valid(owner) &&
                file_.entity(owner).kind == cir::EntityKind::Record) {
                member_record_context = true;
                component_type = lookup_qualified_type_name(context,
                                                            component);
            }
        }
        if (member_record_context && !component_type.valid()) {
            return nullptr;
        }
        if (!component_type.valid()) {
            const cir::Binding* type_binding = context.valid()
                ? file_.lookup_type_name_binding(context,
                                                 component,
                                                 /*include_parents=*/false)
                : file_.lookup_type_name_binding(current_decl_context(),
                                                 component,
                                                 /*include_parents=*/true);
            if (!type_binding) {
                type_binding = context.valid()
                    ? file_.lookup_tag_binding(context,
                                               component,
                                               /*include_parents=*/false)
                    : file_.lookup_tag_binding(current_decl_context(),
                                               component,
                                               /*include_parents=*/true);
            }
            if (!type_binding || !type_binding->type.type.valid()) {
                return nullptr;
            }
            component_type = type_binding->type.type;
        }
        cir::TypeId resolved = file_.resolved_type(component_type);
        if (!file_.valid(resolved) ||
            file_.type(resolved).kind != cir::TypeKind::Record) {
            return nullptr;
        }
        cir::EntityId record = file_.record_entity(resolved);
        if (!record.valid() || !file_.valid(record)) {
            return nullptr;
        }
        context = file_.entity(record).semantic_context;
        if (!context.valid()) {
            return nullptr;
        }
    }
    if (!context.valid()) {
        return nullptr;
    }
    if (const TemplateInfo* direct =
            template_info_in_context(context, terminal,
                                     /*include_parents=*/false)) {
        return direct;
    }

    cir::EntityId owner = file_.decl_context(context).owner;
    if (!owner.valid() || !file_.valid(owner) ||
        file_.entity(owner).kind != cir::EntityKind::Record) {
        return nullptr;
    }
    MemberLookupResult lookup =
        lookup_member_name(file_.entity(owner).type, terminal);
    if (!lookup.found_name || lookup.declarations.empty()) {
        return nullptr;
    }
    const TemplateInfo* selected = nullptr;
    cir::EntityId selected_primary{};
    for (const MemberLookupDeclaration& declaration : lookup.declarations) {
        cir::EntityId entity = declaration.entity;
        const TemplateInfo* info = template_info(entity);
        if (!info && entity.valid() && file_.valid(entity) &&
            file_.entity(entity).kind == cir::EntityKind::Record) {
            cir::EntityId primary = class_template_entity_for_record(entity);
            info = template_info(primary);
            entity = primary;
        }
        if (!info || (!info->is_class_template &&
                      !info->is_alias_template)) {
            return nullptr;
        }
        cir::EntityId primary = info->entity.valid() ? info->entity : entity;
        if (selected_primary.valid() && selected_primary != primary) {
            return nullptr;
        }
        selected_primary = primary;
        selected = info;
    }

    return selected;
}

std::string Session::template_memo_key(
    cir::EntityId entity,
    const std::vector<TemplateArgument>& arguments) const {
    TemplateArgumentBindings bindings;
    const TemplateInfo* info = template_info(entity);
    TemplateArgumentBindingMode mode =
        info && !info->is_class_template && !info->is_alias_template &&
                !info->is_variable_template && !info->is_concept
        ? TemplateArgumentBindingMode::DeducedCanonical
        : TemplateArgumentBindingMode::Canonical;
    if (info &&
        bind_template_arguments_to_parameters(info->parameters,
                                              arguments,
                                              bindings,
                                              nullptr,
                                              mode)) {
        return template_memo_key(entity, bindings);
    }

    bindings.reserve(arguments.size());
    for (const TemplateArgument& argument : arguments) {
        TemplateArgumentBinding binding;
        binding.kind = TemplateArgumentBindingKind::Single;
        binding.arguments = {argument};
        bindings.push_back(std::move(binding));
    }
    return template_memo_key(entity, bindings);
}

std::string Session::template_memo_key(
    cir::EntityId entity,
    const TemplateArgumentBindings& argument_bindings) const {
    std::string key;
    size_t argument_count = 0;
    for (const TemplateArgumentBinding& binding : argument_bindings) {
        argument_count += binding.arguments.size();
    }
    key.reserve(32 + argument_bindings.size() * 8 + argument_count * 24);
    append_key_word(key, static_cast<uint64_t>(MemoKeyFamily::TemplateReplay));
    append_key_word(key, entity.index);
    append_key_word(key, argument_bindings.size());
    for (const TemplateArgumentBinding& binding : argument_bindings) {
        append_key_word(key, static_cast<uint64_t>(binding.kind));
        append_key_word(key, binding.arguments.size());
        for (const TemplateArgument& argument : binding.arguments) {
            append_template_argument_identity_key(key, argument);
        }
    }
    return key;
}

Session::ConstraintSatisfactionScope
Session::begin_constraint_satisfaction(
    ConstraintSatisfactionRequestKind kind,
    cir::EntityId entity,
    const TemplateArgumentBindings& argument_bindings,
    uint64_t point_lookup_generation,
    uint64_t subject_begin,
    uint64_t subject_end) {
    bump_template_counter(PerfCounter::ConstraintSatisfactionRequests);
    point_lookup_generation =
        template_instantiation_point_generation(point_lookup_generation);

    ConstraintSatisfactionScope scope;
    scope.environment_revision = tstate().constraint_environment_revision_;

    scope.stable_identity =
        kind == ConstraintSatisfactionRequestKind::AtomicConstraint ||
        kind == ConstraintSatisfactionRequestKind::ConceptId;
    scope.recursion_key = template_memo_key(entity, argument_bindings);
    auto append_word = [](std::string& key, uint64_t value) {
        char bytes[sizeof(value)];
        std::memcpy(bytes, &value, sizeof(value));
        key.append(bytes, sizeof(bytes));
    };
    append_word(scope.recursion_key, static_cast<uint64_t>(kind));
    append_word(scope.recursion_key, subject_begin);
    append_word(scope.recursion_key, subject_end);
    if (!scope.stable_identity) {
        append_word(scope.recursion_key, scope.environment_revision);
    }
    scope.key = scope.recursion_key;
    if (!scope.stable_identity) {
        append_word(scope.key, point_lookup_generation);
    }

    auto& satisfaction_cache = scope.stable_identity
        ? tstate().stable_constraint_satisfaction_cache_
        : tstate().constraint_satisfaction_cache_;
    auto cached = satisfaction_cache.find(scope.key);
    if (cached != satisfaction_cache.end()) {
        bump_template_counter(
            PerfCounter::ConstraintSatisfactionCacheHits);
        scope.state = ConstraintSatisfactionScope::State::Cached;
        scope.cached_result = cached->second;
        return scope;
    }

    if (std::find(tstate().active_constraint_satisfactions_.begin(),
                  tstate().active_constraint_satisfactions_.end(),
                  scope.recursion_key) !=
        tstate().active_constraint_satisfactions_.end()) {
        scope.state = ConstraintSatisfactionScope::State::Recursive;
        return scope;
    }

    bump_template_counter(PerfCounter::ConstraintSatisfactionCacheMisses);
    tstate().active_constraint_satisfactions_.push_back(
        scope.recursion_key);
    record_template_counter_max(
        PerfCounter::MaxConstraintSatisfactionDepth,
        tstate().active_constraint_satisfactions_.size());
    return scope;
}

void Session::finish_constraint_satisfaction(
    ConstraintSatisfactionScope scope,
    ConstraintSatisfactionResult result) {
    if (!scope.should_evaluate()) {
        return;
    }
    assert(!tstate().active_constraint_satisfactions_.empty());
    assert(tstate().active_constraint_satisfactions_.back() ==
           scope.recursion_key);
    tstate().active_constraint_satisfactions_.pop_back();

    if (result != ConstraintSatisfactionResult::Satisfied &&
        result != ConstraintSatisfactionResult::Unsatisfied) {
        return;
    }

    if (!scope.stable_identity &&
        scope.environment_revision !=
            tstate().constraint_environment_revision_) {
        return;
    }
    auto& satisfaction_cache = scope.stable_identity
        ? tstate().stable_constraint_satisfaction_cache_
        : tstate().constraint_satisfaction_cache_;
    journal_speculative_map_entry(
        scope.stable_identity
            ? "stable constraint satisfaction cache"
            : "constraint satisfaction cache",
        satisfaction_cache,
        scope.key);
    satisfaction_cache.insert_or_assign(
        std::move(scope.key), result);
}

void Session::abandon_constraint_satisfaction(
    ConstraintSatisfactionScope scope) {
    if (!scope.should_evaluate()) {
        return;
    }
    assert(!tstate().active_constraint_satisfactions_.empty());
    assert(tstate().active_constraint_satisfactions_.back() ==
           scope.recursion_key);
    tstate().active_constraint_satisfactions_.pop_back();
}

uint64_t Session::constraint_environment_revision() const {
    return tstate().constraint_environment_revision_;
}

void Session::note_constraint_environment_change() {
    ++tstate().constraint_environment_revision_;
    if (tstate().constraint_environment_revision_ == 0) {
        tstate().constraint_environment_revision_ = 1;
        tstate().constraint_satisfaction_cache_.clear();
    }
    if (!is_speculative_parsing()) {
        tstate().constraint_satisfaction_cache_.clear();
    }
}

std::string Session::template_argument_identity_key(
    const TemplateArgument& argument) const {
    std::string key;
    append_template_argument_identity_key(key, argument);
    return key;
}

void Session::append_template_argument_identity_key(
    std::string& key,
    const TemplateArgument& argument) const {
    append_key_word(key,
                    (static_cast<uint64_t>(argument.kind) << 1) |
                        (argument.expands_parameter_pack ? 1 : 0));
    switch (argument.kind) {
        case cir::TemplateArgumentKind::Type:
            append_key_word(key,
                            file_.resolved_type(argument.type.type).index);
            append_key_word(key, argument.type.qualifiers);
            append_key_word(
                key, static_cast<uint64_t>(argument.type.memory_space));
            break;
        case cir::TemplateArgumentKind::Value: {
            append_key_word(
                key, file_.resolved_type(argument.value_type.type).index);
            append_key_word(key, static_cast<uint64_t>(argument.value_kind));
            append_key_word(key, static_cast<uint64_t>(argument.null_kind));
            append_key_word(key, argument.integer_value.low_bits);
            append_key_word(key, argument.integer_value.high_bits);
            append_key_word(key, argument.integer_value.bit_width);
            append_key_word(key, argument.integer_value.is_unsigned);
            if (argument.value_kind == cir::TemplateValueKind::Floating) {
                append_key_word(
                    key,
                    static_cast<uint64_t>(argument.floating_value.semantics));
                append_key_word(key, argument.floating_value.low_bits);
                append_key_word(key, argument.floating_value.high_bits);
            }
            append_key_word(key, argument.value_entity.index);
            append_key_word(key, argument.closure_identity.index);
            append_key_word(
                key, static_cast<uint64_t>(argument.value_byte_offset));
            append_key_word(key, static_cast<uint64_t>(argument.meta_kind));
            append_key_word(key,
                            argument.type.type.valid()
                                ? argument.type.type.index
                                : 0);
            append_key_word(key, argument.type.qualifiers);
            append_key_word(key, argument.value_param_index);
            append_key_word(key, argument.value_elements.size());
            for (const TemplateArgument& element : argument.value_elements) {
                append_template_argument_identity_key(key, element);
            }
            append_template_value_expr_key(key, argument.dependent_value_expr);
            append_key_word(
                key, static_cast<uint64_t>(argument.generated_pack_kind));
            append_key_word(
                key,
                argument.generated_pack_count_type.type.valid()
                    ? file_.resolved_type(
                          argument.generated_pack_count_type.type).index
                    : 0);
            append_key_word(key,
                            argument.generated_pack_count_type.qualifiers);
            append_key_word(
                key,
                static_cast<uint64_t>(
                    argument.generated_pack_count_type.memory_space));
            append_template_value_expr_key(
                key, argument.generated_pack_count_expr);
            if (template_argument_has_dependent_value_name(argument)) {
                append_key_word(key, 1);
                append_key_word(
                    key,
                    file_.resolved_type(
                        argument.dependent_value_qualifier.type).index);
                append_key_word(key, argument.dependent_value_name.index);
            } else {
                append_key_word(key, 0);
            }
            break;
        }
        case cir::TemplateArgumentKind::Template: {
            append_key_word(key, argument.template_entity.index);
            append_key_word(key, argument.template_param_index);
            if (template_argument_has_dependent_template_name(argument)) {
                append_key_word(key, 1);
                append_key_word(
                    key,
                    file_.resolved_type(
                        argument.dependent_template_qualifier.type).index);
                append_key_word(key, argument.template_name.index);
            } else {
                append_key_word(key, 0);
            }
            break;
        }
    }
}

std::string Session::template_argument_display(
    const TemplateArgument& argument) const {
    auto with_expansion = [&](std::string display) {
        if (argument.expands_parameter_pack) {
            display += "...";
        }
        return display;
    };
    auto type_display = [&](cir::TypeRef type) -> std::string {
        return file_.format_type(type);
    };
    auto entity_display = [&](cir::EntityId entity) -> std::string {
        if (!entity.valid() || !file_.valid(entity)) {
            return {};
        }
        std::string display;
        cir::EntityId owner = file_.entity(entity).parent;
        if (owner.valid() && file_.valid(owner) &&
            file_.entity(owner).name.valid()) {
            display += file_.name(file_.entity(owner).name);
            display += "::";
        }
        if (file_.entity(entity).name.valid()) {
            display += file_.name(file_.entity(entity).name);
        }
        return display;
    };
    switch (argument.kind) {
        case cir::TemplateArgumentKind::Type:
            return with_expansion(type_display(argument.type));
        case cir::TemplateArgumentKind::Value:
            if (template_argument_has_dependent_value_name(argument)) {
                return with_expansion(
                    type_display(argument.dependent_value_qualifier) +
                    "::" + std::string(file_.name(
                                 argument.dependent_value_name)));
            }
            if (template_argument_has_dependent_value_expr(argument)) {
                if (!argument.value_spelling.empty()) {
                    return with_expansion(argument.value_spelling);
                }
                return with_expansion(
                    template_value_expr_display(argument.dependent_value_expr));
            }
            if (argument.is_dependent &&
                argument.value_param_index !=
                    cir::ArrayTypePayload::no_extent_param &&
                !argument.value_spelling.empty()) {
                return with_expansion(argument.value_spelling);
            }
            if (argument.value_kind == cir::TemplateValueKind::Boolean) {
                return with_expansion(
                    argument.integer_value.is_zero() ? "false" : "true");
            }
            if (argument.value_kind == cir::TemplateValueKind::Floating) {
                return with_expansion(
                    floating::display(argument.floating_value));
            }
            if (argument.value_kind == cir::TemplateValueKind::Null) {
                return with_expansion("nullptr");
            }
            if (argument.value_kind == cir::TemplateValueKind::Address) {
                std::string name = entity_display(argument.value_entity);
                return with_expansion(
                    "&" + (name.empty() ? std::string("<address>") : name));
            }
            if (argument.value_kind == cir::TemplateValueKind::MemberPointer) {
                if (!argument.value_entity.valid()) {
                    return with_expansion("<member>");
                }
                std::string name = entity_display(argument.value_entity);
                return with_expansion(
                    "&" + (name.empty() ? std::string("<member>") : name));
            }
            if (argument.value_kind == cir::TemplateValueKind::Closure) {
                return with_expansion(
                    type_display(argument.value_type) + "{}");
            }
            if (argument.value_kind ==
                cir::TemplateValueKind::StructuralObject) {
                std::string display =
                    type_display(argument.value_type) + "{";
                for (size_t i = 0; i < argument.value_elements.size(); ++i) {
                    if (i > 0) {
                        display += ", ";
                    }
                    display +=
                        template_argument_display(argument.value_elements[i]);
                }
                display += "}";
                return with_expansion(std::move(display));
            }
            return with_expansion(argument.integer_value.decimal());
        case cir::TemplateArgumentKind::Template:
            if (template_argument_has_dependent_template_name(argument)) {
                return with_expansion(
                    type_display(argument.dependent_template_qualifier) +
                    "::template " +
                    std::string(file_.name(argument.template_name)));
            }
            if (argument.template_entity.valid() &&
                file_.valid(argument.template_entity)) {
                std::string name = entity_display(argument.template_entity);
                if (!name.empty()) {
                    return with_expansion(name);
                }
                return with_expansion(std::string(
                    file_.name(file_.entity(argument.template_entity).name)));
            }
            if (argument.template_name.valid()) {
                return with_expansion(
                    std::string(file_.name(argument.template_name)));
            }
            return with_expansion("<template>");
    }
    return {};
}

std::string Session::template_display_name(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments) const {

    std::string display = info.name + "<";
    for (size_t i = 0; i < arguments.size(); ++i) {
        if (i > 0) {
            display += ", ";
        }
        display += template_argument_display(arguments[i]);
    }
    display += ">";
    return display;
}

std::string Session::template_argument_completion_memo_key(
    const TemplateInfo& info,
    const TemplateArgumentBindings& bindings) const {
    std::string key;
    key.reserve(24 + bindings.size() * 24);
    append_key_word(key,
                    static_cast<uint64_t>(MemoKeyFamily::DefaultCompletion));
    append_key_word(key, info.entity.index);
    for (const TemplateArgumentBinding& binding : bindings) {
        if (binding.is_single()) {
            if (!binding.arguments.empty()) {
                append_key_word(key, 1);
                append_template_argument_identity_key(
                    key, binding.arguments.front());
            } else {
                append_key_word(key, 2);
            }
        } else if (binding.is_pack()) {
            append_key_word(key, 3);
            append_key_word(key, binding.arguments.size());
            for (const TemplateArgument& argument : binding.arguments) {
                append_template_argument_identity_key(key, argument);
            }
        } else {
            append_key_word(key, 4);
        }
    }
    return key;
}

std::string Session::template_argument_completion_display(
    const TemplateInfo& info,
    const TemplateArgumentBindings& bindings) const {
    std::string display = "default template arguments for " + info.name + "<";
    for (size_t i = 0; i < bindings.size(); ++i) {
        if (i > 0) {
            display += ", ";
        }
        const TemplateArgumentBinding& binding = bindings[i];
        if (binding.is_single() && !binding.arguments.empty()) {
            display += template_argument_display(binding.arguments.front());
        } else if (binding.is_pack()) {
            display += "...";
        } else {
            display += "?";
        }
    }
    display += ">";
    return display;
}

std::string Session::template_argument_list_parsing_memo_key(
    const TemplateInfo& info,
    SrcLoc loc) const {
    std::string key;
    key.reserve(24);
    append_key_word(key,
                    static_cast<uint64_t>(MemoKeyFamily::ArgumentListParsing));
    append_key_word(key, info.entity.index);
    append_key_word(key, loc.offset);
    return key;
}

std::string Session::template_argument_list_parsing_display(
    const TemplateInfo& info) const {
    return "template arguments for " + info.name;
}

cir::EntityId Session::cached_instantiation(const std::string& key) const {
    auto found = tstate().instantiation_cache_.find(key);
    if (found == tstate().instantiation_cache_.end() ||
        !file_.valid(found->second)) {
        bump_template_counter(PerfCounter::InstantiationCacheMisses);
        return cir::EntityId{};
    }
    bump_template_counter(PerfCounter::InstantiationCacheHits);
    return found->second;
}

void Session::add_template_out_of_line_member(cir::EntityId entity,
                                              size_t begin,
                                              size_t end,
                                              bool is_template_declaration,
                                              bool is_static_data_member_definition,
                                              std::vector<TemplateParameter> head_parameters,
                                              std::vector<uint32_t> head_parameter_owner_slots) {
    uint64_t key = static_cast<uint64_t>(entity.index);
    auto found = tstate().templates_.find(key);
    if (found != tstate().templates_.end()) {
        journal_speculative_vector_size(
            "template out-of-line member list",
            found->second.out_of_line_members);
        found->second.out_of_line_members.push_back(
            {begin, end, is_template_declaration,
             is_static_data_member_definition,
             std::move(head_parameters),
             std::move(head_parameter_owner_slots)});
    }
}

SrcLoc Session::register_explicit_member_function_specialization_declaration(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    std::string_view member_name,
    cir::TypeRef member_type,
    SrcLoc loc) {
    if (!info.entity.valid() || !member_type.type.valid()) {
        return {};
    }

    uint64_t key = static_cast<uint64_t>(info.entity.index);
    auto found = tstate().templates_.find(key);
    if (found == tstate().templates_.end()) {
        return {};
    }

    std::string owner_memo_key = template_memo_key(info.entity, arguments);
    SrcLoc first_required_loc{};
    if (cir::EntityId owner = cached_instantiation(owner_memo_key);
        owner.valid() && file_.valid(owner)) {
        if (const cir::RecordFacts* facts = file_.record_facts(owner)) {
            for (const cir::RecordMethodFact& fact : facts->methods) {
                if (!fact.entity.valid() || !fact.name.valid() ||
                    file_.name(fact.name) != member_name ||
                    !types_compatible(fact.type, member_type)) {
                    continue;
                }
                if (!fact.first_required_loc.isInvalid()) {
                    first_required_loc = fact.first_required_loc;
                }
                break;
            }
        }
    }

    for (const TemplateInfo::ExplicitMemberFunctionSpecialization& entry :
         found->second.explicit_member_function_specializations) {
        if (entry.owner_memo_key == owner_memo_key &&
            entry.member_name == member_name &&
            types_compatible(entry.member_type, member_type)) {
            return first_required_loc;
        }
    }

    journal_speculative_vector_size(
        "explicit member function specialization list",
        found->second.explicit_member_function_specializations);
    found->second.explicit_member_function_specializations.push_back(
        TemplateInfo::ExplicitMemberFunctionSpecialization{
            std::move(owner_memo_key),
            std::string(member_name),
            member_type,
            loc});
    return first_required_loc;
}

bool Session::explicit_member_function_specialization_declared(
    cir::EntityId method,
    SrcLoc* declaration_loc) const {
    std::vector<TemplateArgument> arguments;
    const TemplateInfo* info =
        member_instantiation_template(method, &arguments);
    if (!info || info->explicit_member_function_specializations.empty()) {
        return false;
    }

    const cir::RecordMethodFact* fact = file_.method_fact(method);
    if (!fact || !fact->name.valid()) {
        return false;
    }
    std::string owner_memo_key = template_memo_key(info->entity, arguments);
    std::string_view method_name = file_.name(fact->name);
    for (const TemplateInfo::ExplicitMemberFunctionSpecialization& entry :
         info->explicit_member_function_specializations) {
        if (entry.owner_memo_key == owner_memo_key &&
            entry.member_name == method_name &&
            types_compatible(entry.member_type, fact->type)) {
            if (declaration_loc) {
                *declaration_loc = entry.loc;
            }
            return true;
        }
    }
    return false;
}

SrcLoc Session::register_explicit_static_data_member_specialization_declaration(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    std::string_view member_name,
    cir::TypeRef member_type,
    SrcLoc loc) {
    if (!info.entity.valid() || !member_type.type.valid()) {
        return {};
    }

    uint64_t key = static_cast<uint64_t>(info.entity.index);
    auto found = tstate().templates_.find(key);
    if (found == tstate().templates_.end()) {
        return {};
    }

    std::string owner_memo_key = template_memo_key(info.entity, arguments);
    SrcLoc previous_definition_loc{};
    if (cir::EntityId owner = cached_instantiation(owner_memo_key);
        owner.valid() && file_.valid(owner)) {
        if (const cir::RecordFacts* facts = file_.record_facts(owner)) {
            for (const cir::RecordStaticDataMemberFact& fact :
                 facts->static_data_members) {
                if (!fact.entity.valid() || !fact.name.valid() ||
                    file_.name(fact.name) != member_name ||
                    !types_compatible(fact.type, member_type)) {
                    continue;
                }
                const cir::Entity& entity = file_.entity(fact.entity);
                if (entity.is_definition && entity.has_static_initializer) {
                    previous_definition_loc = entity.loc;
                }
                break;
            }
        }
    }

    for (const TemplateInfo::ExplicitStaticDataMemberSpecialization& entry :
         found->second.explicit_static_data_member_specializations) {
        if (entry.owner_memo_key == owner_memo_key &&
            entry.member_name == member_name &&
            types_compatible(entry.member_type, member_type)) {
            return {};
        }
    }

    journal_speculative_vector_size(
        "explicit static data member specialization list",
        found->second.explicit_static_data_member_specializations);
    found->second.explicit_static_data_member_specializations.push_back(
        TemplateInfo::ExplicitStaticDataMemberSpecialization{
            std::move(owner_memo_key),
            std::string(member_name),
            member_type,
            loc});
    return previous_definition_loc;
}

bool Session::explicit_static_data_member_specialization_declared(
    cir::EntityId member,
    SrcLoc* declaration_loc) const {
    if (!member.valid() || !file_.valid(member)) {
        return false;
    }
    cir::EntityId record_entity = file_.entity(member).parent;
    if (!record_entity.valid() || !file_.valid(record_entity)) {
        return false;
    }
    const cir::TemplateSpecializationFact* fact =
        file_.template_specialization(record_entity);
    if (!fact || !fact->template_entity.valid()) {
        return false;
    }
    auto found =
        tstate().templates_.find(static_cast<uint64_t>(fact->template_entity.index));
    if (found == tstate().templates_.end() ||
        found->second.explicit_static_data_member_specializations.empty()) {
        return false;
    }

    const cir::Entity& entity = file_.entity(member);
    if (!entity.name.valid()) {
        return false;
    }
    std::string owner_memo_key =
        template_memo_key(found->second.entity, fact->argument_bindings);
    cir::TypeRef member_type = file_.type_ref(entity.type,
                                              entity.qualifiers);
    std::string_view member_name = file_.name(entity.name);
    for (const TemplateInfo::ExplicitStaticDataMemberSpecialization& entry :
         found->second.explicit_static_data_member_specializations) {
        if (entry.owner_memo_key == owner_memo_key &&
            entry.member_name == member_name &&
            types_compatible(entry.member_type, member_type)) {
            if (declaration_loc) {
                *declaration_loc = entry.loc;
            }
            return true;
        }
    }
    return false;
}

void Session::rename_entity(cir::EntityId entity, std::string_view name) {
    if (entity.valid() && file_.valid(entity)) {
        file_.entity_mut(entity).name = file_.intern_name(name);
    }
}

void Session::remember_instantiation(const std::string& key,
                                     cir::EntityId entity) {

    auto found = tstate().instantiation_cache_.find(key);
    if (found != tstate().instantiation_cache_.end() &&
        !file_.valid(found->second)) {

        tstate().instantiation_cache_.erase(found);
    }
    if (!tstate().instantiation_cache_.contains(key)) {
        journal_speculative_map_entry(
            "template instantiation cache", tstate().instantiation_cache_,
            key);
        tstate().instantiation_cache_.emplace(key, entity);
    }
}

void Session::replace_instantiation(const std::string& key,
                                    cir::EntityId entity) {
    auto found = tstate().instantiation_cache_.find(key);
    if (found == tstate().instantiation_cache_.end()) {
        remember_instantiation(key, entity);
        return;
    }
    journal_speculative_map_entry(
        "template instantiation cache", tstate().instantiation_cache_, key);
    found->second = entity;
}

bool Session::declare_explicit_instantiation_declaration(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    AttributeList attrs) {
    if (!info.entity.valid()) {
        return false;
    }
    if (entity_has_internal_name_linkage(info.entity)) {
        report_error(
            "explicit instantiation declaration shall not name a specialization of a template with internal linkage",
            loc);
        return false;
    }
    if (explicit_template_specialization_declared(info, arguments)) {
        return true;
    }
    std::string key = template_memo_key(info.entity, arguments);
    auto previous = tstate().explicit_instantiation_declarations_.find(key);
    if (previous != tstate().explicit_instantiation_declarations_.end()) {
        if (!attrs.empty()) {
            journal_speculative_map_entry(
                "explicit instantiation declaration cache",
                tstate().explicit_instantiation_declarations_,
                key);
            previous->second.attrs.append(std::move(attrs));
        }
        return true;
    }
    journal_speculative_map_entry(
        "explicit instantiation declaration cache",
        tstate().explicit_instantiation_declarations_, key);
    tstate().explicit_instantiation_declarations_.emplace(
        key,
        TemplateState::ExplicitInstantiationDeclaration{
            info.entity,
            arguments,
            loc,
            std::move(attrs)});
    return true;
}

bool Session::explicit_instantiation_declaration_declared(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc* declaration_loc) const {
    if (!info.entity.valid()) {
        return false;
    }
    std::string key = template_memo_key(info.entity, arguments);
    auto found = tstate().explicit_instantiation_declarations_.find(key);
    if (found == tstate().explicit_instantiation_declarations_.end()) {
        return false;
    }
    if (declaration_loc) {
        *declaration_loc = found->second.loc;
    }
    return true;
}

void Session::declare_explicit_instantiation_definition(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    AttributeList attrs) {
    if (!info.entity.valid()) {
        return;
    }
    if (explicit_template_specialization_declared(info, arguments)) {
        return;
    }
    std::string key = template_memo_key(info.entity, arguments);
    auto previous = tstate().explicit_instantiation_definitions_.find(key);
    if (previous != tstate().explicit_instantiation_definitions_.end()) {
        if (!attrs.empty()) {
            journal_speculative_map_entry(
                "explicit instantiation definition cache",
                tstate().explicit_instantiation_definitions_,
                key);
            previous->second.attrs.append(std::move(attrs));
        }
        return;
    }
    journal_speculative_map_entry(
        "explicit instantiation definition cache",
        tstate().explicit_instantiation_definitions_, key);
    tstate().explicit_instantiation_definitions_.emplace(
        key,
        TemplateState::ExplicitInstantiationDeclaration{
            info.entity,
            arguments,
            loc,
            std::move(attrs)});
}

bool Session::explicit_instantiation_definition_declared(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc* definition_loc) const {
    if (!info.entity.valid()) {
        return false;
    }
    std::string key = template_memo_key(info.entity, arguments);
    auto found = tstate().explicit_instantiation_definitions_.find(key);
    if (found == tstate().explicit_instantiation_definitions_.end()) {
        return false;
    }
    if (definition_loc) {
        *definition_loc = found->second.loc;
    }
    return true;
}

void Session::mark_explicit_template_specialization(cir::EntityId entity) {
    if (entity.valid() && file_.valid(entity)) {
        file_.entity_mut(entity).is_explicit_template_specialization = true;
    }
}

bool Session::is_explicit_template_specialization(
    cir::EntityId entity) const {
    return entity.valid() && file_.valid(entity) &&
           file_.entity(entity).is_explicit_template_specialization;
}

bool Session::explicit_template_specialization_declared(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    cir::EntityId* specialization) const {
    if (!info.entity.valid()) {
        return false;
    }
    cir::EntityId cached = cached_instantiation(
        template_memo_key(info.entity, arguments));
    if (!is_explicit_template_specialization(cached)) {
        return false;
    }
    if (specialization) {
        *specialization = cached;
    }
    return true;
}

void Session::apply_explicit_instantiation_declaration_suppression(
    cir::EntityId entity,
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments) {
    if (!entity.valid() || !file_.valid(entity) ||
        !explicit_instantiation_declaration_declared(info, arguments) ||
        explicit_instantiation_definition_declared(info, arguments)) {
        return;
    }
    std::string key = template_memo_key(info.entity, arguments);
    auto declaration =
        tstate().explicit_instantiation_declarations_.find(key);
    if (declaration !=
            tstate().explicit_instantiation_declarations_.end() &&
        !declaration->second.attrs.empty()) {
        apply_attributes(
            entity,
            explicit_instantiation_attribute_target(file_.entity(entity)),
            declaration->second.attrs,
            declaration->second.loc);
    }
    if (file_.entity(entity).kind == cir::EntityKind::Record) {
        return;
    }
    if (explicit_instantiation_declaration_leaves_specialization_undeclared(
            entity)) {
        return;
    }
    suppress_entity_for_explicit_instantiation_declaration(entity);
}

bool Session::explicit_instantiation_declaration_leaves_specialization_undeclared(
    cir::EntityId entity) const {
    if (!entity.valid() || !file_.valid(entity)) {
        return false;
    }
    const cir::Entity& subject = file_.entity(entity);
    return file_.valid(subject.placeholder_result) ||
           function_has_placeholder_return(subject.type);
}

void Session::apply_explicit_instantiation_definition_emission(
    cir::EntityId entity,
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments) {
    if (!entity.valid() || !file_.valid(entity) ||
        !explicit_instantiation_definition_declared(info, arguments)) {
        return;
    }
    cir::Entity& record = file_.entity_mut(entity);
    std::string key = template_memo_key(info.entity, arguments);
    auto definition =
        tstate().explicit_instantiation_definitions_.find(key);
    if (definition !=
            tstate().explicit_instantiation_definitions_.end() &&
        !definition->second.attrs.empty()) {
        apply_attributes(
            entity,
            explicit_instantiation_attribute_target(record),
            definition->second.attrs,
            definition->second.loc);
    }
    record.suppressed_by_explicit_instantiation_declaration = false;
    record.is_explicit_instantiation_definition = true;
    if (record.kind != cir::EntityKind::Record && record.is_definition &&
        record.linkage == cir::LinkageKind::External) {
        record.linkage = cir::LinkageKind::LinkOnceODR;
    }
}

void Session::apply_class_explicit_instantiation_declaration_suppression(
    cir::EntityId record_entity,
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments) {
    if (!record_entity.valid() || !file_.valid(record_entity) ||
        file_.entity(record_entity).kind != cir::EntityKind::Record ||
        !explicit_instantiation_declaration_declared(info, arguments) ||
        explicit_instantiation_definition_declared(info, arguments)) {
        return;
    }
    file_.entity_mut(record_entity)
        .suppressed_by_explicit_instantiation_declaration = true;
    suppress_record_methods_for_explicit_instantiation_declaration(
        record_entity);
}

void Session::apply_record_explicit_instantiation_declaration_suppression(
    cir::EntityId record_entity) {
    if (!record_entity.valid() || !file_.valid(record_entity) ||
        file_.entity(record_entity).kind != cir::EntityKind::Record ||
        !explicit_entity_instantiation_declaration_declared(record_entity)) {
        return;
    }
    file_.entity_mut(record_entity)
        .suppressed_by_explicit_instantiation_declaration = true;
    suppress_record_methods_for_explicit_instantiation_declaration(
        record_entity);
}

void Session::apply_record_explicit_instantiation_definition_emission(
    cir::EntityId record_entity) {
    if (!record_entity.valid() || !file_.valid(record_entity) ||
        file_.entity(record_entity).kind != cir::EntityKind::Record ||
        !explicit_entity_instantiation_definition_declared(record_entity)) {
        return;
    }
    file_.entity_mut(record_entity)
        .suppressed_by_explicit_instantiation_declaration = false;
    file_.entity_mut(record_entity).is_explicit_instantiation_definition =
        true;
    const cir::RecordFacts* facts = file_.record_facts(record_entity);
    if (!facts) {
        return;
    }
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (!method.entity.valid() || !file_.valid(method.entity) ||
            template_info(method.entity)) {
            continue;
        }
        cir::Entity& entity = file_.entity_mut(method.entity);
        if (entity.attr_facts.is_excluded_from_explicit_instantiation) {
            continue;
        }
        entity.suppressed_by_explicit_instantiation_declaration = false;
        entity.is_explicit_instantiation_definition = true;
        if (entity.is_definition &&
            entity.linkage == cir::LinkageKind::External) {
            entity.linkage = cir::LinkageKind::LinkOnceODR;
        }
    }
}

void Session::suppress_record_methods_for_explicit_instantiation_declaration(
    cir::EntityId record_entity) {
    if (!record_entity.valid() || !file_.valid(record_entity) ||
        file_.entity(record_entity).kind != cir::EntityKind::Record) {
        return;
    }
    const cir::RecordFacts* facts = file_.record_facts(record_entity);
    if (!facts) {
        return;
    }
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (!method.entity.valid() || !file_.valid(method.entity) ||
            template_info(method.entity)) {
            continue;
        }
        if (file_.entity(method.entity)
                .attr_facts.is_excluded_from_explicit_instantiation) {
            continue;
        }
        suppress_entity_for_explicit_instantiation_declaration(method.entity);
    }
}

bool Session::declare_explicit_entity_instantiation_declaration(
    cir::EntityId entity,
    SrcLoc loc,
    AttributeList attrs) {
    if (!entity.valid() || !file_.valid(entity)) {
        return false;
    }
    cir::EntityId origin = entity;
    cir::EntityId owner = file_.entity(entity).parent;
    while (owner.valid() && file_.valid(owner)) {
        if (const cir::TemplateSpecializationFact* specialization =
                file_.template_specialization(owner)) {
            if (specialization->template_entity.valid()) {
                origin = specialization->template_entity;
                break;
            }
        }
        owner = file_.entity(owner).parent;
    }
    if (entity_has_internal_name_linkage(origin)) {
        report_error(
            "explicit instantiation declaration shall not name a specialization of a template with internal linkage",
            loc);
        return false;
    }
    if (is_explicit_template_specialization(entity)) {
        return true;
    }
    apply_attributes(entity,
                     explicit_instantiation_attribute_target(
                         file_.entity(entity)),
                     attrs,
                     loc);
    uint64_t key = static_cast<uint64_t>(entity.index);
    auto previous = tstate().explicit_entity_instantiation_declarations_.find(key);
    if (previous == tstate().explicit_entity_instantiation_declarations_.end()) {
        journal_speculative_map_entry(
            "explicit entity instantiation declaration cache",
            tstate().explicit_entity_instantiation_declarations_, key);
        tstate().explicit_entity_instantiation_declarations_.emplace(key, loc);
    }
    if (explicit_entity_instantiation_definition_declared(entity)) {
        return true;
    }
    suppress_entity_for_explicit_instantiation_declaration(entity);
    apply_record_explicit_instantiation_declaration_suppression(entity);
    return true;
}

bool Session::explicit_entity_instantiation_declaration_declared(
    cir::EntityId entity,
    SrcLoc* declaration_loc) const {
    if (!entity.valid()) {
        return false;
    }
    auto found = tstate().explicit_entity_instantiation_declarations_.find(
        static_cast<uint64_t>(entity.index));
    if (found == tstate().explicit_entity_instantiation_declarations_.end()) {
        return false;
    }
    if (declaration_loc) {
        *declaration_loc = found->second;
    }
    return true;
}

void Session::declare_explicit_entity_instantiation_definition(
    cir::EntityId entity,
    SrcLoc loc,
    AttributeList attrs) {
    if (!entity.valid() || !file_.valid(entity)) {
        return;
    }
    if (is_explicit_template_specialization(entity)) {
        return;
    }
    apply_attributes(entity,
                     explicit_instantiation_attribute_target(
                         file_.entity(entity)),
                     attrs,
                     loc);
    uint64_t key = static_cast<uint64_t>(entity.index);
    auto previous = tstate().explicit_entity_instantiation_definitions_.find(key);
    if (previous != tstate().explicit_entity_instantiation_definitions_.end()) {
        return;
    }
    journal_speculative_map_entry(
        "explicit entity instantiation definition cache",
        tstate().explicit_entity_instantiation_definitions_, key);
    tstate().explicit_entity_instantiation_definitions_.emplace(key, loc);
}

bool Session::explicit_entity_instantiation_definition_declared(
    cir::EntityId entity,
    SrcLoc* definition_loc) const {
    if (!entity.valid()) {
        return false;
    }
    auto found = tstate().explicit_entity_instantiation_definitions_.find(
        static_cast<uint64_t>(entity.index));
    if (found == tstate().explicit_entity_instantiation_definitions_.end()) {
        return false;
    }
    if (definition_loc) {
        *definition_loc = found->second;
    }
    return true;
}

void Session::apply_explicit_entity_instantiation_definition_emission(
    cir::EntityId entity) {
    if (!entity.valid() || !file_.valid(entity) ||
        !explicit_entity_instantiation_definition_declared(entity)) {
        return;
    }
    cir::Entity& record = file_.entity_mut(entity);
    record.suppressed_by_explicit_instantiation_declaration = false;
    record.is_explicit_instantiation_definition = true;
    if (record.kind != cir::EntityKind::Record && record.is_definition &&
        record.linkage == cir::LinkageKind::External) {
        record.linkage = cir::LinkageKind::LinkOnceODR;
    }
}

void Session::suppress_entity_for_explicit_instantiation_declaration(
    cir::EntityId entity) {
    if (!entity.valid() || !file_.valid(entity)) {
        return;
    }
    cir::Entity& record = file_.entity_mut(entity);
    record.suppressed_by_explicit_instantiation_declaration = true;
    if (record.linkage == cir::LinkageKind::LinkOnceODR) {
        record.linkage = cir::LinkageKind::External;
    }
}

void Session::remember_template_specialization(
    cir::EntityId entity,
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc point_of_instantiation,
    uint64_t point_lookup_generation,
    const TemplateInfo* selected_info,
    const std::vector<TemplateArgument>* selected_arguments,
    const TemplateArgumentBindings* exact_bindings,
    const TemplateArgumentBindings* selected_exact_bindings) {

    if (!entity.valid()) {
        return;
    }
    if (point_lookup_generation == 0 && !point_of_instantiation.isInvalid()) {
        point_lookup_generation = current_point_lookup_generation();
        if (point_lookup_generation == 0) {
            point_lookup_generation = lookup_generation_;
        }
    }
    cir::TemplateSpecializationFact fact;
    if (const cir::TemplateSpecializationFact* existing =
            file_.template_specialization(entity)) {
        fact.selected_template_entity = existing->selected_template_entity;
        fact.selected_argument_bindings =
            existing->selected_argument_bindings;
        fact.selected_dependent_arguments =
            existing->selected_dependent_arguments;
        fact.instantiation_demands = existing->instantiation_demands;
        if (point_of_instantiation.isInvalid()) {
            point_of_instantiation = existing->point_of_instantiation;
        }
        if (point_lookup_generation == 0) {
            point_lookup_generation = existing->point_lookup_generation;
        }
    }
    fact.template_entity = info.entity;
    fact.template_param_index = info.template_parameter_index;
    fact.point_of_instantiation = point_of_instantiation;
    fact.point_lookup_generation = point_lookup_generation;
    auto argument_is_dependent_recipe =
        [&](const TemplateArgument& argument) {
            return argument.is_dependent ||
                argument.expands_parameter_pack ||
                argument.expands_pack_pattern ||
                (template_argument_is_type(argument) &&
                 is_dependent_type(argument.type.type));
        };
    TemplateArgumentBindings bindings;
    bool has_grouped_identity = true;
    if (exact_bindings) {
        bindings = *exact_bindings;
    } else {
        TemplateArgumentBindingMode mode =
            !info.is_class_template && !info.is_alias_template &&
                    !info.is_variable_template && !info.is_concept
            ? TemplateArgumentBindingMode::DeducedCanonical
            : TemplateArgumentBindingMode::Canonical;
        if (!bind_template_arguments_to_parameters(info.parameters,
                                                   arguments,
                                                   bindings,
                                                   nullptr,
                                                   mode)) {
            if (!std::any_of(arguments.begin(),
                             arguments.end(),
                             argument_is_dependent_recipe)) {
                return;
            }
            has_grouped_identity = false;
        }
    }
    auto canonicalize_bindings =
        [&](const std::vector<TemplateParameter>& parameters,
            TemplateArgumentBindings& argument_bindings) {
            for (size_t slot = 0; slot < argument_bindings.size(); ++slot) {
                for (cir::TemplateArgument& argument :
                     argument_bindings[slot].arguments) {
                    argument.is_defaulted = false;
                    if (template_argument_is_type(argument)) {
                        argument.type = cir::TypeRef{
                            file_.resolved_type(argument.type.type),
                            argument.type.qualifiers,
                            argument.type.memory_space};
                    } else if (template_argument_is_value(argument)) {
                        cir::TypeId value_type =
                            template_argument_value_type_id(argument);
                        if (!value_type.valid() &&
                            slot < parameters.size() &&
                            parameters[slot].non_type_type.valid()) {
                            value_type = parameters[slot].non_type_type;
                        }
                        if (!value_type.valid()) {
                            value_type = builder_.int_type();
                        }
                        argument.value_type = cir::TypeRef{
                            file_.resolved_type(value_type),
                            argument.value_type.qualifiers,
                            argument.value_type.memory_space};
                        if (argument.value_kind ==
                            cir::TemplateValueKind::None) {
                            argument.value_kind =
                                file_.template_value_kind_for_type(value_type);
                            argument.null_kind =
                                null_kind_for_value_kind(
                                    file_,
                                    value_type,
                                    argument.value_kind);
                        }
                    }
                }
            }
        };
    canonicalize_bindings(info.parameters, bindings);
    if (has_grouped_identity) {
        fact.argument_bindings = std::move(bindings);
    } else {
        fact.dependent_arguments = arguments;
        for (TemplateArgument& argument : fact.dependent_arguments) {
            argument.is_defaulted = false;
            if (template_argument_is_type(argument)) {
                argument.type.type =
                    file_.resolved_type(argument.type.type);
            } else if (template_argument_is_value(argument) &&
                       argument.value_type.type.valid()) {
                argument.value_type.type =
                    file_.resolved_type(argument.value_type.type);
            }
        }
    }
    if ((info.is_class_template || info.is_variable_template) &&
        !fact.selected_template_entity.valid()) {
        fact.selected_template_entity = selected_info
            ? (selected_info->entity.valid()
                   ? selected_info->entity
                   : template_validation_entity(*selected_info))
            : (info.entity.valid()
                   ? info.entity
                   : template_validation_entity(info));
        if (selected_exact_bindings) {
            fact.selected_argument_bindings = *selected_exact_bindings;
        } else if (selected_arguments) {
            const TemplateInfo& selected = selected_info
                ? *selected_info
                : info;
            if (!bind_template_arguments_to_parameters(
                    selected.parameters,
                    *selected_arguments,
                    fact.selected_argument_bindings)) {
                if (!std::any_of(selected_arguments->begin(),
                                 selected_arguments->end(),
                                 argument_is_dependent_recipe)) {
                    return;
                }
                fact.selected_dependent_arguments =
                    *selected_arguments;
            }
        } else {
            fact.selected_argument_bindings =
                fact.argument_bindings;
            fact.selected_dependent_arguments =
                fact.dependent_arguments;
        }
        canonicalize_bindings(
            selected_info ? selected_info->parameters : info.parameters,
            fact.selected_argument_bindings);
    }

    if (!info.is_class_template) {
        fact.pattern_type = info.pattern_type;
    }
    file_.set_template_specialization(entity, std::move(fact));
    if (file_.template_context_references_internal_entity(entity)) {
        file_.entity_mut(entity).linkage = cir::LinkageKind::Internal;
    }
}

const std::vector<Session::TemplateInstantiationRequest>&
Session::template_instantiation_requests() const {
    return tstate().template_instantiation_requests_;
}

const Session::TemplateInstantiationRequest*
Session::template_instantiation_request_by_id(uint64_t request_id) const {
    if (request_id == 0 ||
        request_id > tstate().template_instantiation_requests_.size()) {
        return nullptr;
    }
    return &tstate().template_instantiation_requests_[request_id - 1];
}

uint64_t Session::record_template_instantiation_request(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation,
    TemplateInstantiationRequestKind kind) {
    return record_template_instantiation_request_with_identity(
        info,
        template_memo_key(info.entity, arguments),
        template_display_name(info, arguments),
        loc,
        point_lookup_generation,
        kind);
}

uint64_t Session::record_template_instantiation_request_with_identity(
    const TemplateInfo& info,
    std::string memo_key,
    std::string display_name,
    SrcLoc loc,
    uint64_t point_lookup_generation,
    TemplateInstantiationRequestKind kind) {
    bump_template_counter(PerfCounter::TemplateInstantiationRequests);
    point_lookup_generation =
        template_instantiation_point_generation(point_lookup_generation);
    uint64_t parent_id = active_instantiations_.empty()
        ? 0
        : active_instantiations_.back().request_id;
    uint64_t duplicate_of_id = 0;
    for (auto it = active_instantiations_.rbegin();
         it != active_instantiations_.rend(); ++it) {
        const TemplateInstantiationRequest* active_request =
            template_instantiation_request_by_id(it->request_id);
        if (active_request && active_request->memo_key == memo_key) {
            duplicate_of_id = active_request->id;
            break;
        }
    }
    uint64_t request_id =
        static_cast<uint64_t>(tstate().template_instantiation_requests_.size() + 1);
    journal_speculative_vector_size(
        "template instantiation request log",
        tstate().template_instantiation_requests_);
    tstate().template_instantiation_requests_.push_back(TemplateInstantiationRequest{
        request_id,
        parent_id,
        duplicate_of_id,
        kind,
        info.entity,
        std::move(memo_key),
        std::move(display_name),
        loc,
        point_lookup_generation});
    return request_id;
}

size_t Session::active_template_instantiation_request_depth() const {
    return active_instantiations_.size();
}

void Session::report_template_instantiation_depth_limit(SrcLoc loc) {
    if (reported_instantiation_depth_limit_) {
        return;
    }
    report_error("template instantiation depth limit exceeded", loc);
    constexpr size_t note_limit = 8;
    auto active_point = [&](const ActiveInstantiation& active) {
        if (const TemplateInstantiationRequest* request =
                template_instantiation_request_by_id(active.request_id)) {
            return request->point;
        }
        return active.point;
    };
    auto active_display = [&](const ActiveInstantiation& active) {
        if (const TemplateInstantiationRequest* request =
                template_instantiation_request_by_id(active.request_id)) {
            std::string display = request->display_name;
            if (request->duplicate_of_id != 0) {
                display += " (recursive request)";
            }
            return display;
        }
        std::string display = active.display_name;
        if (!display.empty() && active.duplicate_request) {
            display += " (recursive request)";
        }
        return display;
    };
    size_t valid_points = 0;
    for (const ActiveInstantiation& active : active_instantiations_) {
        if (!active_point(active).isInvalid()) {
            ++valid_points;
        }
    }
    size_t emitted = 0;
    for (auto it = active_instantiations_.rbegin();
         it != active_instantiations_.rend() && emitted < note_limit; ++it) {
        SrcLoc point = active_point(*it);
        if (!point.isInvalid()) {
            std::string display = active_display(*it);
            report_note(display.empty()
                            ? "in instantiation requested here"
                            : "in instantiation requested here: " + display,
                        point);
            ++emitted;
        }
    }
    if (valid_points > emitted) {
        report_note("skipping " +
                        std::to_string(valid_points - emitted) +
                        " older instantiation contexts",
                    loc);
    }
    if (emitted > 0) {
        reported_instantiation_depth_limit_ = true;
        file_.pin_diagnostics();
    }
}

bool Session::check_template_replay_guard_depth(SrcLoc loc) {

    size_t depth = std::max(active_template_instantiation_request_depth(),
                            template_replay_guard_depth_);
    if (depth >= template_replay_guard_depth_limit_) {
        report_template_instantiation_depth_limit(loc);
        return false;
    }
    return true;
}

bool Session::check_template_instantiation_request_depth(SrcLoc loc) {
    record_template_counter_max(
        PerfCounter::MaxInstantiationDepth,
        active_template_instantiation_request_depth() + 1);
    if (active_template_instantiation_request_depth() >=
        template_instantiation_depth_limit_) {
        report_template_instantiation_depth_limit(loc);
        return false;
    }
    return true;
}

Session::TemplateArgumentListParsingScope
Session::begin_template_argument_list_parsing(
    const TemplateInfo& info,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    TemplateArgumentListParsingScope scope;
    if (!check_template_instantiation_request_depth(loc)) {
        return scope;
    }
    point_lookup_generation =
        template_instantiation_point_generation(point_lookup_generation);
    std::string display = template_argument_list_parsing_display(info);
    uint64_t request_id =
        record_template_instantiation_request_with_identity(
            info,
            template_argument_list_parsing_memo_key(info, loc),
            display,
            loc,
            point_lookup_generation,
            TemplateInstantiationRequestKind::TemplateArgumentListParsing);
    const TemplateInstantiationRequest* request =
        template_instantiation_request_by_id(request_id);
    active_instantiations_.push_back(ActiveInstantiation{
        0,
        loc,
        point_lookup_generation,
        request_id,
        std::move(display),
        request && request->duplicate_of_id != 0});
    scope.active = true;
    scope.point_lookup_generation = point_lookup_generation;
    return scope;
}

void Session::finish_template_argument_list_parsing(
    TemplateArgumentListParsingScope scope) {
    if (!scope.active) {
        return;
    }
    if (!active_instantiations_.empty()) {
        active_instantiations_.pop_back();
    }
}

Session::TemplateArgumentCompletionScope
Session::begin_template_argument_completion(
    const TemplateInfo& info,
    const TemplateArgumentBindings& bindings,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    TemplateArgumentCompletionScope scope;
    if (!check_template_instantiation_request_depth(loc)) {
        return scope;
    }
    point_lookup_generation =
        template_instantiation_point_generation(point_lookup_generation);
    std::string display = template_argument_completion_display(info, bindings);
    uint64_t request_id =
        record_template_instantiation_request_with_identity(
            info,
            template_argument_completion_memo_key(info, bindings),
            display,
            loc,
            point_lookup_generation,
            TemplateInstantiationRequestKind::TemplateArgumentCompletion);
    const TemplateInstantiationRequest* request =
        template_instantiation_request_by_id(request_id);
    active_instantiations_.push_back(ActiveInstantiation{
        0,
        loc,
        point_lookup_generation,
        request_id,
        std::move(display),
        request && request->duplicate_of_id != 0});
    scope.active = true;
    return scope;
}

void Session::finish_template_argument_completion(
    TemplateArgumentCompletionScope scope) {
    if (!scope.active) {
        return;
    }
    if (!active_instantiations_.empty()) {
        active_instantiations_.pop_back();
    }
}

bool Session::enter_template_replay_guard(SrcLoc loc) {
    if (!check_template_replay_guard_depth(loc)) {
        return false;
    }
    ++template_replay_guard_depth_;
    return true;
}

void Session::leave_template_replay_guard() {
    if (template_replay_guard_depth_ > 0) {
        --template_replay_guard_depth_;
    }
}

uint64_t Session::template_instantiation_point_generation(
    uint64_t point_lookup_generation) const {
    if (point_lookup_generation == 0 && !active_instantiations_.empty()) {
        point_lookup_generation =
            active_instantiations_.back().point_lookup_generation;
    }
    if (point_lookup_generation == 0) {
        point_lookup_generation = lookup_generation_;
    }
    return point_lookup_generation;
}

cir::EntityId Session::bind_template_template_parameter_placeholder(
    const TemplateParameter& parameter,
    SrcLoc loc) {
    if (parameter.name.empty()) {
        return {};
    }
    cir::EntityId placeholder = builder_.add_entity(
        cir::EntityKind::TemplateParam,
        parameter.name,
        {},
        {},
        loc);

    TemplateInfo placeholder_info;
    placeholder_info.entity = placeholder;
    placeholder_info.name = parameter.name;
    placeholder_info.template_parameter_index = parameter.index;
    placeholder_info.is_class_template =
        parameter.template_template_parameter_kind ==
        TemplateTemplateParameterKind::Type;
    placeholder_info.is_variable_template =
        parameter.template_template_parameter_kind ==
        TemplateTemplateParameterKind::Variable;
    placeholder_info.is_concept =
        parameter.template_template_parameter_kind ==
        TemplateTemplateParameterKind::Concept;
    placeholder_info.is_template_parameter_pack = parameter.is_parameter_pack;
    if (parameter.nested_head) {
        placeholder_info.parameters = parameter.nested_head->parameters;
        placeholder_info.introduced_constraints =
            parameter.nested_head->introduced_constraints;
    }
    placeholder_info.lexical_context = current_decl_context();

    uint64_t key = static_cast<uint64_t>(placeholder.index);
    tstate().templates_[key] = std::move(placeholder_info);
    if (!tstate().scoped_template_parameter_template_keys_.empty()) {
        tstate().scoped_template_parameter_template_keys_.back().push_back(key);
    }
    bind_entity(parameter.name,
                cir::LookupNamespace::Ordinary,
                placeholder,
                {},
                false,
                /*is_template_name=*/true,
                true,
                {},
                loc);
    return placeholder;
}

Session::OutOfLineHeadRebinding Session::bind_out_of_line_member_head(
    const TemplateInfo& head,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    OutOfLineHeadRebinding rebinding;
    rebinding.loc = loc;
    for (const TemplateParameter& parameter : head.parameters) {
        if (parameter.name.empty()) {
            continue;
        }
        const cir::Binding* previous =
            lookup_ordinary_binding(parameter.name, /*include_parents=*/false);
        rebinding.entries.push_back(
            {parameter.name,
             previous ? std::optional<cir::Binding>(*previous) : std::nullopt});
    }
    binding_out_of_line_member_head_ = true;
    bind_template_instantiation_parameters(head, arguments, loc);
    binding_out_of_line_member_head_ = false;
    return rebinding;
}

Session::OutOfLineHeadRebinding
Session::rebind_active_template_header_in_current_scope(SrcLoc loc) {
    if (!active_template_header_info_) {
        return {};
    }
    return bind_out_of_line_member_head(
        *active_template_header_info_,
        self_template_arguments(*active_template_header_info_),
        loc);
}

void Session::restore_out_of_line_member_head(
    const OutOfLineHeadRebinding& rebinding) {
    binding_out_of_line_member_head_ = true;
    for (const OutOfLineHeadRebinding::Entry& entry : rebinding.entries) {
        if (entry.previous.has_value() && entry.previous->is_type_name &&
            entry.previous->type.type.valid()) {

            DeclFlags flags;
            flags.type_qualifiers = entry.previous->type.qualifiers;
            declare_typedef(entry.name,
                            entry.previous->type.type,
                            rebinding.loc,
                            flags);
            continue;
        }

    }
    binding_out_of_line_member_head_ = false;
}

void Session::bind_template_instantiation_parameters(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    const TemplateArgumentBindings* exact_bindings) {
    struct InternalParameterBindingExit {
        bool& flag;
        bool previous = false;
        ~InternalParameterBindingExit() { flag = previous; }
    } internal_binding{binding_out_of_line_member_head_,
                       binding_out_of_line_member_head_};
    binding_out_of_line_member_head_ = true;
    TemplateArgumentBindings parameter_bindings;
    TemplateArgumentBindingMode binding_mode =
        !info.is_class_template && !info.is_alias_template &&
            !info.is_variable_template && !info.is_concept
        ? TemplateArgumentBindingMode::DeducedCanonical
        : TemplateArgumentBindingMode::Canonical;
    if (exact_bindings) {
        parameter_bindings = *exact_bindings;
    } else {
        if (!bind_template_arguments_to_parameters(info.parameters,
                                                   arguments,
                                                   parameter_bindings,
                                                   nullptr,
                                                   binding_mode)) {
            return;
        }
    }
    for (size_t i = 0; i < info.parameters.size(); ++i) {
        const TemplateParameter& parameter = info.parameters[i];
        const TemplateArgument* argument =
            i < parameter_bindings.size() &&
                parameter_bindings[i].is_single() &&
                !parameter_bindings[i].arguments.empty()
            ? &parameter_bindings[i].arguments.front()
            : nullptr;
        if (template_parameter_is_type(parameter)) {
            if (parameter.is_parameter_pack) {
                if (!parameter.name.empty()) {
                    cir::TypeId pack_type = parameter.type_param_type.valid()
                        ? parameter.type_param_type
                        : file_.type_param_type({},
                                                parameter.name,
                                                parameter.index,
                                                parameter.depth,
                                                /*is_parameter_pack=*/true);
                    declare_typedef(parameter.name, pack_type, loc);
                }
                continue;
            }
            if (argument && !parameter.name.empty()) {
                DeclFlags flags;
                flags.type_qualifiers = argument->type.qualifiers;
                DeclResult alias = declare_typedef(
                    parameter.name,
                    template_argument_type_id(*argument),
                    loc,
                    flags);
                if (alias.entity.valid() && file_.valid(alias.entity)) {
                    file_.entity_mut(alias.entity).memory_space =
                        argument->type.memory_space;
                }
                if (cir::Binding* binding = file_.mutable_ordinary_binding(
                        current_decl_context(), parameter.name)) {
                    binding->type.memory_space = argument->type.memory_space;
                }
            }
        } else if (template_parameter_is_value(parameter)) {
            if (parameter.is_parameter_pack) {
                if (parameter.name.empty()) {
                    continue;
                }
                cir::TypeId value_type = parameter.non_type_type.valid()
                    ? parameter.non_type_type
                    : builder_.int_type();
                cir::EntityId constant = builder_.add_entity(
                    cir::EntityKind::TemplateParam,
                    parameter.name,
                    value_type,
                    {},
                    loc);
                cir::Entity& record = file_.entity_mut(constant);
                record.has_constant_value = true;
                record.constant_value_kind =
                    file_.template_value_kind_for_type(value_type);
                record.constant_null_kind =
                    null_kind_for_value_kind(file_,
                                             value_type,
                                             record.constant_value_kind);
                cir::IntegerTypeShape shape =
                    cir::integer_shape_for_type(file_, value_type);
                record.constant_integer_value =
                    cir::IntegerValue::from_signed(0, shape.bit_width)
                        .cast(shape.bit_width, shape.is_unsigned);
                tstate().header_value_params_.emplace(
                    static_cast<uint64_t>(constant.index),
                    parameter.index);
                tstate().header_value_param_packs_.insert(
                    static_cast<uint64_t>(constant.index));
                bind_entity(parameter.name,
                            cir::LookupNamespace::Ordinary,
                            constant,
                            value_type,
                            false,
                            false,
                            true,
                            {},
                            loc);
                continue;
            }
            if (!argument || parameter.name.empty()) {
                continue;
            }
            cir::TypeId value_type = parameter.non_type_type.valid()
                ? parameter.non_type_type
                : builder_.int_type();
            if (class_template_placeholder_info(value_type) &&
                argument->value_type.type.valid()) {
                value_type = argument->value_type.type;
            } else if (type_contains_type_param(value_type)) {
                PatternInstantiationCallbacks callbacks;
                cir::TypeId substituted = substitute_pattern_type(
                    value_type, parameter_bindings, callbacks);
                if (substituted.valid()) {
                    value_type = substituted;
                }
            }
            if ((contains_auto_type(value_type) ||
                 class_template_placeholder_info(value_type)) &&
                argument->value_type.type.valid()) {
                value_type = argument->value_type.type;
            }
            cir::EntityId constant = builder_.add_entity(
                cir::EntityKind::TemplateParam,
                parameter.name,
                value_type,
                {},
                loc);
            if (argument->is_dependent &&
                !tstate().current_instantiation_frames_.empty()) {
                tstate().current_instantiation_frames_.back()
                    .dependent_value_bindings.emplace(
                        static_cast<uint64_t>(constant.index), *argument);
            }
            cir::TemplateValueKind parameter_value_kind =
                file_.template_value_kind_for_type(value_type);
            cir::TemplateValueKind constant_value_kind =
                argument->value_kind ==
                    cir::TemplateValueKind::None
                ? parameter_value_kind
                : argument->value_kind;
            if (parameter_value_kind ==
                    cir::TemplateValueKind::StructuralObject ||
                parameter_value_kind == cir::TemplateValueKind::Closure) {
                constant_value_kind = parameter_value_kind;
            }
            cir::TemplateNullKind constant_null_kind =
                argument->value_kind ==
                    cir::TemplateValueKind::None
                ? null_kind_for_value_kind(file_,
                                           value_type,
                                           constant_value_kind)
                : argument->null_kind;
            if (constant_value_kind ==
                    cir::TemplateValueKind::StructuralObject ||
                constant_value_kind == cir::TemplateValueKind::Closure) {
                constant_null_kind = cir::TemplateNullKind::None;
            }
            cir::EntityId parameter_object{};
            if (constant_value_kind ==
                    cir::TemplateValueKind::StructuralObject ||
                constant_value_kind == cir::TemplateValueKind::Closure) {
                TemplateArgument object_argument = *argument;
                object_argument.value_kind = constant_value_kind;
                parameter_object =
                    materialize_template_parameter_object(value_type,
                                                          object_argument,
                                                          parameter.name,
                                                          loc);
            }

            cir::Entity& record = file_.entity_mut(constant);
            record.has_constant_value = true;
            record.constant_value_kind = constant_value_kind;
            record.constant_null_kind = constant_null_kind;
            if (constant_value_kind == cir::TemplateValueKind::Integer) {
                cir::IntegerTypeShape shape =
                    cir::integer_shape_for_type(file_, value_type);
                record.constant_integer_value =
                    argument->integer_value.cast(shape.bit_width,
                                                 shape.is_unsigned);
            } else if (constant_value_kind ==
                       cir::TemplateValueKind::Boolean) {
                record.constant_integer_value =
                    cir::IntegerValue::from_unsigned(
                        argument->integer_value.is_zero() ? 0 : 1, 1);
            } else {
                record.constant_integer_value = argument->integer_value;
            }
            record.constant_floating_value = argument->floating_value;
            record.constant_entity = argument->value_entity;
            record.constant_closure_identity = argument->closure_identity;
            record.constant_byte_offset = argument->value_byte_offset;
            record.constant_value_elements = argument->value_elements;
            record.constant_meta_kind = argument->meta_kind;
            record.constant_meta_type = argument->type;
            record.template_parameter_object = parameter_object;
            bind_entity(parameter.name,
                        cir::LookupNamespace::Ordinary,
                        constant,
                        value_type,
                        false,
                        false,
                        true,
                        {},
                        loc);
        } else if (parameter.kind == TemplateParameterKind::Template) {
            if (parameter.is_parameter_pack) {
                (void)bind_template_template_parameter_placeholder(parameter,
                                                                   loc);
                continue;
            }
            if (!argument || parameter.name.empty() ||
                argument->kind != cir::TemplateArgumentKind::Template ||
                !argument->template_entity.valid()) {
                continue;
            }
            bind_entity(parameter.name,
                        cir::LookupNamespace::Ordinary,
                        argument->template_entity,
                        {},
                        false,
                        /*is_template_name=*/true,
                        true,
                        {},
                        loc);
        }
    }
}

bool Session::type_name_is_active_template_type_parameter(
    std::string_view name) const {
    if (name.empty()) {
        return false;
    }
    if (parameter_pack_replay_element(ParameterPackKind::Type, name)) {
        return true;
    }
    auto matches_type_parameter =
        [name](const std::vector<TemplateParameter>& parameters) {
        for (const TemplateParameter& parameter : parameters) {
            if (template_parameter_is_type(parameter) &&
                parameter.name == name) {
                return true;
            }
        }
        return false;
    };

    if ((validating_template_info_ &&
         matches_type_parameter(validating_template_info_->parameters)) ||
        (active_template_header_info_ &&
         matches_type_parameter(active_template_header_info_->parameters))) {
        return true;
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (!frame->info) {
            continue;
        }
        if (matches_type_parameter(frame->info->parameters)) {
            return true;
        }
        for (const TemplateInfo::TemplateInstantiationBinding& binding :
             frame->info->enclosing_instantiation_bindings) {
            if (matches_type_parameter(binding.parameters)) {
                return true;
            }
        }
    }
    return false;
}

Session::InstantiationScope Session::begin_template_instantiation(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation,
    cir::EntityId record_to_complete,
    const TemplateArgumentBindings* exact_bindings) {
    InstantiationScope scope;
    if (!check_template_instantiation_request_depth(loc)) {
        return scope;
    }
    scope.active = true;
    point_lookup_generation =
        template_instantiation_point_generation(point_lookup_generation);
    scope.saved_context = save_function_context();
    scope.saved_header_value_params = std::move(tstate().header_value_params_);
    scope.saved_header_value_param_packs =
        std::move(tstate().header_value_param_packs_);
    scope.saved_active_template_header_info = active_template_header_info_;
    tstate().header_value_params_.clear();
    tstate().header_value_param_packs_.clear();
    active_template_header_info_ = nullptr;
    scope.saved_collecting_pattern = collecting_pattern_;
    bool nested_in_template_pattern_replay = collecting_pattern_ ||
        (!tstate().current_instantiation_frames_.empty() &&
         tstate().current_instantiation_frames_.back()
             .replays_as_template_pattern);
    cir::EntityId lexical_owner =
        enclosing_record_for_context(info.lexical_context);
    bool declared_in_template_pattern_record =
        lexical_owner.valid() && file_.valid(lexical_owner) &&
        file_.entity(lexical_owner).is_template_pattern;
    bool replay_as_template_pattern =
        (nested_in_template_pattern_replay ||
         declared_in_template_pattern_record) &&
        info.entity.valid() && file_.valid(info.entity) &&
        file_.entity(info.entity).is_template_pattern;
    collecting_pattern_ = false;
    builder_.set_mark_template_pattern(replay_as_template_pattern);
    scope.saved_lookup_ceiling = lookup_generation_ceiling_;
    lookup_generation_ceiling_ = 0;
    scope.suspended_parameter_pack_pattern_capture = true;
    scope.parameter_pack_pattern_capture_suspension_depth =
        tstate().parameter_pack_pattern_capture_suspensions_.size();
    tstate().parameter_pack_pattern_capture_suspensions_.push_back(
        std::move(tstate().parameter_pack_pattern_captures_));
    tstate().parameter_pack_pattern_captures_.clear();
    scope.suspended_parameter_pack_element_replay = true;
    scope.parameter_pack_element_replay_suspension_depth =
        tstate().parameter_pack_element_replay_suspensions_.size();
    tstate().parameter_pack_element_replay_suspensions_.push_back(
        std::move(tstate().parameter_pack_element_replay_bindings_));
    tstate().parameter_pack_element_replay_bindings_ = {};
    std::string display = template_display_name(info, arguments);
    uint64_t request_id =
        record_template_instantiation_request(info,
                                              arguments,
                                              loc,
                                              point_lookup_generation,
                                              TemplateInstantiationRequestKind::
                                                  TemplateReplay);
    const TemplateInstantiationRequest* request =
        template_instantiation_request_by_id(request_id);
    active_instantiations_.push_back(ActiveInstantiation{
        static_cast<uint64_t>(info.entity.index),
        loc,
        point_lookup_generation,
        request_id,
        display,
        request && request->duplicate_of_id != 0});
    tstate().current_instantiation_frames_.push_back(TemplateState::CurrentInstantiationFrame{
        &info, template_memo_key(info.entity, arguments),
        std::move(display), arguments, {}, loc, point_lookup_generation,
        record_to_complete, {}});
    TemplateState::CurrentInstantiationFrame& current_frame =
        tstate().current_instantiation_frames_.back();
    current_frame.template_entity = info.entity;
    current_frame.replays_as_template_pattern = replay_as_template_pattern;
    if (info.is_partial_specialization && record_to_complete.valid()) {
        if (const cir::TemplateSpecializationFact* specialization =
                file_.template_specialization(record_to_complete);
            specialization && specialization->template_entity.valid()) {

            current_frame.template_entity =
                specialization->template_entity;
        }
    }
    TemplateArgumentBindingMode binding_mode =
        !info.is_class_template && !info.is_alias_template &&
            !info.is_variable_template && !info.is_concept
        ? TemplateArgumentBindingMode::DeducedCanonical
        : TemplateArgumentBindingMode::Canonical;
    if (exact_bindings) {
        current_frame.argument_bindings = *exact_bindings;
    } else {
        (void)bind_template_arguments_to_parameters(
            info.parameters,
            arguments,
            current_frame.argument_bindings,
            nullptr,
            binding_mode);
    }

    enter_existing_context(info.lexical_context,
                           ScopeFlags::FileScope);
    enter_scope(ScopeFlags::TemplateParameterScope);
    tstate().scoped_template_parameter_template_keys_.push_back({});
    for (const TemplateInfo::TemplateInstantiationBinding& binding :
         info.enclosing_instantiation_bindings) {
        TemplateInfo enclosing;
        enclosing.parameters = binding.parameters;
        std::vector<TemplateArgument> enclosing_arguments =
            flatten_template_argument_bindings(binding.argument_bindings);
        bind_template_instantiation_parameters(
            enclosing,
            enclosing_arguments,
            loc,
            &binding.argument_bindings);
    }
    bind_template_instantiation_parameters(info,
                                           arguments,
                                           loc,
                                           exact_bindings);
    return scope;
}

bool Session::is_dependent_type(cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return false;
    }
    if (file_.type(resolved).kind == cir::TypeKind::Dependent) {
        return true;
    }
    auto is_validation_record = [&](cir::EntityId record) {
        for (auto frame = tstate().current_instantiation_frames_.rbegin();
             frame != tstate().current_instantiation_frames_.rend();
             ++frame) {

            if (!frame->memo_key.empty() || !frame->info ||
                !frame->info->is_class_template) {
                continue;
            }
            if (frame->record == record) {
                return true;
            }

            if (!record.valid() || !file_.valid(record)) {
                continue;
            }
            for (cir::DeclContextId context =
                     file_.entity(record).semantic_context;
                 context.valid() && file_.valid(context);
                 context = file_.decl_context(context).parent) {
                const cir::DeclContext& declaration =
                    file_.decl_context(context);
                if (declaration.kind == cir::DeclContextKind::Record &&
                    declaration.owner == frame->record) {
                    return true;
                }
            }
        }
        return false;
    };
    if (file_.type(resolved).kind == cir::TypeKind::Record &&
        is_validation_record(file_.record_entity(resolved))) {
        return true;
    }
    if (type_contains_type_param(resolved)) {
        return true;
    }

    std::unordered_set<uint32_t> visited;
    std::function<bool(const TemplateArgument&)> argument_contains_current;
    std::function<bool(cir::TypeId)> type_contains_current;

    argument_contains_current = [&](const TemplateArgument& argument) {
        if (template_argument_is_type(argument)) {
            return type_contains_current(argument.type.type);
        }
        if (template_argument_is_value(argument)) {
            return type_contains_current(argument.value_type.type) ||
                type_contains_current(
                    argument.dependent_value_qualifier.type);
        }
        return type_contains_current(
            argument.dependent_template_qualifier.type);
    };
    type_contains_current = [&](cir::TypeId candidate) -> bool {
        if (!candidate.valid() || !file_.valid(candidate)) {
            return false;
        }
        candidate = file_.resolved_type(candidate);
        if (!file_.valid(candidate) ||
            !visited.insert(candidate.index).second) {
            return false;
        }
        const cir::TypePayload& payload = file_.type_payload(candidate);
        switch (file_.type(candidate).kind) {
            case cir::TypeKind::Pointer:
                return type_contains_current(
                    std::get<cir::PointerTypePayload>(payload)
                        .pointee.type);
            case cir::TypeKind::BlockPointer:
                return type_contains_current(
                    std::get<cir::BlockPointerTypePayload>(payload)
                        .pointee.type);
            case cir::TypeKind::MemberPointer: {
                const auto& member =
                    std::get<cir::MemberPointerTypePayload>(payload);
                return type_contains_current(member.class_type.type) ||
                    type_contains_current(member.member_type.type);
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference:
                return type_contains_current(
                    std::get<cir::ReferenceTypePayload>(payload)
                        .referred_type.type);
            case cir::TypeKind::Array:
                return type_contains_current(
                    std::get<cir::ArrayTypePayload>(payload)
                        .element_type.type);
            case cir::TypeKind::Function: {
                const auto& function =
                    std::get<cir::FunctionTypePayload>(payload);
                if (type_contains_current(function.return_type.type)) {
                    return true;
                }
                return std::any_of(
                    function.parameters.begin(),
                    function.parameters.end(),
                    [&](cir::TypeRef parameter) {
                        return type_contains_current(parameter.type);
                    });
            }
            case cir::TypeKind::Record: {
                cir::EntityId record = file_.record_entity(candidate);
                if (is_validation_record(record)) {
                    return true;
                }
                const cir::TemplateSpecializationFact* specialization =
                    file_.template_specialization(record);
                if (!specialization) {
                    return false;
                }
                std::vector<TemplateArgument> arguments =
                    specialization->template_arguments();
                return std::any_of(
                    arguments.begin(),
                    arguments.end(),
                    argument_contains_current);
            }
            case cir::TypeKind::TemplateSpecialization: {
                const auto& specialization =
                    std::get<cir::TemplateSpecializationTypePayload>(
                        payload);
                return std::any_of(
                    specialization.arguments.begin(),
                    specialization.arguments.end(),
                    argument_contains_current);
            }
            case cir::TypeKind::AliasSpecialization: {
                const auto& specialization =
                    std::get<cir::AliasSpecializationTypePayload>(payload);
                if (type_contains_current(
                        specialization.associated_type.type)) {
                    return true;
                }
                return std::any_of(
                    specialization.arguments.begin(),
                    specialization.arguments.end(),
                    argument_contains_current);
            }
            case cir::TypeKind::DependentName: {
                const auto& dependent =
                    std::get<cir::DependentNameTypePayload>(payload);
                if (type_contains_current(
                        dependent.qualifier_type.type)) {
                    return true;
                }
                return std::any_of(
                    dependent.template_arguments.begin(),
                    dependent.template_arguments.end(),
                    argument_contains_current);
            }
            case cir::TypeKind::Typedef:
                return type_contains_current(
                    std::get<cir::TypedefTypePayload>(payload)
                        .underlying_type.type);
            case cir::TypeKind::Vector:
                return type_contains_current(
                    std::get<cir::VectorTypePayload>(payload)
                        .element_type.type);
            case cir::TypeKind::Complex:
                return type_contains_current(
                    std::get<cir::ComplexTypePayload>(payload)
                        .element_type.type);
            case cir::TypeKind::TypeofExpr: {
                const auto& expression =
                    std::get<cir::TypeofExprTypePayload>(payload);
                return expression.expr.valid() &&
                    file_.valid(expression.expr) &&
                    type_contains_current(
                        file_.inst(expression.expr).result_type);
            }
            case cir::TypeKind::DecltypeExpr: {
                const auto& expression =
                    std::get<cir::DecltypeExprTypePayload>(payload);
                return type_contains_current(
                           expression.operand_type.type) ||
                    type_contains_current(
                        expression.dependent_value_qualifier.type);
            }
            case cir::TypeKind::BuiltinTransform:
                return type_contains_current(
                    std::get<cir::BuiltinTypeTransformTypePayload>(
                        payload).operand_type.type);
            case cir::TypeKind::BuiltinPackElement: {
                const auto& pack =
                    std::get<cir::BuiltinPackElementTypePayload>(payload);
                return std::any_of(
                    pack.arguments.begin(),
                    pack.arguments.end(),
                    argument_contains_current);
            }
            case cir::TypeKind::PackIndex: {
                const auto& pack =
                    std::get<cir::PackIndexTypePayload>(payload);
                if (type_contains_current(pack.pack_type.type)) {
                    return true;
                }
                return std::any_of(
                    pack.expansions.begin(),
                    pack.expansions.end(),
                    [&](cir::TypeRef expansion) {
                        return type_contains_current(expansion.type);
                    });
            }
            case cir::TypeKind::Place:
                return type_contains_current(
                    file_.place_object_ref(candidate).type);
            default:
                return false;
        }
    };
    return type_contains_current(resolved);
}

const Session::TemplateInfo*
Session::class_template_placeholder_info(cir::TypeId type) const {
    type = file_.resolved_type(type);
    if (!file_.valid(type) ||
        file_.type(type).kind != cir::TypeKind::TemplateSpecialization) {
        return nullptr;
    }
    const auto* specialization =
        std::get_if<cir::TemplateSpecializationTypePayload>(
            &file_.type_payload(type));
    if (!specialization ||
        !specialization->is_class_template_placeholder ||
        !specialization->primary_template.valid()) {
        return nullptr;
    }
    return template_info(specialization->primary_template);
}

bool Session::constant_template_parameter_type_is_supported(
    cir::TypeId type) const {
    std::unordered_set<uint32_t> visiting;
    std::function<bool(cir::TypeId)> supported =
        [&](cir::TypeId candidate) -> bool {
        cir::TypeId resolved = file_.resolved_type(candidate);
        if (!file_.valid(resolved)) {
            return false;
        }
        if (is_dependent_type(candidate)) {

            return true;
        }
        if (contains_auto_type(candidate)) {
            if (file_.type(resolved).kind == cir::TypeKind::Auto) {
                const auto* placeholder =
                    std::get_if<cir::AutoTypePayload>(
                        &file_.type_payload(resolved));
                if (placeholder &&
                    (placeholder->flavor ==
                         cir::AutoTypeFlavor::DecltypeAuto ||
                     placeholder->flavor ==
                         cir::AutoTypeFlavor::DecltypeAutoTemplateNonType)) {
                    return true;
                }
            }
            return contains_auto_type(candidate,
                                      cir::AutoTypeFlavor::Cxx) &&
                !contains_auto_type(candidate,
                                    cir::AutoTypeFlavor::Gnu) &&
                !contains_auto_type(
                    candidate,
                    cir::AutoTypeFlavor::TemplateNonType) &&
                !contains_auto_type(candidate,
                                    cir::AutoTypeFlavor::DecltypeAuto) &&
                !contains_auto_type(
                    candidate,
                    cir::AutoTypeFlavor::DecltypeAutoTemplateNonType);
        }
        switch (file_.type(resolved).kind) {
            case cir::TypeKind::Builtin: {
                const auto* builtin =
                    std::get_if<cir::BuiltinTypePayload>(
                        &file_.type_payload(resolved));
                return builtin &&
                    builtin->kind != cir::BuiltinTypeKind::Void &&
                    builtin->kind != cir::BuiltinTypeKind::Other;
            }
            case cir::TypeKind::BitInt:
            case cir::TypeKind::Enum:
            case cir::TypeKind::Pointer:
            case cir::TypeKind::BlockPointer:
            case cir::TypeKind::MemberPointer:
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::TypeParam:
                return true;
            case cir::TypeKind::Array: {
                const auto* array =
                    std::get_if<cir::ArrayTypePayload>(
                        &file_.type_payload(resolved));
                return array && supported(array->element_type.type);
            }
            case cir::TypeKind::Record: {
                if (!visiting.insert(resolved.index).second) {
                    return true;
                }
                const cir::RecordFacts* facts =
                    file_.record_facts_for_type(resolved);
                if (facts && facts->is_lambda_closure) {
                    visiting.erase(resolved.index);
                    return !facts->lambda_has_capture;
                }
                if (!facts || !facts->is_literal_class_type ||
                    !facts->dependent_bases.empty() ||
                    !facts->virtual_bases.empty()) {
                    visiting.erase(resolved.index);
                    return false;
                }
                for (const cir::RecordBaseFact& base : facts->bases) {
                    if (base.declared_access !=
                            cir::RecordMemberAccess::Public ||
                        base.is_virtual || !supported(base.type.type)) {
                        visiting.erase(resolved.index);
                        return false;
                    }
                }
                for (const cir::RecordFieldFact& field : facts->fields) {
                    if (field.is_base_subobject) {
                        continue;
                    }
                    if (field.declared_access !=
                            cir::RecordMemberAccess::Public ||
                        field.is_mutable ||
                        field.is_flexible_array_member ||
                        !supported(field.type.type)) {
                        visiting.erase(resolved.index);
                        return false;
                    }
                }
                visiting.erase(resolved.index);
                return true;
            }
            default:
                return false;
        }
    };
    return supported(type);
}

bool Session::expr_is_dependent(const ExprResult& expr) const {

    if (expr.category == ValueCategory::FunctionDesignator ||
        expr.category == ValueCategory::MemberPointerDesignator) {
        return false;
    }
    if (expr.category == ValueCategory::InitList && expr.init_list) {

        for (const InitElementInput& element : expr.init_list->elements) {
            if (expr_is_dependent(element.value)) {
                return true;
            }
        }
        return false;
    }
    return expr.type.valid() && is_dependent_type(expr.type);
}

bool Session::expr_is_value_dependent(const ExprResult& expr) const {
    return expr.value_dependent ||
           (collecting_pattern_ &&
            expr.references_template_value_parameter) ||
           expr_is_dependent(expr);
}

bool Session::template_instantiation_reclassifies_data_member_as_function(
    std::string_view name,
    SrcLoc loc) const {
    if (!in_template_instantiation() ||
        tstate().current_instantiation_frames_.empty()) {
        return false;
    }
    const TemplateInfo* info =
        tstate().current_instantiation_frames_.back().info;
    if (!info || !info->is_class_template ||
        !info->pattern_record.valid() ||
        !file_.valid(info->pattern_record)) {
        return false;
    }
    const cir::RecordFacts* facts = file_.record_facts(info->pattern_record);
    if (!facts) {
        return false;
    }

    auto is_original_dependent_data_member =
        [&](cir::NameId member_name,
            cir::EntityId entity,
            cir::TypeRef type) {
        if (!member_name.valid() || file_.name(member_name) != name ||
            !entity.valid() || !file_.valid(entity) ||
            !is_dependent_type(type.type)) {
            return false;
        }
        SrcLoc declaration_loc = file_.entity(entity).loc;
        return loc.isInvalid() || declaration_loc.isInvalid() ||
               declaration_loc.offset == loc.offset;
    };

    for (const cir::RecordFieldFact& field : facts->fields) {
        if (!field.is_base_subobject &&
            is_original_dependent_data_member(field.name,
                                              field.entity,
                                              field.type)) {
            return true;
        }
    }
    for (const cir::RecordStaticDataMemberFact& member :
         facts->static_data_members) {
        if (is_original_dependent_data_member(member.name,
                                              member.entity,
                                              member.type)) {
            return true;
        }
    }
    return false;
}

const Session::TemplateInfo::StaticDataMemberInitializer*
Session::current_instantiation_static_data_member_initializer(
    std::string_view name,
    SrcLoc loc) const {
    if (!in_template_instantiation() ||
        tstate().current_instantiation_frames_.empty()) {
        return nullptr;
    }
    const TemplateInfo* info =
        tstate().current_instantiation_frames_.back().info;
    if (!info || !info->is_class_template) {
        return nullptr;
    }
    for (const TemplateInfo::StaticDataMemberInitializer& initializer :
         info->static_data_member_initializers) {
        if (initializer.name != name ||
            initializer.begin >= initializer.end) {
            continue;
        }
        if (!loc.isInvalid() && !initializer.loc.isInvalid() &&
            loc.offset != initializer.loc.offset) {
            continue;
        }
        return &initializer;
    }
    return nullptr;
}

void Session::begin_template_validation(const TemplateInfo& info) {
    validating_template_info_stack_.push_back(validating_template_info_);
    validating_template_info_ = &info;
    tstate().current_instantiation_frames_.push_back(TemplateState::CurrentInstantiationFrame{
        &info, std::string(), std::string(), {}, {}, {}, {}, {}, {}});
    TemplateState::CurrentInstantiationFrame& frame = tstate().current_instantiation_frames_.back();
    frame.template_entity = info.entity;
    cir::DeclContextId lookup_context = info.lexical_context.valid()
        ? info.lexical_context
        : current_decl_context();
    if (!frame.template_entity.valid() && info.is_class_template &&
        !info.is_partial_specialization) {
        if (const TemplateInfo* previous =
                template_info_from_related_ordinary_binding(
                    lookup_context,
                    info.name,
                    /*include_parents=*/false);
            previous && previous->is_class_template &&
            !previous->is_partial_specialization &&
            template_heads_equivalent(*previous, info)) {
            frame.template_entity = previous->entity;
        }
    }
    if (!frame.template_entity.valid() && info.is_class_template &&
        !info.is_partial_specialization) {
        frame.template_entity =
            hidden_friend_class_template_entity(info.name,
                                                info.parameters,
                                                info.introduced_constraints,
                                                lookup_context);
    }
    if (!frame.template_entity.valid() && !info.is_class_template &&
        !info.is_alias_template && !info.is_variable_template &&
        !info.is_concept && info.pattern_type.valid()) {

        for (const TemplateInfo* previous :
             function_template_infos_for_name(lookup_context,
                                              info.name,
                                              /*include_parents=*/false)) {
            if (previous &&
                function_template_declarations_correspond(*previous, info)) {
                frame.template_entity = previous->entity;
                break;
            }
        }
    }
    if (!frame.template_entity.valid() && !info.is_class_template &&
        !info.is_alias_template && !info.is_variable_template &&
        !info.is_concept &&
        info.pattern_type.valid()) {
        frame.template_entity =
            hidden_friend_function_template_entity(info.name,
                                                   info.parameters,
                                                   info.pattern_type,
                                                   info.introduced_constraints,
                                                   lookup_context);
    }
}

cir::EntityId Session::template_validation_entity(
    const TemplateInfo& info) const {

    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend(); ++frame) {
        if (frame->info == &info && frame->template_entity.valid()) {
            return frame->template_entity;
        }
    }
    return info.entity;
}

void Session::finish_template_validation() {
    validating_template_info_ =
        validating_template_info_stack_.empty()
        ? nullptr
        : validating_template_info_stack_.back();
    if (!validating_template_info_stack_.empty()) {
        validating_template_info_stack_.pop_back();
    }
    if (!tstate().current_instantiation_frames_.empty()) {
        tstate().current_instantiation_frames_.pop_back();
    }
}

void Session::note_current_instantiation_dependent_bases(
    cir::EntityId record,
    bool has_dependent_bases) {
    if (!record.valid() || tstate().current_instantiation_frames_.empty()) {
        return;
    }
    TemplateState::CurrentInstantiationFrame& frame = tstate().current_instantiation_frames_.back();
    if (frame.record == record) {
        frame.has_dependent_bases = has_dependent_bases;
    }
}

bool Session::current_instantiation_context_has_dependent_bases(
    cir::DeclContextId context) const {
    if (!context.valid()) {
        return false;
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend(); ++frame) {
        if (frame->has_dependent_bases &&
            current_decl_context() == context) {
            return true;
        }
        if (!frame->record.valid() || !file_.valid(frame->record)) {
            continue;
        }
        if (file_.entity(frame->record).semantic_context != context) {
            continue;
        }
        if (frame->has_dependent_bases) {
            return true;
        }
        const cir::RecordFacts* facts = file_.record_facts(frame->record);
        return facts && !facts->dependent_bases.empty();
    }
    return false;
}

bool Session::current_instantiation_type_has_dependent_bases(
    cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Record) {
        return false;
    }
    cir::EntityId record = file_.record_entity(resolved);
    if (!record.valid() || !file_.valid(record)) {
        return false;
    }
    return current_instantiation_context_has_dependent_bases(
        file_.entity(record).semantic_context);
}

bool Session::current_instantiation_replay_will_claim_record(
    std::string_view name) const {
    if (tstate().current_instantiation_frames_.empty()) {
        return false;
    }
    const TemplateState::CurrentInstantiationFrame& frame =
        tstate().current_instantiation_frames_.back();
    return frame.info && frame.info->is_class_template &&
           !frame.display_name.empty() && !frame.record.valid() &&
           frame.info->name == name;
}

cir::EntityId Session::current_instantiation_record(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments) const {
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend(); ++frame) {
        if (!frame->info) {
            continue;
        }
        bool same_template = frame->info == &info ||
                             (frame->info->entity.valid() &&
                              frame->info->entity == info.entity);
        if (!same_template || !frame->record.valid()) {
            continue;
        }
        if (frame->memo_key.empty()) {

            if (arguments.size() != info.parameters.size()) {
                continue;
            }
            bool self = true;
            for (size_t i = 0; i < arguments.size(); ++i) {
                const TemplateParameter& parameter = info.parameters[i];
                switch (parameter.kind) {
                    case TemplateParameterKind::Type:
                        if (!template_argument_is_type(arguments[i]) ||
                            !info.param_types[i].valid() ||
                            file_.resolved_type(arguments[i].type.type) !=
                                file_.resolved_type(info.param_types[i])) {
                            self = false;
                        }
                        break;
                    case TemplateParameterKind::NonType:
                        if (!template_argument_is_value(arguments[i]) ||
                            arguments[i].value_param_index !=
                                parameter.index) {
                            self = false;
                        }
                        break;
                    case TemplateParameterKind::Template:
                        if (arguments[i].kind !=
                                cir::TemplateArgumentKind::Template ||
                            arguments[i].template_param_index !=
                                parameter.index) {
                            self = false;
                        }
                        break;
                }
                if (!self) {
                    break;
                }
            }
            if (self) {
                return frame->record;
            }
        } else if (template_memo_key(info.entity, arguments) ==
                   frame->memo_key) {
            return frame->record;
        }
    }
    return {};
}

void Session::begin_pattern_collection() {
    PatternCollectionState saved;
    saved.collecting = collecting_pattern_;
    saved.usable = pattern_usable_;
    saved.taint = pattern_taint_;
    saved.holes = std::move(tstate().pattern_holes_);
    saved.events = std::move(pattern_events_);
    saved.holed_locals = std::move(tstate().pattern_holed_locals_);
    saved.members = std::move(tstate().pattern_members_);
    saved.member_active = member_pattern_active_;
    saved.current_member = std::move(current_member_pattern_);
    saved.member_taint_start = member_pattern_taint_start_;
    saved.member_holes_start = member_pattern_holes_start_;
    saved.member_events_start = member_pattern_events_start_;
    pattern_collection_stack_.push_back(std::move(saved));

    collecting_pattern_ = true;
    pattern_usable_ = true;
    pattern_taint_ = 0;
    tstate().pattern_holes_.clear();
    pattern_events_.clear();
    tstate().pattern_holed_locals_.clear();
    tstate().pattern_members_.clear();
    member_pattern_active_ = false;
    current_member_pattern_ = MemberPattern{};
    member_pattern_taint_start_ = 0;
    member_pattern_holes_start_ = 0;
    member_pattern_events_start_ = 0;
    builder_.set_mark_template_pattern(true);
}

Session::PatternCollection Session::finish_pattern_collection() {
    PatternCollection result;
    result.holes = std::move(tstate().pattern_holes_);
    result.events = std::move(pattern_events_);
    result.members = std::move(tstate().pattern_members_);
    result.usable = pattern_usable_;
    assert(!pattern_collection_stack_.empty());
    PatternCollectionState saved =
        std::move(pattern_collection_stack_.back());
    pattern_collection_stack_.pop_back();
    collecting_pattern_ = saved.collecting;
    pattern_usable_ = saved.usable;
    pattern_taint_ = saved.taint;
    tstate().pattern_holes_ = std::move(saved.holes);
    pattern_events_ = std::move(saved.events);
    tstate().pattern_holed_locals_ = std::move(saved.holed_locals);
    tstate().pattern_members_ = std::move(saved.members);
    member_pattern_active_ = saved.member_active;
    current_member_pattern_ = std::move(saved.current_member);
    member_pattern_taint_start_ = saved.member_taint_start;
    member_pattern_holes_start_ = saved.member_holes_start;
    member_pattern_events_start_ = saved.member_events_start;
    builder_.set_mark_template_pattern(collecting_pattern_);
    return result;
}

void Session::begin_member_pattern(cir::EntityId method,
                                   cir::FunctionId function,
                                   size_t body_token_begin,
                                   size_t leading_blocks) {
    if (!collecting_pattern_ || member_pattern_active_) {
        return;
    }
    member_pattern_active_ = true;
    current_member_pattern_ = MemberPattern{};
    current_member_pattern_.method = method;
    current_member_pattern_.function = function;
    current_member_pattern_.body_token_begin = body_token_begin;

    current_member_pattern_.body_start_block =
        1 + current_prologue_.blocks.size() + leading_blocks;
    current_member_pattern_.hole_index_base =
        static_cast<uint32_t>(tstate().pattern_holes_.size());
    member_pattern_taint_start_ = pattern_taint_;
    member_pattern_holes_start_ = tstate().pattern_holes_.size();
    member_pattern_events_start_ = pattern_events_.size();
}

void Session::finish_member_pattern(size_t body_blocks) {
    if (!collecting_pattern_ || !member_pattern_active_) {
        return;
    }
    member_pattern_active_ = false;
    MemberPattern member = std::move(current_member_pattern_);
    current_member_pattern_ = MemberPattern{};
    member.body_block_count = body_blocks;
    member.holes.assign(tstate().pattern_holes_.begin() + member_pattern_holes_start_,
                        tstate().pattern_holes_.end());
    tstate().pattern_holes_.resize(member_pattern_holes_start_);
    member.events.assign(pattern_events_.begin() + member_pattern_events_start_,
                         pattern_events_.end());
    pattern_events_.resize(member_pattern_events_start_);
    for (PatternHole& hole : member.holes) {
        hole.event_watermark = hole.event_watermark >= member_pattern_events_start_
            ? hole.event_watermark - member_pattern_events_start_
            : 0;
    }

    if (pattern_taint_ != member_pattern_taint_start_) {
        member.usable = false;
    }
    pattern_taint_ = member_pattern_taint_start_;
    tstate().pattern_members_.push_back(std::move(member));
}

cir::EntityId Session::current_validation_record() const {
    if (!tstate().current_instantiation_frames_.empty() &&
        tstate().current_instantiation_frames_.back().memo_key.empty() &&
        tstate().current_instantiation_frames_.back().info == validating_template_info_) {
        return tstate().current_instantiation_frames_.back().record;
    }
    return {};
}

StmtResult Session::make_pattern_hole_stmt(size_t token_begin,
                                           size_t token_end,
                                           uint64_t taint_before,
                                           size_t events_before,
                                           std::string display,
                                           SrcLoc loc,
                                           PatternHole::Kind kind) {

    for (size_t i = events_before; i < pattern_events_.size(); ++i) {
        if (pattern_events_[i].kind == PatternScopeEvent::Kind::DeclareLocal &&
            pattern_events_[i].entity.valid()) {
            tstate().pattern_holed_locals_.insert(
                static_cast<uint64_t>(pattern_events_[i].entity.index));
        }
    }
    pattern_events_.resize(events_before);
    pattern_taint_ = taint_before;

    uint32_t hole_index = static_cast<uint32_t>(tstate().pattern_holes_.size());
    PatternHole hole;
    hole.token_begin = token_begin;
    hole.token_end = token_end;
    hole.event_watermark = events_before;
    hole.kind = kind;
    tstate().pattern_holes_.push_back(std::move(hole));

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("stmt.hole");
    builder_.dependent_region(hole_index, std::move(display), {}, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);
    return make_stmt_result(std::move(fragment), false, false);
}

ExprResult Session::make_dependent_expr(ExprResult operand, SrcLoc loc) {
    bump_pattern_taint();

    ExprResult result;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.dependent");
    cir::TypeId dependent = file_.dependent_type("dependent");
    result.value = builder_.name_ref("<dependent>", dependent, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);
    result.fragment =
        chain(std::move(operand.fragment), std::move(fragment), loc);
    result.type = dependent;
    result.entity = operand.entity;
    result.name = std::move(operand.name);
    result.builtin_call_designator = operand.builtin_call_designator;
    result.candidates = std::move(operand.candidates);
    result.overload_designator = std::move(operand.overload_designator);
    result.has_explicit_template_arguments =
        operand.has_explicit_template_arguments;
    result.explicit_template_arguments =
        std::move(operand.explicit_template_arguments);
    result.candidate_explicit_template_arguments =
        std::move(operand.candidate_explicit_template_arguments);
    result.unresolved_unqualified_name = operand.unresolved_unqualified_name;
    result.qualified_name = operand.qualified_name;
    result.suppress_argument_dependent_lookup =
        operand.suppress_argument_dependent_lookup;
    result.dependent_value_qualifier = operand.dependent_value_qualifier;
    result.dependent_value_name = operand.dependent_value_name;
    result.dependent_member_access = std::move(operand.dependent_member_access);
    result.references_template_value_parameter =
        operand.references_template_value_parameter;
    result.value_dependent = true;
    result.template_value_expr = std::move(operand.template_value_expr);
    result.type_originates_from_template_parameter =
        operand.type_originates_from_template_parameter;
    result.category = ValueCategory::PrValue;
    result.has_error = operand.has_error;
    return result;
}

ExprResult Session::make_deferred_typed_expr(ExprResult operand,
                                             cir::TypeId expression_type,
                                             ValueCategory category,
                                             SrcLoc loc) {
    bump_pattern_taint();

    ExprResult result;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.deferred.typed");
    if (category == ValueCategory::LValue ||
        category == ValueCategory::XValue) {
        cir::TypeId pointer_type =
            builder_.pointer_type(file_.type_ref(expression_type));
        cir::InstId pointer =
            builder_.name_ref("<deferred-address>", pointer_type, loc);
        result.place = builder_.deref(pointer, loc);
    } else if (category == ValueCategory::PrValue &&
               !is_void_type(expression_type)) {
        result.value =
            builder_.name_ref("<deferred-value>", expression_type, loc);
    }
    cir::Fragment fragment = finish_fragment_block(block, previous);

    result.fragment =
        chain(std::move(operand.fragment), std::move(fragment), loc);
    result.type = expression_type;
    result.category = category;
    result.has_error = operand.has_error;
    result.type_originates_from_template_parameter =
        operand.type_originates_from_template_parameter;
    result.references_template_value_parameter =
        operand.references_template_value_parameter;
    result.value_dependent = operand.value_dependent ||
        operand.references_template_value_parameter ||
        expr_is_dependent(operand);
    result.template_value_expr = std::move(operand.template_value_expr);
    return result;
}

ExprResult Session::make_deferred_conversion_expr(ExprResult operand,
                                                  cir::TypeId target_type,
                                                  SrcLoc loc) {
    cir::TemplateValueExpression expression =
        template_value_operand_expression(operand);
    expression.canonical_id = {};
    cir::TypeId resolved = file_.resolved_type(target_type);
    if (file_.valid(resolved) &&
        (file_.type(resolved).kind == cir::TypeKind::LValueReference ||
         file_.type(resolved).kind == cir::TypeKind::RValueReference)) {
        cir::TypeRef referred = file_.reference_referred_ref(resolved);
        cir::TypeId referred_resolved = file_.resolved_type(referred.type);
        bool refers_to_function = file_.valid(referred_resolved) &&
            file_.type(referred_resolved).kind == cir::TypeKind::Function;
        ValueCategory category =
            file_.type(resolved).kind == cir::TypeKind::LValueReference ||
                    refers_to_function
                ? ValueCategory::LValue
                : ValueCategory::XValue;
        ExprResult result = make_deferred_typed_expr(
            std::move(operand),
            referred.type.valid() ? referred.type : builder_.unknown_type(),
            category,
            loc);
        if (expression.valid()) {
            cir::TemplateValueExprNode node;
            node.kind = cir::TemplateValueExprKind::Cast;
            node.lhs = expression.root;
            node.type = target_type;
            node.result_type = type_ref(result.type);
            expression.nodes.push_back(node);
            expression.root = static_cast<uint32_t>(expression.nodes.size() - 1);
            expression.loc = loc;
            expression.definition_context = current_decl_context();
            expression.definition_lookup_generation = lookup_generation_;
            result.template_value_expr = std::move(expression);
        }
        return result;
    }
    ExprResult result = make_deferred_typed_expr(
        std::move(operand),
        target_type.valid() ? target_type : builder_.unknown_type(),
        ValueCategory::PrValue,
        loc);
    if (expression.valid()) {
        cir::TemplateValueExprNode node;
        node.kind = cir::TemplateValueExprKind::Cast;
        node.lhs = expression.root;
        node.type = target_type;
        node.result_type = type_ref(result.type);
        expression.nodes.push_back(node);
        expression.root = static_cast<uint32_t>(expression.nodes.size() - 1);
        expression.loc = loc;
        expression.definition_context = current_decl_context();
        expression.definition_lookup_generation = lookup_generation_;
        result.template_value_expr = std::move(expression);
    }
    return result;
}

bool Session::type_contains_type_param(cir::TypeId type) const {
    return type_contains_type_param_except_record(type, {});
}

bool Session::type_contains_type_param_except_record(
    cir::TypeId type,
    cir::EntityId opaque_record) const {
    std::vector<cir::TypeId> visited;
    std::function<bool(cir::TypeId)> contains =
        [&](cir::TypeId candidate) -> bool {
        cir::TypeId resolved = file_.resolved_type(candidate);
        if (!file_.valid(resolved)) {
            return false;
        }
        if (std::find(visited.begin(), visited.end(), resolved) !=
            visited.end()) {
            return false;
        }
        visited.push_back(resolved);

        const cir::Type& node = file_.type(resolved);
        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (node.kind) {
        case cir::TypeKind::TypeParam:
        case cir::TypeKind::DependentName:
        case cir::TypeKind::Dependent:
        case cir::TypeKind::PackIndex:
            return true;
        case cir::TypeKind::Pointer:
            return contains(
                std::get<cir::PointerTypePayload>(payload).pointee.type);
        case cir::TypeKind::MemberPointer: {
            const auto& member =
                std::get<cir::MemberPointerTypePayload>(payload);
            return contains(member.class_type.type) ||
                   contains(member.member_type.type);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return contains(
                std::get<cir::ReferenceTypePayload>(payload).referred_type.type);
        case cir::TypeKind::Array: {
            const auto& array = std::get<cir::ArrayTypePayload>(payload);

            return array.extent_param != cir::ArrayTypePayload::no_extent_param ||
                   array.size_expr_is_dependent ||
                   contains(array.element_type.type);
        }
        case cir::TypeKind::Complex:
            return contains(
                std::get<cir::ComplexTypePayload>(payload).element_type.type);
        case cir::TypeKind::TypeofExpr: {
            const auto& typeof_expr =
                std::get<cir::TypeofExprTypePayload>(payload);
            return typeof_expr.expr.valid() &&
                   file_.valid(typeof_expr.expr) &&
                   contains(
                       file_.inst(typeof_expr.expr).result_type);
        }
        case cir::TypeKind::DecltypeExpr: {
            const auto& decltype_expr =
                std::get<cir::DecltypeExprTypePayload>(payload);
            if (decltype_expr.operand_expression.valid()) {
                return true;
            }
            if (contains(decltype_expr.operand_type.type) ||
                contains(
                    decltype_expr.dependent_value_qualifier.type)) {
                return true;
            }
            return decltype_expr.expr.valid() &&
                   file_.valid(decltype_expr.expr) &&
                   contains(
                       file_.inst(decltype_expr.expr).result_type);
        }
        case cir::TypeKind::BuiltinTransform:
            return contains(
                std::get<cir::BuiltinTypeTransformTypePayload>(payload)
                    .operand_type.type);
        case cir::TypeKind::BuiltinPackElement: {
            const auto& pack_element =
                std::get<cir::BuiltinPackElementTypePayload>(payload);
            for (const cir::TemplateArgument& argument :
                 pack_element.arguments) {
                if ((template_argument_is_type(argument) &&
                     contains(argument.type.type)) ||
                    (template_argument_is_value(argument) &&
                     (argument.is_dependent ||
                      contains(argument.value_type.type) ||
                      contains(
                          argument.dependent_value_qualifier.type)))) {
                    return true;
                }
            }
            return false;
        }
        case cir::TypeKind::Place:
            return contains(
                file_.place_object_ref(resolved).type);
        case cir::TypeKind::Record: {
            cir::EntityId record = file_.record_entity(resolved);
            if (opaque_record.valid() && record == opaque_record) {
                return false;
            }
            const cir::RecordFacts* facts = file_.record_facts(record);
            if (facts && facts->is_lambda_closure) {
                for (const cir::RecordFieldFact& field : facts->fields) {
                    if (contains(field.type.type)) {
                        return true;
                    }
                }
            }
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(record);
            cir::EntityId template_entity{};
            std::vector<TemplateArgument> arguments;
            if (fact) {
                template_entity = fact->template_entity;
                arguments = fact->template_arguments();
            } else if (!class_template_arguments_for_record(
                           record, &template_entity, &arguments)) {
                return false;
            }
            if (template_entity.valid() &&
                file_.valid(template_entity) &&
                file_.entity(template_entity).kind ==
                    cir::EntityKind::TemplateParam) {
                return true;
            }
            for (const cir::TemplateArgument& argument : arguments) {
                if (template_argument_is_type(argument) &&
                    contains(argument.type.type)) {
                    return true;
                }
                if (template_argument_is_value(argument)) {
                    if (argument.is_dependent ||
                        contains(argument.value_type.type) ||
                        contains(
                            argument.dependent_value_qualifier.type)) {
                        return true;
                    }
                }
                if (argument.kind == cir::TemplateArgumentKind::Template &&
                    (contains(
                         argument.dependent_template_qualifier.type) ||
                     (argument.template_entity.valid() &&
                      file_.valid(argument.template_entity) &&
                      file_.entity(argument.template_entity).kind ==
                          cir::EntityKind::TemplateParam))) {
                    return true;
                }
            }
            return false;
        }
        case cir::TypeKind::TemplateSpecialization: {
            const auto& specialization =
                std::get<cir::TemplateSpecializationTypePayload>(payload);
            if (specialization.is_dependent ||
                (specialization.primary_template.valid() &&
                 file_.valid(specialization.primary_template) &&
                 file_.entity(specialization.primary_template).kind ==
                     cir::EntityKind::TemplateParam)) {
                return true;
            }
            for (const cir::TemplateArgument& argument :
                 specialization.arguments) {
                if ((template_argument_is_type(argument) &&
                     contains(argument.type.type)) ||
                    (template_argument_is_value(argument) &&
                     (argument.is_dependent ||
                      contains(argument.value_type.type))) ||
                    (argument.kind == cir::TemplateArgumentKind::Template &&
                     (argument.template_param_index !=
                          cir::ArrayTypePayload::no_extent_param ||
                      contains(
                          argument.dependent_template_qualifier.type)))) {
                    return true;
                }
            }
            return false;
        }
        case cir::TypeKind::Function: {
            const auto& function = std::get<cir::FunctionTypePayload>(payload);
            if (contains(function.return_type.type)) {
                return true;
            }
            for (const cir::TypeRef& parameter : function.parameters) {
                if (contains(parameter.type)) {
                    return true;
                }
            }
            return function.exception_spec.kind ==
                       cir::FunctionExceptionSpecKind::Dependent &&
                   function.exception_spec.predicate.valid();
        }
        default:
            return false;
        }
    };
    return contains(type);
}

bool Session::type_contains_nondeduced_context(cir::TypeId type) const {
    if (file_.valid(type) &&
        file_.type(type).kind == cir::TypeKind::AliasSpecialization) {
        const auto& alias =
            std::get<cir::AliasSpecializationTypePayload>(
                file_.type_payload(type));
        const TemplateInfo* info = template_info(alias.alias_template);
        if (info &&
            info->alias_type_transform_kind !=
                TemplateInfo::AliasTypeTransformKind::None) {
            return true;
        }
    }
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return false;
    }
    const cir::TypePayload& payload = file_.type_payload(resolved);
    switch (file_.type(resolved).kind) {
        case cir::TypeKind::DependentName:
        case cir::TypeKind::DecltypeExpr:
        case cir::TypeKind::BuiltinPackElement:
        case cir::TypeKind::PackIndex:
            return true;
        case cir::TypeKind::Pointer:
            return type_contains_nondeduced_context(
                std::get<cir::PointerTypePayload>(payload).pointee.type);
        case cir::TypeKind::BlockPointer:
            return type_contains_nondeduced_context(
                std::get<cir::BlockPointerTypePayload>(payload).pointee.type);
        case cir::TypeKind::MemberPointer: {
            const auto& member =
                std::get<cir::MemberPointerTypePayload>(payload);
            return type_contains_nondeduced_context(member.class_type.type) ||
                   type_contains_nondeduced_context(member.member_type.type);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return type_contains_nondeduced_context(
                std::get<cir::ReferenceTypePayload>(payload)
                    .referred_type.type);
        case cir::TypeKind::Array:
            return type_contains_nondeduced_context(
                std::get<cir::ArrayTypePayload>(payload).element_type.type);
        case cir::TypeKind::Function: {
            const auto& function =
                std::get<cir::FunctionTypePayload>(payload);
            if (type_contains_nondeduced_context(
                    function.return_type.type)) {
                return true;
            }
            return std::any_of(
                function.parameters.begin(),
                function.parameters.end(),
                [&](cir::TypeRef parameter) {
                    return type_contains_nondeduced_context(parameter.type);
                });
        }
        case cir::TypeKind::TemplateSpecialization: {
            const auto& specialization =
                std::get<cir::TemplateSpecializationTypePayload>(payload);
            return std::any_of(
                specialization.arguments.begin(),
                specialization.arguments.end(),
                [&](const TemplateArgument& argument) {
                    return argument.kind ==
                               cir::TemplateArgumentKind::Type &&
                           type_contains_nondeduced_context(
                               argument.type.type);
                });
        }
        case cir::TypeKind::Record: {
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(
                    file_.record_entity(resolved));
            if (!fact) {
                return false;
            }
            std::vector<TemplateArgument> arguments =
                fact->template_arguments();
            return std::any_of(
                arguments.begin(), arguments.end(),
                [&](const TemplateArgument& argument) {
                    return argument.kind ==
                               cir::TemplateArgumentKind::Type &&
                           type_contains_nondeduced_context(
                               argument.type.type);
                });
        }
        case cir::TypeKind::Typedef:
            return type_contains_nondeduced_context(
                std::get<cir::TypedefTypePayload>(payload)
                    .underlying_type.type);
        case cir::TypeKind::Complex:
            return type_contains_nondeduced_context(
                std::get<cir::ComplexTypePayload>(payload)
                    .element_type.type);
        case cir::TypeKind::BuiltinTransform:
            return type_contains_nondeduced_context(
                std::get<cir::BuiltinTypeTransformTypePayload>(payload)
                    .operand_type.type);
        case cir::TypeKind::Place:
            return type_contains_nondeduced_context(
                file_.place_object_ref(resolved).type);
        default:
            return false;
    }
}

bool Session::type_contains_dependent_alias_specialization(
    cir::TypeId root) const {
    std::unordered_set<uint32_t> visited;
    std::function<bool(const TemplateArgument&)> argument_contains;
    std::function<bool(cir::TypeId)> type_contains;

    argument_contains = [&](const TemplateArgument& argument) {
        if (template_argument_is_type(argument)) {
            return type_contains(argument.type.type);
        }
        if (template_argument_is_value(argument)) {
            return type_contains(argument.value_type.type) ||
                type_contains(argument.dependent_value_qualifier.type);
        }
        return type_contains(argument.dependent_template_qualifier.type);
    };
    type_contains = [&](cir::TypeId type) -> bool {
        if (!file_.valid(type) ||
            !visited.insert(static_cast<uint32_t>(type.index)).second) {
            return false;
        }
        if (file_.type(type).kind ==
            cir::TypeKind::AliasSpecialization) {
            return true;
        }
        cir::TypeId resolved = file_.resolved_type(type);
        if (!file_.valid(resolved)) {
            return false;
        }
        if (resolved != type &&
            !visited.insert(static_cast<uint32_t>(resolved.index)).second) {
            return false;
        }
        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (file_.type(resolved).kind) {
            case cir::TypeKind::Pointer:
                return type_contains(
                    std::get<cir::PointerTypePayload>(payload)
                        .pointee.type);
            case cir::TypeKind::BlockPointer:
                return type_contains(
                    std::get<cir::BlockPointerTypePayload>(payload)
                        .pointee.type);
            case cir::TypeKind::MemberPointer: {
                const auto& member =
                    std::get<cir::MemberPointerTypePayload>(payload);
                return type_contains(member.class_type.type) ||
                    type_contains(member.member_type.type);
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference:
                return type_contains(
                    std::get<cir::ReferenceTypePayload>(payload)
                        .referred_type.type);
            case cir::TypeKind::Array:
                return type_contains(
                    std::get<cir::ArrayTypePayload>(payload)
                        .element_type.type);
            case cir::TypeKind::Function: {
                const auto& function =
                    std::get<cir::FunctionTypePayload>(payload);
                if (type_contains(function.return_type.type)) {
                    return true;
                }
                return std::any_of(
                    function.parameters.begin(),
                    function.parameters.end(),
                    [&](cir::TypeRef parameter) {
                        return type_contains(parameter.type);
                    });
            }
            case cir::TypeKind::Record: {
                const cir::TemplateSpecializationFact* fact =
                    file_.template_specialization(
                        file_.record_entity(resolved));
                if (!fact) {
                    return false;
                }
                std::vector<TemplateArgument> arguments =
                    fact->template_arguments();
                return std::any_of(arguments.begin(),
                                   arguments.end(),
                                   argument_contains);
            }
            case cir::TypeKind::TemplateSpecialization: {
                const auto& specialization =
                    std::get<cir::TemplateSpecializationTypePayload>(
                        payload);
                return std::any_of(
                    specialization.arguments.begin(),
                    specialization.arguments.end(),
                    argument_contains);
            }
            case cir::TypeKind::DependentName: {
                const auto& dependent =
                    std::get<cir::DependentNameTypePayload>(payload);
                if (type_contains(dependent.qualifier_type.type)) {
                    return true;
                }
                return std::any_of(
                    dependent.template_arguments.begin(),
                    dependent.template_arguments.end(),
                    argument_contains);
            }
            case cir::TypeKind::Typedef:
                return type_contains(
                    std::get<cir::TypedefTypePayload>(payload)
                        .underlying_type.type);
            case cir::TypeKind::Vector:
                return type_contains(
                    std::get<cir::VectorTypePayload>(payload)
                        .element_type.type);
            case cir::TypeKind::Complex:
                return type_contains(
                    std::get<cir::ComplexTypePayload>(payload)
                        .element_type.type);
            case cir::TypeKind::BuiltinTransform:
                return type_contains(
                    std::get<cir::BuiltinTypeTransformTypePayload>(
                        payload).operand_type.type);
            case cir::TypeKind::BuiltinPackElement: {
                const auto& pack =
                    std::get<cir::BuiltinPackElementTypePayload>(payload);
                return std::any_of(pack.arguments.begin(),
                                   pack.arguments.end(),
                                   argument_contains);
            }
            case cir::TypeKind::Place:
                return type_contains(
                    file_.place_object_ref(resolved).type);
            default:
                return false;
        }
    };
    return type_contains(root);
}

cir::TypeRef Session::collect_builtin_pack_element_type(
    std::vector<TemplateArgument> arguments,
    SrcLoc loc,
    bool diagnose) {
    auto fail = [&](std::string message) {
        if (diagnose) {
            report_error(std::move(message), loc);
        }
        return cir::TypeRef{};
    };

    if (arguments.size() < 2) {
        return fail(
            "__type_pack_element requires an index and at least one type");
    }
    if (!template_argument_is_value(arguments.front())) {
        return fail(
            "first __type_pack_element argument must be a constant index");
    }
    for (size_t i = 1; i < arguments.size(); ++i) {
        if (!template_argument_is_type(arguments[i])) {
            return fail(
                "__type_pack_element operands after the index must be types");
        }
    }

    auto argument_is_dependent = [&](const TemplateArgument& argument) {
        if (argument.expands_parameter_pack ||
            argument.expands_pack_pattern ||
            argument.generated_pack_kind !=
                cir::TemplateGeneratedPackKind::None) {
            return true;
        }
        if (template_argument_is_type(argument)) {
            return argument.type.valid() &&
                   is_dependent_type(argument.type.type);
        }
        if (template_argument_is_value(argument)) {
            return argument.is_dependent ||
                   argument.dependent_value_expr.valid() ||
                   argument.dependent_value_qualifier.type.valid();
        }
        return argument.is_dependent;
    };

    if (std::any_of(arguments.begin(),
                    arguments.end(),
                    argument_is_dependent)) {
        return type_ref(
            file_.builtin_pack_element_type(std::move(arguments)));
    }

    const TemplateArgument& index = arguments.front();
    if (index.value_kind != cir::TemplateValueKind::Integer &&
        index.value_kind != cir::TemplateValueKind::Boolean) {
        return fail(
            "first __type_pack_element argument must be an integer constant");
    }

    if (index.integer_value.is_negative()) {
        return fail("__type_pack_element index cannot be negative");
    }
    std::optional<uint64_t> selected =
        index.integer_value.try_as_uint64();
    if (!selected.has_value()) {
        return fail("__type_pack_element index is too large");
    }
    uint64_t selected_index = *selected;
    const uint64_t element_count =
        static_cast<uint64_t>(arguments.size() - 1);
    if (selected_index >= element_count) {
        return fail("__type_pack_element index " +
                    std::to_string(selected_index) +
                    " is outside a pack of " +
                    std::to_string(element_count) + " type" +
                    (element_count == 1 ? "" : "s"));
    }
    return arguments[static_cast<size_t>(selected_index) + 1].type;
}

void Session::record_constraint_parameter_provenance(
    NormalizedConstraint& form) const {
    auto same_reference = [](const ConstraintParameterReference& lhs,
                             const ConstraintParameterReference& rhs) {
        if (lhs.parameter_entity.valid() || rhs.parameter_entity.valid()) {
            return lhs.parameter_entity == rhs.parameter_entity;
        }
        if (lhs.parameter_type.valid() || rhs.parameter_type.valid()) {
            return lhs.parameter_type == rhs.parameter_type;
        }
        return lhs.parameter_kind == rhs.parameter_kind &&
               lhs.parameter_depth == rhs.parameter_depth &&
               lhs.parameter_index == rhs.parameter_index &&
               lhs.owning_template_entity == rhs.owning_template_entity;
    };
    auto add_reference = [&](ConstraintParameterReference reference) {
        if (std::find_if(form.referenced_parameters.begin(),
                         form.referenced_parameters.end(),
                         [&](const ConstraintParameterReference& existing) {
                             return same_reference(existing, reference);
                         }) == form.referenced_parameters.end()) {
            form.referenced_parameters.push_back(std::move(reference));
        }
    };

    std::vector<const TemplateInfo*> owners;
    owners.reserve(tstate().templates_.size() +
                   tstate().current_instantiation_frames_.size() + 1);
    auto remember_owner = [&](const TemplateInfo* info) {
        if (info && std::find(owners.begin(), owners.end(), info) ==
                        owners.end()) {
            owners.push_back(info);
        }
    };
    for (const auto& [_, info] : tstate().templates_) {
        remember_owner(&info);
    }
    for (const auto& frame : tstate().current_instantiation_frames_) {
        remember_owner(frame.info);
    }
    remember_owner(active_template_header_info_);

    auto reference_for_entity = [&](cir::EntityId parameter,
                                    TemplateParameterKind fallback_kind,
                                    uint32_t fallback_depth,
                                    uint32_t fallback_index,
                                    cir::TypeId parameter_type = cir::TypeId{}) {
        ConstraintParameterReference reference;
        reference.parameter_kind = fallback_kind;
        reference.parameter_depth = fallback_depth;
        reference.parameter_index = fallback_index;
        reference.parameter_entity = parameter;
        reference.parameter_type = parameter_type;
        std::function<bool(const TemplateInfo&, cir::EntityId)>
            find_parameter =
                [&](const TemplateInfo& info,
                    cir::EntityId owner) -> bool {
            for (const TemplateParameter& candidate : info.parameters) {
                bool matches = parameter_type.valid() &&
                                       candidate.type_param_type.valid()
                    ? candidate.type_param_type == parameter_type
                    : (parameter.valid() && candidate.entity.valid()
                           ? candidate.entity == parameter
                           : (!parameter.valid() && !parameter_type.valid() &&
                       candidate.kind == fallback_kind &&
                       candidate.depth == fallback_depth &&
                       candidate.index == fallback_index));
                if (matches) {
                    reference.parameter_kind = candidate.kind;
                    reference.parameter_depth = candidate.depth;
                    reference.parameter_index = candidate.index;
                    reference.parameter_entity = candidate.entity.valid()
                        ? candidate.entity
                        : parameter;
                    reference.parameter_type =
                        candidate.type_param_type.valid()
                            ? candidate.type_param_type
                            : parameter_type;
                    reference.owning_template_entity = owner;
                    if (!reference.owning_template_entity.valid() &&
                        info.is_class_template) {
                        reference.owning_template_entity =
                            enclosing_record_for_context(
                                current_decl_context());
                    }
                    return true;
                }
                if (candidate.nested_head &&
                    find_parameter(*candidate.nested_head, owner)) {
                    return true;
                }
            }
            return false;
        };
        for (const TemplateInfo* owner : owners) {
            if (owner && find_parameter(*owner, owner->entity)) {
                break;
            }
        }
        add_reference(std::move(reference));
    };

    std::unordered_set<uint32_t> visited_types;
    std::function<void(const cir::TemplateValueExpression&)> visit_expression;
    std::function<void(const cir::TemplateArgument&)> visit_argument;
    std::function<void(cir::TypeId)> visit_type;

    visit_type = [&](cir::TypeId type) {
        if (!type.valid() || !file_.valid(type) ||
            !visited_types.insert(type.index).second) {
            return;
        }
        const cir::Type& node = file_.type(type);
        const cir::TypePayload& payload = file_.type_payload(type);
        switch (node.kind) {
            case cir::TypeKind::TypeParam: {
                const auto& parameter =
                    std::get<cir::TypeParamTypePayload>(payload);
                reference_for_entity(parameter.entity,
                                     TemplateParameterKind::Type,
                                     parameter.depth,
                                     parameter.index,
                                     type);
                break;
            }
            case cir::TypeKind::Pointer:
                visit_type(std::get<cir::PointerTypePayload>(payload)
                               .pointee.type);
                break;
            case cir::TypeKind::BlockPointer:
                visit_type(std::get<cir::BlockPointerTypePayload>(payload)
                               .pointee.type);
                break;
            case cir::TypeKind::MemberPointer: {
                const auto& member =
                    std::get<cir::MemberPointerTypePayload>(payload);
                visit_type(member.class_type.type);
                visit_type(member.member_type.type);
                break;
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference:
                visit_type(std::get<cir::ReferenceTypePayload>(payload)
                               .referred_type.type);
                break;
            case cir::TypeKind::Array: {
                const auto& array =
                    std::get<cir::ArrayTypePayload>(payload);
                visit_type(array.element_type.type);
                visit_expression(array.dependent_size_expr);
                break;
            }
            case cir::TypeKind::Function: {
                const auto& function =
                    std::get<cir::FunctionTypePayload>(payload);
                visit_type(function.return_type.type);
                for (const cir::TypeRef& parameter : function.parameters) {
                    visit_type(parameter.type);
                }
                visit_expression(function.exception_spec.predicate);
                break;
            }
            case cir::TypeKind::Record: {
                cir::EntityId record = file_.record_entity(type);
                if (const cir::TemplateSpecializationFact* specialization =
                        file_.template_specialization(record)) {
                    for (const cir::TemplateArgument& argument :
                         specialization->template_arguments()) {
                        visit_argument(argument);
                    }
                }
                break;
            }
            case cir::TypeKind::Vector:
                visit_type(std::get<cir::VectorTypePayload>(payload)
                               .element_type.type);
                break;
            case cir::TypeKind::Complex:
                visit_type(std::get<cir::ComplexTypePayload>(payload)
                               .element_type.type);
                break;
            case cir::TypeKind::Typedef:
                visit_type(std::get<cir::TypedefTypePayload>(payload)
                               .underlying_type.type);
                break;
            case cir::TypeKind::TemplateSpecialization: {
                const auto& specialization =
                    std::get<cir::TemplateSpecializationTypePayload>(payload);
                for (const cir::TemplateArgument& argument :
                     specialization.arguments) {
                    visit_argument(argument);
                }
                break;
            }
            case cir::TypeKind::AliasSpecialization: {
                const auto& specialization =
                    std::get<cir::AliasSpecializationTypePayload>(payload);
                for (const cir::TemplateArgument& argument :
                     specialization.arguments) {
                    visit_argument(argument);
                }
                visit_type(specialization.associated_type.type);
                break;
            }
            case cir::TypeKind::DependentName: {
                const auto& dependent =
                    std::get<cir::DependentNameTypePayload>(payload);
                visit_type(dependent.qualifier_type.type);
                for (const cir::TemplateArgument& argument :
                     dependent.template_arguments) {
                    visit_argument(argument);
                }
                break;
            }
            case cir::TypeKind::DecltypeExpr: {
                const auto& decltype_expr =
                    std::get<cir::DecltypeExprTypePayload>(payload);
                visit_type(decltype_expr.operand_type.type);
                visit_type(decltype_expr.dependent_value_qualifier.type);
                visit_expression(decltype_expr.operand_expression);
                break;
            }
            case cir::TypeKind::BuiltinTransform:
                visit_type(std::get<cir::BuiltinTypeTransformTypePayload>(
                               payload).operand_type.type);
                break;
            case cir::TypeKind::BuiltinPackElement:
                for (const cir::TemplateArgument& argument :
                     std::get<cir::BuiltinPackElementTypePayload>(payload)
                         .arguments) {
                    visit_argument(argument);
                }
                break;
            case cir::TypeKind::PackIndex: {
                const auto& pack_index =
                    std::get<cir::PackIndexTypePayload>(payload);
                visit_type(pack_index.pack_type.type);
                visit_expression(pack_index.index_expression);
                for (cir::TypeRef expansion : pack_index.expansions) {
                    visit_type(expansion.type);
                }
                break;
            }
            case cir::TypeKind::Place:
                visit_type(std::get<cir::PlaceTypePayload>(payload)
                               .object_type.type);
                break;
            default:
                break;
        }
        if (node.resolved.valid() && node.resolved != type) {
            visit_type(node.resolved);
        }
    };

    visit_argument = [&](const cir::TemplateArgument& argument) {
        visit_type(argument.type.type);
        visit_type(argument.value_type.type);
        visit_type(argument.dependent_value_qualifier.type);
        visit_type(argument.dependent_template_qualifier.type);
        visit_expression(argument.dependent_value_expr);
        if (argument.template_entity.valid() &&
            file_.valid(argument.template_entity) &&
            file_.entity(argument.template_entity).kind ==
                cir::EntityKind::TemplateParam) {
            reference_for_entity(argument.template_entity,
                                 TemplateParameterKind::Template,
                                 0,
                                 argument.template_param_index);
        }
        for (const cir::TemplateArgument& element : argument.value_elements) {
            visit_argument(element);
        }
    };

    visit_expression = [&](const cir::TemplateValueExpression& expression) {
        for (const cir::TemplateValueExprNode& node : expression.nodes) {
            if (node.entity.valid() && file_.valid(node.entity) &&
                file_.entity(node.entity).kind ==
                    cir::EntityKind::TemplateParam) {
                reference_for_entity(node.entity,
                                     TemplateParameterKind::NonType,
                                     0,
                                     node.parameter_index);
            }
            visit_type(node.type);
            visit_type(node.result_type.type);
            visit_type(node.qualifier_type.type);
        }
    };

    visit_expression(form.value_expression);
    for (const NormalizedConstraintNode& node : form.nodes) {
        for (const ConstraintParameterMapping& mapping :
             node.atom.parameter_mapping) {

            visit_argument(mapping.argument);
            if (mapping.argument_pack.has_value()) {
                for (const cir::TemplateArgument& argument :
                     *mapping.argument_pack) {
                    visit_argument(argument);
                }
            }
        }
        for (const cir::TemplateArgument& argument :
             node.concept_id_arguments) {
            visit_argument(argument);
        }
        for (const ConstraintFoldExpansionParameter& parameter :
             node.fold_expansion_parameters) {
            ConstraintParameterReference reference;
            switch (parameter.kind) {
                case ConstraintFoldExpansionParameterKind::Type:
                    reference.parameter_kind = TemplateParameterKind::Type;
                    break;
                case ConstraintFoldExpansionParameterKind::Value:
                case ConstraintFoldExpansionParameterKind::Function:
                    reference.parameter_kind =
                        TemplateParameterKind::NonType;
                    break;
                case ConstraintFoldExpansionParameterKind::Template:
                    reference.parameter_kind =
                        TemplateParameterKind::Template;
                    break;
            }
            reference.parameter_depth = parameter.parameter_depth;
            reference.parameter_index = parameter.parameter_index;
            reference.parameter_entity = parameter.parameter_entity;
            reference.owning_template_entity =
                parameter.owning_template_entity;
            add_reference(std::move(reference));
        }
    }
}

bool Session::type_contains_type_parameter_pack(cir::TypeId type) const {
    std::vector<cir::TypeId> visited;
    return type_contains_type_parameter_pack(type, visited);
}

bool Session::type_contains_type_parameter_pack(
    cir::TypeId type,
    std::vector<cir::TypeId>& visited) const {
    if (!file_.valid(type)) {
        return false;
    }
    auto argument_contains_pack = [&](const cir::TemplateArgument& argument) {
        if (template_argument_is_type(argument)) {
            return type_contains_type_parameter_pack(argument.type.type,
                                                     visited);
        }
        if (template_argument_is_value(argument)) {
            if (argument.value_param_index !=
                    cir::ArrayTypePayload::no_extent_param &&
                template_argument_names_parameter_pack(argument)) {
                return true;
            }
            return type_contains_type_parameter_pack(argument.value_type.type,
                                                     visited) ||
                   type_contains_type_parameter_pack(
                       argument.dependent_value_qualifier.type, visited);
        }
        if (argument.kind == cir::TemplateArgumentKind::Template) {
            if (argument.template_param_index !=
                    cir::ArrayTypePayload::no_extent_param &&
                template_argument_names_parameter_pack(argument)) {
                return true;
            }
            return type_contains_type_parameter_pack(
                argument.dependent_template_qualifier.type, visited);
        }
        return false;
    };
    if (file_.type(type).kind == cir::TypeKind::AliasSpecialization) {
        const auto& specialization =
            std::get<cir::AliasSpecializationTypePayload>(
                file_.type_payload(type));
        return std::any_of(specialization.arguments.begin(),
                           specialization.arguments.end(),
                           argument_contains_pack);
    }

    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return false;
    }
    if (std::find(visited.begin(), visited.end(), resolved) != visited.end()) {
        return false;
    }
    visited.push_back(resolved);

    const cir::Type& node = file_.type(resolved);
    const cir::TypePayload& payload = file_.type_payload(resolved);
    switch (node.kind) {
        case cir::TypeKind::TypeParam: {
            const auto* param =
                std::get_if<cir::TypeParamTypePayload>(&payload);
            return param && param->is_parameter_pack;
        }
        case cir::TypeKind::PackIndex:

            return false;
        case cir::TypeKind::BuiltinPackElement:

            return false;
        case cir::TypeKind::Pointer:
            return type_contains_type_parameter_pack(
                std::get<cir::PointerTypePayload>(payload).pointee.type,
                visited);
        case cir::TypeKind::BlockPointer:
            return type_contains_type_parameter_pack(
                std::get<cir::BlockPointerTypePayload>(payload).pointee.type,
                visited);
        case cir::TypeKind::MemberPointer: {
            const auto& member =
                std::get<cir::MemberPointerTypePayload>(payload);
            return type_contains_type_parameter_pack(member.class_type.type,
                                                     visited) ||
                   type_contains_type_parameter_pack(member.member_type.type,
                                                     visited);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return type_contains_type_parameter_pack(
                std::get<cir::ReferenceTypePayload>(payload).referred_type.type,
                visited);
        case cir::TypeKind::Array: {
            const auto& array = std::get<cir::ArrayTypePayload>(payload);
            return type_contains_type_parameter_pack(array.element_type.type,
                                                     visited);
        }
        case cir::TypeKind::Complex:
            return type_contains_type_parameter_pack(
                std::get<cir::ComplexTypePayload>(payload).element_type.type,
                visited);
        case cir::TypeKind::TypeofExpr: {
            const auto& typeof_expr =
                std::get<cir::TypeofExprTypePayload>(payload);
            return typeof_expr.expr.valid() &&
                   file_.valid(typeof_expr.expr) &&
                   type_contains_type_parameter_pack(
                       file_.inst(typeof_expr.expr).result_type, visited);
        }
        case cir::TypeKind::DecltypeExpr: {
            const auto& decltype_expr =
                std::get<cir::DecltypeExprTypePayload>(payload);
            bool expression_contains_pack = std::any_of(
                decltype_expr.operand_expression.nodes.begin(),
                decltype_expr.operand_expression.nodes.end(),
                [&](const cir::TemplateValueExprNode& expression_node) {
                    return expression_node.expands_parameter_pack ||
                        type_contains_type_parameter_pack(
                            expression_node.type, visited) ||
                        type_contains_type_parameter_pack(
                            expression_node.result_type.type, visited) ||
                        type_contains_type_parameter_pack(
                            expression_node.qualifier_type.type, visited);
                });
            return type_contains_type_parameter_pack(
                       decltype_expr.operand_type.type, visited) ||
                   type_contains_type_parameter_pack(
                       decltype_expr.dependent_value_qualifier.type, visited) ||
                   expression_contains_pack ||
                   (decltype_expr.expr.valid() &&
                    file_.valid(decltype_expr.expr) &&
                    type_contains_type_parameter_pack(
                        file_.inst(decltype_expr.expr).result_type, visited));
        }
        case cir::TypeKind::BuiltinTransform:
            return type_contains_type_parameter_pack(
                std::get<cir::BuiltinTypeTransformTypePayload>(payload)
                    .operand_type.type,
                visited);
        case cir::TypeKind::Place:
            return type_contains_type_parameter_pack(
                file_.place_object_ref(resolved).type, visited);
        case cir::TypeKind::TemplateSpecialization: {
            const auto& specialization =
                std::get<cir::TemplateSpecializationTypePayload>(payload);
            for (const cir::TemplateArgument& argument :
                 specialization.arguments) {
                if (argument_contains_pack(argument)) {
                    return true;
                }
            }
            return false;
        }
        case cir::TypeKind::DependentName: {
            const auto& dependent =
                std::get<cir::DependentNameTypePayload>(payload);
            if (type_contains_type_parameter_pack(
                    dependent.qualifier_type.type, visited)) {
                return true;
            }
            for (const cir::TemplateArgument& argument :
                 dependent.template_arguments) {
                if (argument_contains_pack(argument)) {
                    return true;
                }
            }
            return false;
        }
        case cir::TypeKind::Record: {
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(file_.record_entity(resolved));
            if (!fact) {
                return false;
            }
            for (const cir::TemplateArgument& argument :
                 fact->template_arguments()) {
                if (argument_contains_pack(argument)) {
                    return true;
                }
            }
            return false;
        }
        case cir::TypeKind::Function: {
            const auto& function = std::get<cir::FunctionTypePayload>(payload);
            if (type_contains_type_parameter_pack(
                    function.return_type.type, visited)) {
                return true;
            }
            for (const cir::TypeRef& parameter : function.parameters) {
                if (type_contains_type_parameter_pack(parameter.type,
                                                      visited)) {
                    return true;
                }
            }
            return false;
        }
        default:
            return false;
    }
}

std::optional<std::vector<Session::TemplateArgument>>
Session::template_type_pack_arguments(cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::TypeParam) {
        return std::nullopt;
    }
    const auto& pack =
        std::get<cir::TypeParamTypePayload>(file_.type_payload(resolved));
    if (!pack.is_parameter_pack) {
        return std::nullopt;
    }
    std::string pack_name = file_.name(pack.name);
    auto elements_from_bindings =
        [&](const TemplateArgumentBindings& bindings)
            -> std::optional<std::vector<TemplateArgument>> {
        if (pack.index >= bindings.size() ||
            !bindings[pack.index].is_pack()) {
            return std::nullopt;
        }
        std::vector<TemplateArgument> elements;
        elements.reserve(bindings[pack.index].arguments.size());
        for (const TemplateArgument& argument :
             bindings[pack.index].arguments) {
            if (!template_argument_is_type(argument)) {
                return std::nullopt;
            }
            TemplateArgument element = argument;
            element.expands_parameter_pack = false;
            elements.push_back(std::move(element));
        }
        return elements;
    };
    auto parameter_matches_pack =
        [&](const std::vector<TemplateParameter>& parameters) {
            if (pack.index >= parameters.size()) {
                return false;
            }
            const TemplateParameter& parameter = parameters[pack.index];
            if (parameter.kind != TemplateParameterKind::Type ||
                !parameter.is_parameter_pack) {
                return false;
            }
            if (parameter.type_param_type.valid()) {
                return file_.resolved_type(parameter.type_param_type) ==
                    resolved;
            }
            return parameter.depth == pack.depth &&
                parameter.index == pack.index &&
                parameter.name == pack_name;
        };
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (!frame->info || frame->memo_key.empty()) {
            continue;
        }
        if (parameter_matches_pack(frame->info->parameters)) {
            return elements_from_bindings(frame->argument_bindings);
        }

        for (auto enclosing =
                 frame->info->enclosing_instantiation_bindings.rbegin();
             enclosing !=
                 frame->info->enclosing_instantiation_bindings.rend();
             ++enclosing) {
            if (parameter_matches_pack(enclosing->parameters)) {
                return elements_from_bindings(
                    enclosing->argument_bindings);
            }
        }
    }
    for (cir::DeclContextId context = current_decl_context();
         context.valid();
         context = file_.decl_context(context).parent) {
        cir::EntityId owner = file_.decl_context(context).owner;
        const cir::TemplateSpecializationFact* fact =
            owner.valid() ? file_.template_specialization(owner) : nullptr;
        const TemplateInfo* fact_info =
            fact ? template_info(fact->template_entity) : nullptr;
        if (!fact_info ||
            !parameter_matches_pack(fact_info->parameters)) {
            continue;
        }
        return elements_from_bindings(fact->argument_bindings);
    }
    return std::nullopt;
}

std::optional<std::vector<Session::TemplateArgument>>
Session::template_type_pack_arguments(
    const TypeParameterPackPattern& pack) const {
    auto elements_from_bindings =
        [&](const TemplateArgumentBindings& bindings)
            -> std::optional<std::vector<TemplateArgument>> {
        if (pack.index >= bindings.size() ||
            !bindings[pack.index].is_pack()) {
            return std::nullopt;
        }
        std::vector<TemplateArgument> elements;
        elements.reserve(bindings[pack.index].arguments.size());
        for (const TemplateArgument& argument :
             bindings[pack.index].arguments) {
            if (!template_argument_is_type(argument)) {
                return std::nullopt;
            }
            TemplateArgument element = argument;
            element.expands_parameter_pack = false;
            elements.push_back(std::move(element));
        }
        return elements;
    };
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (!frame->info || frame->memo_key.empty() ||
            pack.index >= frame->info->parameters.size()) {
            continue;
        }
        if (pack.template_entity.valid() &&
            frame->info->entity != pack.template_entity) {
            continue;
        }
        const TemplateParameter& parameter =
            frame->info->parameters[pack.index];
        if (parameter.kind != TemplateParameterKind::Type ||
            !parameter.is_parameter_pack ||
            parameter.depth != pack.depth ||
            parameter.index != pack.index ||
            parameter.name != pack.name) {
            continue;
        }
        return elements_from_bindings(frame->argument_bindings);
    }
    if (pack.template_entity.valid()) {
        for (cir::DeclContextId context = current_decl_context();
             context.valid();
             context = file_.decl_context(context).parent) {
            cir::EntityId owner = file_.decl_context(context).owner;
            const cir::TemplateSpecializationFact* fact =
                owner.valid() ? file_.template_specialization(owner) : nullptr;
            if (!fact ||
                (pack.template_entity.valid() &&
                 fact->template_entity != pack.template_entity)) {
                continue;
            }
            const TemplateInfo* fact_info = template_info(fact->template_entity);
            if (!fact_info || pack.index >= fact_info->parameters.size()) {
                continue;
            }
            const TemplateParameter& parameter =
                fact_info->parameters[pack.index];
            if (parameter.kind != TemplateParameterKind::Type ||
                !parameter.is_parameter_pack ||
                parameter.depth != pack.depth ||
                parameter.index != pack.index ||
                parameter.name != pack.name) {
                continue;
            }
            return elements_from_bindings(fact->argument_bindings);
        }
    }
    if (pack.type.valid()) {
        return template_type_pack_arguments(pack.type);
    }
    return std::nullopt;
}

std::optional<uint32_t>
Session::type_parameter_pack_index(cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return std::nullopt;
    }

    const cir::Type& node = file_.type(resolved);
    const cir::TypePayload& payload = file_.type_payload(resolved);
    auto argument_pack_index = [&](const TemplateArgument& argument)
        -> std::optional<uint32_t> {
        if (template_argument_is_type(argument)) {
            return type_parameter_pack_index(argument.type.type);
        }
        if (template_argument_is_value(argument) &&
            argument.value_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
            return argument.value_param_index;
        }
        if (argument.kind == cir::TemplateArgumentKind::Template &&
            argument.template_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
            return argument.template_param_index;
        }
        return std::nullopt;
    };
    auto arguments_pack_index =
        [&](const std::vector<TemplateArgument>& arguments)
        -> std::optional<uint32_t> {
        for (const TemplateArgument& argument : arguments) {
            if (std::optional<uint32_t> index =
                    argument_pack_index(argument)) {
                return index;
            }
        }
        return std::nullopt;
    };
    switch (node.kind) {
        case cir::TypeKind::TypeParam: {
            const auto* parameter =
                std::get_if<cir::TypeParamTypePayload>(&payload);
            if (!parameter || !parameter->is_parameter_pack) {
                return std::nullopt;
            }
            return parameter->index;
        }
        case cir::TypeKind::Pointer:
            return type_parameter_pack_index(
                std::get<cir::PointerTypePayload>(payload).pointee.type);
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return type_parameter_pack_index(
                std::get<cir::ReferenceTypePayload>(payload)
                    .referred_type.type);
        case cir::TypeKind::Array:
            return type_parameter_pack_index(
                std::get<cir::ArrayTypePayload>(payload).element_type.type);
        case cir::TypeKind::MemberPointer: {
            const auto& member =
                std::get<cir::MemberPointerTypePayload>(payload);
            if (std::optional<uint32_t> index =
                    type_parameter_pack_index(member.member_type.type)) {
                return index;
            }
            return type_parameter_pack_index(member.class_type.type);
        }
        case cir::TypeKind::TemplateSpecialization:
            return arguments_pack_index(
                std::get<cir::TemplateSpecializationTypePayload>(payload)
                    .arguments);
        case cir::TypeKind::DependentName:
            return arguments_pack_index(
                std::get<cir::DependentNameTypePayload>(payload)
                    .template_arguments);
        case cir::TypeKind::Record: {
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(file_.record_entity(resolved));
            return fact ? arguments_pack_index(fact->template_arguments())
                        : std::nullopt;
        }
        default:
            return std::nullopt;
    }
}

std::optional<cir::TypeId>
Session::type_parameter_pack_type(std::string_view name) const {
    cir::TypeRef type = lookup_active_template_header_type_parameter(name);
    if (!type.valid()) {
        const cir::Binding* binding = lookup_type_name_binding(name);
        if (binding) {
            type = binding->type;
        }
    }
    if (!type.type.valid()) {
        return std::nullopt;
    }
    cir::TypeId resolved = file_.resolved_type(type.type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::TypeParam) {
        return std::nullopt;
    }
    const auto& parameter =
        std::get<cir::TypeParamTypePayload>(file_.type_payload(resolved));
    if (!parameter.is_parameter_pack) {
        return std::nullopt;
    }
    return type.type;
}

std::optional<Session::TypeParameterPackPattern>
type_parameter_pack_pattern_from_type(const Session& session,
                                      cir::TypeId type,
                                      std::string_view name) {
    const cir::File& file = session.file();
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::TypeParam) {
        return std::nullopt;
    }
    const auto& parameter =
        std::get<cir::TypeParamTypePayload>(file.type_payload(resolved));
    if (!parameter.is_parameter_pack) {
        return std::nullopt;
    }
    Session::TypeParameterPackPattern pattern;
    pattern.name = std::string(name);
    pattern.depth = parameter.depth;
    pattern.index = parameter.index;
    pattern.type = type;
    return pattern;
}

bool Session::capture_type_parameter_pack_name(std::string_view name) {
    return capture_parameter_pack(ParameterPackKind::Type, name);
}

namespace {

bool same_parameter_pack_identity(
    const Session::ParameterPackIdentity& lhs,
    const Session::ParameterPackIdentity& rhs) {
    if (lhs.kind != rhs.kind) {
        return false;
    }
    if (lhs.is_unbound_template_parameter !=
        rhs.is_unbound_template_parameter) {
        return false;
    }

    if (lhs.owner.valid() && rhs.owner.valid()) {
        return lhs.owner == rhs.owner && lhs.depth == rhs.depth &&
               lhs.index == rhs.index;
    }
    if (lhs.declaration.valid() && rhs.declaration.valid()) {
        return lhs.declaration == rhs.declaration;
    }
    return lhs.depth == rhs.depth && lhs.index == rhs.index &&
           lhs.name == rhs.name;
}

} // namespace

std::optional<Session::ParameterPackIdentity>
Session::parameter_pack_identity(ParameterPackKind kind,
                                 std::string_view name) const {
    ParameterPackIdentity identity;
    identity.kind = kind;
    identity.name = std::string(name);
    if (active_template_header_info_) {
        const TemplateParameter* active_parameter = nullptr;
        for (auto parameter = active_template_header_info_->parameters.rbegin();
             parameter != active_template_header_info_->parameters.rend();
             ++parameter) {
            if (parameter->name == name) {
                active_parameter = &*parameter;
                break;
            }
        }
        if (active_parameter) {
            ParameterPackKind active_kind = ParameterPackKind::Type;
            switch (active_parameter->kind) {
                case TemplateParameterKind::Type:
                    active_kind = ParameterPackKind::Type;
                    break;
                case TemplateParameterKind::NonType:
                    active_kind = ParameterPackKind::Value;
                    break;
                case TemplateParameterKind::Template:
                    active_kind = ParameterPackKind::Template;
                    break;
            }

            if (!active_parameter->is_parameter_pack || active_kind != kind) {
                return std::nullopt;
            }
            identity.is_unbound_template_parameter = true;
        }
    }
    auto assign_owner_from_frame = [&](uint32_t index,
                                       TemplateParameterKind expected) {
        if (identity.is_unbound_template_parameter) {
            return;
        }
        auto assign_from_parameters =
            [&](const std::vector<TemplateParameter>& parameters,
                cir::EntityId owner) {
                if (index >= parameters.size()) {
                    return false;
                }
                const TemplateParameter& parameter = parameters[index];
                if (parameter.kind != expected ||
                    !parameter.is_parameter_pack ||
                    parameter.name != name) {
                    return false;
                }

                if (identity.parameter_type.valid() &&
                    parameter.type_param_type.valid() &&
                    file_.resolved_type(identity.parameter_type) !=
                        file_.resolved_type(parameter.type_param_type)) {
                    return false;
                }
                identity.owner = owner;
                identity.depth = parameter.depth;
                identity.index = parameter.index;
                identity.parameter_type = parameter.type_param_type;
                if (parameter.entity.valid()) {
                    identity.declaration = parameter.entity;
                }
                return true;
            };
        for (auto frame = tstate().current_instantiation_frames_.rbegin();
             frame != tstate().current_instantiation_frames_.rend(); ++frame) {
            if (!frame->info) {
                continue;
            }
            if (assign_from_parameters(frame->info->parameters,
                                       frame->info->entity)) {
                return;
            }
            for (auto enclosing =
                     frame->info->enclosing_instantiation_bindings.rbegin();
                 enclosing !=
                     frame->info->enclosing_instantiation_bindings.rend();
                 ++enclosing) {
                if (assign_from_parameters(enclosing->parameters, {})) {
                    return;
                }
            }
        }
        for (cir::DeclContextId context = current_decl_context();
             context.valid();
             context = file_.decl_context(context).parent) {
            cir::EntityId owner = file_.decl_context(context).owner;
            const cir::TemplateSpecializationFact* fact =
                owner.valid() ? file_.template_specialization(owner)
                              : nullptr;
            const TemplateInfo* fact_info =
                fact ? template_info(fact->template_entity) : nullptr;
            if (fact_info &&
                assign_from_parameters(fact_info->parameters,
                                       fact->template_entity)) {
                return;
            }
        }
    };
    switch (kind) {
        case ParameterPackKind::Function: {
            if (!function_parameter_pack_name(name)) {
                return std::nullopt;
            }
            if (const cir::Binding* binding = lookup_ordinary_binding(name)) {
                for (cir::EntityId entity : binding->entities) {
                    if (entity.valid() &&
                        tstate().function_parameter_pack_params_.contains(
                            static_cast<uint64_t>(entity.index))) {
                        identity.declaration = entity;
                        identity.owner = file_.entity(entity).parent;
                        break;
                    }
                }
            }
            auto element_pack =
                tstate().function_parameter_pack_elements_.find(identity.name);
            if (!identity.declaration.valid() &&
                element_pack != tstate().function_parameter_pack_elements_.end() &&
                !element_pack->second.empty()) {
                identity.declaration = element_pack->second.front().entity;
                if (identity.declaration.valid() &&
                    file_.valid(identity.declaration)) {
                    identity.owner = file_.entity(identity.declaration).parent;
                }
            }
            auto template_index =
                tstate().function_parameter_pack_template_indices_.find(
                    identity.name);
            if (template_index !=
                tstate().function_parameter_pack_template_indices_.end()) {
                identity.index = template_index->second;
                assign_owner_from_frame(identity.index,
                                        TemplateParameterKind::Type);
            } else if (identity.declaration.valid() &&
                       file_.valid(identity.declaration)) {

                if (std::optional<uint32_t> declaration_index =
                        type_parameter_pack_index(
                            file_.entity(identity.declaration).type)) {
                    identity.index = *declaration_index;
                    assign_owner_from_frame(identity.index,
                                            TemplateParameterKind::Type);
                }
            }
            return identity;
        }
        case ParameterPackKind::Type: {
            std::optional<cir::TypeId> pack_type =
                type_parameter_pack_type(name);
            if (!pack_type.has_value()) {
                return std::nullopt;
            }
            std::optional<TypeParameterPackPattern> pattern =
                type_parameter_pack_pattern_from_type(*this, *pack_type, name);
            if (!pattern.has_value()) {
                return std::nullopt;
            }
            identity.depth = pattern->depth;
            identity.index = pattern->index;
            identity.parameter_type = pattern->type;
            cir::TypeId resolved = file_.resolved_type(*pack_type);
            if (file_.valid(resolved) &&
                file_.type(resolved).kind == cir::TypeKind::TypeParam) {
                identity.declaration =
                    std::get<cir::TypeParamTypePayload>(
                        file_.type_payload(resolved)).entity;
            }
            assign_owner_from_frame(identity.index,
                                    TemplateParameterKind::Type);
            return identity;
        }
        case ParameterPackKind::Value: {
            std::optional<uint32_t> index =
                template_value_pack_param_index_for_name(name);
            if (!index.has_value()) {
                return std::nullopt;
            }
            identity.index = *index;
            if (const cir::Binding* binding = lookup_ordinary_binding(name)) {
                for (cir::EntityId entity : binding->entities) {
                    if (template_value_param_is_pack(entity)) {
                        identity.declaration = entity;
                        if (const TemplateParameter* parameter =
                                template_value_parameter_for_entity(entity)) {
                            identity.depth = parameter->depth;
                            identity.index = parameter->index;
                            identity.parameter_type =
                                parameter->non_type_type;
                            identity.is_unbound_template_parameter = true;
                        }
                        break;
                    }
                }
            }
            assign_owner_from_frame(*index, TemplateParameterKind::NonType);
            return identity;
        }
        case ParameterPackKind::Template: {
            const TemplateInfo* info =
                template_parameter_pack_info_for_name(name);
            if (!info || !info->is_template_parameter_pack) {
                return std::nullopt;
            }
            identity.declaration = info->entity;
            identity.index = info->template_parameter_index;
            assign_owner_from_frame(identity.index,
                                    TemplateParameterKind::Template);
            return identity;
        }
    }
    return std::nullopt;
}

bool Session::capture_parameter_pack(ParameterPackKind kind,
                                     std::string_view name) {
    if (tstate().parameter_pack_pattern_captures_.empty()) {
        return false;
    }
    std::optional<ParameterPackIdentity> identity =
        parameter_pack_identity(kind, name);
    if (!identity.has_value()) {
        return false;
    }
    std::vector<ParameterPackIdentity>& capture =
        tstate().parameter_pack_pattern_captures_.back();
    if (std::none_of(capture.begin(), capture.end(), [&](const auto& existing) {
            return same_parameter_pack_identity(existing, *identity);
        })) {
        capture.push_back(std::move(*identity));
    }
    return true;
}

bool Session::capture_any_parameter_pack_name(std::string_view name) {
    bool captured = false;
    for (ParameterPackKind kind : {ParameterPackKind::Function,
                                   ParameterPackKind::Type,
                                   ParameterPackKind::Value,
                                   ParameterPackKind::Template}) {
        captured = capture_parameter_pack(kind, name) || captured;
    }
    return captured;
}

const Session::ParameterPackElement* Session::parameter_pack_replay_element(
    ParameterPackKind kind,
    std::string_view name) const {

    if (active_template_header_info_ &&
        std::any_of(active_template_header_info_->parameters.begin(),
                    active_template_header_info_->parameters.end(),
                    [name](const TemplateParameter& parameter) {
                        return parameter.name == name;
                    })) {
        return nullptr;
    }
    std::optional<ParameterPackIdentity> requested =
        parameter_pack_identity(kind, name);
    const ParameterPackElement* unique_named = nullptr;
    for (auto it = tstate().parameter_pack_element_replay_bindings_.rbegin();
         it != tstate().parameter_pack_element_replay_bindings_.rend(); ++it) {
        if (it->pack.kind != kind) {
            continue;
        }
        if (requested.has_value() &&
            same_parameter_pack_identity(it->pack, *requested)) {
            return &it->element;
        }
        if (it->pack.name == name) {
            if (unique_named) {
                unique_named = nullptr;
                break;
            }
            unique_named = &it->element;
        }
    }

    return unique_named;
}

std::optional<size_t> Session::parameter_pack_element_count(
    const ParameterPackIdentity& pack) const {
    if (pack.is_unbound_template_parameter) {
        return std::nullopt;
    }
    switch (pack.kind) {
        case ParameterPackKind::Function: {
            auto found = tstate().function_parameter_pack_elements_.find(
                pack.name);
            if (found == tstate().function_parameter_pack_elements_.end()) {
                return std::nullopt;
            }
            return found->second.size();
        }
        case ParameterPackKind::Type: {
            std::optional<cir::TypeId> type =
                type_parameter_pack_type(pack.name);
            std::optional<std::vector<TemplateArgument>> arguments =
                type.has_value() ? template_type_pack_arguments(*type)
                                 : std::nullopt;
            return arguments.has_value()
                ? std::optional<size_t>(arguments->size())
                : std::nullopt;
        }
        case ParameterPackKind::Value: {
            std::optional<std::vector<TemplateArgument>> arguments =
                template_argument_pack_arguments(pack);
            return arguments.has_value()
                ? std::optional<size_t>(arguments->size())
                : std::nullopt;
        }
        case ParameterPackKind::Template: {
            std::optional<std::vector<TemplateArgument>> arguments =
                template_argument_pack_arguments(pack);
            return arguments.has_value()
                ? std::optional<size_t>(arguments->size())
                : std::nullopt;
        }
    }
    return std::nullopt;
}

Session::ParameterPackElementReplayScope
Session::begin_parameter_pack_element_replay(
    const std::vector<ParameterPackIdentity>& packs,
    size_t index) {
    std::vector<ParameterPackElementBinding> bindings;
    bindings.reserve(packs.size());
    for (const ParameterPackIdentity& pack : packs) {
        if (pack.is_unbound_template_parameter) {
            return {};
        }
        ParameterPackElementBinding binding;
        binding.pack = pack;
        switch (pack.kind) {
            case ParameterPackKind::Function: {
                auto found = tstate().function_parameter_pack_elements_.find(
                    pack.name);
                if (found == tstate().function_parameter_pack_elements_.end() ||
                    index >= found->second.size()) {
                    return {};
                }
                binding.element = found->second[index];
                break;
            }
            case ParameterPackKind::Type: {
                std::optional<cir::TypeId> type =
                    type_parameter_pack_type(pack.name);
                std::optional<std::vector<TemplateArgument>> elements =
                    type.has_value() ? template_type_pack_arguments(*type)
                                     : std::nullopt;
                if (!elements.has_value() || index >= elements->size() ||
                    !template_argument_is_type((*elements)[index])) {
                    return {};
                }
                binding.element = (*elements)[index].type;
                break;
            }
            case ParameterPackKind::Value:
            case ParameterPackKind::Template: {
                std::optional<std::vector<TemplateArgument>> elements =
                    template_argument_pack_arguments(pack);
                if (!elements.has_value() || index >= elements->size()) {
                    return {};
                }
                const TemplateArgument& element = (*elements)[index];
                if ((pack.kind == ParameterPackKind::Value &&
                     !template_argument_is_value(element)) ||
                    (pack.kind == ParameterPackKind::Template &&
                     element.kind != cir::TemplateArgumentKind::Template)) {
                    return {};
                }
                binding.element = element;
                break;
            }
        }
        bindings.push_back(std::move(binding));
    }
    return begin_parameter_pack_element_replay(bindings);
}

Session::ParameterPackElementReplayScope
Session::begin_parameter_pack_element_replay(
    const std::vector<ParameterPackElementBinding>& bindings) {
    ParameterPackElementReplayScope scope;
    scope.active = true;
    scope.depth = tstate().parameter_pack_element_replay_stack_.size();
    tstate().parameter_pack_element_replay_stack_.push_back(
        tstate().parameter_pack_element_replay_bindings_);
    for (const ParameterPackElementBinding& binding : bindings) {
        tstate().parameter_pack_element_replay_bindings_.push_back(binding);
    }
    return scope;
}

void Session::finish_parameter_pack_element_replay(
    ParameterPackElementReplayScope scope) {
    if (!scope.active ||
        scope.depth >= tstate().parameter_pack_element_replay_stack_.size()) {
        return;
    }
    tstate().parameter_pack_element_replay_bindings_ =
        std::move(tstate().parameter_pack_element_replay_stack_[scope.depth]);
    tstate().parameter_pack_element_replay_stack_.resize(scope.depth);
}

bool Session::template_argument_names_parameter_pack(
    const TemplateArgument& argument) const {
    if (argument.expands_pack_pattern) {
        return true;
    }
    if (argument.kind == cir::TemplateArgumentKind::Type) {
        return type_contains_type_parameter_pack(argument.type.type);
    }
    if (argument.kind != cir::TemplateArgumentKind::Value ||
        argument.value_param_index == cir::ArrayTypePayload::no_extent_param) {
        if (argument.kind != cir::TemplateArgumentKind::Template ||
            argument.template_param_index ==
                cir::ArrayTypePayload::no_extent_param) {
            return false;
        }
    }
    auto matches_parameter_pack = [&](const TemplateInfo* info,
                                      TemplateParameterKind kind,
                                      uint32_t index) {
        if (!info ||
            index >= info->parameters.size()) {
            return false;
        }
        const TemplateParameter& parameter = info->parameters[index];
        return parameter.kind == kind &&
               parameter.is_parameter_pack;
    };
    TemplateParameterKind kind = argument.kind == cir::TemplateArgumentKind::Value
        ? TemplateParameterKind::NonType
        : TemplateParameterKind::Template;
    uint32_t index = argument.kind == cir::TemplateArgumentKind::Value
        ? argument.value_param_index
        : argument.template_param_index;
    const TemplateInfo* argument_template =
        argument.kind == cir::TemplateArgumentKind::Template
            ? template_info(argument.template_entity)
            : nullptr;
    if (argument_template && argument_template->is_template_parameter_pack) {
        return true;
    }
    if (matches_parameter_pack(validating_template_info_, kind, index)) {
        return true;
    }
    if (matches_parameter_pack(active_template_header_info_, kind, index)) {
        return true;
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (matches_parameter_pack(frame->info, kind, index)) {
            return true;
        }
    }
    return false;
}

std::optional<std::vector<Session::TemplateArgument>>
Session::template_argument_pack_arguments(
    const TemplateArgument& argument) const {
    if (argument.kind == cir::TemplateArgumentKind::Type) {
        return template_type_pack_arguments(argument.type.type);
    }
    if ((argument.kind != cir::TemplateArgumentKind::Value ||
         argument.value_param_index == cir::ArrayTypePayload::no_extent_param) &&
        (argument.kind != cir::TemplateArgumentKind::Template ||
         argument.template_param_index ==
             cir::ArrayTypePayload::no_extent_param)) {
        return std::nullopt;
    }
    TemplateParameterKind expected_parameter_kind =
        argument.kind == cir::TemplateArgumentKind::Value
            ? TemplateParameterKind::NonType
            : TemplateParameterKind::Template;
    uint32_t pack_index = argument.kind == cir::TemplateArgumentKind::Value
        ? argument.value_param_index
        : argument.template_param_index;
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (!frame->info || frame->memo_key.empty() ||
            pack_index >= frame->info->parameters.size()) {
            continue;
        }
        const TemplateParameter& parameter =
            frame->info->parameters[pack_index];
        if (parameter.kind != expected_parameter_kind ||
            !parameter.is_parameter_pack) {
            continue;
        }

        if (argument.kind == cir::TemplateArgumentKind::Value &&
            !argument.value_spelling.empty() &&
            parameter.name != argument.value_spelling) {
            continue;
        }
        if (pack_index >= frame->argument_bindings.size() ||
            !frame->argument_bindings[pack_index].is_pack()) {
            return std::nullopt;
        }
        std::vector<TemplateArgument> elements;
        const std::vector<TemplateArgument>& pack_arguments =
            frame->argument_bindings[pack_index].arguments;
        elements.reserve(pack_arguments.size());
        for (const TemplateArgument& pack_argument : pack_arguments) {
            if (pack_argument.kind != argument.kind) {
                return std::nullopt;
            }
            TemplateArgument element = pack_argument;
            element.expands_parameter_pack = false;
            elements.push_back(std::move(element));
        }
        return elements;
    }
    return std::nullopt;
}

std::optional<std::vector<Session::TemplateArgument>>
Session::template_argument_pack_arguments(
    const ParameterPackIdentity& pack) const {
    if (pack.kind == ParameterPackKind::Type) {
        return pack.parameter_type.valid()
            ? template_type_pack_arguments(pack.parameter_type)
            : std::nullopt;
    }
    if (pack.kind != ParameterPackKind::Value &&
        pack.kind != ParameterPackKind::Template) {
        return std::nullopt;
    }
    TemplateParameterKind expected_kind =
        pack.kind == ParameterPackKind::Value
            ? TemplateParameterKind::NonType
            : TemplateParameterKind::Template;
    cir::TemplateArgumentKind expected_argument_kind =
        pack.kind == ParameterPackKind::Value
            ? cir::TemplateArgumentKind::Value
            : cir::TemplateArgumentKind::Template;
    auto parameter_matches =
        [&](const std::vector<TemplateParameter>& parameters) {
            if (pack.index >= parameters.size()) {
                return false;
            }
            const TemplateParameter& parameter = parameters[pack.index];
            return parameter.kind == expected_kind &&
                parameter.is_parameter_pack &&
                parameter.depth == pack.depth &&
                parameter.index == pack.index &&
                parameter.name == pack.name;
        };
    auto elements_from_bindings =
        [&](const TemplateArgumentBindings& bindings)
            -> std::optional<std::vector<TemplateArgument>> {
            if (pack.index >= bindings.size() ||
                !bindings[pack.index].is_pack()) {
                return std::nullopt;
            }
            std::vector<TemplateArgument> elements;
            const std::vector<TemplateArgument>& arguments =
                bindings[pack.index].arguments;
            elements.reserve(arguments.size());
            for (const TemplateArgument& argument : arguments) {
                if (argument.kind != expected_argument_kind) {
                    return std::nullopt;
                }
                TemplateArgument element = argument;
                element.expands_parameter_pack = false;
                elements.push_back(std::move(element));
            }
            return elements;
        };
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (!frame->info || frame->memo_key.empty() ||
            (pack.owner.valid() && frame->info->entity != pack.owner)) {
            continue;
        }
        if (parameter_matches(frame->info->parameters)) {
            return elements_from_bindings(frame->argument_bindings);
        }
        for (auto enclosing =
                 frame->info->enclosing_instantiation_bindings.rbegin();
             enclosing !=
                 frame->info->enclosing_instantiation_bindings.rend();
             ++enclosing) {
            if (parameter_matches(enclosing->parameters)) {
                return elements_from_bindings(enclosing->argument_bindings);
            }
        }
    }
    for (cir::DeclContextId context = current_decl_context();
         context.valid();
         context = file_.decl_context(context).parent) {
        cir::EntityId owner = file_.decl_context(context).owner;
        const cir::TemplateSpecializationFact* fact =
            owner.valid() ? file_.template_specialization(owner) : nullptr;
        const TemplateInfo* fact_info =
            fact ? template_info(fact->template_entity) : nullptr;
        if (!fact_info ||
            (pack.owner.valid() && fact->template_entity != pack.owner) ||
            !parameter_matches(fact_info->parameters)) {
            continue;
        }
        return elements_from_bindings(fact->argument_bindings);
    }
    return std::nullopt;
}

cir::EntityId Session::create_incomplete_record_specialization(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {

    std::string display = template_display_name(info, arguments);
    cir::EntityId entity = builder_.add_entity(
        cir::EntityKind::Record, display, {}, {}, loc);
    cir::Entity& record = file_.entity_mut(entity);
    record.is_definition = false;
    record.type = file_.record_type(
        entity,
        std::string(cir::record_kind_name(info.record_kind)) + " " + display);
    cir::RecordFacts facts;
    facts.entity = entity;
    facts.type = file_.type_ref(record.type);
    facts.kind = info.record_kind;
    facts.is_incomplete = true;
    file_.set_record_facts(entity, std::move(facts));
    remember_template_specialization(entity, info, arguments);
    if (const cir::TemplateSpecializationFact* stored =
            file_.template_specialization(entity)) {
        cir::TemplateSpecializationFact fact = *stored;
        fact.instantiation_demands.push_back(cir::InstantiationDemandFact{
            cir::InstantiationDemandKind::Identity,
            cir::InstantiationDemandStatus::Satisfied,
            {},
            loc,
            0,
            0});
        file_.set_template_specialization(entity, std::move(fact));
    }
    return entity;
}

cir::EntityId Session::create_dependent_record_specialization(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    return create_incomplete_record_specialization(info, arguments, loc);
}

cir::EntityId Session::create_dependent_variable_specialization(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    std::string display = template_display_name(info, arguments);
    cir::TypeRef pattern_type = info.variable_type_ref.valid()
        ? info.variable_type_ref
        : type_ref(info.variable_type);
    cir::TypeId placeholder_type = pattern_type.type.valid()
        ? pattern_type.type
        : auto_type(cir::AutoTypeFlavor::Cxx);
    const cir::Entity* primary =
        info.entity.valid() && file_.valid(info.entity)
            ? &file_.entity(info.entity)
            : nullptr;
    cir::EntityId entity = builder_.add_entity(
        cir::EntityKind::Variable,
        display,
        placeholder_type,
        {},
        loc,
        primary ? primary->storage_duration : cir::StorageDuration::Static,
        primary ? primary->memory_space : cir::MemorySpace::Default,
        primary ? primary->decl_flags : cir::DeclSemanticFlags{});
    cir::Entity& variable = file_.entity_mut(entity);
    variable.is_definition = false;
    variable.qualifiers = pattern_type.qualifiers;
    if (primary) {
        variable.linkage = primary->linkage;
        variable.module_attachment = primary->module_attachment;
        variable.origin_unit = primary->origin_unit;
        variable.origin_fragment = primary->origin_fragment;
    }

    variable.has_constant_value = false;
    variable.has_initializer = info.has_definition;
    variable.initializer_is_value_dependent = true;
    remember_template_specialization(entity, info, arguments, loc);
    return entity;
}

cir::EntityId Session::create_function_template_declaration_specialization(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    PatternInstantiationCallbacks& callbacks,
    SrcLoc loc,
    cir::TypeId declared_type,
    const TemplateArgumentBindings* exact_bindings) {
    if (info.is_class_template || info.is_alias_template ||
        info.is_variable_template || info.is_concept ||
        !info.pattern_type.valid()) {
        return {};
    }
    cir::TypeId function_type = declared_type;
    if (!function_type.valid()) {
        TemplateArgumentBindings argument_bindings;
        if (exact_bindings) {
            argument_bindings = *exact_bindings;
        } else {
            if (!bind_template_arguments_to_parameters(info.parameters,
                                                       arguments,
                                                       argument_bindings)) {
                return {};
            }
        }
        function_type = substitute_pattern_type(info.pattern_type,
                                                argument_bindings,
                                                callbacks);
    }
    cir::TypeId resolved = file_.resolved_type(function_type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Function) {
        return {};
    }

    std::string display = template_display_name(info, arguments);
    cir::DeclSemanticFlags flags{};
    cir::EntityAttributeFacts inherited_attr_facts{};
    bool has_inherited_attr_facts = false;
    cir::DeclContextId lexical_context = info.lexical_context;
    cir::DeclContextId semantic_context{};
    cir::EntityId parent{};
    bool is_record_member = false;
    bool is_static_member_function = false;
    bool is_extern_c = in_extern_c_linkage();
    cir::EntityId declaration_entity = info.entity;
    if (info.pattern_function.valid() &&
        file_.valid(info.pattern_function)) {
        cir::EntityId pattern_entity =
            file_.function(info.pattern_function).entity;
        if (pattern_entity.valid() && file_.valid(pattern_entity)) {

            declaration_entity = pattern_entity;
        }
    }
    if (declaration_entity.valid() && file_.valid(declaration_entity)) {
        const cir::Entity& primary = file_.entity(declaration_entity);
        flags = primary.decl_flags;
        lexical_context = primary.lexical_context;
        semantic_context = primary.semantic_context;
        is_extern_c = primary.is_extern_c;
        inherited_attr_facts = primary.attr_facts;
        has_inherited_attr_facts = true;
        if (info.entity.valid() && file_.valid(info.entity) &&
            info.entity != declaration_entity) {
            merge_entity_attribute_facts(inherited_attr_facts,
                                         file_.entity(info.entity).attr_facts);
        }
        is_record_member = primary.is_record_member;
        is_static_member_function = primary.is_static_member_function;
        if (is_static_member_function && primary.parent.valid()) {
            parent = primary.parent;
        } else if (info.is_member_template_specialization_overlay &&
            semantic_context.valid() && file_.valid(semantic_context) &&
            file_.decl_context(semantic_context).kind ==
                cir::DeclContextKind::Record) {
            parent = file_.decl_context(semantic_context).owner;
        }
    }

    flags.is_consteval = flags.is_consteval ||
        consteval_only_function_type_immediately_escalates(
            function_type,
            flags.is_constexpr,
            cir::EntityKind::Function,
            /*instantiated_templated_entity=*/true);

    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Function,
                                               display,
                                               function_type,
                                               parent,
                                               loc,
                                               cir::StorageDuration::Unknown,
                                               cir::MemorySpace::Default,
                                               flags);
    cir::Entity& specialization = file_.entity_mut(entity);
    specialization.is_definition = info.is_deleted;
    specialization.is_deleted = info.is_deleted;
    specialization.linkage = cir::LinkageKind::External;
    specialization.is_extern_c = is_extern_c;
    specialization.lexical_context = lexical_context;
    specialization.semantic_context = semantic_context;
    specialization.is_record_member = is_record_member;
    specialization.is_static_member_function = is_static_member_function;
    if (has_inherited_attr_facts) {
        specialization.attr_facts = std::move(inherited_attr_facts);
    } else {
        apply_attributes(entity,
                         AttributeTarget::Function,
                         info.declaration_attrs,
                         loc);
    }
    remember_template_specialization(entity,
                                     info,
                                     arguments,
                                     loc,
                                     callbacks.point_lookup_generation,
                                     nullptr,
                                     nullptr,
                                     exact_bindings);
    inherit_function_template_default_arguments(entity, info);
    apply_explicit_instantiation_declaration_suppression(
        entity, info, arguments);
    return entity;
}

void Session::inherit_function_template_default_arguments(
    cir::EntityId specialization,
    const TemplateInfo& info) {
    if (!specialization.valid() || !file_.valid(specialization)) {
        return;
    }
    auto copy_from = [&](cir::EntityId source) {
        auto found = function_default_arguments_.find(
            static_cast<uint64_t>(source.index));
        if (found == function_default_arguments_.end()) {
            return false;
        }
        uint64_t key = static_cast<uint64_t>(specialization.index);
        journal_speculative_map_entry(
            "function-template default-argument inheritance",
            function_default_arguments_,
            key);
        function_default_arguments_[key] = found->second;
        return true;
    };
    if (info.pattern_function.valid() &&
        file_.valid(info.pattern_function)) {
        cir::EntityId pattern = file_.function(info.pattern_function).entity;
        if (copy_from(pattern)) {
            return;
        }
    }
    (void)copy_from(info.entity);
}

cir::EntityId Session::create_alias_template_specialization(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    cir::TypeRef associated_type,
    SrcLoc loc) {
    if (!associated_type.valid()) {
        return {};
    }
    std::string display = template_display_name(info, arguments);
    auto argument_requires_substitution =
        [&](const TemplateArgument& argument) {
            if (argument.is_dependent ||
                argument.expands_parameter_pack ||
                argument.expands_pack_pattern ||
                argument.generated_pack_kind !=
                    cir::TemplateGeneratedPackKind::None) {
                return true;
            }
            if (template_argument_is_type(argument)) {
                return argument.type.valid() &&
                    (is_dependent_type(argument.type.type) ||
                     type_contains_dependent_alias_specialization(
                         argument.type.type));
            }
            if (template_argument_is_value(argument)) {
                return argument.dependent_value_expr.valid() ||
                    argument.dependent_value_qualifier.type.valid() ||
                    (argument.value_type.valid() &&
                     (is_dependent_type(argument.value_type.type) ||
                      type_contains_dependent_alias_specialization(
                          argument.value_type.type)));
            }
            return argument.dependent_template_qualifier.type.valid() ||
                type_contains_dependent_alias_specialization(
                    argument.dependent_template_qualifier.type);
        };
    cir::TypeId published_type = associated_type.type;
    if (std::any_of(arguments.begin(),
                    arguments.end(),
                    argument_requires_substitution)) {
        published_type = file_.alias_specialization_type(
            file_.intern_name(info.name),
            info.entity,
            arguments,
            associated_type);
        if (!published_type.valid()) {
            return {};
        }
    }
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::TypeAlias,
                                               display,
                                               published_type,
                                               {},
                                               loc);
    cir::Entity& record = file_.entity_mut(entity);
    record.is_definition = true;
    record.qualifiers = associated_type.qualifiers;
    record.memory_space = associated_type.memory_space;
    return entity;
}

const Session::TemplateInfo* Session::member_instantiation_template(
    cir::EntityId method,
    std::vector<TemplateArgument>* arguments,
    const cir::TemplateSpecializationFact** fact_out) const {
    if (!method.valid() || !file_.valid(method)) {
        return nullptr;
    }
    auto template_for_fact =
        [&](const cir::TemplateSpecializationFact* fact)
            -> const TemplateInfo* {
        if (!fact) {
            return nullptr;
        }
        bool has_selected_template =
            fact->selected_template_entity.valid();
        cir::EntityId template_entity = has_selected_template
            ? fact->selected_template_entity
            : fact->template_entity;
        auto found = tstate().templates_.find(
            static_cast<uint64_t>(template_entity.index));
        if (found == tstate().templates_.end()) {
            return nullptr;
        }
        if (arguments) {
            *arguments = has_selected_template
                ? fact->selected_template_arguments()
                : fact->template_arguments();
        }
        if (fact_out) {
            *fact_out = fact;
        }
        return &found->second;
    };

    cir::EntityId record_entity = file_.entity(method).parent;
    if (record_entity.valid() && file_.valid(record_entity)) {
        if (const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(record_entity)) {
            if (const TemplateInfo* selected = template_for_fact(fact)) {
                return selected;
            }
        }

        cir::EntityId function =
            file_.entity(record_entity).local_enclosing_function;
        if (function.valid() && file_.valid(function)) {
            if (const cir::TemplateSpecializationFact* fact =
                    file_.template_specialization(function)) {
                if (const TemplateInfo* selected =
                        template_for_fact(fact)) {
                    return selected;
                }
            }
        }
    }
    cir::DeclContextId context = file_.entity(method).semantic_context;
    const cir::TemplateSpecializationFact* fact = nullptr;
    while (context.valid()) {
        const cir::DeclContext& decl_context = file_.decl_context(context);
        if (decl_context.kind == cir::DeclContextKind::Record &&
            decl_context.owner.valid()) {
            fact = file_.template_specialization(decl_context.owner);
            if (fact) {
                break;
            }
        }
        context = decl_context.parent;
    }
    if (!fact) {
        return nullptr;
    }
    return template_for_fact(fact);
}

cir::EntityId Session::class_template_member_pattern_entity(
    cir::EntityId member,
    const TemplateInfo& info) const {
    member = structor_impl_entity(member);
    if (!member.valid() || !file_.valid(member) ||
        !info.pattern_record.valid() ||
        !file_.valid(info.pattern_record)) {
        return {};
    }
    cir::EntityId record_entity = file_.entity(member).parent;
    if (!record_entity.valid() || !file_.valid(record_entity)) {
        return {};
    }

    std::vector<cir::NameId> path;
    cir::EntityId walk = record_entity;
    while (walk.valid() && file_.valid(walk) &&
           walk != info.pattern_record &&
           !file_.template_specialization(walk)) {
        const cir::Entity& entity = file_.entity(walk);
        if (entity.kind != cir::EntityKind::Record || !entity.name.valid()) {
            return {};
        }
        path.push_back(entity.name);
        cir::DeclContextId own = entity.semantic_context;
        if (!own.valid()) {
            return {};
        }
        cir::DeclContextId up = file_.decl_context(own).parent;
        if (!up.valid()) {
            return {};
        }
        walk = file_.decl_context(up).owner;
    }
    if (!walk.valid() || !file_.valid(walk)) {
        return {};
    }
    cir::EntityId pattern_record = info.pattern_record;
    for (size_t i = path.size(); i-- > 0;) {
        cir::DeclContextId context =
            file_.entity(pattern_record).semantic_context;
        const cir::Binding* binding =
            file_.lookup_tag_binding(context, path[i],
                                     /*include_parents=*/false);
        cir::EntityId next{};
        if (binding) {
            for (cir::EntityId candidate : binding->entities) {
                if (candidate.valid() && file_.valid(candidate) &&
                    file_.entity(candidate).kind ==
                        cir::EntityKind::Record) {
                    next = candidate;
                    break;
                }
            }
        }
        if (!next.valid()) {
            return {};
        }
        pattern_record = next;
    }
    const cir::RecordFacts* instance_facts =
        file_.record_facts(record_entity);
    const cir::RecordFacts* pattern_facts =
        file_.record_facts(pattern_record);
    if (!instance_facts || !pattern_facts) {
        return {};
    }
    for (size_t i = 0; i < instance_facts->methods.size(); ++i) {
        if (instance_facts->methods[i].entity == member) {
            return i < pattern_facts->methods.size() &&
                    pattern_facts->methods[i].name ==
                        instance_facts->methods[i].name
                ? pattern_facts->methods[i].entity
                : cir::EntityId{};
        }
    }

    const cir::Entity& selected = file_.entity(member);
    for (const cir::RecordMethodFact& pattern_method :
         pattern_facts->methods) {
        if (!pattern_method.entity.valid() ||
            !file_.valid(pattern_method.entity)) {
            continue;
        }
        const cir::Entity& candidate =
            file_.entity(pattern_method.entity);
        bool same_named_method =
            selected.name.valid() && candidate.name == selected.name;
        bool same_structor_kind =
            !selected.name.valid() && candidate.kind == selected.kind;
        if ((same_named_method || same_structor_kind) &&
            candidate.loc.offset == selected.loc.offset) {
            return pattern_method.entity;
        }
    }
    return {};
}

bool Session::begin_member_instantiation_scope(cir::EntityId method,
                                               InstantiationScope& scope) {
    std::vector<TemplateArgument> arguments;
    const cir::TemplateSpecializationFact* fact = nullptr;
    const TemplateInfo* info =
        member_instantiation_template(method, &arguments, &fact);
    if (!info) {
        return false;
    }
    SrcLoc point = fact && !fact->point_of_instantiation.isInvalid()
        ? fact->point_of_instantiation
        : file_.entity(method).loc;
    uint64_t point_generation = fact ? fact->point_lookup_generation : 0;
    const TemplateArgumentBindings* exact_bindings = nullptr;
    if (fact) {
        bool uses_selected =
            fact->selected_template_entity.valid() &&
            fact->selected_template_entity == info->entity;
        const TemplateArgumentBindings& stored = uses_selected
            ? fact->selected_argument_bindings
            : fact->argument_bindings;
        if (stored.size() == info->parameters.size()) {
            exact_bindings = &stored;
        }
    }
    scope = begin_template_instantiation(*info,
                                         arguments,
                                         point,
                                         point_generation,
                                         {},
                                         exact_bindings);
    return scope.active;
}

Session::InstantiationScope Session::begin_template_header(TemplateInfo& info,
                                                           SrcLoc loc) {

    std::unique_ptr<BlockContextState> saved_context =
        save_function_context(/*preserve_lambda_context=*/true);
    InstantiationScope scope = begin_template_parameter_scope();
    scope.saved_context = std::move(saved_context);
    active_template_header_info_ = &info;

    info.param_types.assign(info.parameters.size(), cir::TypeId{});
    for (size_t i = 0; i < info.parameters.size(); ++i) {
        TemplateParameter& parameter = info.parameters[i];
        parameter.index = static_cast<uint32_t>(i);
        declare_template_parameter_binding(info, parameter, loc);
    }
    return scope;
}

const Session::TemplateInfo*
Session::current_abbreviated_function_template() const {
    if (validating_template_info_ &&
        !validating_template_info_->invented_function_parameters.empty()) {
        return validating_template_info_;
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (frame->info &&
            !frame->info->invented_function_parameters.empty() &&
            !frame->info->is_class_template &&
            !frame->info->is_alias_template &&
            !frame->info->is_variable_template &&
            !frame->info->is_concept) {
            return frame->info;
        }
    }
    return nullptr;
}

cir::TypeRef Session::abbreviated_function_parameter_replacement(
    const TemplateInfo& info,
    uint32_t template_parameter_index) const {
    if (template_parameter_index >= info.parameters.size()) {
        return {};
    }
    const TemplateParameter& parameter =
        info.parameters[template_parameter_index];
    if (parameter.kind != TemplateParameterKind::Type ||
        !parameter.type_param_type.valid()) {
        return {};
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (frame->info != &info || frame->memo_key.empty() ||
            template_parameter_index >= frame->argument_bindings.size()) {
            continue;
        }
        const TemplateArgumentBinding& binding =
            frame->argument_bindings[template_parameter_index];
        if (binding.is_single() && binding.arguments.size() == 1 &&
            binding.arguments.front().kind ==
                cir::TemplateArgumentKind::Type) {
            return binding.arguments.front().type;
        }

        break;
    }
    return type_ref(parameter.type_param_type);
}

void Session::finish_template_header(InstantiationScope scope) {
    std::unique_ptr<BlockContextState> saved_context =
        std::move(scope.saved_context);
    finish_template_parameter_scope(std::move(scope));
    restore_function_context(std::move(saved_context));
}

Session::InstantiationScope Session::begin_template_parameter_scope() {
    InstantiationScope scope;
    scope.saved_header_value_params = std::move(tstate().header_value_params_);
    scope.saved_header_value_param_packs =
        std::move(tstate().header_value_param_packs_);
    scope.saved_active_template_header_info = active_template_header_info_;
    tstate().header_value_params_.clear();
    tstate().header_value_param_packs_.clear();
    active_template_header_info_ = nullptr;
    enter_scope(ScopeFlags::TemplateParameterScope);
    tstate().scoped_template_parameter_template_keys_.push_back({});
    return scope;
}

Session::InstantiationScope
Session::begin_current_template_instantiation_parameter_scope(
    cir::EntityId function,
    SrcLoc loc) {
    InstantiationScope scope;
    if (!function.valid() || !file_.valid(function)) {
        return scope;
    }
    const cir::TemplateSpecializationFact* fact =
        file_.template_specialization(function);
    const TemplateInfo* info =
        fact && fact->template_entity.valid()
        ? template_info(fact->template_entity)
        : nullptr;
    if (!info || info->is_class_template || info->is_alias_template ||
        info->is_variable_template || info->is_concept) {
        return scope;
    }
    scope = begin_template_parameter_scope();
    scope.active = true;
    for (const TemplateInfo::TemplateInstantiationBinding& binding :
         info->enclosing_instantiation_bindings) {
        TemplateInfo enclosing;
        enclosing.parameters = binding.parameters;
        std::vector<TemplateArgument> enclosing_arguments =
            flatten_template_argument_bindings(binding.argument_bindings);
        bind_template_instantiation_parameters(enclosing,
                                               enclosing_arguments,
                                               loc,
                                               &binding.argument_bindings);
    }
    std::vector<TemplateArgument> arguments = fact->template_arguments();
    bind_template_instantiation_parameters(*info,
                                           arguments,
                                           loc,
                                           &fact->argument_bindings);
    return scope;
}

void Session::declare_template_parameter_binding(TemplateInfo& info,
                                                 TemplateParameter& parameter,
                                                 SrcLoc loc) {
    if (info.param_types.size() <= parameter.index) {
        info.param_types.resize(static_cast<size_t>(parameter.index) + 1);
    }
    SrcLoc binding_loc = parameter.loc.isInvalid() ? loc : parameter.loc;
    if (template_parameter_is_type(parameter)) {
        cir::TypeId type_param = file_.type_param_type(
            {},
            parameter.name,
            parameter.index,
            parameter.depth,
            parameter.is_parameter_pack);
        parameter.type_param_type = type_param;
        info.param_types[parameter.index] = type_param;
        if (!parameter.name.empty()) {
            declare_typedef(parameter.name, type_param, binding_loc);
        }
    } else if (template_parameter_is_value(parameter)) {

        cir::TypeId value_type = parameter.non_type_type.valid()
            ? parameter.non_type_type
            : builder_.int_type();
        parameter.non_type_type = value_type;
        if (parameter.name.empty()) {
            return;
        }
        cir::EntityId constant = builder_.add_entity(
            cir::EntityKind::TemplateParam,
            parameter.name,
            value_type,
            {},
            binding_loc);
        parameter.entity = constant;
        cir::Entity& record = file_.entity_mut(constant);
        record.has_constant_value = true;
        record.constant_value_kind =
            file_.template_value_kind_for_type(value_type);
        record.constant_null_kind =
            null_kind_for_value_kind(file_,
                                     value_type,
                                     record.constant_value_kind);
        cir::IntegerTypeShape shape =
            cir::integer_shape_for_type(file_, value_type);
        record.constant_integer_value =
            cir::IntegerValue::from_signed(0, shape.bit_width)
                .cast(shape.bit_width, shape.is_unsigned);
        tstate().header_value_params_.emplace(static_cast<uint64_t>(constant.index),
                                     parameter.index);
        if (parameter.is_parameter_pack) {
            tstate().header_value_param_packs_.insert(
                static_cast<uint64_t>(constant.index));
        }
        bind_entity(parameter.name,
                    cir::LookupNamespace::Ordinary,
                    constant,
                    value_type,
                    false,
                    false,
                    true,
                    {},
                    binding_loc);
    } else if (parameter.kind == TemplateParameterKind::Template) {
        if (parameter.nested_head) {

            TemplateInfo& retained = *parameter.nested_head;
            retained.name = parameter.name;
            retained.template_parameter_index = parameter.index;
            retained.is_class_template =
                parameter.template_template_parameter_kind ==
                TemplateTemplateParameterKind::Type;
            retained.is_variable_template =
                parameter.template_template_parameter_kind ==
                TemplateTemplateParameterKind::Variable;
            retained.is_concept =
                parameter.template_template_parameter_kind ==
                TemplateTemplateParameterKind::Concept;
            retained.is_template_parameter_pack =
                parameter.is_parameter_pack;
        }
        parameter.entity =
            bind_template_template_parameter_placeholder(parameter,
                                                         binding_loc);
        if (parameter.nested_head) {
            parameter.nested_head->entity = parameter.entity;
        }
    }
}

void Session::finish_template_parameter_scope(InstantiationScope scope) {
    if (!tstate().scoped_template_parameter_template_keys_.empty()) {
        for (uint64_t key : tstate().scoped_template_parameter_template_keys_.back()) {
            tstate().templates_.erase(key);
        }
        tstate().scoped_template_parameter_template_keys_.pop_back();
    }
    leave_scope();
    tstate().header_value_params_ = std::move(scope.saved_header_value_params);
    tstate().header_value_param_packs_ =
        std::move(scope.saved_header_value_param_packs);
    active_template_header_info_ = scope.saved_active_template_header_info;
}

void Session::finish_template_instantiation(InstantiationScope scope) {
    if (!scope.active) {
        return;
    }
    if (!active_instantiations_.empty()) {
        active_instantiations_.pop_back();
    }
    if (!tstate().current_instantiation_frames_.empty()) {
        tstate().current_instantiation_frames_.pop_back();
    }
    if (!tstate().scoped_template_parameter_template_keys_.empty()) {
        for (uint64_t key : tstate().scoped_template_parameter_template_keys_.back()) {
            tstate().templates_.erase(key);
        }
        tstate().scoped_template_parameter_template_keys_.pop_back();
    }
    leave_scope();
    leave_scope();
    tstate().header_value_params_ = std::move(scope.saved_header_value_params);
    tstate().header_value_param_packs_ =
        std::move(scope.saved_header_value_param_packs);
    active_template_header_info_ = scope.saved_active_template_header_info;
    collecting_pattern_ = scope.saved_collecting_pattern;
    builder_.set_mark_template_pattern(collecting_pattern_);
    lookup_generation_ceiling_ = scope.saved_lookup_ceiling;
    if (scope.suspended_parameter_pack_pattern_capture &&
        scope.parameter_pack_pattern_capture_suspension_depth <
            tstate().parameter_pack_pattern_capture_suspensions_.size()) {
        tstate().parameter_pack_pattern_captures_ =
            std::move(tstate().parameter_pack_pattern_capture_suspensions_
                          [scope
                               .parameter_pack_pattern_capture_suspension_depth]);
        tstate().parameter_pack_pattern_capture_suspensions_.resize(
            scope.parameter_pack_pattern_capture_suspension_depth);
    }
    if (scope.suspended_parameter_pack_element_replay &&
        scope.parameter_pack_element_replay_suspension_depth <
            tstate().parameter_pack_element_replay_suspensions_.size()) {
        tstate().parameter_pack_element_replay_bindings_ =
            std::move(tstate().parameter_pack_element_replay_suspensions_
                          [scope.parameter_pack_element_replay_suspension_depth]);
        tstate().parameter_pack_element_replay_suspensions_.resize(
            scope.parameter_pack_element_replay_suspension_depth);
    }
    restore_function_context(std::move(scope.saved_context));
}

Session::DefaultArgumentInstantiationScope
Session::begin_default_argument_instantiation(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    DefaultArgumentInstantiationScope scope;
    if (!check_template_replay_guard_depth(loc)) {
        return scope;
    }
    point_lookup_generation =
        template_instantiation_point_generation(point_lookup_generation);
    scope.saved_header_value_params = std::move(tstate().header_value_params_);
    scope.saved_header_value_param_packs =
        std::move(tstate().header_value_param_packs_);
    scope.saved_active_template_header_info = active_template_header_info_;
    tstate().header_value_params_.clear();
    tstate().header_value_param_packs_.clear();
    active_template_header_info_ = nullptr;
    scope.saved_collecting_pattern = collecting_pattern_;
    collecting_pattern_ = false;
    builder_.set_mark_template_pattern(false);
    scope.saved_lookup_ceiling = lookup_generation_ceiling_;
    lookup_generation_ceiling_ = 0;
    scope.suspended_parameter_pack_pattern_capture = true;
    scope.parameter_pack_pattern_capture_suspension_depth =
        tstate().parameter_pack_pattern_capture_suspensions_.size();
    tstate().parameter_pack_pattern_capture_suspensions_.push_back(
        std::move(tstate().parameter_pack_pattern_captures_));
    tstate().parameter_pack_pattern_captures_.clear();
    scope.active = true;
    std::string display = template_display_name(info, arguments);
    uint64_t request_id =
        record_template_instantiation_request(info,
                                              arguments,
                                              loc,
                                              point_lookup_generation,
                                              TemplateInstantiationRequestKind::
                                                  FunctionDefaultArgument);
    const TemplateInstantiationRequest* request =
        template_instantiation_request_by_id(request_id);
    active_instantiations_.push_back(ActiveInstantiation{
        static_cast<uint64_t>(info.entity.index),
        loc,
        point_lookup_generation,
        request_id,
        display,
        request && request->duplicate_of_id != 0});
    tstate().current_instantiation_frames_.push_back(TemplateState::CurrentInstantiationFrame{
        &info, template_memo_key(info.entity, arguments),
        std::move(display), arguments, {}, loc, point_lookup_generation,
        {}, {}});
    (void)bind_template_arguments_to_parameters(
        info.parameters,
        arguments,
        tstate().current_instantiation_frames_.back().argument_bindings);

    enter_existing_context(info.lexical_context, ScopeFlags::FileScope);
    enter_scope(ScopeFlags::TemplateParameterScope);
    tstate().scoped_template_parameter_template_keys_.push_back({});
    bind_template_instantiation_parameters(info, arguments, loc);
    return scope;
}

void Session::finish_default_argument_instantiation(
    DefaultArgumentInstantiationScope scope) {
    if (!scope.active) {
        return;
    }
    if (!active_instantiations_.empty()) {
        active_instantiations_.pop_back();
    }
    if (!tstate().current_instantiation_frames_.empty()) {
        tstate().current_instantiation_frames_.pop_back();
    }
    if (!tstate().scoped_template_parameter_template_keys_.empty()) {
        for (uint64_t key : tstate().scoped_template_parameter_template_keys_.back()) {
            tstate().templates_.erase(key);
        }
        tstate().scoped_template_parameter_template_keys_.pop_back();
    }
    leave_scope();
    leave_scope();
    tstate().header_value_params_ = std::move(scope.saved_header_value_params);
    tstate().header_value_param_packs_ =
        std::move(scope.saved_header_value_param_packs);
    active_template_header_info_ = scope.saved_active_template_header_info;
    collecting_pattern_ = scope.saved_collecting_pattern;
    builder_.set_mark_template_pattern(collecting_pattern_);
    lookup_generation_ceiling_ = scope.saved_lookup_ceiling;
    if (scope.suspended_parameter_pack_pattern_capture &&
        scope.parameter_pack_pattern_capture_suspension_depth <
            tstate().parameter_pack_pattern_capture_suspensions_.size()) {
        tstate().parameter_pack_pattern_captures_ =
            std::move(tstate().parameter_pack_pattern_capture_suspensions_
                          [scope
                               .parameter_pack_pattern_capture_suspension_depth]);
        tstate().parameter_pack_pattern_capture_suspensions_.resize(
            scope.parameter_pack_pattern_capture_suspension_depth);
    }
}

const Session::TemplateParameter*
Session::template_value_parameter_for_entity(cir::EntityId entity) const {
    if (!entity.valid()) {
        return nullptr;
    }
    auto find_parameter = [&](const TemplateInfo* info)
        -> const TemplateParameter* {
        if (!info) {
            return nullptr;
        }
        for (const TemplateParameter& parameter : info->parameters) {
            if (parameter.kind == TemplateParameterKind::NonType &&
                parameter.entity == entity) {
                return &parameter;
            }
        }
        return nullptr;
    };
    if (const TemplateParameter* parameter =
            find_parameter(active_template_header_info_)) {
        return parameter;
    }
    if (const TemplateParameter* parameter =
            find_parameter(validating_template_info_)) {
        return parameter;
    }
    // A nested template head swaps out the outer head's transient value maps,
    // but its template-parameter scope and declaration entities remain live.
    // Follow those entities through validation nesting without treating an
    // uninstantiated, memo-less frame as a source of concrete pack elements.
    for (auto info = validating_template_info_stack_.rbegin();
         info != validating_template_info_stack_.rend(); ++info) {
        if (const TemplateParameter* parameter = find_parameter(*info)) {
            return parameter;
        }
    }
    return nullptr;
}

uint32_t Session::template_value_param_index(cir::EntityId entity) const {
    if (!entity.valid()) {
        return cir::ArrayTypePayload::no_extent_param;
    }
    auto found = tstate().header_value_params_.find(
        static_cast<uint64_t>(entity.index));
    if (found != tstate().header_value_params_.end()) {
        return found->second;
    }
    const TemplateParameter* parameter =
        template_value_parameter_for_entity(entity);
    return parameter
        ? parameter->index
        : cir::ArrayTypePayload::no_extent_param;
}

bool Session::template_value_param_is_pack(cir::EntityId entity) const {
    if (!entity.valid()) {
        return false;
    }
    if (tstate().header_value_param_packs_.contains(
            static_cast<uint64_t>(entity.index))) {
        return true;
    }
    const TemplateParameter* parameter =
        template_value_parameter_for_entity(entity);
    return parameter && parameter->is_parameter_pack;
}

const Session::TemplateArgument*
Session::dependent_instantiation_value_argument(cir::EntityId entity) const {
    if (!entity.valid()) {
        return nullptr;
    }
    uint64_t key = static_cast<uint64_t>(entity.index);
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        auto found = frame->dependent_value_bindings.find(key);
        if (found != frame->dependent_value_bindings.end()) {
            return &found->second;
        }
    }
    return nullptr;
}

std::optional<uint32_t>
Session::template_value_pack_param_index_for_name(std::string_view name) const {
    auto find_named_value_pack =
        [&](const std::vector<TemplateParameter>& parameters)
        -> std::optional<uint32_t> {
        for (const TemplateParameter& parameter : parameters) {
            if (parameter.kind == TemplateParameterKind::NonType &&
                parameter.is_parameter_pack &&
                parameter.name == name) {
                return parameter.index;
            }
        }
        return std::nullopt;
    };
    if (validating_template_info_) {
        if (std::optional<uint32_t> active =
                find_named_value_pack(
                    validating_template_info_->parameters)) {
            return active;
        }
    }
    if (active_template_header_info_) {
        if (std::optional<uint32_t> active =
                find_named_value_pack(
                    active_template_header_info_->parameters)) {
            return active;
        }
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (frame->memo_key.empty()) {
            continue;
        }
        if (frame->info) {
            if (std::optional<uint32_t> active =
                    find_named_value_pack(frame->info->parameters)) {
                return active;
            }
            for (auto enclosing =
                     frame->info->enclosing_instantiation_bindings.rbegin();
                 enclosing !=
                     frame->info->enclosing_instantiation_bindings.rend();
                 ++enclosing) {
                if (std::optional<uint32_t> active =
                        find_named_value_pack(enclosing->parameters)) {
                    return active;
                }
            }
        }
    }
    for (cir::DeclContextId context = current_decl_context();
         context.valid();
         context = file_.decl_context(context).parent) {
        cir::EntityId owner = file_.decl_context(context).owner;
        const cir::TemplateSpecializationFact* fact =
            owner.valid() ? file_.template_specialization(owner) : nullptr;
        const TemplateInfo* fact_info =
            fact ? template_info(fact->template_entity) : nullptr;
        if (fact_info) {
            if (std::optional<uint32_t> active =
                    find_named_value_pack(fact_info->parameters)) {
                return active;
            }
        }
    }
    const cir::Binding* binding = lookup_ordinary_binding(name);
    cir::EntityId entity = binding && !binding->entities.empty()
        ? binding->entities.back()
        : cir::EntityId{};
    uint32_t index = template_value_param_index(entity);
    if (index != cir::ArrayTypePayload::no_extent_param &&
        template_value_param_is_pack(entity)) {
        return index;
    }
    return std::nullopt;
}

std::optional<uint32_t>
Session::template_template_pack_param_index_for_name(
    std::string_view name) const {
    auto find_named_template_pack = [&](const TemplateInfo* info)
        -> std::optional<uint32_t> {
        if (!info) {
            return std::nullopt;
        }
        for (const TemplateParameter& parameter : info->parameters) {
            if (parameter.kind == TemplateParameterKind::Template &&
                parameter.is_parameter_pack &&
                parameter.name == name) {
                return parameter.index;
            }
        }
        return std::nullopt;
    };
    if (std::optional<uint32_t> active =
            find_named_template_pack(validating_template_info_)) {
        return active;
    }
    if (std::optional<uint32_t> active =
            find_named_template_pack(active_template_header_info_)) {
        return active;
    }
    for (auto frame = tstate().current_instantiation_frames_.rbegin();
         frame != tstate().current_instantiation_frames_.rend();
         ++frame) {
        if (frame->memo_key.empty()) {
            continue;
        }
        if (std::optional<uint32_t> active =
                find_named_template_pack(frame->info)) {
            return active;
        }
    }
    if (const TemplateInfo* pack_info =
            template_parameter_pack_info_for_name(name);
        pack_info && pack_info->is_template_parameter_pack &&
        pack_info->template_parameter_index !=
            cir::ArrayTypePayload::no_extent_param) {
        return pack_info->template_parameter_index;
    }
    return std::nullopt;
}

void Session::register_template_value_parameter_equivalence(
    cir::EntityId variable,
    cir::TypeId variable_type,
    const ExprResult& initializer) {
    if (!variable.valid() || !validating_template_info_ ||
        !initializer.unparenthesized_identifier) {
        return;
    }
    uint32_t parameter_index = template_value_param_index(initializer.entity);
    if (parameter_index == cir::ArrayTypePayload::no_extent_param ||
        parameter_index >= validating_template_info_->parameters.size()) {
        return;
    }
    const TemplateParameter& parameter =
        validating_template_info_->parameters[parameter_index];
    if (!template_parameter_is_value(parameter) ||
        !parameter.non_type_type.valid() ||
        !variable_type.valid()) {
        return;
    }
    if (file_.resolved_type(variable_type) !=
        file_.resolved_type(parameter.non_type_type)) {
        return;
    }
    tstate().header_value_params_[static_cast<uint64_t>(variable.index)] =
        parameter_index;
    if (parameter.is_parameter_pack) {
        tstate().header_value_param_packs_.insert(
            static_cast<uint64_t>(variable.index));
    }
}

bool Session::bind_template_arguments_to_parameters(
    const std::vector<TemplateParameter>& parameters,
    const std::vector<TemplateArgument>& arguments,
    TemplateArgumentBindings& bindings_out,
    TemplateArgumentBindingFailure* failure_out,
    TemplateArgumentBindingMode mode) const {
    if (failure_out) {
        *failure_out = TemplateArgumentBindingFailure{};
    }
    if (!bind_explicit_template_arguments_prefix_to_parameters(
            parameters, arguments, bindings_out, failure_out, mode)) {
        return false;
    }
    for (size_t i = 0; i < parameters.size(); ++i) {
        if (bindings_out[i].is_unbound()) {
            if (parameters[i].is_parameter_pack) {
                bindings_out[i].kind = TemplateArgumentBindingKind::Pack;
                continue;
            }
            if (TemplateArgumentBindingFailure* failure =
                    set_template_binding_failure(
                        failure_out,
                        TemplateArgumentBindingFailureKind::
                            MissingRequiredArgument)) {
                failure->parameter_index = static_cast<uint32_t>(i);
                failure->supplied_argument_count =
                    static_cast<uint32_t>(arguments.size());
                failure->minimum_argument_count =
                    minimum_template_argument_count(parameters);
                failure->maximum_argument_count =
                    static_cast<uint32_t>(parameters.size());
            }
            bindings_out.clear();
            return false;
        }
    }
    if (flatten_template_argument_bindings(bindings_out).size() !=
        arguments.size()) {
        set_template_binding_failure(
            failure_out,
            TemplateArgumentBindingFailureKind::Internal,
            TemplateArgumentBindingFailureReason::
                InternalBindingCountMismatch);
        bindings_out.clear();
        return false;
    }
    return true;
}

void Session::canonicalize_template_argument_bindings(
    TemplateArgumentBindings& bindings) const {
    std::function<void(TemplateArgument&)> canonicalize_argument =
        [&](TemplateArgument& argument) {
        if (template_argument_is_type(argument)) {
            argument.type.type = file_.resolved_type(argument.type.type);
        } else if (template_argument_is_value(argument)) {
            argument.value_type.type =
                file_.resolved_type(argument.value_type.type);
            argument.generated_pack_count_type.type =
                file_.resolved_type(argument.generated_pack_count_type.type);
            argument.dependent_value_qualifier.type =
                file_.resolved_type(
                    argument.dependent_value_qualifier.type);
        } else if (argument.kind ==
                   cir::TemplateArgumentKind::Template) {
            argument.dependent_template_qualifier.type =
                file_.resolved_type(
                    argument.dependent_template_qualifier.type);
        }
        for (TemplateArgument& element : argument.value_elements) {
            canonicalize_argument(element);
        }
    };

    for (TemplateArgumentBinding& binding : bindings) {
        for (TemplateArgument& argument : binding.arguments) {
            canonicalize_argument(argument);
        }
    }
}

bool Session::bind_explicit_template_arguments_prefix_to_parameters(
    const std::vector<TemplateParameter>& parameters,
    const std::vector<TemplateArgument>& explicit_arguments,
    TemplateArgumentBindings& bindings_out,
    TemplateArgumentBindingFailure* failure_out,
    TemplateArgumentBindingMode mode) const {
    if (failure_out) {
        *failure_out = TemplateArgumentBindingFailure{};
    }
    bindings_out.clear();
    bindings_out.resize(parameters.size());

    size_t pack_count = 0;
    size_t pack_index = parameters.size();
    for (size_t i = 0; i < parameters.size(); ++i) {
        if (parameters[i].is_parameter_pack) {
            ++pack_count;
            if (pack_index == parameters.size()) {
                pack_index = i;
            }
        }
    }
    if (pack_count > 1 &&
        mode != TemplateArgumentBindingMode::FunctionExplicitPrefix) {
        set_template_binding_failure(
            failure_out,
            TemplateArgumentBindingFailureKind::PackBinding,
            TemplateArgumentBindingFailureReason::
                MultipleParameterPacksUnsupported);
        bindings_out.clear();
        return false;
    }

    auto convert_for_parameter =
        [&](const TemplateParameter& parameter,
            const TemplateArgument& source,
            TemplateArgument& converted,
            std::string& error) -> bool {
        converted = source;
        if (parameter.kind != TemplateParameterKind::NonType ||
            source.kind != cir::TemplateArgumentKind::Value) {
            return true;
        }

        const TemplateArgument* recipe = &source;
        cir::TypeId target = parameter.non_type_type.valid()
            ? parameter.non_type_type
            : file_.builtin_type(cir::BuiltinTypeKind::Int);
        if (contains_auto_type(target, cir::AutoTypeFlavor::Cxx)) {
            if (source.unconverted_value_alternative) {
                recipe = source.unconverted_value_alternative.get();
            }
            target = recipe->value_type.type.valid()
                ? recipe->value_type.type
                : file_.builtin_type(cir::BuiltinTypeKind::Int);
        }
        if (type_contains_type_param(target) || is_dependent_type(target)) {

            return true;
        }
        if (source.is_dependent ||
            source.value_kind == cir::TemplateValueKind::None) {
            converted.value_type = type_ref(target);
            return true;
        }

        cir::TypeId resolved_target = file_.resolved_type(target);
        auto source_category_is_compatible =
            [&](const TemplateArgument& candidate) {
            cir::TypeId source_type = candidate.value_type.type.valid()
                ? file_.resolved_type(candidate.value_type.type)
                : cir::TypeId{};
            if (!file_.valid(source_type) ||
                !file_.valid(resolved_target)) {
                return true;
            }
            cir::TypeKind source_kind = file_.type(source_type).kind;
            cir::TypeKind target_kind = file_.type(resolved_target).kind;
            bool compatible_source_category = true;
            if (target_kind == cir::TypeKind::LValueReference ||
                target_kind == cir::TypeKind::RValueReference) {
                compatible_source_category =
                    source_kind == cir::TypeKind::LValueReference ||
                    source_kind == cir::TypeKind::RValueReference;
            } else if (target_kind == cir::TypeKind::Pointer) {
                compatible_source_category =
                    source_kind == cir::TypeKind::Pointer ||
                    template_value_type_is_nullptr_t(*this, source_type) ||
                    ((source_kind == cir::TypeKind::LValueReference ||
                      source_kind == cir::TypeKind::RValueReference) &&
                     file_.type(file_.resolved_type(
                         file_.reference_referred_type(source_type))).kind ==
                         cir::TypeKind::Function);
            } else if (target_kind == cir::TypeKind::MemberPointer) {
                compatible_source_category =
                    source_kind == cir::TypeKind::MemberPointer ||
                    template_value_type_is_nullptr_t(*this, source_type);
            } else if (template_value_type_is_nullptr_t(*this,
                                                        resolved_target)) {
                compatible_source_category =
                    template_value_type_is_nullptr_t(*this, source_type);
            } else if (cir::is_integer_like_type(file_, resolved_target)) {
                compatible_source_category =
                    cir::is_integer_like_type(file_, source_type);
            } else if (file_.template_value_kind_for_type(resolved_target) ==
                           cir::TemplateValueKind::StructuralObject ||
                       file_.template_value_kind_for_type(resolved_target) ==
                           cir::TemplateValueKind::Closure) {
                compatible_source_category =
                    type_equal(source_type, resolved_target);
            }
            return compatible_source_category;
        };
        if (!source_category_is_compatible(*recipe) &&
            source.unconverted_value_alternative &&
            source_category_is_compatible(
                *source.unconverted_value_alternative)) {
            recipe = source.unconverted_value_alternative.get();
        }
        if (!source_category_is_compatible(*recipe)) {
            error =
                "non-type template argument has an incompatible source type";
            return false;
        }

        TemplateValueConstant constant;
        constant.kind = recipe->value_kind;
        constant.null_kind = recipe->null_kind;
        constant.integer_value = recipe->integer_value;
        constant.floating_value = recipe->floating_value;
        constant.entity = recipe->value_entity;
        constant.closure_identity = recipe->closure_identity;
        constant.byte_offset = recipe->value_byte_offset;
        constant.elements = recipe->value_elements;
        constant.meta_kind = recipe->meta_kind;
        constant.meta_type = recipe->type;
        if (!build_template_value_argument(target,
                                           constant,
                                           converted,
                                           &error)) {
            return false;
        }
        converted.value_spelling = source.value_spelling;
        converted.is_defaulted = source.is_defaulted;
        converted.expands_parameter_pack = source.expands_parameter_pack;
        converted.expands_pack_pattern = source.expands_pack_pattern;
        return true;
    };

    auto bind_single =
        [&](size_t parameter_index, size_t argument_index) -> bool {
        if (explicit_arguments[argument_index].expands_parameter_pack &&
            !parameters[parameter_index].is_parameter_pack) {
            if (TemplateArgumentBindingFailure* failure =
                    set_template_binding_failure(
                        failure_out,
                        TemplateArgumentBindingFailureKind::PackBinding,
                        TemplateArgumentBindingFailureReason::
                            PackExpansionForNonPackUnsupported)) {
                failure->parameter_index =
                    static_cast<uint32_t>(parameter_index);
                failure->argument_index =
                    static_cast<uint32_t>(argument_index);
            }
            bindings_out.clear();
            return false;
        }
        TemplateArgument converted;
        std::string conversion_error;
        bool already_canonical =
            mode == TemplateArgumentBindingMode::DeducedCanonical;
        if (already_canonical) {
            converted = explicit_arguments[argument_index];
        } else if (!convert_for_parameter(parameters[parameter_index],
                                          explicit_arguments[argument_index],
                                          converted,
                                          conversion_error)) {
            TemplateArgumentBindingFailureReason reason =
                conversion_error.find("narrowing") != std::string::npos
                    ? TemplateArgumentBindingFailureReason::
                          NonTypeArgumentNarrowing
                    : TemplateArgumentBindingFailureReason::None;
            if (TemplateArgumentBindingFailure* failure =
                    set_template_binding_failure(
                        failure_out,
                        TemplateArgumentBindingFailureKind::SubstitutionFailure,
                        reason,
                        conversion_error)) {
                failure->parameter_index =
                    static_cast<uint32_t>(parameter_index);
                failure->argument_index =
                    static_cast<uint32_t>(argument_index);
                failure->expected_parameter_kind =
                    parameters[parameter_index].kind;
                failure->actual_argument_kind =
                    explicit_arguments[argument_index].kind;
            }
            bindings_out.clear();
            return false;
        }
        TemplateArgumentBindingFailureReason reason =
            TemplateArgumentBindingFailureReason::None;
        if (!already_canonical &&
            !template_parameter_accepts_argument(*this,
                                                 parameters[parameter_index],
                                                 converted,
                                                 &reason)) {
            TemplateArgumentBindingFailureKind kind =
                parameters[parameter_index].kind ==
                            TemplateParameterKind::Template &&
                        explicit_arguments[argument_index].kind ==
                            cir::TemplateArgumentKind::Template
                    ? TemplateArgumentBindingFailureKind::
                          TemplateTemplateMismatch
                    : TemplateArgumentBindingFailureKind::ArgumentKindMismatch;
            if (TemplateArgumentBindingFailure* failure =
                    set_template_binding_failure(failure_out,
                                                 kind,
                                                 reason)) {
                failure->parameter_index =
                    static_cast<uint32_t>(parameter_index);
                failure->argument_index =
                    static_cast<uint32_t>(argument_index);
                failure->expected_parameter_kind =
                    parameters[parameter_index].kind;
                failure->actual_argument_kind =
                    explicit_arguments[argument_index].kind;
            }
            bindings_out.clear();
            return false;
        }
        bindings_out[parameter_index].kind =
            TemplateArgumentBindingKind::Single;
        bindings_out[parameter_index].arguments = {std::move(converted)};
        return true;
    };
    auto bind_pack =
        [&](size_t parameter_index,
            size_t argument_begin,
            size_t argument_count) -> bool {
        std::vector<TemplateArgument> pack_arguments;
        pack_arguments.reserve(argument_count);
        for (size_t i = 0; i < argument_count; ++i) {
            const TemplateArgument& argument =
                explicit_arguments[argument_begin + i];
            TemplateArgument converted;
            std::string conversion_error;
            if (!convert_for_parameter(parameters[parameter_index],
                                       argument,
                                       converted,
                                       conversion_error)) {
                TemplateArgumentBindingFailureReason reason =
                    conversion_error.find("narrowing") != std::string::npos
                        ? TemplateArgumentBindingFailureReason::
                              NonTypeArgumentNarrowing
                        : TemplateArgumentBindingFailureReason::None;
                if (TemplateArgumentBindingFailure* failure =
                        set_template_binding_failure(
                            failure_out,
                            TemplateArgumentBindingFailureKind::
                                SubstitutionFailure,
                            reason,
                            conversion_error)) {
                    failure->parameter_index =
                        static_cast<uint32_t>(parameter_index);
                    failure->argument_index = static_cast<uint32_t>(
                        argument_begin + i);
                    failure->expected_parameter_kind =
                        parameters[parameter_index].kind;
                    failure->actual_argument_kind = argument.kind;
                }
                bindings_out.clear();
                return false;
            }
            TemplateArgumentBindingFailureReason reason =
                TemplateArgumentBindingFailureReason::None;
            if (!template_parameter_accepts_argument(*this,
                                                    parameters[parameter_index],
                                                    converted,
                                                    &reason)) {
                TemplateArgumentBindingFailureKind kind =
                    parameters[parameter_index].kind ==
                                TemplateParameterKind::Template &&
                            argument.kind == cir::TemplateArgumentKind::Template
                        ? TemplateArgumentBindingFailureKind::
                              TemplateTemplateMismatch
                        : TemplateArgumentBindingFailureKind::
                              ArgumentKindMismatch;
                if (TemplateArgumentBindingFailure* failure =
                        set_template_binding_failure(failure_out,
                                                     kind,
                                                     reason)) {
                    failure->parameter_index =
                        static_cast<uint32_t>(parameter_index);
                    failure->argument_index =
                        static_cast<uint32_t>(argument_begin + i);
                    failure->expected_parameter_kind =
                        parameters[parameter_index].kind;
                    failure->actual_argument_kind = argument.kind;
                }
                bindings_out.clear();
                return false;
            }
            pack_arguments.push_back(std::move(converted));
        }
        bindings_out[parameter_index].kind = TemplateArgumentBindingKind::Pack;
        bindings_out[parameter_index].arguments = std::move(pack_arguments);
        return true;
    };

    if (pack_count == 0) {
        if (explicit_arguments.size() > parameters.size()) {
            if (TemplateArgumentBindingFailure* failure =
                    set_template_binding_failure(
                        failure_out,
                        TemplateArgumentBindingFailureKind::TooManyArguments)) {
                failure->argument_index =
                    static_cast<uint32_t>(parameters.size());
                failure->supplied_argument_count =
                    static_cast<uint32_t>(explicit_arguments.size());
                failure->minimum_argument_count =
                    minimum_template_argument_count(parameters);
                failure->maximum_argument_count =
                    static_cast<uint32_t>(parameters.size());
            }
            bindings_out.clear();
            return false;
        }
        for (size_t i = 0; i < explicit_arguments.size(); ++i) {
            if (!bind_single(i, i)) {
                return false;
            }
        }
        return true;
    }

    if (mode == TemplateArgumentBindingMode::FunctionExplicitPrefix) {

        size_t argument_index = 0;
        for (size_t parameter_index = 0;
             parameter_index < parameters.size() &&
             argument_index < explicit_arguments.size();
             ++parameter_index) {
            if (parameters[parameter_index].is_parameter_pack) {
                return bind_pack(
                    parameter_index,
                    argument_index,
                    explicit_arguments.size() - argument_index);
            }
            if (!bind_single(parameter_index, argument_index)) {
                return false;
            }
            ++argument_index;
        }
        if (argument_index != explicit_arguments.size()) {
            bindings_out.clear();
            return false;
        }
        return true;
    }

    const size_t leading = pack_index;
    const size_t trailing = parameters.size() - pack_index - 1;
    if (explicit_arguments.size() < leading + trailing) {
        if (explicit_arguments.size() > leading) {
            set_template_binding_failure(
                failure_out,
                TemplateArgumentBindingFailureKind::PackBinding,
                TemplateArgumentBindingFailureReason::
                    PartialNonTrailingPackBinding);
            bindings_out.clear();
            return false;
        }
        for (size_t i = 0; i < explicit_arguments.size(); ++i) {
            if (!bind_single(i, i)) {
                return false;
            }
        }
        return true;
    }

    for (size_t i = 0; i < leading; ++i) {
        if (!bind_single(i, i)) {
            return false;
        }
    }
    size_t pack_argument_count = explicit_arguments.size() - leading - trailing;
    if (!bind_pack(pack_index, leading, pack_argument_count)) {
        return false;
    }
    for (size_t i = 0; i < trailing; ++i) {
        size_t parameter_index = pack_index + 1 + i;
        size_t argument_index = leading + pack_argument_count + i;
        if (!bind_single(parameter_index, argument_index)) {
            return false;
        }
    }
    return true;
}

bool Session::complete_template_argument_bindings_with_defaults(
    const TemplateInfo& info,
    TemplateArgumentBindings& bindings_out,
    TemplateArgumentBindingFailure* failure_out,
    PatternInstantiationCallbacks* callbacks,
    SrcLoc loc,
    TemplateArgumentCompletionMode mode) {
    if (failure_out) {
        *failure_out = TemplateArgumentBindingFailure{};
    }
    if (bindings_out.size() != info.parameters.size()) {
        set_template_binding_failure(
            failure_out,
            TemplateArgumentBindingFailureKind::Internal,
            TemplateArgumentBindingFailureReason::
                InternalBindingCountMismatch);
        return false;
    }
    PatternInstantiationCallbacks empty_callbacks;
    PatternInstantiationCallbacks& substitution_callbacks =
        callbacks ? *callbacks : empty_callbacks;

    struct DefaultCompletionTransaction {
        TemplateArgumentBindings* bindings = nullptr;
        PatternInstantiationCallbacks* callbacks = nullptr;
        TemplateArgumentBindings original_bindings;
        uint64_t point_lookup_generation = 0;
        cir::EntityId access_record{};
        cir::EntityId access_function{};
        SrcLoc access_loc{};
        bool has_explicit_access_context = false;
        TemplateArgumentCompletionMode argument_completion_mode =
            TemplateArgumentCompletionMode::Required;
        std::unordered_map<uint32_t, TemplateArgumentBinding>
            exact_type_parameter_bindings;
        std::unordered_map<uint32_t, TemplateArgumentBinding>
            exact_value_parameter_bindings;
        std::unordered_map<uint32_t, TemplateArgumentBinding>
            exact_template_parameter_bindings;
        bool committed = false;

        ~DefaultCompletionTransaction() {
            if (committed) {
                return;
            }
            *bindings = std::move(original_bindings);
            callbacks->point_lookup_generation = point_lookup_generation;
            callbacks->access_record = access_record;
            callbacks->access_function = access_function;
            callbacks->access_loc = access_loc;
            callbacks->has_explicit_access_context =
                has_explicit_access_context;
            callbacks->argument_completion_mode = argument_completion_mode;
            callbacks->exact_type_parameter_bindings =
                std::move(exact_type_parameter_bindings);
            callbacks->exact_value_parameter_bindings =
                std::move(exact_value_parameter_bindings);
            callbacks->exact_template_parameter_bindings =
                std::move(exact_template_parameter_bindings);
        }
    } transaction{
        &bindings_out,
        &substitution_callbacks,
        bindings_out,
        substitution_callbacks.point_lookup_generation,
        substitution_callbacks.access_record,
        substitution_callbacks.access_function,
        substitution_callbacks.access_loc,
        substitution_callbacks.has_explicit_access_context,
        substitution_callbacks.argument_completion_mode,
        substitution_callbacks.exact_type_parameter_bindings,
        substitution_callbacks.exact_value_parameter_bindings,
        substitution_callbacks.exact_template_parameter_bindings};
    substitution_callbacks.argument_completion_mode = mode;

    std::optional<SpeculativeParseGuard> candidate_transaction;
    bool candidate_has_transactional_work = false;
    if (mode == TemplateArgumentCompletionMode::Candidate) {
        for (size_t i = 0; i < info.parameters.size(); ++i) {
            const TemplateParameter& parameter = info.parameters[i];
            if (bindings_out[i].is_unbound() &&
                !parameter.is_parameter_pack &&
                parameter.default_argument.has_value()) {
                candidate_has_transactional_work = true;
                break;
            }
            if (parameter.kind == TemplateParameterKind::NonType &&
                !bindings_out[i].is_unbound() &&
                type_contains_type_param(parameter.non_type_type)) {
                candidate_has_transactional_work = true;
                break;
            }
        }
    }
    if (candidate_has_transactional_work) {
        candidate_transaction.emplace(speculative_parse());
    }
    substitution_callbacks.point_lookup_generation =
        template_instantiation_point_generation(
            substitution_callbacks.point_lookup_generation);
    substitution_callbacks.access_record =
        enclosing_record_for_context(info.lexical_context);
    substitution_callbacks.access_function = {};
    if (info.entity.valid() && file_.valid(info.entity)) {
        cir::EntityKind kind = file_.entity(info.entity).kind;
        if (kind == cir::EntityKind::Function ||
            kind == cir::EntityKind::Method ||
            kind == cir::EntityKind::Constructor ||
            kind == cir::EntityKind::Destructor) {
            substitution_callbacks.access_function = info.entity;
        }
    }
    substitution_callbacks.has_explicit_access_context = true;
    if (!populate_exact_template_parameter_bindings(
            info, bindings_out, substitution_callbacks)) {
        set_template_binding_failure(
            failure_out,
            TemplateArgumentBindingFailureKind::Internal,
            TemplateArgumentBindingFailureReason::InternalBindingCountMismatch);
        return false;
    }
    bool needs_default_completion_request = false;
    for (size_t i = 0; i < info.parameters.size(); ++i) {
        if (!bindings_out[i].is_unbound()) {
            continue;
        }
        const TemplateParameter& parameter = info.parameters[i];
        if (!parameter.is_parameter_pack &&
            parameter.default_argument.has_value()) {
            needs_default_completion_request = true;
            break;
        }
    }
    struct TemplateArgumentCompletionScopeExit {
        Session* session = nullptr;
        TemplateArgumentCompletionScope scope;
        ~TemplateArgumentCompletionScopeExit() {
            if (session) {
                session->finish_template_argument_completion(scope);
            }
        }
    } completion_scope;
    if (needs_default_completion_request) {
        completion_scope.scope =
            begin_template_argument_completion(
                info,
                bindings_out,
                loc,
                substitution_callbacks.point_lookup_generation);
        if (!completion_scope.scope.active) {
            set_template_binding_failure(
                failure_out,
                TemplateArgumentBindingFailureKind::InstantiationDepth,
                TemplateArgumentBindingFailureReason::None);
            return false;
        }
        completion_scope.session = this;
    }
    auto substitute_default_argument = [&](TemplateArgument& argument) -> bool {
        std::string substitution_error;
        if (argument.kind == cir::TemplateArgumentKind::Value &&
            argument.is_dependent) {
            if (!substitute_template_value_argument(argument,
                                                    bindings_out,
                                                    substitution_callbacks,
                                                    &substitution_error)) {
                set_template_binding_failure(
                    failure_out,
                    TemplateArgumentBindingFailureKind::SubstitutionFailure,
                    TemplateArgumentBindingFailureReason::
                        DependentDefaultArgumentSubstitution,
                    substitution_error.empty()
                        ? "dependent default template argument could not be substituted"
                        : std::move(substitution_error));
                return false;
            }
            argument.is_defaulted = true;
            return true;
        }
        if (argument.kind == cir::TemplateArgumentKind::Template &&
            argument.is_dependent) {
            if (!substitute_template_template_argument(argument,
                                                       bindings_out,
                                                       substitution_callbacks,
                                                       &substitution_error)) {
                set_template_binding_failure(
                    failure_out,
                    TemplateArgumentBindingFailureKind::SubstitutionFailure,
                    TemplateArgumentBindingFailureReason::
                        DependentDefaultArgumentSubstitution,
                    substitution_error.empty()
                        ? "dependent default template argument could not be substituted"
                        : std::move(substitution_error));
                return false;
            }
            argument.is_defaulted = true;
            return true;
        }
        if (argument.kind != cir::TemplateArgumentKind::Type ||
            !argument.type.type.valid() ||
            (!is_dependent_type(argument.type.type) &&
             !type_contains_dependent_alias_specialization(
                 argument.type.type))) {
            return true;
        }

        const bool saved_materialization =
            substitution_callbacks.materialize_type_template_definition;
        substitution_callbacks.materialize_type_template_definition = false;
        cir::TypeRef substituted = substitute_pattern_type_ref(
            argument.type,
            bindings_out,
            substitution_callbacks);
        substitution_callbacks.materialize_type_template_definition =
            saved_materialization;
        if (!substituted.valid()) {
            set_template_binding_failure(
                failure_out,
                TemplateArgumentBindingFailureKind::SubstitutionFailure,
                TemplateArgumentBindingFailureReason::
                    DependentDefaultArgumentSubstitution);
            return false;
        }
        argument.type = substituted;
        argument.is_dependent = is_dependent_type(substituted.type);
        return true;
    };
    for (size_t i = 0; i < info.parameters.size(); ++i) {
        if (!bindings_out[i].is_unbound()) {
            continue;
        }
        const TemplateParameter& parameter = info.parameters[i];
        if (parameter.is_parameter_pack) {
            bindings_out[i].kind = TemplateArgumentBindingKind::Pack;
            continue;
        }
        if (!parameter.default_argument.has_value()) {
            if (TemplateArgumentBindingFailure* failure =
                    set_template_binding_failure(
                        failure_out,
                        TemplateArgumentBindingFailureKind::
                            MissingRequiredArgument)) {
                failure->parameter_index = static_cast<uint32_t>(i);
                failure->supplied_argument_count =
                    supplied_template_argument_count(bindings_out);
                failure->minimum_argument_count =
                    minimum_template_argument_count(info.parameters);
                bool has_pack = std::any_of(
                    info.parameters.begin(),
                    info.parameters.end(),
                    [](const TemplateParameter& candidate) {
                        return candidate.is_parameter_pack;
                    });
                if (!has_pack) {
                    failure->maximum_argument_count =
                        static_cast<uint32_t>(info.parameters.size());
                }
            }
            return false;
        }
        TemplateArgument argument = *parameter.default_argument;
        argument.is_defaulted = true;
        substitution_callbacks.access_loc = parameter.loc;
        if (!substitute_default_argument(argument)) {
            return false;
        }
        TemplateArgumentBindingFailureReason default_reason =
            TemplateArgumentBindingFailureReason::None;
        if (!template_parameter_accepts_argument(*this,
                                                parameter,
                                                argument,
                                                &default_reason)) {
            if (TemplateArgumentBindingFailure* failure =
                    set_template_binding_failure(
                        failure_out,
                        TemplateArgumentBindingFailureKind::
                            InvalidDefaultArgument,
                        default_reason)) {
                failure->parameter_index = static_cast<uint32_t>(i);
                failure->expected_parameter_kind = parameter.kind;
                failure->actual_argument_kind = argument.kind;
            }
            return false;
        }
        bindings_out[i].kind = TemplateArgumentBindingKind::Single;
        bindings_out[i].arguments = {std::move(argument)};

        if (!populate_exact_template_parameter_bindings(
                info, bindings_out, substitution_callbacks)) {
            set_template_binding_failure(
                failure_out,
                TemplateArgumentBindingFailureKind::Internal,
                TemplateArgumentBindingFailureReason::
                    InternalBindingCountMismatch);
            return false;
        }
    }

    for (size_t i = 0; i < info.parameters.size(); ++i) {
        const TemplateParameter& parameter = info.parameters[i];
        if (parameter.kind != TemplateParameterKind::NonType ||
            bindings_out[i].is_unbound() ||
            !type_contains_type_param(parameter.non_type_type)) {
            continue;
        }
        if (class_template_placeholder_info(parameter.non_type_type)) {

            continue;
        }
        cir::TypeId target_type = parameter.non_type_type.valid()
            ? parameter.non_type_type
            : builder_.int_type();
        if (type_contains_type_param(target_type)) {
            target_type = substitute_pattern_type(target_type,
                                                  bindings_out,
                                                  substitution_callbacks);
            if (!target_type.valid()) {
                set_template_binding_failure(
                    failure_out,
                    TemplateArgumentBindingFailureKind::SubstitutionFailure,
                    TemplateArgumentBindingFailureReason::
                        DependentDefaultArgumentSubstitution,
                    "dependent template value argument type could not be substituted");
                return false;
            }
        }
        if (contains_auto_type(target_type)) {

            continue;
        }
        if (is_dependent_type(target_type)) {
            continue;
        }
        for (TemplateArgument& argument : bindings_out[i].arguments) {
            if (argument.kind != cir::TemplateArgumentKind::Value) {
                continue;
            }
            if (argument.is_dependent && !argument.is_defaulted) {

                argument.value_type = type_ref(target_type);
                continue;
            }
            std::string substitution_error;
            if (argument.is_dependent &&
                !substitute_template_value_argument(argument,
                                                    bindings_out,
                                                    substitution_callbacks,
                                                    &substitution_error)) {
                set_template_binding_failure(
                    failure_out,
                    TemplateArgumentBindingFailureKind::SubstitutionFailure,
                    TemplateArgumentBindingFailureReason::
                        DependentDefaultArgumentSubstitution,
                    substitution_error.empty()
                        ? "constant template argument could not be substituted"
                        : std::move(substitution_error));
                return false;
            }
            if (argument.is_dependent) {
                continue;
            }
            TemplateValueConstant constant;
            constant.kind = argument.value_kind;
            constant.null_kind = argument.null_kind;
            constant.integer_value = argument.integer_value;
            constant.floating_value = argument.floating_value;
            constant.entity = argument.value_entity;
            constant.closure_identity = argument.closure_identity;
            constant.byte_offset = argument.value_byte_offset;
            constant.elements = argument.value_elements;
            constant.meta_kind = argument.meta_kind;
            constant.meta_type = argument.type;
            TemplateArgument converted;
            std::string conversion_error;
            if (!build_template_value_argument(target_type,
                                               constant,
                                               converted,
                                               &conversion_error)) {
                set_template_binding_failure(
                    failure_out,
                    TemplateArgumentBindingFailureKind::SubstitutionFailure,
                    TemplateArgumentBindingFailureReason::None,
                    conversion_error.empty()
                        ? "constant template argument conversion failed"
                        : std::move(conversion_error));
                return false;
            }
            converted.is_defaulted = argument.is_defaulted;
            converted.value_spelling = argument.value_spelling;
            converted.expands_parameter_pack =
                argument.expands_parameter_pack;
            converted.expands_pack_pattern = argument.expands_pack_pattern;
            argument = std::move(converted);
        }
    }
    transaction.committed = true;
    if (candidate_transaction.has_value()) {
        candidate_transaction->commit();
    }
    return true;
}

std::vector<Session::TemplateArgument>
Session::flatten_template_argument_bindings(
    const TemplateArgumentBindings& bindings) const {
    std::vector<TemplateArgument> flattened;
    size_t total = 0;
    for (const TemplateArgumentBinding& binding : bindings) {
        if (!binding.is_unbound()) {
            total += binding.arguments.size();
        }
    }
    flattened.reserve(total);
    for (const TemplateArgumentBinding& binding : bindings) {
        if (!binding.is_unbound()) {
            flattened.insert(flattened.end(),
                             binding.arguments.begin(),
                             binding.arguments.end());
        }
    }
    return flattened;
}

} // namespace aburi::collect
