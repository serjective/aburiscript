#include "collect.h"

#include <algorithm>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::collect {

namespace {

class PatternCloneDepthScope {
public:
    explicit PatternCloneDepthScope(size_t& depth) : depth_(depth) {
        ++depth_;
    }
    PatternCloneDepthScope(const PatternCloneDepthScope&) = delete;
    PatternCloneDepthScope& operator=(const PatternCloneDepthScope&) = delete;

    ~PatternCloneDepthScope() {
        --depth_;
    }

private:
    size_t& depth_;
};

bool template_argument_is_type(const Session::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Type;
}

bool template_argument_is_value(const Session::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Value;
}

const Session::TemplateArgumentBinding* substitution_binding(
    const Session::TemplateArgumentBindings& bindings,
    uint32_t parameter_index) {
    if (parameter_index >= bindings.size()) {
        return nullptr;
    }
    return &bindings[parameter_index];
}

const Session::TemplateArgument* single_substitution_argument(
    const Session::TemplateArgumentBindings& bindings,
    uint32_t parameter_index,
    bool allow_pack_element = false) {
    const Session::TemplateArgumentBinding* binding =
        substitution_binding(bindings, parameter_index);
    if (!binding || binding->arguments.size() != 1 ||
        (!binding->is_single() &&
         !(allow_pack_element && binding->is_pack()))) {
        return nullptr;
    }
    return &binding->arguments.front();
}

std::optional<uint32_t> direct_value_parameter(
    const cir::TemplateValueExpression& expression) {
    if (!expression.valid()) {
        return std::nullopt;
    }
    uint32_t index = expression.root;
    while (index < expression.nodes.size() &&
           expression.nodes[index].kind ==
               cir::TemplateValueExprKind::Cast) {
        index = expression.nodes[index].lhs;
    }
    if (index >= expression.nodes.size()) {
        return std::nullopt;
    }
    const cir::TemplateValueExprNode& root = expression.nodes[index];
    if (root.kind != cir::TemplateValueExprKind::Parameter ||
        root.parameter_index == cir::TemplateValueExprNoParameter) {
        return std::nullopt;
    }
    return root.parameter_index;
}

bool decltype_category_is_known(cir::DecltypeOperandCategory category) {
    return category != cir::DecltypeOperandCategory::Unknown;
}

std::optional<cir::DecltypeOperandCategory> category_for_declared_entity(
    const cir::File& file,
    cir::EntityId entity) {
    if (!entity.valid() || !file.valid(entity)) {
        return std::nullopt;
    }
    switch (file.entity(entity).kind) {
        case cir::EntityKind::Variable:
        case cir::EntityKind::Parameter:
        case cir::EntityKind::Field:
            return cir::DecltypeOperandCategory::LValue;
        case cir::EntityKind::Function:
        case cir::EntityKind::Method:
        case cir::EntityKind::Destructor:
            return cir::DecltypeOperandCategory::FunctionDesignator;
        case cir::EntityKind::Enumerator:
        case cir::EntityKind::TemplateParam:
            return cir::DecltypeOperandCategory::PrValue;
        default:
            return std::nullopt;
    }
}

cir::TypeRef type_ref_for_declared_entity(const cir::File& file,
                                          cir::EntityId entity) {
    if (!entity.valid() || !file.valid(entity)) {
        return {};
    }
    const cir::Entity& record = file.entity(entity);
    if (!record.type.valid()) {
        return {};
    }
    return file.type_ref(record.type, record.qualifiers, record.memory_space);
}

struct DecltypeQualifiedValue {
    cir::TypeRef type;
    cir::DecltypeOperandCategory category =
        cir::DecltypeOperandCategory::Unknown;
};

cir::TypeId decltype_result_from_category(cir::File& file,
                                          cir::TypeRef operand_type,
                                          cir::DecltypeOperandCategory category) {
    if (!operand_type.type.valid()) {
        return {};
    }
    switch (category) {
        case cir::DecltypeOperandCategory::LValue:
            return file.reference_type(operand_type,
                                       cir::ReferenceKind::LValue);
        case cir::DecltypeOperandCategory::XValue:
            return file.reference_type(operand_type,
                                       cir::ReferenceKind::RValue);
        case cir::DecltypeOperandCategory::FunctionDesignator:
            return file.reference_type(operand_type,
                                       cir::ReferenceKind::LValue);
        case cir::DecltypeOperandCategory::PrValue:
        case cir::DecltypeOperandCategory::MemberPointerDesignator:
            return operand_type.type;
        case cir::DecltypeOperandCategory::Unknown:
            return {};
    }
    return {};
}

cir::TypeRef adjust_substituted_function_parameter(cir::File& file,
                                                   cir::TypeRef type) {
    cir::TypeId resolved = file.resolved_type(type.type);
    if (!file.valid(resolved)) {
        return {};
    }
    if (file.type(resolved).kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file.type_payload(resolved));
        if (!array) {
            return {};
        }
        type.type = file.pointer_type(array->element_type);
    } else if (file.type(resolved).kind == cir::TypeKind::Function) {
        type.type = file.pointer_type(file.type_ref(resolved));
    }
    return type;
}

std::optional<BuiltinKind> builtin_kind_for_transform(
    cir::BuiltinTypeTransformKind kind) {
    switch (kind) {
        case cir::BuiltinTypeTransformKind::RemoveConst:
            return BuiltinKind::REMOVE_CONST;
        case cir::BuiltinTypeTransformKind::RemoveVolatile:
            return BuiltinKind::REMOVE_VOLATILE;
        case cir::BuiltinTypeTransformKind::RemoveCV:
            return BuiltinKind::REMOVE_CV;
        case cir::BuiltinTypeTransformKind::RemoveCVRef:
            return BuiltinKind::REMOVE_CVREF;
        case cir::BuiltinTypeTransformKind::RemoveReference:
            return BuiltinKind::REMOVE_REFERENCE;
        case cir::BuiltinTypeTransformKind::UnderlyingType:
            return BuiltinKind::UNDERLYING_TYPE;
        case cir::BuiltinTypeTransformKind::RemoveExtent:
            return BuiltinKind::REMOVE_EXTENT;
        case cir::BuiltinTypeTransformKind::RemoveAllExtents:
            return BuiltinKind::REMOVE_ALL_EXTENTS;
        case cir::BuiltinTypeTransformKind::AddLValueReference:
            return BuiltinKind::ADD_LVALUE_REFERENCE;
        case cir::BuiltinTypeTransformKind::AddRValueReference:
            return BuiltinKind::ADD_RVALUE_REFERENCE;
        case cir::BuiltinTypeTransformKind::AddPointer:
            return BuiltinKind::ADD_POINTER;
        case cir::BuiltinTypeTransformKind::Decay:
            return BuiltinKind::DECAY;
        default:
            return std::nullopt;
    }
}

} // namespace

cir::TypeRef Session::substitute_pattern_type_ref(
    cir::TypeRef type,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks) {
    if (!type.type.valid() || !file_.valid(type.type)) {
        return type;
    }
    if (file_.type(type.type).kind ==
        cir::TypeKind::AliasSpecialization) {
        cir::TypeRef complete_substitution;
        cir::TypeId substituted =
            substitute_pattern_type(type.type,
                                    argument_bindings,
                                    callbacks,
                                    &complete_substitution);
        if (!substituted.valid()) {
            return {};
        }
        cir::TypeRef result = complete_substitution.valid()
            ? complete_substitution
            : file_.type_ref(substituted);
        result.qualifiers = static_cast<uint8_t>(
            result.qualifiers | type.qualifiers);
        if (type.memory_space != cir::MemorySpace::Default) {
            result.memory_space = type.memory_space;
        }
        return result;
    }
    cir::TypeId resolved = file_.resolved_type(type.type);
    if (!file_.valid(resolved)) {
        return type;
    }
    if (file_.type(resolved).kind == cir::TypeKind::TypeParam) {
        const auto* parameter = std::get_if<cir::TypeParamTypePayload>(
            &file_.type_payload(resolved));
        if (!parameter) {
            return {};
        }
        const TemplateArgument* argument = nullptr;
        auto exact = callbacks.exact_type_parameter_bindings.find(
            static_cast<uint32_t>(resolved.index));
        if (exact != callbacks.exact_type_parameter_bindings.end()) {
            const TemplateArgumentBinding& binding = exact->second;
            if (binding.is_single() && binding.arguments.size() == 1) {
                argument = &binding.arguments.front();
            }
        } else if (
            callbacks.exact_type_parameter_bindings_are_authoritative) {
            return type;
        } else {
            argument = single_substitution_argument(
                argument_bindings,
                parameter->index,
                parameter->is_parameter_pack &&
                    callbacks.allow_parameter_pack_element_substitution);
        }
        if (parameter->is_parameter_pack &&
            !callbacks.allow_parameter_pack_element_substitution) {
            return {};
        }
        if (!argument || !template_argument_is_type(*argument)) {
            return {};
        }
        cir::TypeRef substituted = argument->type;
        substituted.qualifiers |= type.qualifiers;
        if (type.memory_space != cir::MemorySpace::Default) {
            substituted.memory_space = type.memory_space;
        }
        return substituted;
    }
    if (file_.type(resolved).kind == cir::TypeKind::BuiltinTransform) {
        const auto& transform =
            std::get<cir::BuiltinTypeTransformTypePayload>(
                file_.type_payload(resolved));
        cir::TypeRef operand = substitute_pattern_type_ref(
            transform.operand_type, argument_bindings, callbacks);
        std::optional<BuiltinKind> kind =
            builtin_kind_for_transform(transform.transform_kind);
        if (!operand.valid() || !kind) {
            return {};
        }

        cir::TypeRef substituted = collect_builtin_type_transform(
            *kind, operand, callbacks.access_loc);
        if (!substituted.valid()) {
            return {};
        }
        substituted.qualifiers = static_cast<uint8_t>(
            substituted.qualifiers | type.qualifiers);
        if (type.memory_space != cir::MemorySpace::Default) {
            substituted.memory_space = type.memory_space;
        }
        return substituted;
    }
    if (file_.type(resolved).kind ==
        cir::TypeKind::BuiltinPackElement) {
        const auto& pack_element =
            std::get<cir::BuiltinPackElementTypePayload>(
                file_.type_payload(resolved));
        cir::TypeRef substituted =
            substitute_builtin_pack_element_type(
                pack_element, argument_bindings, callbacks);
        if (!substituted.valid()) {
            return {};
        }
        substituted.qualifiers = static_cast<uint8_t>(
            substituted.qualifiers | type.qualifiers);
        if (type.memory_space != cir::MemorySpace::Default) {
            substituted.memory_space = type.memory_space;
        }
        return substituted;
    }
    const auto* dependent_name =
        file_.type(resolved).kind == cir::TypeKind::DependentName
            ? std::get_if<cir::DependentNameTypePayload>(
                  &file_.type_payload(resolved))
            : nullptr;
    cir::TypeRef complete_substitution;
    cir::TypeId substituted =
        substitute_pattern_type(type.type,
                                argument_bindings,
                                callbacks,
                                &complete_substitution);
    if (!substituted.valid()) {
        return {};
    }
    if (complete_substitution.valid()) {
        complete_substitution.qualifiers = static_cast<uint8_t>(
            complete_substitution.qualifiers | type.qualifiers);
        if (type.memory_space != cir::MemorySpace::Default) {
            complete_substitution.memory_space = type.memory_space;
        }
        return complete_substitution;
    }

    if (dependent_name && dependent_name->template_arguments.empty()) {
        cir::TypeRef qualifier = substitute_pattern_type_ref(
            dependent_name->qualifier_type,
            argument_bindings,
            callbacks);
        cir::TypeId resolved_qualifier =
            qualifier.valid() ? file_.resolved_type(qualifier.type)
                              : cir::TypeId{};
        cir::EntityId record = file_.valid(resolved_qualifier) &&
                file_.type(resolved_qualifier).kind == cir::TypeKind::Record
            ? file_.record_entity(resolved_qualifier)
            : cir::EntityId{};
        cir::DeclContextId context = record.valid() && file_.valid(record)
            ? file_.entity(record).semantic_context
            : cir::DeclContextId{};
        cir::TypeRef qualified = context.valid()
            ? lookup_qualified_type_name_ref(
                  context, file_.name(dependent_name->member_name))
            : cir::TypeRef{};
        if (qualified.valid() &&
            file_.resolved_type(qualified.type) ==
                file_.resolved_type(substituted)) {
            qualified.qualifiers = static_cast<uint8_t>(
                qualified.qualifiers | type.qualifiers);
            if (type.memory_space != cir::MemorySpace::Default) {
                qualified.memory_space = type.memory_space;
            }
            return qualified;
        }
    }
    return file_.type_ref(substituted,
                          type.qualifiers,
                          type.memory_space);
}

cir::TypeRef Session::substitute_builtin_pack_element_type(
    const cir::BuiltinPackElementTypePayload& pack_element,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks) {
    std::vector<TemplateArgument> arguments;
    arguments.reserve(pack_element.arguments.size());
    for (const TemplateArgument& argument : pack_element.arguments) {
        if (argument.generated_pack_kind !=
            cir::TemplateGeneratedPackKind::None) {
            if (!append_substituted_generated_pack(
                    argument,
                    argument_bindings,
                    callbacks,
                    arguments,
                    /*reject_unresolved_template_parameter=*/false)) {
                return {};
            }
            continue;
        }
        if (argument.expands_parameter_pack) {
            if (!template_argument_is_type(argument)) {
                return {};
            }
            cir::TypeId pack_type =
                file_.resolved_type(argument.type.type);
            const auto* pack =
                file_.valid(pack_type)
                    ? std::get_if<cir::TypeParamTypePayload>(
                          &file_.type_payload(pack_type))
                    : nullptr;
            if (!pack || !pack->is_parameter_pack) {
                return {};
            }
            const TemplateArgumentBinding* binding = nullptr;
            auto exact = callbacks.exact_type_parameter_bindings.find(
                static_cast<uint32_t>(pack_type.index));
            if (exact !=
                callbacks.exact_type_parameter_bindings.end()) {
                binding = &exact->second;
            } else {
                binding =
                    substitution_binding(argument_bindings, pack->index);
            }
            if (!binding || !binding->is_pack()) {
                return {};
            }
            for (const TemplateArgument& element : binding->arguments) {
                if (!template_argument_is_type(element)) {
                    return {};
                }
                arguments.push_back(element);
            }
            continue;
        }
        if (argument.expands_pack_pattern) {
            switch (expand_template_argument_pack_pattern(argument,
                                                          argument_bindings,
                                                          callbacks,
                                                          &arguments)) {
                case PackPatternExpansionStatus::Expanded:
                    continue;
                case PackPatternExpansionStatus::StillDependent:
                    arguments.push_back(argument);
                    continue;
                default:
                    return {};
            }
        }

        TemplateArgument substituted = argument;
        if (template_argument_is_type(argument)) {
            substituted.type = substitute_pattern_type_ref(
                argument.type, argument_bindings, callbacks);
            if (!substituted.type.valid()) {
                return {};
            }
            substituted.is_dependent =
                is_dependent_type(substituted.type.type);
        } else if (template_argument_is_value(argument)) {

            const bool direct_index_parameter =
                substituted.value_param_index !=
                cir::ArrayTypePayload::no_extent_param;
            if (direct_index_parameter) {
                substituted.value_type = {};
            }
            if (!substitute_template_value_argument(
                    substituted,
                    argument_bindings,
                    callbacks)) {
                return {};
            }
            if (direct_index_parameter) {
                substituted.value_type =
                    type_ref(builder_.usize_type());
            }
        } else {
            return {};
        }
        arguments.push_back(std::move(substituted));
    }
    return collect_builtin_pack_element_type(
        std::move(arguments),
        callbacks.access_loc,
        /*diagnose=*/false);
}

bool Session::populate_exact_template_parameter_bindings(
    const TemplateInfo& info,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks) const {
    callbacks.exact_type_parameter_bindings_are_authoritative = true;
    auto append =
        [&](const std::vector<TemplateParameter>& parameters,
            const TemplateArgumentBindings& bindings) {
            for (size_t i = 0; i < parameters.size() && i < bindings.size();
                 ++i) {
                const TemplateParameter& parameter = parameters[i];
                if (bindings[i].is_unbound()) {
                    continue;
                }
                if (parameter.kind == TemplateParameterKind::Type &&
                    parameter.type_param_type.valid()) {
                    cir::TypeId identity =
                        file_.resolved_type(parameter.type_param_type);
                    callbacks.exact_type_parameter_bindings[
                        static_cast<uint32_t>(identity.index)] = bindings[i];
                } else if (parameter.kind ==
                               TemplateParameterKind::NonType &&
                           parameter.entity.valid()) {
                    callbacks.exact_value_parameter_bindings[
                        static_cast<uint32_t>(parameter.entity.index)] =
                        bindings[i];
                } else if (parameter.kind ==
                               TemplateParameterKind::Template &&
                           parameter.entity.valid()) {
                    callbacks.exact_template_parameter_bindings[
                        static_cast<uint32_t>(parameter.entity.index)] =
                        bindings[i];
                }
            }
        };
    for (const TemplateInfo::TemplateInstantiationBinding& enclosing :
         info.enclosing_instantiation_bindings) {
        append(enclosing.parameters, enclosing.argument_bindings);
    }
    cir::EntityId owner = info.entity.valid() && file_.valid(info.entity)
        ? file_.entity(info.entity).parent
        : cir::EntityId{};
    std::unordered_set<uint32_t> visited;
    while (owner.valid() && file_.valid(owner) &&
           visited.insert(static_cast<uint32_t>(owner.index)).second) {
        if (const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(owner)) {
            if (const TemplateInfo* owner_info =
                    template_info(fact->template_entity)) {
                append(owner_info->parameters, fact->argument_bindings);
            }
        }
        owner = file_.entity(owner).parent;
    }
    append(info.parameters, argument_bindings);
    return true;
}

namespace {

uint64_t pack_pattern_reference_key(
    const cir::TemplateValuePackReference& reference) {
    uint64_t discriminator = static_cast<uint64_t>(reference.kind) << 62;
    if (reference.kind == cir::TemplateValuePackKind::Type &&
        reference.parameter_type.valid()) {
        return discriminator | (1ull << 60) |
               static_cast<uint64_t>(reference.parameter_type.index);
    }
    if (reference.declaration.valid()) {
        return discriminator | (1ull << 61) |
               static_cast<uint64_t>(reference.declaration.index);
    }
    return discriminator | static_cast<uint64_t>(reference.index);
}

} // namespace

void Session::collect_type_pack_pattern_references(
    cir::TypeId type,
    const TemplateArgumentBindings& argument_bindings,
    const PatternInstantiationCallbacks& callbacks,
    std::vector<cir::TemplateValuePackReference>& references,
    std::unordered_set<uint32_t>& visited_types) const {
    if (!type.valid() || !file_.valid(type)) {
        return;
    }

    cir::TypeId inspected =
        file_.type(type).kind == cir::TypeKind::AliasSpecialization
        ? type
        : file_.resolved_type(type);
    if (!file_.valid(inspected) ||
        !visited_types.insert(static_cast<uint32_t>(inspected.index)).second) {
        return;
    }
    auto add_type = [&](cir::TypeRef ref) {
        collect_type_pack_pattern_references(ref.type,
                                             argument_bindings,
                                             callbacks,
                                             references,
                                             visited_types);
    };
    auto value_binding_is_pack = [&](cir::EntityId declaration,
                                     uint32_t parameter_index) {
        if (declaration.valid()) {
            auto exact = callbacks.exact_value_parameter_bindings.find(
                static_cast<uint32_t>(declaration.index));
            if (exact != callbacks.exact_value_parameter_bindings.end()) {
                return exact->second.is_pack();
            }
        }
        return parameter_index != cir::TemplateValueExprNoParameter &&
               parameter_index < argument_bindings.size() &&
               argument_bindings[parameter_index].is_pack();
    };
    auto template_binding_is_pack = [&](cir::EntityId declaration,
                                        uint32_t parameter_index) {
        if (declaration.valid()) {
            auto exact = callbacks.exact_template_parameter_bindings.find(
                static_cast<uint32_t>(declaration.index));
            if (exact != callbacks.exact_template_parameter_bindings.end()) {
                return exact->second.is_pack();
            }
        }
        return parameter_index != cir::ArrayTypePayload::no_extent_param &&
               parameter_index < argument_bindings.size() &&
               argument_bindings[parameter_index].is_pack();
    };
    std::function<void(const cir::TemplateValueExpression&)> add_value_expr =
        [&](const cir::TemplateValueExpression& expression) {
            if (!expression.valid()) {
                return;
            }
            for (const cir::TemplateValueExprNode& node : expression.nodes) {
                for (const cir::TemplateValuePackReference& reference :
                     node.pack_references) {
                    references.push_back(reference);
                }
                if (node.kind == cir::TemplateValueExprKind::Parameter &&
                    node.parameter_index !=
                        cir::TemplateValueExprNoParameter &&
                    value_binding_is_pack(node.entity,
                                          node.parameter_index)) {
                    cir::TemplateValuePackReference reference;
                    reference.kind = cir::TemplateValuePackKind::Value;
                    reference.index = node.parameter_index;
                    reference.declaration = node.entity;
                    reference.name = node.name;
                    references.push_back(reference);
                }
                if (node.type.valid()) {
                    collect_type_pack_pattern_references(node.type,
                                                         argument_bindings,
                                                         callbacks,
                                                         references,
                                                         visited_types);
                }
                if (node.result_type.type.valid()) {
                    collect_type_pack_pattern_references(
                        node.result_type.type,
                        argument_bindings,
                        callbacks,
                        references,
                        visited_types);
                }
                if (node.qualifier_type.type.valid()) {
                    collect_type_pack_pattern_references(
                        node.qualifier_type.type,
                        argument_bindings,
                        callbacks,
                        references,
                        visited_types);
                }
            }
        };
    auto add_arguments = [&](const std::vector<TemplateArgument>& arguments) {
        for (const TemplateArgument& argument : arguments) {
            if (template_argument_is_type(argument)) {
                add_type(argument.type);
            } else if (template_argument_is_value(argument)) {
                if (argument.value_param_index !=
                        cir::ArrayTypePayload::no_extent_param &&
                    value_binding_is_pack(argument.value_entity,
                                          argument.value_param_index)) {
                    cir::TemplateValuePackReference reference;
                    reference.kind = cir::TemplateValuePackKind::Value;
                    reference.index = argument.value_param_index;
                    reference.declaration = argument.value_entity;
                    reference.name = argument.dependent_value_name;
                    references.push_back(reference);
                }
                add_value_expr(argument.dependent_value_expr);
                add_type(argument.dependent_value_qualifier);
                add_type(argument.value_type);
            } else if (argument.kind == cir::TemplateArgumentKind::Template &&
                       template_binding_is_pack(
                           argument.template_entity,
                           argument.template_param_index)) {
                cir::TemplateValuePackReference reference;
                reference.kind = cir::TemplateValuePackKind::Template;
                reference.index = argument.template_param_index;
                reference.declaration = argument.template_entity;
                reference.name = argument.template_name;
                references.push_back(reference);
            }
        }
    };
    const cir::TypePayload& payload = file_.type_payload(inspected);
    switch (file_.type(inspected).kind) {
        case cir::TypeKind::AliasSpecialization:
            add_arguments(std::get<cir::AliasSpecializationTypePayload>(
                              payload)
                              .arguments);
            break;
        case cir::TypeKind::TypeParam: {
            const auto& parameter =
                std::get<cir::TypeParamTypePayload>(payload);
            if (parameter.is_parameter_pack) {
                cir::TemplateValuePackReference reference;
                reference.kind = cir::TemplateValuePackKind::Type;
                reference.index = parameter.index;
                reference.parameter_type = inspected;
                reference.declaration = parameter.entity;
                reference.depth = parameter.depth;
                reference.name = parameter.name;
                references.push_back(reference);
            }
            break;
        }
        case cir::TypeKind::Pointer:
            add_type(std::get<cir::PointerTypePayload>(payload).pointee);
            break;
        case cir::TypeKind::BlockPointer:
            add_type(std::get<cir::BlockPointerTypePayload>(payload).pointee);
            break;
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            add_type(std::get<cir::ReferenceTypePayload>(payload)
                         .referred_type);
            break;
        case cir::TypeKind::Array: {
            const auto& array = std::get<cir::ArrayTypePayload>(payload);
            add_type(array.element_type);
            add_value_expr(array.dependent_size_expr);
            break;
        }
        case cir::TypeKind::Vector:
            add_type(std::get<cir::VectorTypePayload>(payload).element_type);
            break;
        case cir::TypeKind::Complex:
            add_type(std::get<cir::ComplexTypePayload>(payload).element_type);
            break;
        case cir::TypeKind::MemberPointer: {
            const auto& member =
                std::get<cir::MemberPointerTypePayload>(payload);
            add_type(member.class_type);
            add_type(member.member_type);
            break;
        }
        case cir::TypeKind::Function: {
            const auto& function =
                std::get<cir::FunctionTypePayload>(payload);
            add_type(function.return_type);
            for (const cir::TypeRef& parameter : function.parameters) {
                add_type(parameter);
            }
            break;
        }
        case cir::TypeKind::TemplateSpecialization:
            add_arguments(std::get<cir::TemplateSpecializationTypePayload>(
                              payload)
                              .arguments);
            break;
        case cir::TypeKind::Record: {

            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(file_.record_entity(inspected));
            if (fact) {
                add_arguments(fact->template_arguments());
            }
            break;
        }
        case cir::TypeKind::DependentName: {
            const auto& dependent =
                std::get<cir::DependentNameTypePayload>(payload);
            add_type(dependent.qualifier_type);
            add_arguments(dependent.template_arguments);
            break;
        }
        case cir::TypeKind::DecltypeExpr: {
            const auto& decltype_expr =
                std::get<cir::DecltypeExprTypePayload>(payload);
            add_type(decltype_expr.operand_type);
            add_type(decltype_expr.dependent_value_qualifier);
            add_value_expr(decltype_expr.operand_expression);
            break;
        }
        case cir::TypeKind::BuiltinTransform:
            add_type(std::get<cir::BuiltinTypeTransformTypePayload>(payload)
                         .operand_type);
            break;
        case cir::TypeKind::BuiltinPackElement:
            add_arguments(std::get<cir::BuiltinPackElementTypePayload>(
                              payload)
                              .arguments);
            break;
        case cir::TypeKind::PackIndex: {
            const auto& pack_index =
                std::get<cir::PackIndexTypePayload>(payload);
            add_type(pack_index.pack_type);
            add_value_expr(pack_index.index_expression);
            break;
        }
        default:
            break;
    }
}

Session::PackPatternExpansionStatus
Session::expand_template_argument_pack_pattern(
    const TemplateArgument& argument,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks,
    std::vector<TemplateArgument>* destination,
    std::vector<cir::TemplateValuePackReference>* discovered_references) {

    std::vector<cir::TemplateValuePackReference> references;
    std::unordered_set<uint32_t> visited_types;
    if (template_argument_is_type(argument)) {
        collect_type_pack_pattern_references(argument.type.type,
                                             argument_bindings,
                                             callbacks,
                                             references,
                                             visited_types);
    } else if (template_argument_is_value(argument)) {

        cir::TemplateValueExpression probe_holder;
        const cir::TemplateValueExpression& expression =
            argument.dependent_value_expr.valid()
                ? argument.dependent_value_expr
                : probe_holder;
        for (const cir::TemplateValueExprNode& node : expression.nodes) {
            for (const cir::TemplateValuePackReference& reference :
                 node.pack_references) {
                references.push_back(reference);
            }
            if (node.kind == cir::TemplateValueExprKind::Parameter &&
                node.parameter_index != cir::TemplateValueExprNoParameter &&
                node.parameter_index < argument_bindings.size() &&
                argument_bindings[node.parameter_index].is_pack()) {
                cir::TemplateValuePackReference reference;
                reference.kind = cir::TemplateValuePackKind::Value;
                reference.index = node.parameter_index;
                reference.declaration = node.entity;
                reference.name = node.name;
                references.push_back(reference);
            }
            if (node.type.valid()) {
                collect_type_pack_pattern_references(node.type,
                                                     argument_bindings,
                                                     callbacks,
                                                     references,
                                                     visited_types);
            }
            if (node.result_type.type.valid()) {
                collect_type_pack_pattern_references(
                    node.result_type.type,
                    argument_bindings,
                    callbacks,
                    references,
                    visited_types);
            }
            if (node.qualifier_type.type.valid()) {
                collect_type_pack_pattern_references(
                    node.qualifier_type.type,
                    argument_bindings,
                    callbacks,
                    references,
                    visited_types);
            }
        }
        collect_type_pack_pattern_references(
            argument.dependent_value_qualifier.type,
            argument_bindings,
            callbacks,
            references,
            visited_types);
        collect_type_pack_pattern_references(argument.value_type.type,
                                             argument_bindings,
                                             callbacks,
                                             references,
                                             visited_types);
        if (argument.value_param_index !=
                cir::ArrayTypePayload::no_extent_param &&
            argument.value_param_index < argument_bindings.size() &&
            argument_bindings[argument.value_param_index].is_pack()) {
            cir::TemplateValuePackReference reference;
            reference.kind = cir::TemplateValuePackKind::Value;
            reference.index = argument.value_param_index;
            reference.declaration = argument.value_entity;
            reference.name = argument.dependent_value_name;
            references.push_back(reference);
        }
    } else {
        return PackPatternExpansionStatus::Failure;
    }

    std::unordered_set<uint64_t> seen;
    std::vector<cir::TemplateValuePackReference> unique;
    for (const cir::TemplateValuePackReference& reference : references) {
        if (reference.kind == cir::TemplateValuePackKind::Function) {

            return PackPatternExpansionStatus::StillDependent;
        }
        if (seen.insert(pack_pattern_reference_key(reference)).second) {
            unique.push_back(reference);
        }
    }
    if (discovered_references) {
        *discovered_references = unique;
    }
    if (unique.empty()) {
        return PackPatternExpansionStatus::NoPacks;
    }

    auto binding_for_reference = [&](
        const cir::TemplateValuePackReference& reference)
        -> const TemplateArgumentBinding* {
        if (reference.kind == cir::TemplateValuePackKind::Type &&
            reference.parameter_type.valid()) {
            auto exact = callbacks.exact_type_parameter_bindings.find(
                static_cast<uint32_t>(reference.parameter_type.index));
            if (exact != callbacks.exact_type_parameter_bindings.end()) {
                return &exact->second;
            }
        }
        if (reference.kind == cir::TemplateValuePackKind::Value &&
            reference.declaration.valid()) {
            auto exact = callbacks.exact_value_parameter_bindings.find(
                static_cast<uint32_t>(reference.declaration.index));
            if (exact != callbacks.exact_value_parameter_bindings.end()) {
                return &exact->second;
            }
        }
        if (reference.kind == cir::TemplateValuePackKind::Template &&
            reference.declaration.valid()) {
            auto exact = callbacks.exact_template_parameter_bindings.find(
                static_cast<uint32_t>(reference.declaration.index));
            if (exact != callbacks.exact_template_parameter_bindings.end()) {
                return &exact->second;
            }
        }
        if (reference.index != cir::TemplateValueExprNoParameter &&
            reference.index < argument_bindings.size() &&
            !argument_bindings[reference.index].is_unbound()) {
            return &argument_bindings[reference.index];
        }
        return nullptr;
    };

    std::optional<size_t> width;
    for (const cir::TemplateValuePackReference& reference : unique) {
        const TemplateArgumentBinding* binding =
            binding_for_reference(reference);
        if (!binding || !binding->is_pack()) {

            return PackPatternExpansionStatus::StillDependent;
        }
        if (width.has_value() && *width != binding->arguments.size()) {
            return PackPatternExpansionStatus::LengthMismatch;
        }
        width = binding->arguments.size();
    }
    if (!destination) {
        return PackPatternExpansionStatus::Expanded;
    }

    for (size_t element = 0; element < width.value_or(0); ++element) {
        TemplateArgumentBindings projected_bindings = argument_bindings;
        PatternInstantiationCallbacks element_callbacks = callbacks;
        element_callbacks.allow_parameter_pack_element_substitution = true;
        for (const cir::TemplateValuePackReference& reference : unique) {
            const TemplateArgumentBinding* binding =
                binding_for_reference(reference);
            if (!binding || element >= binding->arguments.size()) {
                return PackPatternExpansionStatus::Failure;
            }
            TemplateArgumentBinding single;
            single.kind = TemplateArgumentBindingKind::Single;
            single.arguments = {binding->arguments[element]};

            if (reference.index != cir::TemplateValueExprNoParameter &&
                reference.index < projected_bindings.size() &&
                binding == &argument_bindings[reference.index]) {
                projected_bindings[reference.index] = single;
            }
            if (reference.kind == cir::TemplateValuePackKind::Type &&
                reference.parameter_type.valid()) {
                element_callbacks.exact_type_parameter_bindings[
                    static_cast<uint32_t>(
                        reference.parameter_type.index)] = single;
            } else if (reference.kind == cir::TemplateValuePackKind::Value &&
                       reference.declaration.valid()) {
                element_callbacks.exact_value_parameter_bindings[
                    static_cast<uint32_t>(reference.declaration.index)] =
                    single;
            } else if (reference.kind ==
                           cir::TemplateValuePackKind::Template &&
                       reference.declaration.valid()) {
                element_callbacks.exact_template_parameter_bindings[
                    static_cast<uint32_t>(reference.declaration.index)] =
                    single;
            }
        }
        TemplateArgument substituted = argument;
        substituted.expands_parameter_pack = false;
        substituted.expands_pack_pattern = false;
        if (template_argument_is_type(argument)) {
            cir::TypeRef element_type = substitute_pattern_type_ref(
                argument.type, projected_bindings, element_callbacks);
            if (!element_type.valid()) {
                return PackPatternExpansionStatus::Failure;
            }
            substituted.type = element_type;
            substituted.is_dependent = is_dependent_type(element_type.type);
        } else {
            if (!substitute_template_value_argument(substituted,
                                                    projected_bindings,
                                                    element_callbacks)) {
                return PackPatternExpansionStatus::Failure;
            }
        }
        destination->push_back(std::move(substituted));
    }
    return PackPatternExpansionStatus::Expanded;
}

bool Session::type_pack_pattern_lengths_mismatch(
    cir::TypeId type,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks) {
    if (!type.valid() || !file_.valid(type)) {
        return false;
    }
    auto scan_arguments = [&](const std::vector<TemplateArgument>& arguments) {
        for (const TemplateArgument& argument : arguments) {
            if (argument.expands_pack_pattern &&
                expand_template_argument_pack_pattern(argument,
                                                      argument_bindings,
                                                      callbacks,
                                                      nullptr) ==
                    PackPatternExpansionStatus::LengthMismatch) {
                return true;
            }
            if (template_argument_is_type(argument) &&
                type_pack_pattern_lengths_mismatch(argument.type.type,
                                                   argument_bindings,
                                                   callbacks)) {
                return true;
            }
        }
        return false;
    };
    if (file_.type(type).kind == cir::TypeKind::AliasSpecialization) {
        return scan_arguments(
            std::get<cir::AliasSpecializationTypePayload>(
                file_.type_payload(type))
                .arguments);
    }
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return false;
    }
    const cir::TypePayload& payload = file_.type_payload(resolved);
    switch (file_.type(resolved).kind) {
        case cir::TypeKind::TemplateSpecialization:
            return scan_arguments(
                std::get<cir::TemplateSpecializationTypePayload>(payload)
                    .arguments);
        case cir::TypeKind::Record: {
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(file_.record_entity(resolved));
            return fact && scan_arguments(fact->template_arguments());
        }
        case cir::TypeKind::DependentName:
            return scan_arguments(
                std::get<cir::DependentNameTypePayload>(payload)
                    .template_arguments);
        case cir::TypeKind::Pointer:
            return type_pack_pattern_lengths_mismatch(
                std::get<cir::PointerTypePayload>(payload).pointee.type,
                argument_bindings,
                callbacks);
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return type_pack_pattern_lengths_mismatch(
                std::get<cir::ReferenceTypePayload>(payload)
                    .referred_type.type,
                argument_bindings,
                callbacks);
        case cir::TypeKind::Array:
            return type_pack_pattern_lengths_mismatch(
                std::get<cir::ArrayTypePayload>(payload).element_type.type,
                argument_bindings,
                callbacks);
        default:
            return false;
    }
}

std::optional<std::vector<cir::TypeRef>>
Session::substitute_pattern_function_parameter_pack(
    cir::TypeRef pattern,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks) {
    cir::TypeId wrapper = file_.function_type(
        file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::Void)),
        {pattern},
        /*is_variadic=*/false,
        /*has_prototype=*/true,
        /*member_is_const=*/false,
        {},
        {1});
    cir::TypeId substituted =
        substitute_pattern_type(wrapper, argument_bindings, callbacks);
    cir::TypeId resolved = file_.resolved_type(substituted);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Function) {
        return std::nullopt;
    }
    const auto* function = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(resolved));
    if (!function) {
        return std::nullopt;
    }
    return function->parameters;
}
// todo: also massive function (althrough most is lambdas)
Session::UnevaluatedCallResolution
Session::resolve_unevaluated_call_expression(
    cir::TemplateValueExpression expression,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks) {
    UnevaluatedCallResolution result;
    result.expression = std::move(expression);
    if (!result.expression.valid()) {
        result.status = UnevaluatedCallResolutionStatus::SubstitutionFailure;
        return result;
    }

    begin_unevaluated_operand();
    struct UnevaluatedResolutionScope {
        Session* session = nullptr;
        ~UnevaluatedResolutionScope() {
            if (session) {
                session->end_unevaluated_operand();
            }
        }
    } unevaluated_scope{this};

    SpeculativeParseGuard transaction = speculative_parse();
    PatternInstantiationCallbacks substitution_callbacks = callbacks;
    substitution_callbacks.preserve_opaque_dependent_call_types = true;

    auto append_expression = [](
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

    auto extract_expression = [](
        const cir::TemplateValueExpression& source,
        uint32_t root,
        std::unordered_map<uint32_t, uint32_t>* source_to_extracted = nullptr)
        -> std::optional<cir::TemplateValueExpression> {
        if (root == cir::TemplateValueExprNoNode ||
            root >= source.nodes.size()) {
            return std::nullopt;
        }
        cir::TemplateValueExpression extracted;
        extracted.loc = source.loc;
        extracted.definition_context = source.definition_context;
        extracted.definition_lookup_generation =
            source.definition_lookup_generation;
        std::unordered_map<uint32_t, uint32_t> remap;
        std::unordered_set<uint32_t> visiting;
        std::function<std::optional<uint32_t>(uint32_t)> clone;
        clone = [&](uint32_t index) -> std::optional<uint32_t> {
            if (index == cir::TemplateValueExprNoNode) {
                return cir::TemplateValueExprNoNode;
            }
            if (index >= source.nodes.size() || visiting.contains(index)) {
                return std::nullopt;
            }
            if (auto found = remap.find(index); found != remap.end()) {
                return found->second;
            }
            visiting.insert(index);
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
                visiting.erase(index);
                return std::nullopt;
            }
            for (uint32_t& operand : node.operands) {
                if (!clone_child(operand)) {
                    visiting.erase(index);
                    return std::nullopt;
                }
            }
            uint32_t mapped =
                static_cast<uint32_t>(extracted.nodes.size());
            extracted.nodes.push_back(std::move(node));
            remap[index] = mapped;
            visiting.erase(index);
            return mapped;
        };
        std::optional<uint32_t> mapped_root = clone(root);
        if (!mapped_root.has_value()) {
            return std::nullopt;
        }
        if (source_to_extracted) {
            *source_to_extracted = remap;
        }
        extracted.root = *mapped_root;
        return extracted;
    };

    enum class PackExpansionStatus : uint8_t {
        Expanded,
        StillDependent,
        Failure,
    };
    auto element_bindings = [&](
        const std::vector<cir::TemplateValuePackReference>& references,
        size_t element,
        TemplateArgumentBindings& bindings,
        size_t* common_size) -> PackExpansionStatus {
        bindings = argument_bindings;
        std::optional<size_t> width;
        for (const cir::TemplateValuePackReference& reference : references) {
            if (reference.index == cir::TemplateValueExprNoParameter ||
                reference.index >= argument_bindings.size()) {
                return PackExpansionStatus::StillDependent;
            }
            const TemplateArgumentBinding& source =
                argument_bindings[reference.index];
            if (source.is_unbound()) {
                return PackExpansionStatus::StillDependent;
            }
            if (!source.is_pack()) {
                return PackExpansionStatus::Failure;
            }
            if (width.has_value() && *width != source.arguments.size()) {
                return PackExpansionStatus::Failure;
            }
            width = source.arguments.size();
            if (element >= source.arguments.size()) {
                return PackExpansionStatus::Failure;
            }
            cir::TemplateArgumentKind expected =
                reference.kind == cir::TemplateValuePackKind::Value
                    ? cir::TemplateArgumentKind::Value
                    : reference.kind ==
                              cir::TemplateValuePackKind::Template
                          ? cir::TemplateArgumentKind::Template
                          : cir::TemplateArgumentKind::Type;
            if (source.arguments[element].kind != expected) {
                return PackExpansionStatus::Failure;
            }
            TemplateArgumentBinding projected;
            projected.kind = TemplateArgumentBindingKind::Single;
            projected.arguments = {source.arguments[element]};
            bindings[reference.index] = std::move(projected);
        }
        if (!width.has_value()) {
            return PackExpansionStatus::Failure;
        }
        if (common_size) {
            *common_size = *width;
        }
        return PackExpansionStatus::Expanded;
    };

    auto expansion_width = [&](
        const std::vector<cir::TemplateValuePackReference>& references,
        size_t& width) -> PackExpansionStatus {
        if (references.empty()) {
            return PackExpansionStatus::Failure;
        }
        TemplateArgumentBindings projected;

        std::optional<size_t> common;
        for (const cir::TemplateValuePackReference& reference : references) {
            if (reference.index == cir::TemplateValueExprNoParameter ||
                reference.index >= argument_bindings.size() ||
                argument_bindings[reference.index].is_unbound()) {
                return PackExpansionStatus::StillDependent;
            }
            const TemplateArgumentBinding& binding =
                argument_bindings[reference.index];
            if (!binding.is_pack()) {
                return PackExpansionStatus::Failure;
            }
            if (common.has_value() && *common != binding.arguments.size()) {
                return PackExpansionStatus::Failure;
            }
            common = binding.arguments.size();
            cir::TemplateArgumentKind expected =
                reference.kind == cir::TemplateValuePackKind::Value
                    ? cir::TemplateArgumentKind::Value
                    : reference.kind ==
                              cir::TemplateValuePackKind::Template
                          ? cir::TemplateArgumentKind::Template
                          : cir::TemplateArgumentKind::Type;
            if (std::any_of(
                    binding.arguments.begin(), binding.arguments.end(),
                    [&](const TemplateArgument& argument) {
                        return argument.kind != expected;
                    })) {
                return PackExpansionStatus::Failure;
            }
        }
        width = common.value_or(0);
        return PackExpansionStatus::Expanded;
    };

    std::function<cir::TypeId(cir::TypeId, uint32_t)> pack_parameter_type;
    pack_parameter_type = [&](cir::TypeId type,
                              uint32_t parameter_index) -> cir::TypeId {
        cir::TypeId resolved = file_.resolved_type(type);
        if (!file_.valid(resolved)) {
            return {};
        }
        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (file_.type(resolved).kind) {
            case cir::TypeKind::TypeParam: {
                const auto* parameter =
                    std::get_if<cir::TypeParamTypePayload>(&payload);
                return parameter && parameter->index == parameter_index
                    ? resolved
                    : cir::TypeId{};
            }
            case cir::TypeKind::Pointer:
                return pack_parameter_type(
                    std::get<cir::PointerTypePayload>(payload)
                        .pointee.type,
                    parameter_index);
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference:
                return pack_parameter_type(
                    std::get<cir::ReferenceTypePayload>(payload)
                        .referred_type.type,
                    parameter_index);
            case cir::TypeKind::Array:
                return pack_parameter_type(
                    std::get<cir::ArrayTypePayload>(payload)
                        .element_type.type,
                    parameter_index);
            case cir::TypeKind::MemberPointer: {
                const auto& member =
                    std::get<cir::MemberPointerTypePayload>(payload);
                cir::TypeId found = pack_parameter_type(
                    member.member_type.type, parameter_index);
                return found.valid()
                    ? found
                    : pack_parameter_type(member.class_type.type,
                                          parameter_index);
            }
            default:
                return {};
        }
    };

    auto callbacks_for_element = [&](
        const std::vector<cir::TemplateValuePackReference>& references,
        const TemplateArgumentBindings& bindings) {
        PatternInstantiationCallbacks projected = substitution_callbacks;
        projected.allow_parameter_pack_element_substitution = true;
        for (const cir::TemplateValuePackReference& reference : references) {
            if (reference.index >= bindings.size()) {
                continue;
            }
            const TemplateArgumentBinding& binding =
                bindings[reference.index];
            if (reference.kind == cir::TemplateValuePackKind::Type ||
                reference.kind == cir::TemplateValuePackKind::Function) {
                cir::TypeId parameter_type{};
                if (reference.parameter_type.valid()) {
                    parameter_type = pack_parameter_type(
                        reference.parameter_type, reference.index);
                }
                if (reference.declaration.valid() &&
                    file_.valid(reference.declaration) &&
                    !parameter_type.valid()) {
                    parameter_type = pack_parameter_type(
                        file_.entity(reference.declaration).type,
                        reference.index);
                }
                if (parameter_type.valid()) {
                    projected.exact_type_parameter_bindings[
                        static_cast<uint32_t>(parameter_type.index)] =
                        binding;
                }
            } else if (reference.kind ==
                           cir::TemplateValuePackKind::Value &&
                       reference.declaration.valid()) {
                projected.exact_value_parameter_bindings[
                    static_cast<uint32_t>(
                        reference.declaration.index)] = binding;
            } else if (reference.kind ==
                           cir::TemplateValuePackKind::Template &&
                       reference.declaration.valid()) {
                projected.exact_template_parameter_bindings[
                    static_cast<uint32_t>(
                        reference.declaration.index)] = binding;
            }
        }
        return projected;
    };

    auto project_bare_function_pack_operand = [&](
        cir::TemplateValueExprNode& node,
        const TemplateArgumentBindings& bindings,
        PatternInstantiationCallbacks& element_callbacks) {
        if (node.kind != cir::TemplateValueExprKind::TypeOperand ||
            node.lhs != cir::TemplateValueExprNoNode) {
            return true;
        }
        auto function_reference = std::find_if(
            node.pack_references.begin(),
            node.pack_references.end(),
            [](const cir::TemplateValuePackReference& reference) {
                return reference.kind ==
                    cir::TemplateValuePackKind::Function;
            });
        if (function_reference == node.pack_references.end()) {
            return true;
        }
        if (std::find_if(
                std::next(function_reference),
                node.pack_references.end(),
                [](const cir::TemplateValuePackReference& reference) {
                    return reference.kind ==
                        cir::TemplateValuePackKind::Function;
                }) != node.pack_references.end() ||
            !function_reference->declaration.valid() ||
            !file_.valid(function_reference->declaration)) {
            return false;
        }
        cir::TypeRef substituted = substitute_pattern_type_ref(
            file_.entity_type_ref(function_reference->declaration),
            bindings,
            element_callbacks);
        if (!substituted.valid()) {
            return false;
        }
        node.expands_parameter_pack = false;
        node.pack_references.clear();
        node.parameter_index = cir::TemplateValueExprNoParameter;
        node.type = substituted.type;
        node.result_type = {};
        node.entity = {};
        node.value = static_cast<int64_t>(ValueCategory::LValue);
        return true;
    };

    auto substitute_explicit_descriptor = [&](
        const cir::TemplateValueExprNode& pattern,
        const TemplateArgumentBindings& bindings,
        PatternInstantiationCallbacks& element_callbacks,
        cir::TemplateValueExpression& destination)
        -> std::optional<uint32_t> {
        if (pattern.value < static_cast<int64_t>(
                cir::TemplateArgumentKind::Type) ||
            pattern.value > static_cast<int64_t>(
                cir::TemplateArgumentKind::Template)) {
            return std::nullopt;
        }
        TemplateArgument argument;
        bool has_canonical_argument =
            pattern.template_arguments.size() == 1;
        if (has_canonical_argument) {
            argument = pattern.template_arguments.values().front();
        } else {
            argument.kind = static_cast<cir::TemplateArgumentKind>(
                pattern.value);
        }
        if (!has_canonical_argument &&
            argument.kind == cir::TemplateArgumentKind::Type) {
            argument.type = file_.type_ref(pattern.type);
        } else if (!has_canonical_argument &&
                   argument.kind ==
                       cir::TemplateArgumentKind::Value) {
            argument.value_type = pattern.result_type;
            argument.value_entity = pattern.entity;
            argument.dependent_value_qualifier = pattern.qualifier_type;
            argument.dependent_value_name = pattern.name;
            if (pattern.lhs != cir::TemplateValueExprNoNode) {
                std::optional<cir::TemplateValueExpression> value =
                    extract_expression(result.expression, pattern.lhs);
                if (!value.has_value()) {
                    return std::nullopt;
                }
                argument.dependent_value_expr = std::move(*value);
            }
            argument.is_dependent = true;
        } else if (!has_canonical_argument) {
            argument.template_entity = pattern.entity;
            argument.dependent_template_qualifier = pattern.qualifier_type;
            argument.template_name = pattern.name;
            argument.is_dependent = true;
        }

        std::string error;
        if (argument.kind == cir::TemplateArgumentKind::Type) {
            cir::TypeRef substituted = substitute_pattern_type_ref(
                argument.type, bindings, element_callbacks);
            if (!substituted.valid()) {
                return std::nullopt;
            }
            argument.type = substituted;
            argument.is_dependent = is_dependent_type(substituted.type);
        } else if (argument.kind == cir::TemplateArgumentKind::Value) {
            if (!substitute_template_value_argument(
                    argument, bindings, element_callbacks, &error)) {
                return std::nullopt;
            }
        } else if (!substitute_template_template_argument(
                       argument, bindings, element_callbacks, &error)) {
            return std::nullopt;
        }

        argument.expands_parameter_pack = false;
        argument.expands_pack_pattern = false;

        cir::TemplateValueExprNode descriptor = pattern;
        descriptor.expands_parameter_pack = false;
        descriptor.pack_references.clear();
        descriptor.parameter_index = cir::TemplateValueExprNoParameter;
        descriptor.rhs = cir::TemplateValueExprNoNode;
        descriptor.lhs = cir::TemplateValueExprNoNode;
        descriptor.template_arguments =
            cir::TemplateArgumentList({argument});
        if (argument.kind == cir::TemplateArgumentKind::Type) {
            descriptor.type = argument.type.type;
        } else if (argument.kind == cir::TemplateArgumentKind::Value) {
            descriptor.result_type = argument.value_type;
            descriptor.entity = argument.value_entity;
            descriptor.name = argument.dependent_value_name;
            descriptor.qualifier_type =
                argument.dependent_value_qualifier;
            if (argument.dependent_value_expr.valid()) {
                descriptor.lhs = append_expression(
                    destination, argument.dependent_value_expr);
            } else if (argument.value_kind ==
                           cir::TemplateValueKind::Integer ||
                       argument.value_kind ==
                           cir::TemplateValueKind::Boolean) {
                cir::TemplateValueExprNode literal =
                    file_.template_integer_expression_node(
                        argument.integer_value, argument.value_type);
                destination.nodes.push_back(std::move(literal));
                descriptor.lhs = static_cast<uint32_t>(
                    destination.nodes.size() - 1);
            }
        } else {
            descriptor.entity = argument.template_entity;
            descriptor.name = argument.template_name;
            descriptor.qualifier_type =
                argument.dependent_template_qualifier;
        }
        destination.nodes.push_back(std::move(descriptor));
        return static_cast<uint32_t>(destination.nodes.size() - 1);
    };

    bool has_pack_expansion = std::any_of(
        result.expression.nodes.begin(), result.expression.nodes.end(),
        [](const cir::TemplateValueExprNode& node) {
            return node.expands_parameter_pack ||
                !node.pack_references.empty();
        });
    std::unordered_set<uint32_t> projected_nodes;
    if (has_pack_expansion) {
        cir::TemplateValueExpression expanded = result.expression;
        const size_t original_node_count = expanded.nodes.size();
        for (size_t call_index = 0; call_index < original_node_count;
             ++call_index) {
            if (expanded.nodes[call_index].kind !=
                cir::TemplateValueExprKind::Call) {
                continue;
            }
            auto expand_chain = [&](uint32_t head, bool explicit_chain,
                                    uint32_t& expanded_head)
                -> PackExpansionStatus {
                std::vector<uint32_t> source_nodes;
                std::unordered_set<uint32_t> seen;
                for (uint32_t current = head;
                     current != cir::TemplateValueExprNoNode;) {
                    if (current >= original_node_count ||
                        !seen.insert(current).second ||
                        expanded.nodes[current].kind !=
                            cir::TemplateValueExprKind::TypeOperand) {
                        return PackExpansionStatus::Failure;
                    }
                    source_nodes.push_back(current);
                    current = expanded.nodes[current].rhs;
                }

                std::vector<uint32_t> destination_nodes;
                for (uint32_t source_index : source_nodes) {
                    cir::TemplateValueExprNode source =
                        expanded.nodes[source_index];
                    if (source.pack_references.empty()) {
                        destination_nodes.push_back(source_index);
                        continue;
                    }
                    size_t width = 0;
                    PackExpansionStatus width_status = expansion_width(
                        source.pack_references, width);
                    if (width_status != PackExpansionStatus::Expanded) {
                        return width_status;
                    }
                    for (size_t element = 0; element < width; ++element) {
                        TemplateArgumentBindings projected;
                        PackExpansionStatus binding_status = element_bindings(
                            source.pack_references, element, projected,
                            nullptr);
                        if (binding_status != PackExpansionStatus::Expanded) {
                            return binding_status;
                        }
                        PatternInstantiationCallbacks element_callbacks =
                            callbacks_for_element(source.pack_references,
                                                  projected);
                        if (explicit_chain) {
                            std::optional<uint32_t> descriptor =
                                substitute_explicit_descriptor(
                                    source, projected, element_callbacks,
                                    expanded);
                            if (!descriptor.has_value()) {
                                return PackExpansionStatus::Failure;
                            }
                            destination_nodes.push_back(*descriptor);
                            continue;
                        }

                        if (source.lhs ==
                                cir::TemplateValueExprNoNode &&
                            std::any_of(
                                source.pack_references.begin(),
                                source.pack_references.end(),
                                [](const cir::TemplateValuePackReference&
                                       reference) {
                                    return reference.kind ==
                                        cir::TemplateValuePackKind::Function;
                                })) {
                            cir::TemplateValueExprNode descriptor = source;
                            descriptor.lhs = cir::TemplateValueExprNoNode;
                            descriptor.rhs = cir::TemplateValueExprNoNode;
                            if (!project_bare_function_pack_operand(
                                    descriptor,
                                    projected,
                                    element_callbacks)) {
                                return PackExpansionStatus::Failure;
                            }
                            expanded.nodes.push_back(std::move(descriptor));
                            destination_nodes.push_back(
                                static_cast<uint32_t>(
                                    expanded.nodes.size() - 1));
                            continue;
                        }

                        std::optional<cir::TemplateValueExpression> pattern =
                            extract_expression(expanded, source.lhs);
                        if (!pattern.has_value()) {
                            return PackExpansionStatus::Failure;
                        }
                        TemplateArgument recipe;
                        recipe.kind = cir::TemplateArgumentKind::Value;
                        recipe.dependent_value_expr = std::move(*pattern);
                        recipe.is_dependent = true;
                        auto source_function_reference = std::find_if(
                            source.pack_references.begin(),
                            source.pack_references.end(),
                            [](const cir::TemplateValuePackReference&
                                   reference) {
                                return reference.kind ==
                                    cir::TemplateValuePackKind::Function;
                            });
                        cir::TypeId function_pack_placeholder =
                            file_.dependent_type(
                                "function parameter pack expansion");
                        for (cir::TemplateValueExprNode& node :
                             recipe.dependent_value_expr.nodes) {
                            if (source_function_reference !=
                                    source.pack_references.end() &&
                                node.kind ==
                                    cir::TemplateValueExprKind::TypeOperand &&
                                node.lhs == cir::TemplateValueExprNoNode &&
                                node.pack_references.empty() &&
                                file_.resolved_type(node.type) ==
                                    file_.resolved_type(
                                        function_pack_placeholder)) {

                                node.pack_references.push_back(
                                    *source_function_reference);
                            }
                            if (!project_bare_function_pack_operand(
                                    node,
                                    projected,
                                    element_callbacks)) {
                                return PackExpansionStatus::Failure;
                            }
                        }
                        std::string error;
                        if (!substitute_template_value_argument(
                                recipe, projected, element_callbacks,
                                &error) ||
                            !recipe.dependent_value_expr.valid()) {
                            return PackExpansionStatus::Failure;
                        }
                        uint32_t pattern_root = append_expression(
                            expanded, recipe.dependent_value_expr);
                        cir::TemplateValueExprNode descriptor = source;
                        descriptor.lhs = pattern_root;
                        descriptor.rhs = cir::TemplateValueExprNoNode;
                        descriptor.expands_parameter_pack = false;
                        descriptor.pack_references.clear();
                        descriptor.parameter_index =
                            cir::TemplateValueExprNoParameter;
                        expanded.nodes.push_back(std::move(descriptor));
                        destination_nodes.push_back(static_cast<uint32_t>(
                            expanded.nodes.size() - 1));
                    }
                }
                for (size_t index = 0; index < destination_nodes.size();
                     ++index) {
                    expanded.nodes[destination_nodes[index]].rhs =
                        index + 1 < destination_nodes.size()
                            ? destination_nodes[index + 1]
                            : cir::TemplateValueExprNoNode;
                }
                expanded_head = destination_nodes.empty()
                    ? cir::TemplateValueExprNoNode
                    : destination_nodes.front();
                return PackExpansionStatus::Expanded;
            };

            uint32_t ordinary_head = cir::TemplateValueExprNoNode;
            PackExpansionStatus ordinary_status = expand_chain(
                expanded.nodes[call_index].lhs,
                /*explicit_chain=*/false, ordinary_head);
            if (ordinary_status == PackExpansionStatus::StillDependent) {
                file_.canonicalize_template_value_expression(
                    result.expression);
                result.status =
                    UnevaluatedCallResolutionStatus::StillDependent;
                transaction.commit();
                return result;
            }
            if (ordinary_status == PackExpansionStatus::Failure) {
                result.status =
                    UnevaluatedCallResolutionStatus::SubstitutionFailure;
                return result;
            }
            uint32_t explicit_head = cir::TemplateValueExprNoNode;
            PackExpansionStatus explicit_status = expand_chain(
                expanded.nodes[call_index].rhs,
                /*explicit_chain=*/true, explicit_head);
            if (explicit_status == PackExpansionStatus::StillDependent) {
                file_.canonicalize_template_value_expression(
                    result.expression);
                result.status =
                    UnevaluatedCallResolutionStatus::StillDependent;
                transaction.commit();
                return result;
            }
            if (explicit_status == PackExpansionStatus::Failure) {
                result.status =
                    UnevaluatedCallResolutionStatus::SubstitutionFailure;
                return result;
            }
            expanded.nodes[call_index].lhs = ordinary_head;
            expanded.nodes[call_index].rhs = explicit_head;

            uint32_t target_index = expanded.nodes[call_index].third;
            if (target_index < expanded.nodes.size() &&
                expanded.nodes[target_index].kind ==
                    cir::TemplateValueExprKind::Callee) {
                std::vector<uint32_t> candidate_nodes =
                    expanded.nodes[target_index].operands;
                for (uint32_t candidate_index : candidate_nodes) {
                    if (candidate_index >= expanded.nodes.size() ||
                        expanded.nodes[candidate_index].kind !=
                            cir::TemplateValueExprKind::TypeOperand) {
                        result.status =
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure;
                        return result;
                    }
                    uint32_t candidate_head =
                        cir::TemplateValueExprNoNode;
                    PackExpansionStatus candidate_status =
                        expand_chain(
                            expanded.nodes[candidate_index].lhs,
                            /*explicit_chain=*/true,
                            candidate_head);
                    if (candidate_status ==
                        PackExpansionStatus::StillDependent) {
                        file_.canonicalize_template_value_expression(
                            result.expression);
                        result.status =
                            UnevaluatedCallResolutionStatus::
                                StillDependent;
                        transaction.commit();
                        return result;
                    }
                    if (candidate_status ==
                        PackExpansionStatus::Failure) {
                        result.status =
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure;
                        return result;
                    }
                    expanded.nodes[candidate_index].lhs =
                        candidate_head;
                }
            }
        }

        std::unordered_map<uint32_t, uint32_t> compact_mapping;
        std::optional<cir::TemplateValueExpression> compact =
            extract_expression(expanded,
                               expanded.root,
                               &compact_mapping);
        if (!compact.has_value()) {
            result.status =
                UnevaluatedCallResolutionStatus::SubstitutionFailure;
            return result;
        }
        for (const auto& [source_index, compact_index] : compact_mapping) {
            if (source_index >= original_node_count) {
                projected_nodes.insert(compact_index);
            }
        }
        result.expression = std::move(*compact);
    }

    TemplateArgument recipe;
    recipe.kind = cir::TemplateArgumentKind::Value;
    recipe.dependent_value_expr = result.expression;
    recipe.is_dependent = true;
    std::string substitution_error;
    if (!substitute_template_value_argument(
            recipe,
            argument_bindings,
            substitution_callbacks,
            &substitution_error,
            projected_nodes.empty() ? nullptr : &projected_nodes) ||
        !recipe.dependent_value_expr.valid()) {
        result.status = UnevaluatedCallResolutionStatus::SubstitutionFailure;
        return result;
    }
    result.expression = std::move(recipe.dependent_value_expr);
    result.expression.canonical_id = {};

    for (const cir::TemplateValueExprNode& node : result.expression.nodes) {
        if (node.expands_parameter_pack ||
            !node.pack_references.empty()) {
            file_.canonicalize_template_value_expression(result.expression);
            result.status =
                UnevaluatedCallResolutionStatus::StillDependent;
            transaction.commit();
            return result;
        }
    }

    struct NodeResolution {
        UnevaluatedCallResolutionStatus status =
            UnevaluatedCallResolutionStatus::StillDependent;
        cir::TypeRef expression_type;
        ValueCategory category = ValueCategory::Dependent;
        cir::TypeRef decltype_type;
        bool bound_member_function = false;
        cir::TypeRef bound_member_object;
        ValueCategory bound_member_object_category = ValueCategory::Invalid;
        uint8_t bound_member_object_qualifiers = cir::QualNone;
        cir::TypeId bound_member_class{};
        bool exception_state_known = true;
        bool potentially_throwing = false;
    };

    auto dependent_type = [&](cir::TypeId type) {
        return type.valid() && is_dependent_type(type);
    };
    auto category_from_recipe = [](int64_t encoded) {
        if (encoded >= static_cast<int64_t>(ValueCategory::Invalid) &&
            encoded <= static_cast<int64_t>(ValueCategory::Dependent)) {
            return static_cast<ValueCategory>(encoded);
        }
        return ValueCategory::Dependent;
    };
    auto subexpression = [&](uint32_t root) {
        cir::TemplateValueExpression nested = result.expression;
        nested.root = root;
        nested.canonical_id = {};
        return nested;
    };

    bool hard_error = false;
    bool unresolved_template_candidate = false;
    SrcLoc loc = result.expression.loc;

    auto append_unique = [](std::vector<cir::EntityId>& entities,
                            cir::EntityId entity) {
        if (entity.valid() &&
            std::find(entities.begin(), entities.end(), entity) ==
                entities.end()) {
            entities.push_back(entity);
        }
    };

    auto expand_candidates =
        [&](const std::vector<cir::EntityId>& candidates,
            const std::vector<ExprResult>& arguments,
            bool has_explicit_arguments,
            const std::vector<TemplateArgument>& explicit_arguments,
            const std::vector<CandidateExplicitTemplateArguments>&
                candidate_explicit_arguments) {
            std::vector<cir::EntityId> expanded;
            for (cir::EntityId candidate : candidates) {
                if (!candidate.valid() || !file_.valid(candidate)) {
                    continue;
                }
                const TemplateInfo* info = template_info(candidate);
                if (!info) {
                    append_unique(expanded, candidate);
                    continue;
                }
                if (info->is_class_template || info->is_alias_template ||
                    info->is_variable_template || info->is_concept) {
                    continue;
                }
                if (!has_function_template_instantiation_callback()) {
                    unresolved_template_candidate = true;
                    continue;
                }
                std::vector<TemplateArgument> deduced;
                const std::vector<TemplateArgument>* written =
                    has_explicit_arguments ? &explicit_arguments
                                           : nullptr;
                auto candidate_arguments = std::find_if(
                    candidate_explicit_arguments.begin(),
                    candidate_explicit_arguments.end(),
                    [&](const CandidateExplicitTemplateArguments& entry) {
                        return entry.template_entity == candidate;
                    });
                if (candidate_arguments !=
                    candidate_explicit_arguments.end()) {
                    if (!candidate_arguments->viable) {
                        continue;
                    }
                    written = &candidate_arguments->arguments;
                }
                TemplateArgumentBindings deduced_bindings;
                if (!deduce_template_arguments(*info,
                                               arguments,
                                               deduced,
                                               written,
                                               &substitution_callbacks,
                                               &deduced_bindings,
                                               loc)) {
                    continue;
                }
                size_t error_watermark = file_.errors().size();
                cir::EntityId specialization =
                    form_function_template_specialization_candidate(
                        *info, deduced_bindings, loc);
                if (file_.errors().size() != error_watermark) {
                    hard_error = true;
                    break;
                }
                append_unique(expanded, specialization);
            }
            return expanded;
        };

    std::vector<uint8_t> visiting(result.expression.nodes.size(), 0);
    std::function<NodeResolution(uint32_t, size_t)> resolve_node;
    resolve_node = [&](uint32_t index, size_t depth) -> NodeResolution {
        if (depth > 128 || index >= result.expression.nodes.size() ||
            visiting[index] != 0) {
            return {UnevaluatedCallResolutionStatus::SubstitutionFailure};
        }
        visiting[index] = 1;
        auto finish = [&](NodeResolution resolution) {
            visiting[index] = 0;
            return resolution;
        };

        cir::TemplateValueExprNode& node = result.expression.nodes[index];
        if (node.kind == cir::TemplateValueExprKind::Integer) {
            cir::TypeRef type = node.result_type.type.valid()
                ? node.result_type
                : file_.type_ref(
                      file_.builtin_type(cir::BuiltinTypeKind::Int));
            return finish({UnevaluatedCallResolutionStatus::Resolved,
                           type,
                           ValueCategory::PrValue,
                           type});
        }
        if (node.kind == cir::TemplateValueExprKind::Noexcept &&
            node.lhs != cir::TemplateValueExprNoNode) {
            NodeResolution operand = resolve_node(node.lhs, depth + 1);
            if (operand.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(operand));
            }
            if (!operand.exception_state_known) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }
            cir::TypeRef bool_type = file_.type_ref(
                file_.builtin_type(cir::BuiltinTypeKind::Bool));
            cir::TemplateValueExprNode folded =
                file_.template_integer_expression_node(
                    cir::IntegerValue::from_unsigned(
                        operand.potentially_throwing ? 0 : 1, 1),
                    bool_type);
            node = std::move(folded);
            return finish({UnevaluatedCallResolutionStatus::Resolved,
                           bool_type,
                           ValueCategory::PrValue,
                           bool_type});
        }
        if (node.kind == cir::TemplateValueExprKind::Conditional &&
            node.lhs != cir::TemplateValueExprNoNode &&
            node.rhs != cir::TemplateValueExprNoNode &&
            node.third != cir::TemplateValueExprNoNode) {
            NodeResolution condition = resolve_node(node.lhs, depth + 1);
            NodeResolution true_operand = resolve_node(node.rhs, depth + 1);
            NodeResolution false_operand =
                resolve_node(node.third, depth + 1);

            auto terminal_failure = [](const NodeResolution& resolution) {
                return resolution.status ==
                           UnevaluatedCallResolutionStatus::SubstitutionFailure ||
                    resolution.status ==
                           UnevaluatedCallResolutionStatus::HardError;
            };
            if (terminal_failure(condition)) {
                return finish(std::move(condition));
            }
            if (terminal_failure(true_operand)) {
                return finish(std::move(true_operand));
            }
            if (terminal_failure(false_operand)) {
                return finish(std::move(false_operand));
            }
            if (condition.status !=
                    UnevaluatedCallResolutionStatus::Resolved ||
                true_operand.status !=
                    UnevaluatedCallResolutionStatus::Resolved ||
                false_operand.status !=
                    UnevaluatedCallResolutionStatus::Resolved) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }

            ExprResult condition_view;
            condition_view.type = condition.expression_type.type;
            condition_view.category = condition.category;
            condition_view.semantic_object_qualifiers =
                condition.expression_type.qualifiers;
            if (conversion_rank(
                    condition_view,
                    file_.type_ref(file_.builtin_type(
                        cir::BuiltinTypeKind::Bool)),
                    condition.expression_type.qualifiers,
                    nullptr,
                    /*allow_user_defined=*/true) == ConversionRank::Bad) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }

            auto make_result = [&](cir::TypeRef expression_type,
                                   ValueCategory category) {
                NodeResolution resolution;
                resolution.status =
                    UnevaluatedCallResolutionStatus::Resolved;
                resolution.expression_type = expression_type;
                resolution.category = category;
                if (category == ValueCategory::LValue ||
                    category == ValueCategory::XValue) {
                    cir::ReferenceKind reference_kind =
                        category == ValueCategory::LValue
                            ? cir::ReferenceKind::LValue
                            : cir::ReferenceKind::RValue;
                    resolution.decltype_type = file_.type_ref(
                        reference_type(expression_type, reference_kind));
                } else {
                    resolution.decltype_type = expression_type;
                }
                resolution.exception_state_known =
                    condition.exception_state_known &&
                    true_operand.exception_state_known &&
                    false_operand.exception_state_known;
                resolution.potentially_throwing =
                    condition.potentially_throwing ||
                    true_operand.potentially_throwing ||
                    false_operand.potentially_throwing;
                node.result_type = expression_type;
                node.value = static_cast<int64_t>(category);
                return resolution;
            };

            cir::TypeId true_type =
                file_.resolved_type(true_operand.expression_type.type);
            cir::TypeId false_type =
                file_.resolved_type(false_operand.expression_type.type);
            if (!file_.valid(true_type) || !file_.valid(false_type)) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }

            bool same_glvalue_category =
                true_operand.category == false_operand.category &&
                (true_operand.category == ValueCategory::LValue ||
                 true_operand.category == ValueCategory::XValue);
            if (same_glvalue_category && true_type == false_type &&
                true_operand.expression_type.memory_space ==
                    false_operand.expression_type.memory_space) {
                cir::TypeRef common = true_operand.expression_type;
                common.qualifiers = static_cast<uint8_t>(
                    common.qualifiers |
                    false_operand.expression_type.qualifiers);
                return finish(make_result(common, true_operand.category));
            }

            if (is_void_type(true_type) || is_void_type(false_type)) {
                if (!is_void_type(true_type) || !is_void_type(false_type)) {

                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                return finish(make_result(
                    file_.type_ref(file_.builtin_type(
                        cir::BuiltinTypeKind::Void)),
                    ValueCategory::PrValue));
            }

            bool either_class =
                file_.type(true_type).kind == cir::TypeKind::Record ||
                file_.type(false_type).kind == cir::TypeKind::Record;
            if (either_class) {
                ExprResult true_view;
                true_view.type = true_operand.expression_type.type;
                true_view.category = true_operand.category;
                true_view.semantic_object_qualifiers =
                    true_operand.expression_type.qualifiers;
                ExprResult false_view;
                false_view.type = false_operand.expression_type.type;
                false_view.category = false_operand.category;
                false_view.semantic_object_qualifiers =
                    false_operand.expression_type.qualifiers;
                if (same_glvalue_category) {
                    cir::ReferenceKind reference_kind =
                        true_operand.category == ValueCategory::LValue
                            ? cir::ReferenceKind::LValue
                            : cir::ReferenceKind::RValue;
                    cir::TypeRef false_reference = file_.type_ref(
                        reference_type(false_operand.expression_type,
                                       reference_kind));
                    cir::TypeRef true_reference = file_.type_ref(
                        reference_type(true_operand.expression_type,
                                       reference_kind));
                    bool true_to_false_reference = conversion_rank(
                        true_view,
                        false_reference,
                        true_operand.expression_type.qualifiers,
                        nullptr,
                        /*allow_user_defined=*/false) != ConversionRank::Bad;
                    bool false_to_true_reference = conversion_rank(
                        false_view,
                        true_reference,
                        false_operand.expression_type.qualifiers,
                        nullptr,
                        /*allow_user_defined=*/false) != ConversionRank::Bad;
                    if (true_to_false_reference &&
                        false_to_true_reference) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    if (true_to_false_reference) {
                        return finish(make_result(
                            false_operand.expression_type,
                            false_operand.category));
                    }
                    if (false_to_true_reference) {
                        return finish(make_result(
                            true_operand.expression_type,
                            true_operand.category));
                    }
                }
                bool true_to_false = conversion_rank(
                    true_view,
                    false_operand.expression_type,
                    true_operand.expression_type.qualifiers,
                    nullptr,
                    /*allow_user_defined=*/true) != ConversionRank::Bad;
                bool false_to_true = conversion_rank(
                    false_view,
                    true_operand.expression_type,
                    false_operand.expression_type.qualifiers,
                    nullptr,
                    /*allow_user_defined=*/true) != ConversionRank::Bad;
                if (true_to_false && false_to_true) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                if (true_to_false) {
                    true_operand.expression_type =
                        false_operand.expression_type;
                    true_operand.category = ValueCategory::PrValue;
                    false_operand.category = ValueCategory::PrValue;
                    true_type = false_type;
                } else if (false_to_true) {
                    false_operand.expression_type =
                        true_operand.expression_type;
                    false_operand.category = ValueCategory::PrValue;
                    true_operand.category = ValueCategory::PrValue;
                    false_type = true_type;
                }
                same_glvalue_category =
                    true_operand.category == false_operand.category &&
                    (true_operand.category == ValueCategory::LValue ||
                     true_operand.category == ValueCategory::XValue);
                if (same_glvalue_category && true_type == false_type) {
                    cir::TypeRef common = true_operand.expression_type;
                    common.qualifiers = static_cast<uint8_t>(
                        common.qualifiers |
                        false_operand.expression_type.qualifiers);
                    return finish(
                        make_result(common, true_operand.category));
                }
            }

            auto adjusted_prvalue_type = [&](const NodeResolution& operand) {
                cir::TypeRef adjusted = operand.expression_type;
                cir::TypeId resolved = file_.resolved_type(adjusted.type);
                if (file_.valid(resolved) &&
                    file_.type(resolved).kind == cir::TypeKind::Array) {
                    return file_.type_ref(
                        pointer_type(file_.array_element_ref(resolved)));
                }
                if (file_.valid(resolved) &&
                    file_.type(resolved).kind == cir::TypeKind::Function) {
                    return file_.type_ref(pointer_type(
                        file_.type_ref(resolved)));
                }
                adjusted.type = resolved;
                if (file_.valid(resolved) &&
                    file_.type(resolved).kind != cir::TypeKind::Record) {
                    adjusted.qualifiers = cir::QualNone;
                }
                return adjusted;
            };
            cir::TypeRef true_adjusted =
                adjusted_prvalue_type(true_operand);
            cir::TypeRef false_adjusted =
                adjusted_prvalue_type(false_operand);
            true_type = file_.resolved_type(true_adjusted.type);
            false_type = file_.resolved_type(false_adjusted.type);

            if (true_type == false_type &&
                true_adjusted.memory_space == false_adjusted.memory_space) {
                cir::TypeRef common = true_adjusted;
                common.qualifiers = static_cast<uint8_t>(
                    common.qualifiers | false_adjusted.qualifiers);
                return finish(
                    make_result(common, ValueCategory::PrValue));
            }
            if (is_arithmetic_type(true_type) &&
                is_arithmetic_type(false_type)) {
                cir::TypeId common = usual_arithmetic_conversion_type(
                    true_type, false_type);
                if (!common.valid()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                return finish(make_result(
                    file_.type_ref(common), ValueCategory::PrValue));
            }

            auto ordinary_pointer_pointee = [&](cir::TypeId pointer)
                -> cir::TypeRef {
                pointer = file_.resolved_type(pointer);
                return file_.valid(pointer) &&
                        file_.type(pointer).kind == cir::TypeKind::Pointer
                    ? file_.pointer_pointee_ref(pointer)
                    : cir::TypeRef{};
            };
            auto is_void_ref = [&](cir::TypeRef ref) {
                cir::TypeId resolved = file_.resolved_type(ref.type);
                return file_.valid(resolved) &&
                    file_.type(resolved).kind == cir::TypeKind::Builtin &&
                    std::get<cir::BuiltinTypePayload>(
                        file_.type_payload(resolved)).kind ==
                        cir::BuiltinTypeKind::Void;
            };
            cir::TypeRef true_pointee =
                ordinary_pointer_pointee(true_type);
            cir::TypeRef false_pointee =
                ordinary_pointer_pointee(false_type);
            if (true_pointee.valid() && false_pointee.valid()) {
                cir::TypeId true_pointee_type =
                    file_.resolved_type(true_pointee.type);
                cir::TypeId false_pointee_type =
                    file_.resolved_type(false_pointee.type);
                cir::TypeRef common;
                if (true_pointee_type == false_pointee_type) {
                    common = true_pointee;
                } else if (is_void_ref(true_pointee)) {
                    common = true_pointee;
                } else if (is_void_ref(false_pointee)) {
                    common = false_pointee;
                } else if (file_.type(true_pointee_type).kind ==
                               cir::TypeKind::Record &&
                           file_.type(false_pointee_type).kind ==
                               cir::TypeKind::Record &&
                           derived_to_base_path(
                               true_pointee_type,
                               false_pointee_type,
                               nullptr)) {
                    common = false_pointee;
                } else if (file_.type(true_pointee_type).kind ==
                               cir::TypeKind::Record &&
                           file_.type(false_pointee_type).kind ==
                               cir::TypeKind::Record &&
                           derived_to_base_path(
                               false_pointee_type,
                               true_pointee_type,
                               nullptr)) {
                    common = true_pointee;
                }
                if (common.valid()) {
                    common.qualifiers = static_cast<uint8_t>(
                        true_pointee.qualifiers |
                        false_pointee.qualifiers);
                    return finish(make_result(
                        file_.type_ref(pointer_type(common)),
                        ValueCategory::PrValue));
                }
            }

            bool true_pointer_like = true_pointee.valid() ||
                file_.type(true_type).kind == cir::TypeKind::MemberPointer;
            bool false_pointer_like = false_pointee.valid() ||
                file_.type(false_type).kind == cir::TypeKind::MemberPointer;
            if ((true_pointer_like &&
                 (false_pointer_like || is_nullptr_type(false_type))) ||
                (false_pointer_like && is_nullptr_type(true_type))) {
                ExprResult true_view;
                true_view.type = true_adjusted.type;
                true_view.category = ValueCategory::PrValue;
                true_view.semantic_object_qualifiers =
                    true_adjusted.qualifiers;
                ExprResult false_view;
                false_view.type = false_adjusted.type;
                false_view.category = ValueCategory::PrValue;
                false_view.semantic_object_qualifiers =
                    false_adjusted.qualifiers;
                bool true_to_false = conversion_rank(
                    true_view,
                    false_adjusted,
                    true_adjusted.qualifiers,
                    nullptr,
                    /*allow_user_defined=*/false) != ConversionRank::Bad;
                bool false_to_true = conversion_rank(
                    false_view,
                    true_adjusted,
                    false_adjusted.qualifiers,
                    nullptr,
                    /*allow_user_defined=*/false) != ConversionRank::Bad;
                if (true_to_false != false_to_true) {
                    return finish(make_result(
                        true_to_false ? false_adjusted : true_adjusted,
                        ValueCategory::PrValue));
                }
            }

            return finish({
                UnevaluatedCallResolutionStatus::SubstitutionFailure});
        }
        if (node.kind == cir::TemplateValueExprKind::TypeOperand) {
            cir::TemplateCalleeFlag operand_flags =
                static_cast<cir::TemplateCalleeFlag>(node.value);
            bool member_access =
                (static_cast<uint32_t>(operand_flags) &
                 static_cast<uint32_t>(
                     cir::TemplateCalleeFlag::MemberAccess)) != 0;
            if (member_access) {
                if (node.lhs == cir::TemplateValueExprNoNode ||
                    !node.name.valid() || !file_.valid(node.name)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                NodeResolution base = resolve_node(node.lhs, depth + 1);
                if (base.status !=
                    UnevaluatedCallResolutionStatus::Resolved) {
                    return finish(std::move(base));
                }

                cir::TypeRef object_ref = base.expression_type;
                ValueCategory object_category = base.category;
                bool member_arrow =
                    (static_cast<uint32_t>(operand_flags) &
                     static_cast<uint32_t>(
                         cir::TemplateCalleeFlag::MemberArrow)) != 0;
                if (member_arrow) {
                    cir::TypeId pointer =
                        file_.resolved_type(object_ref.type);
                    if (!file_.valid(pointer) ||
                        file_.type(pointer).kind !=
                            cir::TypeKind::Pointer) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    object_ref = file_.pointer_pointee_ref(pointer);
                    object_category = ValueCategory::LValue;
                }

                cir::TypeId object_type =
                    file_.resolved_type(object_ref.type);
                if (!file_.valid(object_type) ||
                    file_.type(object_type).kind !=
                        cir::TypeKind::Record) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                if (!require_complete_class_type(
                        object_type,
                        loc,
                        cir::InstantiationDemandKind::BaseMemberList)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::HardError});
                }

                cir::TypeId lookup_type = object_type;
                if (node.qualifier_type.type.valid()) {
                    cir::TypeId qualifier = file_.resolved_type(
                        node.qualifier_type.type);
                    if (!file_.valid(qualifier) ||
                        dependent_type(qualifier)) {
                        return finish({
                            UnevaluatedCallResolutionStatus::StillDependent});
                    }
                    if (file_.type(qualifier).kind !=
                            cir::TypeKind::Record ||
                        (qualifier != object_type &&
                         analyze_derived_to_base_path(
                             object_type, qualifier).kind !=
                             DerivedToBasePathKind::Unique)) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    lookup_type = qualifier;
                }

                MemberLookupResult lookup = lookup_member_name(
                    lookup_type, file_.name(node.name));
                if (lookup.has_dependent_bases) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                if (lookup.ambiguous || !lookup.found_name ||
                    lookup.declarations.size() != 1) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                const MemberLookupDeclaration& declaration =
                    lookup.declarations.front();
                if (!declaration.entity.valid() ||
                    !file_.valid(declaration.entity)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }

                AccessContext access_context =
                    callbacks.has_explicit_access_context
                    ? AccessContext{{}, callbacks.access_record,
                                    callbacks.access_function, {}, true}
                    : current_access_context();
                if (!callbacks.has_explicit_access_context &&
                    result.expression.definition_context.valid()) {
                    cir::EntityId definition_record =
                        enclosing_record_for_context(
                            result.expression.definition_context);
                    if (definition_record.valid()) {
                        access_context.declaring_entity = definition_record;
                        access_context.accessing_record = definition_record;
                        access_context.lexical_context =
                            result.expression.definition_context;
                        access_context.exact = true;
                    }
                }

                cir::EntityId object_record =
                    file_.record_entity(object_type);
                const cir::TemplateSpecializationFact* object_specialization =
                    object_record.valid()
                    ? file_.template_specialization(object_record)
                    : nullptr;
                if (object_specialization &&
                    object_specialization->template_entity ==
                        access_context.accessing_record) {
                    access_context.declaring_entity = object_record;
                    access_context.accessing_record = object_record;
                }
                bool member_access_ok = true;
                if (declaration.has_declared_access) {
                    AccessObligation obligation;
                    obligation.kind = AccessObligationKind::Member;
                    obligation.member = declaration.entity;
                    obligation.access_owner = declaration.access_owner;
                    obligation.declared_access =
                        declaration.declared_access;
                    obligation.declaring_class =
                        declaration.declaring_class;
                    obligation.designating_class = object_type;
                    obligation.captured_context = access_context;
                    obligation.fixed_context = true;
                    obligation.loc = loc;
                    member_access_ok = capture_access_obligation(obligation) ||
                        evaluate_access_obligation(obligation,
                                                   access_context);
                }
                bool base_access_ok = member_access_ok &&
                    declaration.found_through_using;
                if (member_access_ok && !base_access_ok) {
                    AccessObligation obligation;
                    obligation.kind =
                        AccessObligationKind::MemberLookupBase;
                    obligation.declaring_class =
                        declaration.declaring_class;
                    obligation.derived_type = object_type;
                    obligation.base_routes = declaration.base_paths;
                    obligation.captured_context = access_context;
                    obligation.fixed_context = true;
                    obligation.loc = loc;
                    base_access_ok = capture_access_obligation(obligation) ||
                        evaluate_access_obligation(obligation,
                                                   access_context);
                }
                if (!member_access_ok || !base_access_ok) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }

                const cir::Entity& member_entity =
                    file_.entity(declaration.entity);
                cir::TypeRef member_type =
                    type_ref_for_declared_entity(
                        file_, declaration.entity);
                ValueCategory member_category = ValueCategory::Invalid;
                if (member_entity.kind == cir::EntityKind::Field) {
                    if (!member_type.valid()) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    cir::TypeId resolved_member =
                        file_.resolved_type(member_type.type);
                    if (file_.valid(resolved_member) &&
                        (file_.type(resolved_member).kind ==
                             cir::TypeKind::LValueReference ||
                         file_.type(resolved_member).kind ==
                             cir::TypeKind::RValueReference)) {
                        member_type =
                            file_.reference_referred_ref(resolved_member);
                        member_category = ValueCategory::LValue;
                    } else {
                        const cir::RecordFieldFact* field =
                            file_.field_fact(declaration.entity);
                        uint8_t object_qualifiers = object_ref.qualifiers;
                        if (field && field->is_mutable) {
                            object_qualifiers = static_cast<uint8_t>(
                                object_qualifiers &
                                static_cast<uint8_t>(~cir::QualConst));
                        }
                        member_type.qualifiers = static_cast<uint8_t>(
                            member_type.qualifiers | object_qualifiers);
                        member_category =
                            object_category == ValueCategory::LValue
                                ? ValueCategory::LValue
                                : ValueCategory::XValue;
                    }
                } else if (member_entity.kind ==
                               cir::EntityKind::Variable) {
                    member_category = ValueCategory::LValue;
                } else if (member_entity.kind ==
                               cir::EntityKind::Enumerator) {
                    member_category = ValueCategory::PrValue;
                } else {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }

                cir::TypeRef decltype_type = member_type;
                if (member_category == ValueCategory::LValue ||
                    member_category == ValueCategory::XValue) {
                    decltype_type = file_.type_ref(reference_type(
                        member_type,
                        member_category == ValueCategory::LValue
                            ? cir::ReferenceKind::LValue
                            : cir::ReferenceKind::RValue));
                }
                node.result_type = member_type;
                NodeResolution member{
                    UnevaluatedCallResolutionStatus::Resolved,
                    member_type,
                    member_category,
                    decltype_type};
                member.exception_state_known =
                    base.exception_state_known;
                member.potentially_throwing =
                    base.potentially_throwing;
                return finish(std::move(member));
            }
            if (node.lhs != cir::TemplateValueExprNoNode) {
                NodeResolution nested = resolve_node(node.lhs, depth + 1);
                if (nested.status ==
                    UnevaluatedCallResolutionStatus::Resolved) {
                    node.type = nested.expression_type.type;
                    node.result_type = nested.expression_type;
                    node.value = static_cast<int64_t>(nested.category);
                    return finish(std::move(nested));
                }
                return finish(std::move(nested));
            }
            cir::TypeRef type = node.result_type.type.valid()
                ? node.result_type
                : file_.type_ref(node.type);
            ValueCategory category = category_from_recipe(node.value);
            if (!type.type.valid() || dependent_type(type.type) ||
                category == ValueCategory::Dependent) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent,
                    type,
                    category,
                    {}});
            }

            cir::TypeId resolved_type = file_.resolved_type(type.type);
            if (file_.valid(resolved_type) &&
                (file_.type(resolved_type).kind ==
                     cir::TypeKind::LValueReference ||
                 file_.type(resolved_type).kind ==
                     cir::TypeKind::RValueReference)) {
                type = file_.reference_referred_ref(resolved_type);
            }
            cir::TypeRef decltype_type = type;
            if (category == ValueCategory::LValue ||
                category == ValueCategory::XValue) {
                decltype_type = file_.type_ref(reference_type(
                    type,
                    category == ValueCategory::LValue
                        ? cir::ReferenceKind::LValue
                        : cir::ReferenceKind::RValue));
            }
            node.type = type.type;
            node.result_type = type;
            return finish({UnevaluatedCallResolutionStatus::Resolved,
                           type,
                           category,
                           decltype_type});
        }
        if (node.kind == cir::TemplateValueExprKind::Entity) {
            if (!node.entity.valid() || !file_.valid(node.entity)) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            cir::TypeRef type = node.result_type.type.valid()
                ? node.result_type
                : file_.entity_type_ref(node.entity);
            ValueCategory category = category_from_recipe(node.value);
            if (category == ValueCategory::Invalid ||
                category == ValueCategory::Dependent) {
                category = ValueCategory::LValue;
            }
            if (!type.type.valid() || dependent_type(type.type)) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent,
                    type,
                    category,
                    {}});
            }
            return finish({UnevaluatedCallResolutionStatus::Resolved,
                           type,
                           category,
                           type});
        }

        if (node.kind == cir::TemplateValueExprKind::Cast &&
            node.lhs != cir::TemplateValueExprNoNode &&
            node.type.valid()) {
            NodeResolution operand = resolve_node(node.lhs, depth + 1);
            if (operand.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(operand));
            }
            cir::TypeId target = file_.resolved_type(node.type);
            if (!file_.valid(target) || dependent_type(target)) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }
            NodeResolution cast;
            cast.status = UnevaluatedCallResolutionStatus::Resolved;
            cast.decltype_type = file_.type_ref(node.type);
            cir::TypeKind target_kind = file_.type(target).kind;
            if (target_kind == cir::TypeKind::LValueReference ||
                target_kind == cir::TypeKind::RValueReference) {
                cast.expression_type = file_.reference_referred_ref(target);
                cir::TypeId referred =
                    file_.resolved_type(cast.expression_type.type);
                bool function = file_.valid(referred) &&
                    file_.type(referred).kind == cir::TypeKind::Function;
                cast.category =
                    target_kind == cir::TypeKind::LValueReference || function
                        ? ValueCategory::LValue
                        : ValueCategory::XValue;
            } else {
                cast.expression_type = file_.type_ref(node.type);
                cast.category = ValueCategory::PrValue;
            }
            node.result_type = cast.expression_type;
            node.value = static_cast<int64_t>(cast.category);
            cast.exception_state_known = operand.exception_state_known;
            cast.potentially_throwing = operand.potentially_throwing;
            return finish(std::move(cast));
        }

        if (node.kind == cir::TemplateValueExprKind::Unary &&
            node.op == cir::TemplateValueExprOp::AddressOf &&
            node.lhs != cir::TemplateValueExprNoNode) {
            cir::TemplateValueExprNode& operand_node =
                result.expression.nodes[node.lhs];
            cir::TypeRef result_type;
            if (operand_node.kind ==
                    cir::TemplateValueExprKind::TypeOperand &&
                operand_node.qualifier_type.type.valid() &&
                operand_node.name.valid()) {
                cir::TypeId qualifier = file_.resolved_type(
                    operand_node.qualifier_type.type);
                if (!file_.valid(qualifier) ||
                    dependent_type(qualifier)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                if (file_.type(qualifier).kind !=
                    cir::TypeKind::Record) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                const cir::RecordFacts* facts =
                    file_.record_facts_for_type(qualifier);
                if ((!facts || facts->is_incomplete) &&
                    !require_complete_class_type(
                        qualifier,
                        loc,
                        cir::InstantiationDemandKind::BaseMemberList)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::HardError});
                }
                MemberLookupResult lookup = lookup_member_name(
                    qualifier, file_.name(operand_node.name));
                if (lookup.has_dependent_bases) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                if (!lookup.found_name || lookup.ambiguous ||
                    lookup.declarations.size() != 1) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                const MemberLookupDeclaration& declaration =
                    lookup.declarations.front();
                if (!declaration.entity.valid() ||
                    !file_.valid(declaration.entity) ||
                    !check_member_lookup_access(
                        declaration, loc, qualifier) ||
                    !check_member_lookup_base_access(
                        declaration, qualifier, loc)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                const cir::Entity& entity =
                    file_.entity(declaration.entity);
                if (entity.kind == cir::EntityKind::Method) {
                    const cir::RecordMethodFact* method =
                        file_.method_fact(declaration.entity);
                    if (!method || !method->type.type.valid()) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    if (method->is_static ||
                        entity.is_static_member_function) {
                        result_type = file_.type_ref(
                            pointer_type(method->type));
                    } else {
                        cir::TypeId declaring_class =
                            entity.parent.valid() &&
                                    file_.valid(entity.parent)
                                ? file_.entity(entity.parent).type
                                : cir::TypeId{};
                        if (!declaring_class.valid()) {
                            return finish({
                                UnevaluatedCallResolutionStatus::
                                    SubstitutionFailure});
                        }
                        result_type = file_.type_ref(
                            member_pointer_type(
                                file_.type_ref(declaring_class),
                                method->type));
                    }
                } else if (entity.kind == cir::EntityKind::Field) {
                    const cir::RecordFieldFact* field =
                        file_.field_fact(declaration.entity);
                    if (!field || field->is_bitfield) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    result_type = file_.type_ref(
                        member_pointer_type(
                            file_.type_ref(qualifier),
                            file_.type_ref(entity.type,
                                           entity.qualifiers,
                                           entity.memory_space)));
                } else if (entity.kind == cir::EntityKind::Variable ||
                           entity.kind == cir::EntityKind::Function) {
                    result_type = file_.type_ref(
                        pointer_type(file_.type_ref(
                            entity.type,
                            entity.qualifiers,
                            entity.memory_space)));
                } else {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
            } else {
                NodeResolution operand =
                    resolve_node(node.lhs, depth + 1);
                if (operand.status !=
                    UnevaluatedCallResolutionStatus::Resolved) {
                    return finish(std::move(operand));
                }
                cir::TypeId operand_type =
                    file_.resolved_type(operand.expression_type.type);
                if (!file_.valid(operand_type) ||
                    (operand.category != ValueCategory::LValue &&
                     operand.category !=
                         ValueCategory::FunctionDesignator)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                result_type = file_.type_ref(
                    pointer_type(operand.expression_type));
            }
            node.result_type = result_type;
            node.value =
                static_cast<int64_t>(ValueCategory::PrValue);
            return finish({
                UnevaluatedCallResolutionStatus::Resolved,
                result_type,
                ValueCategory::PrValue,
                result_type});
        }

        if (node.kind == cir::TemplateValueExprKind::Unary &&
            node.op == cir::TemplateValueExprOp::Dereference &&
            node.lhs != cir::TemplateValueExprNoNode) {
            NodeResolution operand = resolve_node(node.lhs, depth + 1);
            if (operand.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(operand));
            }
            cir::TypeId pointer =
                file_.resolved_type(operand.expression_type.type);
            if (!file_.valid(pointer)) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            if (file_.type(pointer).kind != cir::TypeKind::Pointer) {
                ExprResult operand_view;
                operand_view.type = operand.expression_type.type;
                operand_view.category = operand.category;
                operand_view.semantic_object_qualifiers =
                    operand.expression_type.qualifiers;
                cir::EntityId selected =
                    select_overloaded_unary_candidate(
                        syntax::UnaryOperator::Dereference,
                        operand_view,
                        nullptr,
                        nullptr,
                        nullptr,
                        result.expression.loc,
                        /*diagnose=*/false);
                if (!selected.valid() || !file_.valid(selected)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                cir::TypeId function_type =
                    file_.resolved_type(file_.entity(selected).type);
                const auto* function = file_.valid(function_type)
                    ? std::get_if<cir::FunctionTypePayload>(
                          &file_.type_payload(function_type))
                    : nullptr;
                if (!function || !function->return_type.type.valid()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                cir::TypeRef return_type = function->return_type;
                if (dependent_type(return_type.type) ||
                    contains_auto_type(return_type.type)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                cir::TypeId resolved_return =
                    file_.resolved_type(return_type.type);
                NodeResolution dereference{
                    UnevaluatedCallResolutionStatus::Resolved,
                    return_type,
                    ValueCategory::PrValue,
                    return_type};
                if (file_.valid(resolved_return) &&
                    (file_.type(resolved_return).kind ==
                         cir::TypeKind::LValueReference ||
                     file_.type(resolved_return).kind ==
                         cir::TypeKind::RValueReference)) {
                    dereference.expression_type =
                        file_.reference_referred_ref(resolved_return);
                    dereference.category =
                        file_.type(resolved_return).kind ==
                                cir::TypeKind::LValueReference
                            ? ValueCategory::LValue
                            : ValueCategory::XValue;
                }
                node.result_type = dereference.expression_type;
                node.value =
                    static_cast<int64_t>(dereference.category);
                dereference.exception_state_known =
                    operand.exception_state_known &&
                    function->exception_spec.kind !=
                        cir::FunctionExceptionSpecKind::Dependent;
                dereference.potentially_throwing =
                    operand.potentially_throwing ||
                    function->exception_spec.kind !=
                        cir::FunctionExceptionSpecKind::NonThrowing;
                return finish(std::move(dereference));
            }
            cir::TypeRef pointee = file_.pointer_pointee_ref(pointer);
            if (!pointee.type.valid() || dependent_type(pointee.type)) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }
            node.result_type = pointee;
            node.value = static_cast<int64_t>(ValueCategory::LValue);
            NodeResolution dereference{
                UnevaluatedCallResolutionStatus::Resolved,
                pointee,
                ValueCategory::LValue,
                file_.type_ref(reference_type(
                    pointee, cir::ReferenceKind::LValue))};
            dereference.exception_state_known =
                operand.exception_state_known;
            dereference.potentially_throwing =
                operand.potentially_throwing;
            return finish(std::move(dereference));
        }

        if (node.kind == cir::TemplateValueExprKind::Unary &&
            (node.op == cir::TemplateValueExprOp::Delete ||
             node.op == cir::TemplateValueExprOp::DeleteArray) &&
            node.lhs != cir::TemplateValueExprNoNode) {
            NodeResolution operand = resolve_node(node.lhs, depth + 1);
            if (operand.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(operand));
            }
            if (!operand.expression_type.type.valid() ||
                dependent_type(operand.expression_type.type)) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }

            SpeculativeParseGuard delete_probe = speculative_parse();
            size_t diagnostic_watermark = file_.errors().size();
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block =
                begin_fragment_block("expr.delete.unevaluated");
            ExprResult operand_view;
            operand_view.type = operand.expression_type.type;
            operand_view.category = operand.category;
            operand_view.semantic_object_qualifiers =
                operand.expression_type.qualifiers;
            if (operand.category == ValueCategory::LValue ||
                operand.category == ValueCategory::XValue) {
                cir::TypeId address_type =
                    builder_.pointer_type(operand.expression_type);
                cir::InstId address = builder_.name_ref(
                    "<unevaluated-delete-address>",
                    address_type,
                    result.expression.loc);
                operand_view.place =
                    builder_.deref(address, result.expression.loc);
            } else {
                operand_view.value = builder_.name_ref(
                    "<unevaluated-delete-value>",
                    operand.expression_type.type,
                    result.expression.loc);
            }
            operand_view.fragment =
                finish_fragment_block(block, previous);
            DeleteExpressionInput delete_input;
            delete_input.pointer = std::move(operand_view);
            delete_input.is_array =
                node.op == cir::TemplateValueExprOp::DeleteArray;
            ExprResult deleted = collect_delete_expr(
                std::move(delete_input), result.expression.loc);
            bool invalid = deleted.has_error ||
                file_.errors().size() != diagnostic_watermark;
            bool exception_dependent = false;
            bool potentially_throwing = !invalid &&
                expression_potentially_throws(
                    deleted, &exception_dependent);
            if (invalid) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }

            cir::TypeRef void_type =
                file_.type_ref(builder_.void_type());
            node.result_type = void_type;
            node.value =
                static_cast<int64_t>(ValueCategory::PrValue);
            NodeResolution resolution{
                UnevaluatedCallResolutionStatus::Resolved,
                void_type,
                ValueCategory::PrValue,
                void_type};
            resolution.exception_state_known = !exception_dependent;
            resolution.potentially_throwing = potentially_throwing;
            return finish(std::move(resolution));
        }

        if (node.kind == cir::TemplateValueExprKind::Unary &&
            node.op != cir::TemplateValueExprOp::Dereference &&
            node.lhs != cir::TemplateValueExprNoNode) {
            NodeResolution operand = resolve_node(node.lhs, depth + 1);
            if (operand.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(operand));
            }
            cir::TypeId operand_type =
                file_.resolved_type(operand.expression_type.type);
            if (!file_.valid(operand_type) ||
                dependent_type(operand_type)) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }

            cir::TypeRef result_type;
            if (node.op ==
                cir::TemplateValueExprOp::LogicalNot) {
                ExprResult view;
                view.type = operand.expression_type.type;
                view.category = operand.category;
                view.semantic_object_qualifiers =
                    operand.expression_type.qualifiers;
                result_type = file_.type_ref(
                    file_.builtin_type(cir::BuiltinTypeKind::Bool));
                if (conversion_rank(
                        view,
                        result_type,
                        operand.expression_type.qualifiers,
                        nullptr,
                        /*allow_user_defined=*/true) ==
                    ConversionRank::Bad) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
            } else if (node.op ==
                           cir::TemplateValueExprOp::UnaryPlus ||
                       node.op ==
                           cir::TemplateValueExprOp::UnaryMinus) {
                if (!is_arithmetic_type(operand_type)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                cir::TypeId promoted = is_integer_type(operand_type)
                    ? integer_promotion_type(operand_type)
                    : operand_type;
                if (!promoted.valid()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                result_type = file_.type_ref(promoted);
            } else if (node.op ==
                       cir::TemplateValueExprOp::BitwiseNot) {
                if (!is_integer_type(operand_type)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                cir::TypeId promoted =
                    integer_promotion_type(operand_type);
                if (!promoted.valid()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                result_type = file_.type_ref(promoted);
            } else {
                return finish({
                    UnevaluatedCallResolutionStatus::
                        SubstitutionFailure});
            }

            node.result_type = result_type;
            node.value =
                static_cast<int64_t>(ValueCategory::PrValue);
            NodeResolution unary{
                UnevaluatedCallResolutionStatus::Resolved,
                result_type,
                ValueCategory::PrValue,
                result_type};
            unary.exception_state_known =
                operand.exception_state_known;
            unary.potentially_throwing =
                operand.potentially_throwing;
            return finish(std::move(unary));
        }

        if (node.kind == cir::TemplateValueExprKind::Binary &&
            node.op != cir::TemplateValueExprOp::MemberPointerDot &&
            node.op != cir::TemplateValueExprOp::MemberPointerArrow &&
            node.lhs != cir::TemplateValueExprNoNode &&
            node.rhs != cir::TemplateValueExprNoNode) {
            NodeResolution lhs = resolve_node(node.lhs, depth + 1);
            NodeResolution rhs = resolve_node(node.rhs, depth + 1);
            auto terminal_failure = [](const NodeResolution& resolution) {
                return resolution.status ==
                           UnevaluatedCallResolutionStatus::
                               SubstitutionFailure ||
                    resolution.status ==
                           UnevaluatedCallResolutionStatus::HardError;
            };
            if (terminal_failure(lhs)) {
                return finish(std::move(lhs));
            }
            if (terminal_failure(rhs)) {
                return finish(std::move(rhs));
            }
            if (lhs.status !=
                    UnevaluatedCallResolutionStatus::Resolved ||
                rhs.status !=
                    UnevaluatedCallResolutionStatus::Resolved) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }

            auto finish_binary = [&](cir::TypeRef expression_type,
                                     ValueCategory category,
                                     cir::TypeRef decltype_type = {}) {
                NodeResolution resolution;
                resolution.status =
                    UnevaluatedCallResolutionStatus::Resolved;
                resolution.expression_type = expression_type;
                resolution.category = category;
                if (decltype_type.type.valid()) {
                    resolution.decltype_type = decltype_type;
                } else if (category == ValueCategory::LValue ||
                           category == ValueCategory::XValue) {
                    resolution.decltype_type = file_.type_ref(
                        reference_type(
                            expression_type,
                            category == ValueCategory::LValue
                                ? cir::ReferenceKind::LValue
                                : cir::ReferenceKind::RValue));
                } else {
                    resolution.decltype_type = expression_type;
                }
                resolution.exception_state_known =
                    lhs.exception_state_known &&
                    rhs.exception_state_known;
                resolution.potentially_throwing =
                    lhs.potentially_throwing || rhs.potentially_throwing;
                node.result_type = expression_type;
                node.value = static_cast<int64_t>(category);
                return resolution;
            };

            if (node.op == cir::TemplateValueExprOp::Comma) {
                return finish(finish_binary(rhs.expression_type,
                                            rhs.category,
                                            rhs.decltype_type));
            }

            cir::TypeId lhs_type =
                file_.resolved_type(lhs.expression_type.type);
            cir::TypeId rhs_type =
                file_.resolved_type(rhs.expression_type.type);
            if (!file_.valid(lhs_type) || !file_.valid(rhs_type) ||
                dependent_type(lhs_type) || dependent_type(rhs_type)) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }

            auto boolean_result = [&]() {
                return finish_binary(
                    file_.type_ref(file_.builtin_type(
                        cir::BuiltinTypeKind::Bool)),
                    ValueCategory::PrValue);
            };
            std::optional<syntax::BinaryOperator> comparison_operator;
            switch (node.op) {
                case cir::TemplateValueExprOp::Less:
                    comparison_operator = syntax::BinaryOperator::Less;
                    break;
                case cir::TemplateValueExprOp::LessEqual:
                    comparison_operator = syntax::BinaryOperator::LessEqual;
                    break;
                case cir::TemplateValueExprOp::Greater:
                    comparison_operator = syntax::BinaryOperator::Greater;
                    break;
                case cir::TemplateValueExprOp::GreaterEqual:
                    comparison_operator = syntax::BinaryOperator::GreaterEqual;
                    break;
                case cir::TemplateValueExprOp::Equal:
                    comparison_operator = syntax::BinaryOperator::Equal;
                    break;
                case cir::TemplateValueExprOp::NotEqual:
                    comparison_operator = syntax::BinaryOperator::NotEqual;
                    break;
                case cir::TemplateValueExprOp::ThreeWay:
                    comparison_operator = syntax::BinaryOperator::ThreeWay;
                    break;
                default:
                    break;
            }
            if (comparison_operator.has_value()) {

                SpeculativeParseGuard comparison_probe =
                    speculative_parse();
                size_t diagnostic_watermark = file_.errors().size();
                auto make_operand =
                    [&](const NodeResolution& resolution,
                        std::string_view name) {
                        ExprResult operand;
                        operand.type = resolution.expression_type.type;
                        operand.category = resolution.category;
                        operand.semantic_object_qualifiers =
                            resolution.expression_type.qualifiers;

                        cir::BlockId previous = builder_.current_block();
                        cir::BlockId block =
                            begin_fragment_block("expr.comparison.unevaluated");
                        if (resolution.category == ValueCategory::LValue ||
                            resolution.category == ValueCategory::XValue) {
                            cir::TypeId address_type =
                                builder_.pointer_type(
                                    resolution.expression_type);
                            cir::InstId address =
                                builder_.name_ref(name, address_type,
                                                  result.expression.loc);
                            operand.place =
                                builder_.deref(address,
                                               result.expression.loc);
                        } else {
                            operand.value =
                                builder_.name_ref(
                                    name,
                                    resolution.expression_type.type,
                                    result.expression.loc);
                        }
                        operand.fragment =
                            finish_fragment_block(block, previous);
                        return operand;
                    };

                ExprResult comparison = collect_binary_expr(
                    *comparison_operator,
                    make_operand(lhs, "<unevaluated-comparison-lhs>"),
                    make_operand(rhs, "<unevaluated-comparison-rhs>"),
                    result.expression.loc);
                bool invalid = comparison.has_error ||
                    file_.errors().size() != diagnostic_watermark;
                bool exception_dependent = false;
                bool operator_potentially_throwing = !invalid &&
                    expression_potentially_throws(
                        comparison, &exception_dependent);
                cir::TypeRef comparison_type =
                    file_.type_ref(comparison.type);
                ValueCategory comparison_category =
                    comparison.category;
                comparison_probe.rollback();

                if (invalid) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                if (exception_dependent ||
                    !comparison_type.type.valid() ||
                    !file_.valid(comparison_type.type)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                NodeResolution comparison_resolution =
                    finish_binary(comparison_type,
                                  comparison_category);
                comparison_resolution.exception_state_known =
                    lhs.exception_state_known &&
                    rhs.exception_state_known;
                comparison_resolution.potentially_throwing =
                    lhs.potentially_throwing ||
                    rhs.potentially_throwing ||
                    operator_potentially_throwing;
                return finish(std::move(comparison_resolution));
            }
            switch (node.op) {
                case cir::TemplateValueExprOp::LogicalAnd:
                case cir::TemplateValueExprOp::LogicalOr: {
                    ExprResult lhs_view;
                    lhs_view.type = lhs.expression_type.type;
                    lhs_view.category = lhs.category;
                    lhs_view.semantic_object_qualifiers =
                        lhs.expression_type.qualifiers;
                    ExprResult rhs_view;
                    rhs_view.type = rhs.expression_type.type;
                    rhs_view.category = rhs.category;
                    rhs_view.semantic_object_qualifiers =
                        rhs.expression_type.qualifiers;
                    cir::TypeRef bool_type = file_.type_ref(
                        file_.builtin_type(cir::BuiltinTypeKind::Bool));
                    if (conversion_rank(
                            lhs_view,
                            bool_type,
                            lhs.expression_type.qualifiers,
                            nullptr,
                            /*allow_user_defined=*/true) ==
                            ConversionRank::Bad ||
                        conversion_rank(
                            rhs_view,
                            bool_type,
                            rhs.expression_type.qualifiers,
                            nullptr,
                            /*allow_user_defined=*/true) ==
                            ConversionRank::Bad) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    return finish(boolean_result());
                }
                case cir::TemplateValueExprOp::Add:
                case cir::TemplateValueExprOp::Sub:
                case cir::TemplateValueExprOp::Mul:
                case cir::TemplateValueExprOp::Div:
                    if (!is_arithmetic_type(lhs_type) ||
                        !is_arithmetic_type(rhs_type)) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    break;
                case cir::TemplateValueExprOp::Mod:
                case cir::TemplateValueExprOp::Shl:
                case cir::TemplateValueExprOp::Shr:
                case cir::TemplateValueExprOp::BitAnd:
                case cir::TemplateValueExprOp::BitOr:
                case cir::TemplateValueExprOp::BitXor:
                    if (!is_integer_type(lhs_type) ||
                        !is_integer_type(rhs_type)) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                    break;
                case cir::TemplateValueExprOp::Less:
                case cir::TemplateValueExprOp::LessEqual:
                case cir::TemplateValueExprOp::Greater:
                case cir::TemplateValueExprOp::GreaterEqual:
                case cir::TemplateValueExprOp::Equal:
                case cir::TemplateValueExprOp::NotEqual:
                case cir::TemplateValueExprOp::ThreeWay:
                case cir::TemplateValueExprOp::Comma:
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
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
            }
            cir::TypeId common =
                node.op == cir::TemplateValueExprOp::Shl ||
                        node.op == cir::TemplateValueExprOp::Shr
                    ? integer_promotion_type(lhs_type)
                    : usual_arithmetic_conversion_type(lhs_type,
                                                       rhs_type);
            if (!common.valid()) {
                return finish({
                    UnevaluatedCallResolutionStatus::
                        SubstitutionFailure});
            }
            return finish(finish_binary(file_.type_ref(common),
                                        ValueCategory::PrValue));
        }

        if (node.kind == cir::TemplateValueExprKind::Binary &&
            (node.op == cir::TemplateValueExprOp::MemberPointerDot ||
             node.op == cir::TemplateValueExprOp::MemberPointerArrow) &&
            node.lhs != cir::TemplateValueExprNoNode &&
            node.rhs != cir::TemplateValueExprNoNode) {
            NodeResolution object = resolve_node(node.lhs, depth + 1);
            if (object.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(object));
            }
            NodeResolution pointer = resolve_node(node.rhs, depth + 1);
            if (pointer.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(pointer));
            }
            cir::TypeId member_pointer =
                file_.resolved_type(pointer.expression_type.type);
            if (!file_.valid(member_pointer) ||
                file_.type(member_pointer).kind !=
                    cir::TypeKind::MemberPointer) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }

            cir::TypeRef object_ref = object.expression_type;
            ValueCategory object_category = object.category;
            if (node.op ==
                cir::TemplateValueExprOp::MemberPointerArrow) {
                cir::TypeId object_pointer =
                    file_.resolved_type(object_ref.type);
                if (!file_.valid(object_pointer) ||
                    file_.type(object_pointer).kind !=
                        cir::TypeKind::Pointer) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                object_ref = file_.pointer_pointee_ref(object_pointer);
                object_category = ValueCategory::LValue;
            }
            cir::TypeId object_type = file_.resolved_type(object_ref.type);
            cir::TypeId member_class = file_.resolved_type(
                file_.member_pointer_class_ref(member_pointer).type);
            if (!file_.valid(object_type) ||
                file_.type(object_type).kind != cir::TypeKind::Record ||
                !file_.valid(member_class) ||
                file_.type(member_class).kind != cir::TypeKind::Record ||
                (object_type != member_class &&
                 !derived_to_base_path(object_type, member_class, nullptr))) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }

            cir::TypeRef member =
                file_.member_pointer_member_ref(member_pointer);
            cir::TypeId resolved_member = file_.resolved_type(member.type);
            if (!file_.valid(resolved_member) ||
                dependent_type(resolved_member)) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }
            if (file_.type(resolved_member).kind ==
                cir::TypeKind::Function) {
                node.result_type = member;
                node.value = static_cast<int64_t>(
                    ValueCategory::MemberFunctionPointerCallee);
                NodeResolution bound{
                    UnevaluatedCallResolutionStatus::Resolved,
                    member,
                    ValueCategory::MemberFunctionPointerCallee,
                    member};
                bound.bound_member_function = true;
                bound.bound_member_object = object_ref;
                bound.bound_member_object_category = object_category;
                bound.bound_member_object_qualifiers = object_ref.qualifiers;
                bound.bound_member_class = member_class;
                bound.exception_state_known =
                    object.exception_state_known &&
                    pointer.exception_state_known;
                bound.potentially_throwing =
                    object.potentially_throwing ||
                    pointer.potentially_throwing;
                return finish(std::move(bound));
            }

            member.qualifiers = static_cast<uint8_t>(
                member.qualifiers | object_ref.qualifiers);
            ValueCategory category = object_category == ValueCategory::LValue
                ? ValueCategory::LValue
                : ValueCategory::XValue;
            cir::ReferenceKind reference_kind =
                category == ValueCategory::LValue
                    ? cir::ReferenceKind::LValue
                    : cir::ReferenceKind::RValue;
            node.result_type = member;
            node.value = static_cast<int64_t>(category);
            NodeResolution access{
                UnevaluatedCallResolutionStatus::Resolved,
                member,
                category,
                file_.type_ref(reference_type(member, reference_kind))};
            access.exception_state_known =
                object.exception_state_known &&
                pointer.exception_state_known;
            access.potentially_throwing =
                object.potentially_throwing || pointer.potentially_throwing;
            return finish(std::move(access));
        }

        if (node.kind != cir::TemplateValueExprKind::Call ||
            node.third == cir::TemplateValueExprNoNode ||
            node.third >= result.expression.nodes.size()) {
            return finish({
                UnevaluatedCallResolutionStatus::StillDependent});
        }

        cir::TemplateValueExprNode& target =
            result.expression.nodes[node.third];
        if (target.kind != cir::TemplateValueExprKind::Callee) {
            return finish({
                UnevaluatedCallResolutionStatus::SubstitutionFailure});
        }

        std::vector<ExprResult> arguments;
        bool subexpressions_exception_known = true;
        bool subexpressions_potentially_throw = false;
        std::unordered_set<uint32_t> argument_nodes;
        for (uint32_t current = node.lhs;
             current != cir::TemplateValueExprNoNode;) {
            if (current >= result.expression.nodes.size() ||
                !argument_nodes.insert(current).second) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            cir::TemplateValueExprNode& argument_node =
                result.expression.nodes[current];
            if (argument_node.kind !=
                cir::TemplateValueExprKind::TypeOperand) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            NodeResolution argument = resolve_node(current, depth + 1);
            if (argument.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(argument));
            }
            ExprResult view;
            view.type = argument.expression_type.type;
            view.category = argument.category;
            view.semantic_object_qualifiers =
                argument.expression_type.qualifiers;
            view.unevaluated_semantic_operand = true;
            arguments.push_back(std::move(view));
            subexpressions_exception_known =
                subexpressions_exception_known &&
                argument.exception_state_known;
            subexpressions_potentially_throw =
                subexpressions_potentially_throw ||
                argument.potentially_throwing;
            current = argument_node.rhs;
        }

        auto decode_explicit_arguments =
            [&](uint32_t head,
                std::vector<TemplateArgument>& destination)
            -> UnevaluatedCallResolutionStatus {
            std::unordered_set<uint32_t> explicit_nodes;
            for (uint32_t current = head;
                 current != cir::TemplateValueExprNoNode;) {
                if (current >= result.expression.nodes.size() ||
                    !explicit_nodes.insert(current).second) {
                    return UnevaluatedCallResolutionStatus::
                        SubstitutionFailure;
                }
                const cir::TemplateValueExprNode& explicit_node =
                    result.expression.nodes[current];
                if (explicit_node.kind !=
                        cir::TemplateValueExprKind::TypeOperand ||
                    explicit_node.value < static_cast<int64_t>(
                        cir::TemplateArgumentKind::Type) ||
                    explicit_node.value > static_cast<int64_t>(
                        cir::TemplateArgumentKind::Template)) {
                    return UnevaluatedCallResolutionStatus::
                        SubstitutionFailure;
                }
                TemplateArgument argument;
                bool has_concrete_canonical_argument =
                    explicit_node.template_arguments.size() == 1 &&
                    !explicit_node.template_arguments.values().front()
                         .is_dependent &&
                    (explicit_node.template_arguments.values().front().kind !=
                         cir::TemplateArgumentKind::Value ||
                     explicit_node.template_arguments.values().front()
                             .value_kind !=
                         cir::TemplateValueKind::None);
                if (has_concrete_canonical_argument) {
                    argument =
                        explicit_node.template_arguments.values().front();
                } else {
                    argument.kind =
                        static_cast<cir::TemplateArgumentKind>(
                            explicit_node.value);
                }
                if (!has_concrete_canonical_argument &&
                    argument.kind ==
                        cir::TemplateArgumentKind::Type) {
                    argument.type =
                        file_.type_ref(explicit_node.type);
                    argument.is_dependent =
                        dependent_type(argument.type.type);
                } else if (!has_concrete_canonical_argument &&
                           argument.kind ==
                               cir::TemplateArgumentKind::Value) {
                    argument.value_type = explicit_node.result_type;
                    argument.value_entity = explicit_node.entity;
                    argument.dependent_value_qualifier =
                        explicit_node.qualifier_type;
                    argument.dependent_value_name =
                        explicit_node.name;
                    if (explicit_node.lhs !=
                        cir::TemplateValueExprNoNode) {
                        const cir::TemplateValueExprNode& value_root =
                            result.expression.nodes[
                                explicit_node.lhs];
                        if (value_root.kind ==
                            cir::TemplateValueExprKind::Integer) {
                            argument.value_kind =
                                cir::TemplateValueKind::Integer;
                            argument.integer_value =
                                value_root.integer_value;
                        } else {
                            argument.dependent_value_expr =
                                subexpression(explicit_node.lhs);
                            argument.is_dependent = true;
                        }
                    }
                } else if (!has_concrete_canonical_argument) {
                    argument.template_entity =
                        explicit_node.entity;
                    argument.template_name = explicit_node.name;
                    argument.dependent_template_qualifier =
                        explicit_node.qualifier_type;
                    argument.is_dependent =
                        !argument.template_entity.valid();
                }
                if (argument.is_dependent) {
                    return UnevaluatedCallResolutionStatus::
                        StillDependent;
                }
                destination.push_back(std::move(argument));
                current = explicit_node.rhs;
            }
            return UnevaluatedCallResolutionStatus::Resolved;
        };

        std::vector<TemplateArgument> explicit_arguments;
        UnevaluatedCallResolutionStatus explicit_status =
            decode_explicit_arguments(node.rhs, explicit_arguments);
        if (explicit_status !=
            UnevaluatedCallResolutionStatus::Resolved) {
            return finish({explicit_status});
        }
        std::vector<CandidateExplicitTemplateArguments>
            candidate_explicit_arguments;
        for (uint32_t candidate_index : target.operands) {
            if (candidate_index >= result.expression.nodes.size()) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            const cir::TemplateValueExprNode& candidate_node =
                result.expression.nodes[candidate_index];
            if (candidate_node.kind !=
                    cir::TemplateValueExprKind::TypeOperand ||
                candidate_node.lhs ==
                    cir::TemplateValueExprNoNode) {
                continue;
            }
            CandidateExplicitTemplateArguments candidate_arguments;
            candidate_arguments.template_entity =
                candidate_node.entity;
            UnevaluatedCallResolutionStatus candidate_status =
                decode_explicit_arguments(
                    candidate_node.lhs,
                    candidate_arguments.arguments);
            if (candidate_status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish({candidate_status});
            }
            candidate_explicit_arguments.push_back(
                std::move(candidate_arguments));
        }

        std::vector<cir::EntityId> candidates;
        bool member_object_leading = false;
        ExprResult object;
        if (target.lhs != cir::TemplateValueExprNoNode) {
            NodeResolution callable = resolve_node(target.lhs, depth + 1);
            if (callable.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(callable));
            }
            subexpressions_exception_known =
                subexpressions_exception_known &&
                callable.exception_state_known;
            subexpressions_potentially_throw =
                subexpressions_potentially_throw ||
                callable.potentially_throwing;
            cir::TypeId callable_type =
                file_.resolved_type(callable.expression_type.type);
            if (!file_.valid(callable_type)) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            if (callable.bound_member_function) {
                if (file_.type(callable_type).kind !=
                    cir::TypeKind::Function) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                const auto* function =
                    std::get_if<cir::FunctionTypePayload>(
                        &file_.type_payload(callable_type));
                if (!function || !function->return_type.type.valid()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                if ((!function->member_is_const &&
                     (callable.bound_member_object_qualifiers &
                      cir::QualConst) != 0) ||
                    (!function->member_is_volatile &&
                     (callable.bound_member_object_qualifiers &
                      cir::QualVolatile) != 0) ||
                    (function->member_ref_qualifier ==
                         cir::FunctionRefQualifierKind::LValue &&
                     callable.bound_member_object_category !=
                         ValueCategory::LValue) ||
                    (function->member_ref_qualifier ==
                         cir::FunctionRefQualifierKind::RValue &&
                     callable.bound_member_object_category ==
                         ValueCategory::LValue)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                if (function->has_prototype &&
                    ((!function->is_variadic &&
                      arguments.size() != function->parameters.size()) ||
                     (function->is_variadic &&
                      arguments.size() < function->parameters.size()))) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                for (size_t argument_index = 0;
                     function->has_prototype &&
                     argument_index < function->parameters.size();
                     ++argument_index) {
                    if (conversion_rank(
                            arguments[argument_index],
                            function->parameters[argument_index],
                            arguments[argument_index]
                                .semantic_object_qualifiers.value_or(0),
                            nullptr,
                            /*allow_user_defined=*/true) ==
                        ConversionRank::Bad) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                }
                cir::TypeRef return_type = function->return_type;
                if (dependent_type(return_type.type)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                cir::TypeId resolved_return =
                    file_.resolved_type(return_type.type);
                NodeResolution direct{
                    UnevaluatedCallResolutionStatus::Resolved,
                    return_type,
                    ValueCategory::PrValue,
                    return_type};
                if (file_.valid(resolved_return) &&
                    (file_.type(resolved_return).kind ==
                         cir::TypeKind::LValueReference ||
                     file_.type(resolved_return).kind ==
                         cir::TypeKind::RValueReference)) {
                    direct.expression_type =
                        file_.reference_referred_ref(resolved_return);
                    direct.category =
                        file_.type(resolved_return).kind ==
                                cir::TypeKind::LValueReference
                            ? ValueCategory::LValue
                            : ValueCategory::XValue;
                }
                node.result_type = return_type;
                direct.exception_state_known =
                    subexpressions_exception_known &&
                    function->exception_spec.kind !=
                        cir::FunctionExceptionSpecKind::Dependent;
                direct.potentially_throwing =
                    subexpressions_potentially_throw ||
                    function->exception_spec.kind !=
                        cir::FunctionExceptionSpecKind::NonThrowing;
                return finish(std::move(direct));
            }
            if (file_.type(callable_type).kind ==
                cir::TypeKind::Record) {
                MemberLookupResult lookup =
                    lookup_member_name(callable_type, "operator()");
                if (lookup.has_dependent_bases) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                if (lookup.ambiguous || !lookup.found_name) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                for (const MemberLookupDeclaration& declaration :
                     lookup.declarations) {
                    append_unique(candidates, declaration.entity);
                }
                member_object_leading = true;
                object.type = callable.expression_type.type;
                object.category = callable.category;
                object.semantic_object_qualifiers =
                    callable.expression_type.qualifiers;
                object.unevaluated_semantic_operand = true;
            } else {
                cir::TypeId function_type = callable_type;
                if (file_.type(callable_type).kind ==
                    cir::TypeKind::Pointer) {
                    function_type = file_.resolved_type(
                        file_.pointer_pointee_type(callable_type));
                }
                if (!file_.valid(function_type) ||
                    file_.type(function_type).kind !=
                        cir::TypeKind::Function) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                const auto* function =
                    std::get_if<cir::FunctionTypePayload>(
                        &file_.type_payload(function_type));
                if (!function || !function->return_type.type.valid()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                if (function->has_prototype &&
                    ((!function->is_variadic &&
                      arguments.size() != function->parameters.size()) ||
                     (function->is_variadic &&
                      arguments.size() < function->parameters.size()))) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                for (size_t argument_index = 0;
                     function->has_prototype &&
                     argument_index < function->parameters.size();
                     ++argument_index) {
                    if (conversion_rank(
                            arguments[argument_index],
                            function->parameters[argument_index],
                            arguments[argument_index]
                                .semantic_object_qualifiers.value_or(0),
                            nullptr,
                            /*allow_user_defined=*/true) ==
                        ConversionRank::Bad) {
                        return finish({
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure});
                    }
                }
                cir::TypeRef return_type = function->return_type;
                cir::TypeId resolved_return =
                    file_.resolved_type(return_type.type);
                if (dependent_type(return_type.type)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                NodeResolution direct{
                    UnevaluatedCallResolutionStatus::Resolved,
                    return_type,
                    ValueCategory::PrValue,
                    return_type};
                if (file_.valid(resolved_return) &&
                    (file_.type(resolved_return).kind ==
                         cir::TypeKind::LValueReference ||
                     file_.type(resolved_return).kind ==
                         cir::TypeKind::RValueReference)) {
                    direct.expression_type =
                        file_.reference_referred_ref(resolved_return);
                    direct.category =
                        file_.type(resolved_return).kind ==
                                cir::TypeKind::LValueReference
                            ? ValueCategory::LValue
                            : ValueCategory::XValue;
                }
                node.result_type = return_type;
                direct.exception_state_known =
                    subexpressions_exception_known &&
                    function->exception_spec.kind !=
                        cir::FunctionExceptionSpecKind::Dependent;
                direct.potentially_throwing =
                    subexpressions_potentially_throw ||
                    function->exception_spec.kind !=
                        cir::FunctionExceptionSpecKind::NonThrowing;
                return finish(std::move(direct));
            }
        } else if (target.rhs != cir::TemplateValueExprNoNode) {
            NodeResolution base = resolve_node(target.rhs, depth + 1);
            if (base.status !=
                UnevaluatedCallResolutionStatus::Resolved) {
                return finish(std::move(base));
            }
            subexpressions_exception_known =
                subexpressions_exception_known &&
                base.exception_state_known;
            subexpressions_potentially_throw =
                subexpressions_potentially_throw ||
                base.potentially_throwing;
            cir::TemplateCalleeFlag flags =
                static_cast<cir::TemplateCalleeFlag>(target.value);
            auto has_flag = [&](cir::TemplateCalleeFlag flag) {
                return (static_cast<uint32_t>(flags) &
                        static_cast<uint32_t>(flag)) != 0;
            };
            cir::TypeRef object_ref = base.expression_type;
            ValueCategory object_category = base.category;
            if (has_flag(cir::TemplateCalleeFlag::MemberArrow)) {
                cir::TypeId pointer = file_.resolved_type(object_ref.type);
                if (!file_.valid(pointer) ||
                    file_.type(pointer).kind != cir::TypeKind::Pointer) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                object_ref = file_.pointer_pointee_ref(pointer);
                object_category = ValueCategory::LValue;
            }
            cir::TypeId object_type = file_.resolved_type(object_ref.type);
            if (!file_.valid(object_type) ||
                file_.type(object_type).kind != cir::TypeKind::Record ||
                !target.name.valid() || !file_.valid(target.name)) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            cir::TypeId lookup_type = object_type;
            if (target.qualifier_type.type.valid()) {
                cir::TypeId qualifier = file_.resolved_type(
                    target.qualifier_type.type);
                if (!file_.valid(qualifier) || dependent_type(qualifier)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                if (file_.type(qualifier).kind != cir::TypeKind::Record ||
                    (object_type != qualifier &&
                     analyze_derived_to_base_path(object_type, qualifier).kind !=
                         DerivedToBasePathKind::Unique)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                lookup_type = qualifier;
            }
            MemberLookupResult lookup = lookup_member_name(
                lookup_type, file_.name(target.name));
            if (lookup.has_dependent_bases) {
                return finish({
                    UnevaluatedCallResolutionStatus::StillDependent});
            }
            if (lookup.ambiguous || !lookup.found_name) {
                return finish({
                    UnevaluatedCallResolutionStatus::SubstitutionFailure});
            }
            for (const MemberLookupDeclaration& declaration :
                 lookup.declarations) {
                append_unique(candidates, declaration.entity);
            }
            member_object_leading = true;
            object.type = object_ref.type;
            object.category = object_category;
            object.semantic_object_qualifiers = object_ref.qualifiers;
            object.unevaluated_semantic_operand = true;
        } else {
            append_unique(candidates, target.entity);
            for (uint32_t candidate_index : target.operands) {
                if (candidate_index >= result.expression.nodes.size()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::SubstitutionFailure});
                }
                append_unique(candidates,
                              result.expression.nodes[candidate_index]
                                  .entity);
            }
            std::string name = target.name.valid() && file_.valid(target.name)
                ? std::string(file_.name(target.name))
                : std::string();
            if (target.qualifier_type.type.valid()) {
                cir::TypeId qualifier =
                    file_.resolved_type(target.qualifier_type.type);
                if (!file_.valid(qualifier) ||
                    dependent_type(qualifier)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                if (file_.type(qualifier).kind !=
                    cir::TypeKind::Record) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                const cir::RecordFacts* facts =
                    file_.record_facts_for_type(qualifier);
                if ((!facts || facts->is_incomplete) &&
                    !require_complete_class_type(
                        qualifier,
                        loc,
                        cir::InstantiationDemandKind::BaseMemberList)) {
                    return finish({
                        UnevaluatedCallResolutionStatus::HardError});
                }
                if (name.empty()) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                MemberLookupResult lookup =
                    lookup_member_name(qualifier, name);
                if (lookup.has_dependent_bases) {
                    return finish({
                        UnevaluatedCallResolutionStatus::StillDependent});
                }
                if (lookup.ambiguous || !lookup.found_name) {
                    return finish({
                        UnevaluatedCallResolutionStatus::
                            SubstitutionFailure});
                }
                for (const MemberLookupDeclaration& declaration :
                     lookup.declarations) {
                    append_unique(candidates, declaration.entity);
                }
            }
            if (candidates.empty() && !name.empty() &&
                result.expression.definition_context.valid()) {
                if (const cir::Binding* binding =
                        file_.lookup_callable_binding(
                            result.expression.definition_context,
                            name,
                            /*include_parents=*/true)) {
                    for (cir::EntityId entity : binding->entities) {
                        append_unique(candidates, entity);
                    }
                }
            }
            cir::TemplateCalleeFlag flags =
                static_cast<cir::TemplateCalleeFlag>(target.value);
            auto has_flag = [&](cir::TemplateCalleeFlag flag) {
                return (static_cast<uint32_t>(flags) &
                        static_cast<uint32_t>(flag)) != 0;
            };
            if (!name.empty() &&
                !has_flag(cir::TemplateCalleeFlag::QualifiedName) &&
                !has_flag(cir::TemplateCalleeFlag::
                              SuppressArgumentDependentLookup)) {
                std::vector<cir::EntityId> adl;
                add_adl_candidates(name, arguments, adl);
                for (cir::EntityId entity : adl) {
                    append_unique(candidates, entity);
                }
            }
        }

        bool has_explicit_arguments =
            (static_cast<uint64_t>(target.value) &
             static_cast<uint32_t>(
                 cir::TemplateCalleeFlag::
                     HasExplicitTemplateArguments)) != 0;
        candidates = expand_candidates(
            candidates,
            arguments,
            has_explicit_arguments,
            explicit_arguments,
            candidate_explicit_arguments);
        if (hard_error) {
            return finish({
                UnevaluatedCallResolutionStatus::HardError});
        }
        if (candidates.empty()) {
            return finish({
                unresolved_template_candidate
                    ? UnevaluatedCallResolutionStatus::StillDependent
                    : UnevaluatedCallResolutionStatus::SubstitutionFailure});
        }

        std::vector<ExprResult> ranking = arguments;
        if (member_object_leading) {
            ranking.insert(ranking.begin(), std::move(object));
        }
        bool ambiguous = false;
        cir::EntityId selected = select_overload(
            candidates,
            ranking,
            member_object_leading,
            &ambiguous);
        if (!selected.valid() || !file_.valid(selected)) {
            return finish({
                UnevaluatedCallResolutionStatus::SubstitutionFailure});
        }
        cir::TypeId selected_function_type =
            file_.resolved_type(file_.entity(selected).type);
        const auto* selected_function =
            file_.valid(selected_function_type)
                ? std::get_if<cir::FunctionTypePayload>(
                      &file_.type_payload(selected_function_type))
                : nullptr;
        if (selected_function &&
            contains_auto_type(selected_function->return_type.type) &&
            !require_placeholder_result(
                selected,
                cir::InstantiationDemandKind::ResultType,
                loc)) {

            return finish({
                UnevaluatedCallResolutionStatus::HardError});
        }
        cir::TypeId function_type =
            file_.resolved_type(file_.entity(selected).type);
        const auto* function = file_.valid(function_type)
            ? std::get_if<cir::FunctionTypePayload>(
                  &file_.type_payload(function_type))
            : nullptr;
        if (!function || !function->return_type.type.valid()) {
            return finish({
                UnevaluatedCallResolutionStatus::SubstitutionFailure});
        }
        cir::TypeRef return_type = function->return_type;
        if (dependent_type(return_type.type) ||
            contains_auto_type(return_type.type)) {
            return finish({
                UnevaluatedCallResolutionStatus::StillDependent});
        }
        cir::TypeId resolved_return = file_.resolved_type(return_type.type);
        NodeResolution call{
            UnevaluatedCallResolutionStatus::Resolved,
            return_type,
            ValueCategory::PrValue,
            return_type};
        if (file_.valid(resolved_return) &&
            (file_.type(resolved_return).kind ==
                 cir::TypeKind::LValueReference ||
             file_.type(resolved_return).kind ==
                 cir::TypeKind::RValueReference)) {
            call.expression_type =
                file_.reference_referred_ref(resolved_return);
            call.category = file_.type(resolved_return).kind ==
                    cir::TypeKind::LValueReference
                ? ValueCategory::LValue
                : ValueCategory::XValue;
        }
        node.result_type = return_type;
        call.exception_state_known = subexpressions_exception_known &&
            function->exception_spec.kind !=
                cir::FunctionExceptionSpecKind::Dependent;
        call.potentially_throwing = subexpressions_potentially_throw ||
            function->exception_spec.kind !=
                cir::FunctionExceptionSpecKind::NonThrowing;
        auto selected_call = std::find_if(
            result.selected_calls.begin(),
            result.selected_calls.end(),
            [&](const UnevaluatedCallResolution::SelectedCall& entry) {
                return entry.node == index;
            });
        UnevaluatedCallResolution::SelectedCall selection{
            index, selected, member_object_leading};
        if (selected_call == result.selected_calls.end()) {
            result.selected_calls.push_back(selection);
        } else {
            *selected_call = selection;
        }
        return finish(std::move(call));
    };

    NodeResolution root = resolve_node(result.expression.root, 0);
    result.status = root.status;
    if (root.status == UnevaluatedCallResolutionStatus::Resolved) {
        result.type = root.decltype_type;
    }
    file_.canonicalize_template_value_expression(result.expression);
    if (root.status == UnevaluatedCallResolutionStatus::Resolved ||
        root.status == UnevaluatedCallResolutionStatus::StillDependent ||
        root.status == UnevaluatedCallResolutionStatus::HardError) {
        transaction.commit();
    }
    return result;
}

std::optional<ExprResult>
Session::materialize_resolved_template_value_expression(
    const UnevaluatedCallResolution& resolution,
    std::string* error_out) {
    auto set_error = [&](std::string message) {
        if (error_out && error_out->empty()) {
            *error_out = std::move(message);
        }
    };
    const cir::TemplateValueExpression& expression = resolution.expression;
    if (resolution.status != UnevaluatedCallResolutionStatus::Resolved ||
        !expression.valid()) {
        set_error(
            "dependent call expression is not fully resolved");
        return std::nullopt;
    }

    auto selection_for = [&](uint32_t node)
        -> const UnevaluatedCallResolution::SelectedCall* {
        auto found = std::find_if(
            resolution.selected_calls.begin(),
            resolution.selected_calls.end(),
            [&](const UnevaluatedCallResolution::SelectedCall& entry) {
                return entry.node == node;
            });
        return found == resolution.selected_calls.end() ? nullptr : &*found;
    };
    auto name_for = [&](const cir::TemplateValueExprNode& node,
                        cir::EntityId fallback) {
        if (node.name.valid() && file_.valid(node.name)) {
            return std::string(file_.name(node.name));
        }
        if (fallback.valid() && file_.valid(fallback) &&
            file_.entity(fallback).name.valid()) {
            return std::string(file_.name(file_.entity(fallback).name));
        }
        return node.semantic_key;
    };
    auto callee_has_flag = [](const cir::TemplateValueExprNode& node,
                              cir::TemplateCalleeFlag flag) {
        return (static_cast<uint64_t>(node.value) &
                static_cast<uint32_t>(flag)) != 0;
    };
    auto unary_operator = [](cir::TemplateValueExprOp op)
        -> std::optional<syntax::UnaryOperator> {
        switch (op) {
            case cir::TemplateValueExprOp::UnaryPlus:
                return syntax::UnaryOperator::Plus;
            case cir::TemplateValueExprOp::UnaryMinus:
                return syntax::UnaryOperator::Minus;
            case cir::TemplateValueExprOp::LogicalNot:
                return syntax::UnaryOperator::LogicalNot;
            case cir::TemplateValueExprOp::BitwiseNot:
                return syntax::UnaryOperator::BitwiseNot;
            case cir::TemplateValueExprOp::Dereference:
                return syntax::UnaryOperator::Dereference;
            case cir::TemplateValueExprOp::AddressOf:
                return syntax::UnaryOperator::AddressOf;
            case cir::TemplateValueExprOp::Delete:
            case cir::TemplateValueExprOp::DeleteArray:
            default:
                return std::nullopt;
        }
    };
    auto binary_operator = [](cir::TemplateValueExprOp op)
        -> std::optional<syntax::BinaryOperator> {
        switch (op) {
            case cir::TemplateValueExprOp::Add:
                return syntax::BinaryOperator::Add;
            case cir::TemplateValueExprOp::Sub:
                return syntax::BinaryOperator::Sub;
            case cir::TemplateValueExprOp::Mul:
                return syntax::BinaryOperator::Mul;
            case cir::TemplateValueExprOp::Div:
                return syntax::BinaryOperator::Div;
            case cir::TemplateValueExprOp::Mod:
                return syntax::BinaryOperator::Mod;
            case cir::TemplateValueExprOp::Less:
                return syntax::BinaryOperator::Less;
            case cir::TemplateValueExprOp::LessEqual:
                return syntax::BinaryOperator::LessEqual;
            case cir::TemplateValueExprOp::Greater:
                return syntax::BinaryOperator::Greater;
            case cir::TemplateValueExprOp::GreaterEqual:
                return syntax::BinaryOperator::GreaterEqual;
            case cir::TemplateValueExprOp::Equal:
                return syntax::BinaryOperator::Equal;
            case cir::TemplateValueExprOp::NotEqual:
                return syntax::BinaryOperator::NotEqual;
            case cir::TemplateValueExprOp::ThreeWay:
                return syntax::BinaryOperator::ThreeWay;
            case cir::TemplateValueExprOp::LogicalAnd:
                return syntax::BinaryOperator::LogicalAnd;
            case cir::TemplateValueExprOp::LogicalOr:
                return syntax::BinaryOperator::LogicalOr;
            case cir::TemplateValueExprOp::BitAnd:
                return syntax::BinaryOperator::BitAnd;
            case cir::TemplateValueExprOp::BitOr:
                return syntax::BinaryOperator::BitOr;
            case cir::TemplateValueExprOp::BitXor:
                return syntax::BinaryOperator::BitXor;
            case cir::TemplateValueExprOp::Shl:
                return syntax::BinaryOperator::Shl;
            case cir::TemplateValueExprOp::Shr:
                return syntax::BinaryOperator::Shr;
            case cir::TemplateValueExprOp::MemberPointerDot:
                return syntax::BinaryOperator::PtrMemDot;
            case cir::TemplateValueExprOp::MemberPointerArrow:
                return syntax::BinaryOperator::PtrMemArrow;
            case cir::TemplateValueExprOp::Comma:
                return syntax::BinaryOperator::Comma;
            default:
                return std::nullopt;
        }
    };

    std::vector<uint8_t> visiting(expression.nodes.size(), 0);
    std::function<std::optional<ExprResult>(uint32_t, size_t)> materialize;
    materialize = [&](uint32_t index,
                      size_t depth) -> std::optional<ExprResult> {
        if (depth > 128 || index >= expression.nodes.size() ||
            visiting[index] != 0) {
            set_error(
                "resolved dependent call expression graph is malformed");
            return std::nullopt;
        }
        visiting[index] = 1;
        auto finish = [&](std::optional<ExprResult> result) {
            visiting[index] = 0;
            return result;
        };

        const cir::TemplateValueExprNode& node = expression.nodes[index];
        SrcLoc loc = expression.loc;
        if (node.kind == cir::TemplateValueExprKind::Integer) {
            cir::TypeId type = node.result_type.type.valid()
                ? node.result_type.type
                : builder_.int_type();
            ExprResult result = is_bool_type(type)
                ? make_boolean_literal(!node.integer_value.is_zero(),
                                       !node.integer_value.is_zero()
                                           ? "true"
                                           : "false",
                                       loc)
                : make_integer_literal(node.integer_value,
                                       node.integer_value.decimal(),
                                       type,
                                       loc);
            return finish(std::move(result));
        }
        if (node.kind == cir::TemplateValueExprKind::Entity ||
            (node.kind == cir::TemplateValueExprKind::TypeOperand &&
             node.lhs == cir::TemplateValueExprNoNode &&
             node.entity.valid())) {
            if (!node.entity.valid() || !file_.valid(node.entity)) {
                set_error(
                    "resolved dependent call operand has no concrete entity");
                return finish(std::nullopt);
            }
            return finish(make_entity_reference(
                node.entity,
                name_for(node, node.entity),
                loc,
                /*qualified_name=*/true));
        }
        if (node.kind == cir::TemplateValueExprKind::TypeOperand) {
            cir::TemplateCalleeFlag operand_flags =
                static_cast<cir::TemplateCalleeFlag>(node.value);
            bool member_access =
                (static_cast<uint32_t>(operand_flags) &
                 static_cast<uint32_t>(
                     cir::TemplateCalleeFlag::MemberAccess)) != 0;
            if (member_access) {
                if (node.lhs == cir::TemplateValueExprNoNode ||
                    !node.name.valid() || !file_.valid(node.name)) {
                    set_error(
                        "resolved dependent member operand is incomplete");
                    return finish(std::nullopt);
                }
                std::optional<ExprResult> base =
                    materialize(node.lhs, depth + 1);
                if (!base.has_value()) {
                    return finish(std::nullopt);
                }
                bool member_arrow =
                    (static_cast<uint32_t>(operand_flags) &
                     static_cast<uint32_t>(
                         cir::TemplateCalleeFlag::MemberArrow)) != 0;
                ExprResult result = node.qualifier_type.type.valid()
                    ? collect_qualified_member_access_expr(
                          std::move(*base),
                          node.qualifier_type.type,
                          file_.name(node.name),
                          member_arrow,
                          loc)
                    : collect_member_access_expr(
                          std::move(*base),
                          file_.name(node.name),
                          member_arrow,
                          loc);
                if (result.has_error) {
                    set_error(
                        "resolved dependent member operand is invalid");
                    return finish(std::nullopt);
                }
                return finish(std::move(result));
            }
            if (node.qualifier_type.type.valid() &&
                node.name.valid()) {
                cir::TypeId qualifier =
                    file_.resolved_type(node.qualifier_type.type);
                if (!file_.valid(qualifier) ||
                    file_.type(qualifier).kind !=
                        cir::TypeKind::Record ||
                    is_dependent_type(qualifier)) {
                    set_error(
                        "resolved dependent qualified operand has no concrete class");
                    return finish(std::nullopt);
                }
                cir::EntityId record = file_.record_entity(qualifier);
                if (!record.valid() || !file_.valid(record) ||
                    !file_.entity(record).semantic_context.valid()) {
                    set_error(
                        "resolved dependent qualified operand has no lookup context");
                    return finish(std::nullopt);
                }
                ExprResult qualified = lookup_qualified_name(
                    file_.entity(record).semantic_context,
                    file_.name(node.name),
                    loc);
                if (qualified.has_error) {
                    set_error(
                        "resolved dependent qualified operand lookup failed");
                    return finish(std::nullopt);
                }
                return finish(std::move(qualified));
            }
            if (node.lhs == cir::TemplateValueExprNoNode) {
                set_error(
                    "resolved dependent call operand has no retained value");
                return finish(std::nullopt);
            }
            return finish(materialize(node.lhs, depth + 1));
        }
        if (node.kind == cir::TemplateValueExprKind::Cast &&
            node.lhs != cir::TemplateValueExprNoNode &&
            node.type.valid()) {
            std::optional<ExprResult> operand =
                materialize(node.lhs, depth + 1);
            if (!operand.has_value()) {
                return finish(std::nullopt);
            }
            ExprResult result =
                collect_cast_expr(node.type, std::move(*operand), loc);
            if (result.has_error) {
                set_error(
                    "resolved dependent call cast could not be materialized");
                return finish(std::nullopt);
            }
            return finish(std::move(result));
        }
        if (node.kind == cir::TemplateValueExprKind::Unary &&
            node.lhs != cir::TemplateValueExprNoNode) {
            if (node.op == cir::TemplateValueExprOp::Delete ||
                node.op == cir::TemplateValueExprOp::DeleteArray) {
                std::optional<ExprResult> operand =
                    materialize(node.lhs, depth + 1);
                if (!operand.has_value()) {
                    set_error(
                        "resolved dependent delete operand is unavailable");
                    return finish(std::nullopt);
                }
                DeleteExpressionInput input;
                input.pointer = std::move(*operand);
                input.is_array =
                    node.op == cir::TemplateValueExprOp::DeleteArray;
                ExprResult result = collect_delete_expr(
                    std::move(input), loc);
                if (result.has_error) {
                    set_error(
                        "resolved dependent delete expression is invalid");
                    return finish(std::nullopt);
                }
                return finish(std::move(result));
            }
            std::optional<syntax::UnaryOperator> op =
                unary_operator(node.op);
            std::optional<ExprResult> operand =
                materialize(node.lhs, depth + 1);
            if (!op.has_value() || !operand.has_value()) {
                set_error(
                    "resolved dependent unary expression is unsupported");
                return finish(std::nullopt);
            }
            ExprResult result =
                collect_unary_expr(*op, std::move(*operand), loc);
            if (result.has_error) {
                return finish(std::nullopt);
            }
            return finish(std::move(result));
        }
        if (node.kind == cir::TemplateValueExprKind::Binary &&
            node.lhs != cir::TemplateValueExprNoNode &&
            node.rhs != cir::TemplateValueExprNoNode) {
            std::optional<syntax::BinaryOperator> op =
                binary_operator(node.op);
            std::optional<ExprResult> lhs =
                materialize(node.lhs, depth + 1);
            std::optional<ExprResult> rhs =
                materialize(node.rhs, depth + 1);
            if (!op.has_value() || !lhs.has_value() || !rhs.has_value()) {
                set_error(
                    "resolved dependent binary expression is unsupported");
                return finish(std::nullopt);
            }
            ExprResult result = collect_binary_expr(
                *op, std::move(*lhs), std::move(*rhs), loc);
            if (result.has_error) {
                return finish(std::nullopt);
            }
            return finish(std::move(result));
        }
        if (node.kind == cir::TemplateValueExprKind::Conditional &&
            node.lhs != cir::TemplateValueExprNoNode &&
            node.rhs != cir::TemplateValueExprNoNode &&
            node.third != cir::TemplateValueExprNoNode) {
            std::optional<ExprResult> condition =
                materialize(node.lhs, depth + 1);
            std::optional<ExprResult> true_operand =
                materialize(node.rhs, depth + 1);
            std::optional<ExprResult> false_operand =
                materialize(node.third, depth + 1);
            if (!condition.has_value() || !true_operand.has_value() ||
                !false_operand.has_value()) {
                return finish(std::nullopt);
            }
            ExprResult result = collect_conditional_expr(
                std::move(*condition),
                std::optional<ExprResult>(std::move(*true_operand)),
                std::move(*false_operand),
                loc);
            if (result.has_error) {
                return finish(std::nullopt);
            }
            return finish(std::move(result));
        }
        if (node.kind == cir::TemplateValueExprKind::SizeofType &&
            node.type.valid()) {
            ExprResult result = collect_sizeof_type(node.type, loc);
            return result.has_error
                ? finish(std::nullopt)
                : finish(std::move(result));
        }
        if (node.kind == cir::TemplateValueExprKind::AlignofType &&
            node.type.valid()) {
            ExprResult result = collect_alignof_type(node.type, loc);
            return result.has_error
                ? finish(std::nullopt)
                : finish(std::move(result));
        }
        if (node.kind == cir::TemplateValueExprKind::Call &&
            node.third != cir::TemplateValueExprNoNode &&
            node.third < expression.nodes.size()) {
            const cir::TemplateValueExprNode& target =
                expression.nodes[node.third];
            if (target.kind != cir::TemplateValueExprKind::Callee) {
                set_error(
                    "resolved dependent call has no canonical callee");
                return finish(std::nullopt);
            }

            std::vector<ExprResult> arguments;
            std::unordered_set<uint32_t> argument_nodes;
            for (uint32_t current = node.lhs;
                 current != cir::TemplateValueExprNoNode;) {
                if (current >= expression.nodes.size() ||
                    !argument_nodes.insert(current).second ||
                    expression.nodes[current].kind !=
                        cir::TemplateValueExprKind::TypeOperand) {
                    set_error(
                        "resolved dependent call argument list is malformed");
                    return finish(std::nullopt);
                }
                std::optional<ExprResult> argument =
                    materialize(current, depth + 1);
                if (!argument.has_value()) {
                    return finish(std::nullopt);
                }
                arguments.push_back(std::move(*argument));
                current = expression.nodes[current].rhs;
            }

            const UnevaluatedCallResolution::SelectedCall* selection =
                selection_for(index);
            ExprResult callee;
            if (target.lhs != cir::TemplateValueExprNoNode) {
                std::optional<ExprResult> callable =
                    materialize(target.lhs, depth + 1);
                if (!callable.has_value()) {
                    return finish(std::nullopt);
                }
                callee = std::move(*callable);
                if (selection && selection->has_implicit_object) {
                    callee = collect_resolved_member_function_access_expr(
                        std::move(callee),
                        selection->entity,
                        "operator()",
                        /*is_arrow=*/false,
                        loc);
                }
            } else if (target.rhs != cir::TemplateValueExprNoNode) {
                if (!selection || !selection->entity.valid()) {
                    set_error(
                        "resolved member call has no selected method");
                    return finish(std::nullopt);
                }
                std::optional<ExprResult> base =
                    materialize(target.rhs, depth + 1);
                if (!base.has_value()) {
                    return finish(std::nullopt);
                }
                std::string member_name =
                    name_for(target, selection->entity);
                bool is_arrow = callee_has_flag(
                    target, cir::TemplateCalleeFlag::MemberArrow);
                if (target.qualifier_type.type.valid()) {
                    callee = collect_qualified_member_access_expr(
                        std::move(*base),
                        target.qualifier_type.type,
                        member_name,
                        is_arrow,
                        loc,
                        {selection->entity});
                } else {
                    callee = collect_resolved_member_function_access_expr(
                        std::move(*base),
                        selection->entity,
                        member_name,
                        is_arrow,
                        loc);
                }
            } else {
                cir::EntityId entity = selection
                    ? selection->entity
                    : target.entity;
                if (!entity.valid() || !file_.valid(entity)) {
                    set_error(
                        "resolved dependent call has no selected function");
                    return finish(std::nullopt);
                }
                callee = make_entity_reference(
                    entity,
                    name_for(target, entity),
                    loc,
                    callee_has_flag(
                        target, cir::TemplateCalleeFlag::QualifiedName));
            }
            if (callee.has_error) {
                return finish(std::nullopt);
            }
            ExprResult result =
                collect_call_expr(std::move(callee),
                                  std::move(arguments),
                                  loc);
            if (result.has_error) {
                set_error(
                    "resolved dependent call could not be materialized");
                return finish(std::nullopt);
            }
            return finish(std::move(result));
        }

        set_error(
            "resolved dependent value expression contains an unsupported node");
        return finish(std::nullopt);
    };

    return materialize(expression.root, 0);
}

bool Session::append_substituted_template_argument(
    const TemplateArgument& argument,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks,
    std::vector<TemplateArgument>& destination,
    bool reject_unresolved_template_parameter,
    std::string* error_out) {
    if (argument.generated_pack_kind !=
        cir::TemplateGeneratedPackKind::None) {
        return append_substituted_generated_pack(
            argument,
            argument_bindings,
            callbacks,
            destination,
            reject_unresolved_template_parameter,
            error_out);
    }
    if (argument.expands_pack_pattern) {
        switch (expand_template_argument_pack_pattern(argument,
                                                      argument_bindings,
                                                      callbacks,
                                                      &destination)) {
            case PackPatternExpansionStatus::Expanded:
                return true;
            case PackPatternExpansionStatus::StillDependent:
                destination.push_back(argument);
                return true;
            case PackPatternExpansionStatus::LengthMismatch:
                if (error_out && error_out->empty()) {
                    *error_out =
                        "pack expansion contains packs with different lengths";
                }
                return false;
            default:
                return false;
        }
    }
    if (argument.expands_parameter_pack) {
        uint32_t pack_index = cir::ArrayTypePayload::no_extent_param;
        cir::TemplateArgumentKind expected_kind = argument.kind;
        const TemplateArgumentBinding* binding = nullptr;
        if (template_argument_is_type(argument)) {
            cir::TypeId pack_type = file_.resolved_type(argument.type.type);
            if (!file_.valid(pack_type) ||
                file_.type(pack_type).kind != cir::TypeKind::TypeParam) {
                return false;
            }
            const auto pack =
                std::get<cir::TypeParamTypePayload>(
                    file_.type_payload(pack_type));
            if (!pack.is_parameter_pack) {
                return false;
            }
            pack_index = pack.index;
            auto exact = callbacks.exact_type_parameter_bindings.find(
                static_cast<uint32_t>(pack_type.index));
            if (exact != callbacks.exact_type_parameter_bindings.end()) {
                binding = &exact->second;
            } else if (
                callbacks.exact_type_parameter_bindings_are_authoritative) {

                callbacks.deferred_on_enclosing_type_pack = true;
                return false;
            }
        } else if (template_argument_is_value(argument)) {
            pack_index = argument.value_param_index;
            if (argument.value_entity.valid()) {
                auto exact = callbacks.exact_value_parameter_bindings.find(
                    static_cast<uint32_t>(argument.value_entity.index));
                if (exact != callbacks.exact_value_parameter_bindings.end()) {
                    binding = &exact->second;
                }
            }
        } else if (argument.kind == cir::TemplateArgumentKind::Template) {
            pack_index = argument.template_param_index;
            if (argument.template_entity.valid()) {
                auto exact =
                    callbacks.exact_template_parameter_bindings.find(
                        static_cast<uint32_t>(
                            argument.template_entity.index));
                if (exact !=
                    callbacks.exact_template_parameter_bindings.end()) {
                    binding = &exact->second;
                }
            }
        } else {
            return false;
        }
        if (!binding &&
            pack_index != cir::ArrayTypePayload::no_extent_param) {
            binding = substitution_binding(argument_bindings, pack_index);
        }
        if (!binding || !binding->is_pack()) {
            return false;
        }
        for (const TemplateArgument& bound : binding->arguments) {
            if (bound.kind != expected_kind) {
                return false;
            }

            destination.push_back(bound);
        }
        return true;
    }

    TemplateArgument out = argument;
    if (template_argument_is_type(argument)) {

        const bool saved_materialization =
            callbacks.materialize_type_template_definition;
        callbacks.materialize_type_template_definition = false;
        cir::TypeRef substituted = substitute_pattern_type_ref(
            argument.type, argument_bindings, callbacks);
        callbacks.materialize_type_template_definition =
            saved_materialization;
        if (!substituted.valid()) {
            return false;
        }
        out.type = substituted;
        out.is_dependent = is_dependent_type(substituted.type);
    } else if (template_argument_is_value(argument)) {
        if (!substitute_template_value_argument(
                out, argument_bindings, callbacks, error_out)) {
            return false;
        }
        if (reject_unresolved_template_parameter && out.is_dependent) {
            return false;
        }
    } else if (argument.kind == cir::TemplateArgumentKind::Template) {
        if (!substitute_template_template_argument(
                out, argument_bindings, callbacks, error_out)) {
            return false;
        }
        if (reject_unresolved_template_parameter &&
            out.template_entity.valid() &&
            file_.valid(out.template_entity) &&
            file_.entity(out.template_entity).kind ==
                cir::EntityKind::TemplateParam) {
            return false;
        }
    }
    destination.push_back(std::move(out));
    return true;
}

cir::TypeId Session::substitute_pattern_type(
    cir::TypeId type,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks& callbacks,
    cir::TypeRef* complete_type) {
    if (!type.valid() || !file_.valid(type)) {
        return type;
    }
    if (file_.type(type).kind ==
        cir::TypeKind::AliasSpecialization) {
        const auto specialization =
            std::get<cir::AliasSpecializationTypePayload>(
                file_.type_payload(type));
        std::vector<TemplateArgument> arguments;
        arguments.reserve(specialization.arguments.size());
        for (const TemplateArgument& argument :
             specialization.arguments) {
            if (!append_substituted_template_argument(
                    argument,
                    argument_bindings,
                    callbacks,
                    arguments,
                    /*reject_unresolved_template_parameter=*/false)) {
                return {};
            }
        }
        if (!specialization.alias_template.valid() ||
            !file_.valid(specialization.alias_template) ||
            !callbacks.instantiate_type_template) {
            return {};
        }
        cir::TypeRef instantiated =
            callbacks.instantiate_type_template(
                specialization.alias_template,
                std::move(arguments),
                callbacks.point_lookup_generation,
                callbacks.materialize_type_template_definition,
                callbacks.argument_completion_mode);
        if (!instantiated.valid()) {
            return {};
        }
        if (complete_type) {
            *complete_type = instantiated;
        }
        return instantiated.type;
    }
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return type;
    }

    if (callbacks.self_pattern_type.valid() &&
        resolved == callbacks.self_pattern_type) {
        return callbacks.self_instance_type;
    }
    cir::TypeKind kind = file_.type(resolved).kind;
    if (kind == cir::TypeKind::Dependent) {
        return {};
    }

    if (!callbacks.self_pattern_type.valid() &&
        !type_contains_type_param(resolved) &&
        !type_contains_dependent_alias_specialization(type)) {
        return type;
    }
    switch (kind) {
        case cir::TypeKind::TypeParam: {
            const auto param =
                std::get<cir::TypeParamTypePayload>(file_.type_payload(resolved));
            const TemplateArgument* argument = nullptr;
            auto exact = callbacks.exact_type_parameter_bindings.find(
                static_cast<uint32_t>(resolved.index));
            if (exact != callbacks.exact_type_parameter_bindings.end()) {
                const TemplateArgumentBinding& binding = exact->second;
                if (binding.is_single() && binding.arguments.size() == 1) {
                    argument = &binding.arguments.front();
                }
            } else if (
                callbacks.exact_type_parameter_bindings_are_authoritative) {
                return type;
            } else {
                argument = single_substitution_argument(
                    argument_bindings,
                    param.index,
                    param.is_parameter_pack &&
                        callbacks.allow_parameter_pack_element_substitution);
            }
            if (param.is_parameter_pack &&
                !callbacks.allow_parameter_pack_element_substitution) {
                return {};
            }
            if (!argument || !template_argument_is_type(*argument)) {
                return {};
            }
            return argument->type.type;
        }
        case cir::TypeKind::BuiltinPackElement: {
            const auto& pack_element =
                std::get<cir::BuiltinPackElementTypePayload>(
                    file_.type_payload(resolved));
            return substitute_builtin_pack_element_type(
                       pack_element, argument_bindings, callbacks)
                .type;
        }
        case cir::TypeKind::PackIndex: {
            const auto pack_index = std::get<cir::PackIndexTypePayload>(
                file_.type_payload(resolved));
            cir::TypeId source_pack =
                file_.resolved_type(pack_index.pack_type.type);
            const auto* parameter = file_.valid(source_pack)
                ? std::get_if<cir::TypeParamTypePayload>(
                      &file_.type_payload(source_pack))
                : nullptr;
            if (!parameter || !parameter->is_parameter_pack) {
                return {};
            }

            std::vector<cir::TypeRef> expansions;
            if (pack_index.fully_substituted) {
                expansions.reserve(pack_index.expansions.size());
                for (cir::TypeRef expansion : pack_index.expansions) {
                    cir::TypeRef substituted = substitute_pattern_type_ref(
                        expansion, argument_bindings, callbacks);
                    expansions.push_back(substituted.valid()
                                             ? substituted
                                             : expansion);
                }
            } else {
                const TemplateArgumentBinding* binding = nullptr;
                auto exact = callbacks.exact_type_parameter_bindings.find(
                    static_cast<uint32_t>(source_pack.index));
                if (exact != callbacks.exact_type_parameter_bindings.end()) {
                    binding = &exact->second;
                } else {
                    binding = substitution_binding(argument_bindings,
                                                   parameter->index);
                }
                if (!binding || !binding->is_pack()) {
                    return {};
                }
                expansions.reserve(binding->arguments.size());
                for (const TemplateArgument& argument : binding->arguments) {
                    if (!template_argument_is_type(argument) ||
                        !argument.type.valid()) {
                        return {};
                    }
                    expansions.push_back(argument.type);
                }
            }

            TemplateArgument index_argument;
            index_argument.kind = cir::TemplateArgumentKind::Value;
            index_argument.value_type = type_ref(builder_.usize_type());
            index_argument.dependent_value_expr =
                pack_index.index_expression;
            index_argument.is_dependent = true;
            if (!substitute_template_value_argument(index_argument,
                                                    argument_bindings,
                                                    callbacks)) {
                return {};
            }
            if (!index_argument.is_dependent &&
                (index_argument.value_kind == cir::TemplateValueKind::Integer ||
                 index_argument.value_kind == cir::TemplateValueKind::Boolean)) {
                std::optional<uint64_t> selected =
                    index_argument.integer_value.try_as_uint64();
                if (!selected.has_value() ||
                    *selected >= expansions.size()) {
                    return {};
                }
                return expansions[static_cast<size_t>(*selected)]
                    .type;
            }
            if (!index_argument.dependent_value_expr.valid()) {
                return {};
            }
            return file_.pack_index_type(
                pack_index.pack_type,
                std::move(index_argument.dependent_value_expr),
                std::move(expansions),
                true);
        }
        case cir::TypeKind::TemplateSpecialization: {
            const auto specialization =
                std::get<cir::TemplateSpecializationTypePayload>(
                    file_.type_payload(resolved));
            std::vector<TemplateArgument> arguments;
            arguments.reserve(specialization.arguments.size());
            for (const TemplateArgument& argument :
                 specialization.arguments) {
                if (!append_substituted_template_argument(
                        argument,
                        argument_bindings,
                        callbacks,
                        arguments,
                        /*reject_unresolved_template_parameter=*/false)) {
                    return {};
                }
            }
            cir::EntityId primary = specialization.primary_template;
            cir::TemplateValueExpression splice_operand =
                specialization.splice_operand;
            bool designator_is_dependent = false;
            if (splice_operand.valid()) {
                std::optional<uint32_t> parameter =
                    direct_value_parameter(splice_operand);
                if (!parameter.has_value()) {
                    return {};
                }
                const TemplateArgument* reflected =
                    single_substitution_argument(argument_bindings,
                                                 *parameter);
                if (!reflected ||
                    reflected->kind != cir::TemplateArgumentKind::Value) {
                    return {};
                }
                if (!reflected->is_dependent &&
                    reflected->value_kind ==
                        cir::TemplateValueKind::MetaInfo &&
                    reflected->meta_kind == cir::MetaInfoKind::Template &&
                    reflected->value_entity.valid() &&
                    file_.valid(reflected->value_entity)) {
                    primary = reflected->value_entity;
                    splice_operand = {};
                } else if (reflected->is_dependent &&
                           reflected->dependent_value_expr.valid()) {
                    splice_operand = reflected->dependent_value_expr;
                    designator_is_dependent = true;
                } else if (reflected->is_dependent &&
                           reflected->value_param_index !=
                               cir::ArrayTypePayload::no_extent_param) {
                    cir::TemplateValueExprNode node;
                    node.kind = cir::TemplateValueExprKind::Parameter;
                    node.parameter_index = reflected->value_param_index;
                    node.result_type = reflected->value_type;
                    splice_operand = {};
                    splice_operand.nodes.push_back(std::move(node));
                    splice_operand.root = 0;
                    designator_is_dependent = true;
                } else {
                    return {};
                }
            }

            bool arguments_are_dependent = std::any_of(
                arguments.begin(),
                arguments.end(),
                [&](const TemplateArgument& argument) {
                    if (template_argument_is_type(argument)) {
                        return argument.type.type.valid() &&
                            (is_dependent_type(argument.type.type) ||
                             type_contains_dependent_alias_specialization(
                                 argument.type.type));
                    }
                    if (template_argument_is_value(argument)) {
                        return argument.is_dependent;
                    }
                    return argument.is_dependent ||
                        (argument.template_entity.valid() &&
                         file_.valid(argument.template_entity) &&
                         file_.entity(argument.template_entity).kind ==
                             cir::EntityKind::TemplateParam);
                });
            if (designator_is_dependent || arguments_are_dependent) {
                return file_.template_specialization_type(
                    specialization.template_name,
                    primary,
                    std::move(arguments),
                    /*is_dependent=*/true,
                    specialization.is_class_template_placeholder,
                    std::move(splice_operand));
            }
            if (!primary.valid() || !file_.valid(primary) ||
                !callbacks.instantiate_type_template) {
                return {};
            }
            cir::TypeRef instantiated =
                callbacks.instantiate_type_template(primary,
                                                    std::move(arguments),
                                                    callbacks.point_lookup_generation,
                                                    callbacks.materialize_type_template_definition,
                                                    callbacks.argument_completion_mode);
            if (complete_type) {
                *complete_type = instantiated;
            }
            return instantiated.type;
        }
        case cir::TypeKind::DependentName: {
            const auto dependent =
                std::get<cir::DependentNameTypePayload>(
                    file_.type_payload(resolved));
            if (!dependent.qualifier_type.type.valid()) {
                return {};
            }
            cir::TypeRef qualifier = substitute_pattern_type_ref(
                dependent.qualifier_type, argument_bindings, callbacks);
            if (!qualifier.valid()) {
                return {};
            }
            std::vector<TemplateArgument> member_arguments;
            member_arguments.reserve(dependent.template_arguments.size());
            for (const TemplateArgument& argument :
                 dependent.template_arguments) {
                if (!append_substituted_template_argument(
                        argument,
                        argument_bindings,
                        callbacks,
                        member_arguments,
                        /*reject_unresolved_template_parameter=*/false)) {
                    return {};
                }
            }

            cir::TypeId resolved_qualifier =
                file_.resolved_type(qualifier.type);
            cir::EntityId qualifier_record =
                file_.valid(resolved_qualifier) &&
                    file_.type(resolved_qualifier).kind ==
                        cir::TypeKind::Record
                ? file_.record_entity(resolved_qualifier)
                : cir::EntityId{};
            cir::EntityId qualifier_primary = qualifier_record;
            if (const cir::TemplateSpecializationFact* specialization =
                    qualifier_record.valid()
                    ? file_.template_specialization(qualifier_record)
                    : nullptr;
                specialization && specialization->template_entity.valid()) {
                qualifier_primary = specialization->template_entity;
            }
            bool same_staged_primary =
                qualifier_primary.valid() &&
                callbacks.dependent_primary_record.valid() &&
                file_.valid(qualifier_primary) &&
                file_.valid(callbacks.dependent_primary_record) &&
                file_.entity(qualifier_primary).name ==
                    file_.entity(callbacks.dependent_primary_record).name &&
                file_.entity(qualifier_primary).parent ==
                    file_.entity(callbacks.dependent_primary_record).parent;
            bool qualifier_is_dependent_primary =
                callbacks.dependent_primary_record.valid() &&
                (qualifier_record == callbacks.dependent_primary_record ||
                 same_staged_primary);
            bool member_arity_is_dependent = std::any_of(
                member_arguments.begin(),
                member_arguments.end(),
                [](const TemplateArgument& argument) {
                    return argument.expands_parameter_pack ||
                        argument.expands_pack_pattern ||
                        argument.generated_pack_kind !=
                            cir::TemplateGeneratedPackKind::None;
                });
            if (is_dependent_type(qualifier.type) ||
                qualifier_is_dependent_primary ||
                member_arity_is_dependent) {

                return file_.dependent_name_type(
                    qualifier,
                    file_.name(dependent.member_name),
                    std::move(member_arguments),
                    dependent.is_current_instantiation);
            }
            if (!file_.valid(resolved_qualifier) ||
                file_.type(resolved_qualifier).kind != cir::TypeKind::Record) {
                return {};
            }
            cir::EntityId record = file_.record_entity(resolved_qualifier);
            if (!record.valid() || !file_.valid(record)) {
                return {};
            }
            const cir::RecordFacts* qualifier_facts =
                file_.record_facts(record);
            bool qualifier_replay_unavailable = false;
            if (!qualifier_facts || qualifier_facts->is_incomplete) {
                InstantiationDemandResult demand =
                    require_complete_class_type_result(
                        resolved_qualifier,
                        callbacks.access_loc,
                        cir::InstantiationDemandKind::BaseMemberList);
                const bool replay_owned_qualifier =
                    file_.template_specialization(record) != nullptr;
                if (demand != InstantiationDemandResult::Satisfied &&
                    replay_owned_qualifier) {
                    if (demand == InstantiationDemandResult::Failed) {
                        if (callbacks.replay_outcome) {
                            callbacks.replay_outcome->note_hard_error();
                        }
                        return {};
                    }

                    qualifier_replay_unavailable = true;
                }
            }
            auto unavailable_member = [&]() -> cir::TypeId {
                if (qualifier_replay_unavailable &&
                    callbacks.replay_outcome) {
                    if (callbacks.argument_completion_mode ==
                        TemplateArgumentCompletionMode::Candidate) {
                        callbacks.replay_outcome
                            ->note_substitution_failure();
                    } else {
                        callbacks.replay_outcome->note_unavailable(record);
                    }
                }
                return {};
            };
            cir::DeclContextId context = file_.entity(record).semantic_context;
            if (!context.valid()) {
                return unavailable_member();
            }
            if (!member_arguments.empty()) {
                if (!callbacks.instantiate_type_template) {
                    return unavailable_member();
                }
                const TemplateInfo* info = template_info_in_context(
                    context,
                    file_.name(dependent.member_name),
                    /*include_parents=*/false);
                if (!info ||
                    (!info->is_class_template && !info->is_alias_template)) {
                    return unavailable_member();
                }
                cir::TypeRef instantiated =
                    callbacks.instantiate_type_template(
                        info->entity,
                        std::move(member_arguments),
                        callbacks.point_lookup_generation,
                        callbacks.materialize_type_template_definition,
                        callbacks.argument_completion_mode);
                if (complete_type) {
                    *complete_type = instantiated;
                }
                return instantiated.type;
            }
            cir::TypeId named = lookup_qualified_type_name(
                context,
                file_.name(dependent.member_name));
            if (!named.valid()) {
                return unavailable_member();
            }
            MemberLookupResult lookup = lookup_member_name(
                resolved_qualifier,
                file_.name(dependent.member_name));
            cir::TypeId resolved_named = file_.resolved_type(named);
            for (const MemberLookupDeclaration& declaration :
                 lookup.declarations) {
                if (!declaration.designated_type.valid() ||
                    file_.resolved_type(declaration.designated_type.type) !=
                        resolved_named) {
                    continue;
                }
                AccessContext access_context = callbacks.has_explicit_access_context
                    ? AccessContext{{}, callbacks.access_record,
                                    callbacks.access_function, {}, true}
                    : current_access_context();
                AccessObligation member;
                member.kind = AccessObligationKind::Member;
                member.member = declaration.entity;
                member.access_owner = declaration.access_owner;
                member.declared_access = declaration.declared_access;
                member.declaring_class = declaration.declaring_class;
                member.captured_context = access_context;
                member.fixed_context = true;
                member.loc = callbacks.access_loc;
                // [temp.deduct]p8
                if (declaration.has_declared_access) {
                    if (capture_access_obligation(member)) {
                        return named;
                    }
                    if (!evaluate_access_obligation(member, access_context,
                                                    /*report=*/false)) {
                        if (callbacks.replay_outcome) {
                            callbacks.replay_outcome
                                ->note_substitution_failure();
                        }
                        return {};
                    }
                }
                AccessObligation base_access;
                base_access.kind = AccessObligationKind::MemberLookupBase;
                base_access.declaring_class = declaration.declaring_class;
                base_access.derived_type = resolved_qualifier;
                base_access.base_routes = declaration.base_paths;
                base_access.captured_context = access_context;
                base_access.fixed_context = true;
                base_access.loc = callbacks.access_loc;
                if (!capture_access_obligation(base_access) &&
                    !evaluate_access_obligation(base_access, access_context,
                                                /*report=*/false)) {
                    if (callbacks.replay_outcome) {
                        callbacks.replay_outcome->note_substitution_failure();
                    }
                    return {};
                }
                break;
            }
            return named;
        }
        case cir::TypeKind::Pointer: {
            const auto pointer =
                std::get<cir::PointerTypePayload>(file_.type_payload(resolved));
            cir::TypeRef pointee = substitute_pattern_type_ref(
                pointer.pointee, argument_bindings, callbacks);
            if (!pointee.valid()) {
                return {};
            }
            cir::TypeId resolved_pointee =
                file_.resolved_type(pointee.type);
            if (file_.valid(resolved_pointee) &&
                (file_.type(resolved_pointee).kind ==
                     cir::TypeKind::LValueReference ||
                 file_.type(resolved_pointee).kind ==
                     cir::TypeKind::RValueReference)) {
                return {};
            }
            return file_.pointer_type(pointee);
        }
        case cir::TypeKind::MemberPointer: {
            const auto member =
                std::get<cir::MemberPointerTypePayload>(
                    file_.type_payload(resolved));
            cir::TypeRef class_type = substitute_pattern_type_ref(
                member.class_type, argument_bindings, callbacks);
            cir::TypeRef member_type = substitute_pattern_type_ref(
                member.member_type, argument_bindings, callbacks);
            if (!class_type.valid() || !member_type.valid()) {
                return {};
            }
            cir::TypeId resolved_class =
                file_.resolved_type(class_type.type);
            if (!file_.valid(resolved_class) ||
                file_.type(resolved_class).kind != cir::TypeKind::Record) {
                return {};
            }
            return file_.member_pointer_type(class_type, member_type);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {
            const auto reference =
                std::get<cir::ReferenceTypePayload>(file_.type_payload(resolved));
            cir::TypeRef referred = substitute_pattern_type_ref(
                reference.referred_type, argument_bindings, callbacks);
            if (!referred.valid()) {
                return {};
            }
            cir::TypeId resolved_referred =
                file_.resolved_type(referred.type);
            if (file_.valid(resolved_referred) &&
                file_.type(resolved_referred).kind == cir::TypeKind::Builtin) {
                const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
                    &file_.type_payload(resolved_referred));
                if (builtin &&
                    builtin->kind == cir::BuiltinTypeKind::Void) {
                    return {};
                }
            }
            return file_.reference_type(referred, reference.reference_kind);
        }
        case cir::TypeKind::Array: {
            const auto array =
                std::get<cir::ArrayTypePayload>(file_.type_payload(resolved));
            cir::TypeRef element = substitute_pattern_type_ref(
                array.element_type, argument_bindings, callbacks);
            if (!element.valid()) {
                return {};
            }
            cir::TypeId resolved_element = file_.resolved_type(element.type);
            if (!file_.valid(resolved_element)) {
                return {};
            }
            cir::TypeKind element_kind = file_.type(resolved_element).kind;
            bool void_element = false;
            if (element_kind == cir::TypeKind::Builtin) {
                const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
                    &file_.type_payload(resolved_element));
                void_element = builtin &&
                    builtin->kind == cir::BuiltinTypeKind::Void;
            }
            if (void_element || element_kind == cir::TypeKind::Function ||
                element_kind == cir::TypeKind::LValueReference ||
                element_kind == cir::TypeKind::RValueReference) {
                return {};
            }
            if (array.extent_param != cir::ArrayTypePayload::no_extent_param) {
                const TemplateArgument* extent =
                    single_substitution_argument(argument_bindings,
                                                 array.extent_param);
                if (!extent || !template_argument_is_value(*extent)) {
                    return {};
                }
                std::optional<uint64_t> size =
                    extent->integer_value.try_as_uint64();
                if (!size.has_value()) {
                    return {};
                }
                return file_.array_type(
                    element, cir::ArraySizeKind::Constant,
                    static_cast<size_t>(*size));
            }
            if (array.dependent_size_expr.valid()) {
                TemplateArgument bound;
                bound.kind = cir::TemplateArgumentKind::Value;
                bound.value_type = type_ref(builder_.usize_type());
                bound.dependent_value_expr = array.dependent_size_expr;
                bound.is_dependent = true;
                if (!substitute_template_value_argument(bound,
                                                        argument_bindings,
                                                        callbacks)) {
                    return {};
                }
                if (!bound.is_dependent &&
                    (bound.value_kind == cir::TemplateValueKind::Integer ||
                     bound.value_kind == cir::TemplateValueKind::Boolean)) {
                    std::optional<uint64_t> size =
                        bound.integer_value.try_as_uint64();
                    if (!size.has_value()) {
                        return {};
                    }
                    return file_.array_type(
                        element,
                        cir::ArraySizeKind::Constant,
                        static_cast<size_t>(*size));
                }
                if (!bound.dependent_value_expr.valid()) {
                    return {};
                }
                return file_.array_type(
                    element,
                    cir::ArraySizeKind::Variable,
                    std::nullopt,
                    {},
                    true,
                    cir::ArrayTypePayload::no_extent_param,
                    std::move(bound.dependent_value_expr));
            }
            return file_.array_type(element,
                                    array.size_kind,
                                    array.size,
                                    array.size_expr,
                                    array.size_expr_is_dependent,
                                    cir::ArrayTypePayload::no_extent_param,
                                    array.dependent_size_expr);
        }
        case cir::TypeKind::Complex: {
            const auto complex_payload =
                std::get<cir::ComplexTypePayload>(file_.type_payload(resolved));
            cir::TypeRef element = substitute_pattern_type_ref(
                complex_payload.element_type, argument_bindings, callbacks);
            if (!element.valid()) {
                return {};
            }
            return file_.complex_type(element);
        }
        case cir::TypeKind::DecltypeExpr: {
            const auto decltype_payload =
                std::get<cir::DecltypeExprTypePayload>(
                    file_.type_payload(resolved));
            cir::TemplateValueExpression operand_expression =
                decltype_payload.operand_expression;
            if (operand_expression.valid()) {
                UnevaluatedCallResolution call =
                    resolve_unevaluated_call_expression(
                        std::move(operand_expression),
                        argument_bindings,
                        callbacks);
                if (call.status ==
                    UnevaluatedCallResolutionStatus::Resolved) {
                    if (decltype_payload.use_declared_type_rule &&
                        call.expression.root <
                            call.expression.nodes.size()) {
                        const cir::TemplateValueExprNode& root =
                            call.expression.nodes[call.expression.root];
                        bool member_access =
                            root.kind ==
                                cir::TemplateValueExprKind::TypeOperand &&
                            (static_cast<uint64_t>(root.value) &
                             static_cast<uint32_t>(
                                 cir::TemplateCalleeFlag::MemberAccess)) != 0;
                        if (member_access &&
                            root.result_type.type.valid()) {
                            return root.result_type.type;
                        }
                    }
                    return call.type.type;
                }
                if (call.status ==
                        UnevaluatedCallResolutionStatus::SubstitutionFailure ||
                    call.status ==
                        UnevaluatedCallResolutionStatus::HardError) {
                    return {};
                }
                operand_expression = std::move(call.expression);
            }
            auto substitute_ref = [&](cir::TypeRef ref)
                -> std::optional<cir::TypeRef> {
                if (!ref.type.valid()) {
                    return ref;
                }
                cir::TypeRef substituted = substitute_pattern_type_ref(
                    ref, argument_bindings, callbacks);
                if (!substituted.valid()) {
                    return std::nullopt;
                }
                return substituted;
            };

            std::optional<cir::TypeRef> substituted_operand =
                substitute_ref(decltype_payload.operand_type);
            if (!substituted_operand.has_value()) {
                if (decltype_payload.dependent_value_qualifier.type.valid() &&
                    decltype_payload.dependent_value_name.valid()) {
                    substituted_operand = cir::TypeRef{};
                } else if (operand_expression.valid()) {
                    substituted_operand = cir::TypeRef{};
                } else {
                    return {};
                }
            }
            std::optional<cir::TypeRef> substituted_qualifier =
                substitute_ref(decltype_payload.dependent_value_qualifier);
            if (!substituted_qualifier.has_value()) {
                return {};
            }

            cir::DecltypeOperandCategory category =
                decltype_payload.operand_category;
            cir::TypeRef operand_type = *substituted_operand;
            std::optional<DecltypeQualifiedValue> qualified_value;
            if (substituted_qualifier->type.valid() &&
                decltype_payload.dependent_value_name.valid()) {
                MemberLookupResult lookup = lookup_member_name(
                    substituted_qualifier->type,
                    file_.name(decltype_payload.dependent_value_name));
                if (lookup.found_name && !lookup.ambiguous &&
                    lookup.declarations.size() == 1) {
                    const MemberLookupDeclaration& declaration =
                        lookup.declarations.front();
                    cir::TypeRef member_type =
                        type_ref_for_declared_entity(file_,
                                                     declaration.entity);
                    if (!member_type.valid()) {
                        member_type = declaration.designated_type;
                    }
                    if (member_type.valid()) {
                        qualified_value =
                            DecltypeQualifiedValue{member_type};
                        if (auto member_category =
                                category_for_declared_entity(
                                    file_, declaration.entity)) {
                            qualified_value->category = *member_category;
                        }
                    }
                }
                if (qualified_value.has_value()) {
                    operand_type = qualified_value->type;
                    if (!decltype_category_is_known(category)) {
                        category = qualified_value->category;
                    }
                }
            }

            if (decltype_payload.use_declared_type_rule) {
                if (qualified_value.has_value()) {
                    return qualified_value->type.type;
                }
            } else if (decltype_category_is_known(category) &&
                       operand_type.type.valid() &&
                       !is_dependent_type(operand_type.type)) {
                cir::TypeId result =
                    decltype_result_from_category(file_, operand_type, category);
                if (result.valid()) {
                    return result;
                }
            }

            bool still_dependent =
                (operand_type.type.valid() &&
                 is_dependent_type(operand_type.type)) ||
                (substituted_qualifier->type.valid() &&
                 is_dependent_type(substituted_qualifier->type)) ||
                operand_expression.valid();
            if (!still_dependent) {
                return {};
            }
            return file_.decltype_expr_type(
                decltype_payload.expr,
                decltype_payload.use_declared_type_rule,
                category,
                operand_type,
                *substituted_qualifier,
                decltype_payload.dependent_value_name,
                std::move(operand_expression));
        }
        case cir::TypeKind::BuiltinTransform: {
            const auto transform =
                std::get<cir::BuiltinTypeTransformTypePayload>(
                    file_.type_payload(resolved));
            cir::TypeRef operand = substitute_pattern_type_ref(
                transform.operand_type, argument_bindings, callbacks);
            if (!operand.valid()) {
                return {};
            }
            std::optional<BuiltinKind> kind =
                builtin_kind_for_transform(transform.transform_kind);
            if (!kind) {
                return {};
            }
            return collect_builtin_type_transform(
                       *kind, operand, callbacks.access_loc)
                .type;
        }
        case cir::TypeKind::Place: {
            cir::TypeRef object = file_.place_object_ref(resolved);
            cir::TypeRef substituted = substitute_pattern_type_ref(
                object, argument_bindings, callbacks);
            if (!substituted.valid()) {
                return {};
            }
            return file_.place_type(substituted);
        }
        case cir::TypeKind::Function: {
            const auto function =
                std::get<cir::FunctionTypePayload>(file_.type_payload(resolved));
            cir::TypeRef result = substitute_pattern_type_ref(
                function.return_type, argument_bindings, callbacks);
            if (!result.valid()) {
                return {};
            }
            cir::TypeId resolved_result = file_.resolved_type(result.type);
            if (!file_.valid(resolved_result) ||
                file_.type(resolved_result).kind == cir::TypeKind::Array ||
                file_.type(resolved_result).kind == cir::TypeKind::Function) {
                return {};
            }
            std::vector<cir::TypeRef> parameters;
            std::vector<uint8_t> parameter_pack_flags;
            parameters.reserve(function.parameters.size());
            parameter_pack_flags.reserve(function.parameters.size());
            auto collect_exact_type_packs =
                [&](auto&& self,
                    cir::TypeId candidate,
                    std::vector<cir::TypeId>& packs) -> void {
                    candidate = file_.resolved_type(candidate);
                    if (!file_.valid(candidate)) {
                        return;
                    }
                    const cir::TypePayload& payload =
                        file_.type_payload(candidate);
                    auto add = [&](cir::TypeId pack) {
                        if (std::find(packs.begin(), packs.end(), pack) ==
                            packs.end()) {
                            packs.push_back(pack);
                        }
                    };
                    auto visit_arguments =
                        [&](const std::vector<TemplateArgument>& arguments) {
                            for (const TemplateArgument& argument : arguments) {
                                if (template_argument_is_type(argument)) {
                                    self(self, argument.type.type, packs);
                                }
                            }
                        };
                    switch (file_.type(candidate).kind) {
                        case cir::TypeKind::TypeParam: {
                            const auto& parameter =
                                std::get<cir::TypeParamTypePayload>(payload);
                            if (parameter.is_parameter_pack &&
                                callbacks.exact_type_parameter_bindings
                                    .contains(static_cast<uint32_t>(
                                        candidate.index))) {
                                add(candidate);
                            }
                            return;
                        }
                        case cir::TypeKind::Pointer:
                            self(self,
                                 std::get<cir::PointerTypePayload>(payload)
                                     .pointee.type,
                                 packs);
                            return;
                        case cir::TypeKind::BlockPointer:
                            self(self,
                                 std::get<cir::BlockPointerTypePayload>(payload)
                                     .pointee.type,
                                 packs);
                            return;
                        case cir::TypeKind::LValueReference:
                        case cir::TypeKind::RValueReference:
                            self(self,
                                 std::get<cir::ReferenceTypePayload>(payload)
                                     .referred_type.type,
                                 packs);
                            return;
                        case cir::TypeKind::Array:
                            self(self,
                                 std::get<cir::ArrayTypePayload>(payload)
                                     .element_type.type,
                                 packs);
                            return;
                        case cir::TypeKind::MemberPointer: {
                            const auto& member =
                                std::get<cir::MemberPointerTypePayload>(payload);
                            self(self, member.class_type.type, packs);
                            self(self, member.member_type.type, packs);
                            return;
                        }
                        case cir::TypeKind::Function: {
                            const auto& nested =
                                std::get<cir::FunctionTypePayload>(payload);
                            self(self, nested.return_type.type, packs);
                            for (const cir::TypeRef& parameter :
                                 nested.parameters) {
                                self(self, parameter.type, packs);
                            }
                            return;
                        }
                        case cir::TypeKind::TemplateSpecialization:
                            visit_arguments(
                                std::get<
                                    cir::TemplateSpecializationTypePayload>(
                                    payload).arguments);
                            return;
                        case cir::TypeKind::DependentName:
                            visit_arguments(
                                std::get<cir::DependentNameTypePayload>(payload)
                                    .template_arguments);
                            return;
                        case cir::TypeKind::Record: {
                            const cir::TemplateSpecializationFact* fact =
                                file_.template_specialization(
                                    file_.record_entity(candidate));
                            if (fact) {
                                visit_arguments(fact->template_arguments());
                            }
                            return;
                        }
                        default:
                            return;
                    }
                };
            for (size_t i = 0; i < function.parameters.size(); ++i) {
                const cir::TypeRef& parameter = function.parameters[i];
                bool is_parameter_pack =
                    i < function.parameter_pack_flags.size() &&
                    function.parameter_pack_flags[i] != 0;
                if (is_parameter_pack) {
                    std::vector<cir::TypeId> exact_pack_types;
                    collect_exact_type_packs(collect_exact_type_packs,
                                             parameter.type,
                                             exact_pack_types);
                    if (!exact_pack_types.empty()) {
                        std::optional<size_t> element_count;
                        for (cir::TypeId pack_type : exact_pack_types) {
                            const TemplateArgumentBinding& binding =
                                callbacks.exact_type_parameter_bindings.at(
                                    static_cast<uint32_t>(pack_type.index));
                            if (!binding.is_pack() ||
                                (element_count.has_value() &&
                                 *element_count != binding.arguments.size())) {
                                return {};
                            }
                            element_count = binding.arguments.size();
                        }
                        for (size_t element_index = 0;
                             element_index < element_count.value_or(0);
                             ++element_index) {
                            PatternInstantiationCallbacks element_callbacks =
                                callbacks;
                            for (cir::TypeId pack_type : exact_pack_types) {
                                TemplateArgumentBinding& binding =
                                    element_callbacks
                                        .exact_type_parameter_bindings[
                                            static_cast<uint32_t>(
                                                pack_type.index)];
                                TemplateArgument element =
                                    binding.arguments[element_index];
                                binding.kind =
                                    TemplateArgumentBindingKind::Single;
                                binding.arguments = {std::move(element)};
                            }
                            element_callbacks
                                .allow_parameter_pack_element_substitution =
                                true;
                            cir::TypeRef substituted =
                                substitute_pattern_type_ref(
                                    parameter,
                                    argument_bindings,
                                    element_callbacks);
                            substituted = adjust_substituted_function_parameter(
                                file_, substituted);
                            if (!substituted.valid()) {
                                return {};
                            }
                            parameters.push_back(substituted);
                            parameter_pack_flags.push_back(0);
                        }
                        continue;
                    }
                    std::optional<uint32_t> pack_index =
                        type_parameter_pack_index(parameter.type);
                    const TemplateArgumentBinding* pack_binding =
                        pack_index.has_value()
                            ? substitution_binding(argument_bindings,
                                                   *pack_index)
                            : nullptr;
                    if (!pack_binding || !pack_binding->is_pack()) {
                        return {};
                    }
                    for (const TemplateArgument& element :
                         pack_binding->arguments) {
                        if (!template_argument_is_type(element)) {
                            return {};
                        }
                        TemplateArgumentBindings element_bindings =
                            argument_bindings;
                        element_bindings[*pack_index].kind =
                            TemplateArgumentBindingKind::Single;
                        element_bindings[*pack_index].arguments = {element};
                        PatternInstantiationCallbacks element_callbacks =
                            callbacks;
                        element_callbacks
                            .allow_parameter_pack_element_substitution = true;
                        cir::TypeRef substituted =
                            substitute_pattern_type_ref(
                                parameter,
                                element_bindings,
                                element_callbacks);
                        substituted = adjust_substituted_function_parameter(
                            file_, substituted);
                        if (!substituted.valid()) {
                            return {};
                        }
                        parameters.push_back(substituted);
                        parameter_pack_flags.push_back(0);
                    }
                    continue;
                }
                cir::TypeRef substituted = substitute_pattern_type_ref(
                    parameter, argument_bindings, callbacks);
                substituted = adjust_substituted_function_parameter(
                    file_, substituted);
                if (!substituted.valid()) {
                    return {};
                }
                cir::TypeId resolved_parameter =
                    file_.resolved_type(substituted.type);
                if (!file_.valid(resolved_parameter)) {
                    return {};
                }
                if (file_.type(resolved_parameter).kind ==
                    cir::TypeKind::Builtin) {
                    const auto* builtin =
                        std::get_if<cir::BuiltinTypePayload>(
                            &file_.type_payload(resolved_parameter));
                    if (builtin &&
                        builtin->kind == cir::BuiltinTypeKind::Void) {
                        return {};
                    }
                }
                parameters.push_back(substituted);
                parameter_pack_flags.push_back(is_parameter_pack ? 1 : 0);
            }
            if (std::none_of(parameter_pack_flags.begin(),
                             parameter_pack_flags.end(),
                             [](uint8_t flag) { return flag != 0; })) {
                parameter_pack_flags.clear();
            }
            cir::FunctionExceptionSpec exception_spec =
                function.exception_spec;
            if (exception_spec.kind ==
                    cir::FunctionExceptionSpecKind::Dependent &&
                !callbacks.defer_function_exception_spec) {
                bool has_noexcept_recipe = std::any_of(
                    exception_spec.predicate.nodes.begin(),
                    exception_spec.predicate.nodes.end(),
                    [](const cir::TemplateValueExprNode& node) {
                        return node.kind ==
                            cir::TemplateValueExprKind::Noexcept;
                    });
                if (has_noexcept_recipe) {
                    UnevaluatedCallResolution resolved_predicate =
                        resolve_unevaluated_call_expression(
                            exception_spec.predicate,
                            argument_bindings,
                            callbacks);
                    if (resolved_predicate.status ==
                            UnevaluatedCallResolutionStatus::
                                SubstitutionFailure ||
                        resolved_predicate.status ==
                            UnevaluatedCallResolutionStatus::HardError) {
                        return {};
                    }
                    exception_spec.predicate =
                        std::move(resolved_predicate.expression);
                    if (resolved_predicate.status ==
                        UnevaluatedCallResolutionStatus::Resolved) {
                        if (!exception_spec.predicate.valid()) {
                            return {};
                        }
                        const cir::TemplateValueExprNode& resolved_root =
                            exception_spec.predicate.nodes[
                                exception_spec.predicate.root];
                        if (resolved_root.kind !=
                            cir::TemplateValueExprKind::Integer) {
                            return {};
                        }
                        exception_spec =
                            !resolved_root.integer_value.is_zero()
                            ? cir::FunctionExceptionSpecKind::NonThrowing
                            : cir::FunctionExceptionSpecKind::
                                  PotentiallyThrowing;
                    }
                }
            }
            if (exception_spec.kind ==
                    cir::FunctionExceptionSpecKind::Dependent &&
                !callbacks.defer_function_exception_spec) {
                if (!exception_spec.predicate.valid()) {
                    return {};
                }
                const cir::TemplateValueExprNode& root =
                    exception_spec.predicate.nodes[
                        exception_spec.predicate.root];
                bool root_is_bool = root.result_type.type.valid() &&
                    file_.template_value_kind_for_type(
                        root.result_type.type) ==
                        cir::TemplateValueKind::Boolean;
                if (root.result_type.type.valid() && !root_is_bool) {

                    TemplateArgument contextual_operand;
                    contextual_operand.kind =
                        cir::TemplateArgumentKind::Value;
                    cir::TypeId contextual_type =
                        file_.resolved_type(root.result_type.type);
                    bool root_type_is_opaque_dependent =
                        file_.valid(contextual_type) &&
                        file_.type(contextual_type).kind ==
                            cir::TypeKind::Dependent;

                    if (!root_type_is_opaque_dependent) {
                        contextual_operand.value_type = root.result_type;
                    }
                    contextual_operand.value_kind =
                        cir::TemplateValueKind::None;
                    contextual_operand.dependent_value_expr =
                        exception_spec.predicate;
                    contextual_operand.is_dependent = true;
                    if (!substitute_template_value_argument(
                            contextual_operand,
                            argument_bindings,
                            callbacks)) {
                        return {};
                    }
                    if (!contextual_operand.is_dependent &&
                        (contextual_operand.value_kind ==
                             cir::TemplateValueKind::Integer ||
                         contextual_operand.value_kind ==
                             cir::TemplateValueKind::Boolean) &&
                        contextual_operand.integer_value.try_as_uint64()
                                .value_or(2) > 1) {

                        note_substitution_hard_error();
                        report_error(
                            "contextual conversion of noexcept specifier "
                            "operand to bool is narrowing",
                            callbacks.access_loc);
                        return {};
                    }
                }
                TemplateArgument predicate;
                predicate.kind = cir::TemplateArgumentKind::Value;
                predicate.value_type = file_.type_ref(
                    file_.builtin_type(cir::BuiltinTypeKind::Bool));
                predicate.value_kind = cir::TemplateValueKind::None;
                predicate.dependent_value_expr = exception_spec.predicate;
                predicate.is_dependent = true;
                if (!substitute_template_value_argument(
                        predicate, argument_bindings, callbacks)) {
                    return {};
                }
                if (predicate.is_dependent) {
                    exception_spec.predicate =
                        std::move(predicate.dependent_value_expr);
                } else if (predicate.value_kind ==
                               cir::TemplateValueKind::Boolean ||
                           predicate.value_kind ==
                               cir::TemplateValueKind::Integer) {
                    exception_spec =
                        !predicate.integer_value.is_zero()
                            ? cir::FunctionExceptionSpecKind::NonThrowing
                            : cir::FunctionExceptionSpecKind::PotentiallyThrowing;
                } else {
                    return {};
                }
            }
            return file_.function_type(
                result,
                parameters, function.is_variadic, function.has_prototype,
                function.member_is_const,
                std::move(exception_spec),
                parameter_pack_flags,
                function.member_ref_qualifier,
                function.member_is_volatile);
        }
        case cir::TypeKind::Record: {
            cir::EntityId record = file_.record_entity(resolved);
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(record);
            cir::EntityId template_entity{};
            std::vector<TemplateArgument> fact_arguments;
            if (!fact) {
                if (callbacks.self_pattern_type.valid()) {

                    bool nested_in_self = false;
                    cir::TypeId mapped =
                        current_instantiation_nested_record_type(
                            resolved, callbacks, nested_in_self);
                    if (nested_in_self) {
                        return mapped;
                    }
                }
                if (!class_template_arguments_for_record(
                        record, &template_entity, &fact_arguments)) {

                    return type;
                }
            } else {
                template_entity = fact->template_entity;
                fact_arguments = fact->template_arguments();
                if (!template_entity.valid() &&
                    callbacks.argument_completion_mode ==
                        TemplateArgumentCompletionMode::Candidate &&
                    fact->selected_template_entity.valid()) {
                    template_entity = fact->selected_template_entity;
                }
            }
            std::vector<TemplateArgument> substituted_arguments;
            substituted_arguments.reserve(fact_arguments.size());
            for (const cir::TemplateArgument& argument : fact_arguments) {
                if (!append_substituted_template_argument(
                        argument,
                        argument_bindings,
                        callbacks,
                        substituted_arguments,
                        /*reject_unresolved_template_parameter=*/false)) {
                    return {};
                }
            }
            if (fact &&
                fact->template_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
                const TemplateArgument* argument = nullptr;
                auto exact = callbacks.exact_template_parameter_bindings.find(
                    static_cast<uint32_t>(template_entity.index));
                if (exact !=
                        callbacks.exact_template_parameter_bindings.end() &&
                    exact->second.is_single() &&
                    exact->second.arguments.size() == 1) {
                    argument = &exact->second.arguments.front();
                } else {
                    argument = single_substitution_argument(
                        argument_bindings, fact->template_param_index);
                }
                if (!argument ||
                    argument->kind != cir::TemplateArgumentKind::Template) {
                    return {};
                }
                template_entity = argument->template_entity;
            }
            bool designator_is_dependent =
                template_entity.valid() && file_.valid(template_entity) &&
                file_.entity(template_entity).kind ==
                    cir::EntityKind::TemplateParam;
            if (designator_is_dependent) {
                cir::NameId template_name =
                    template_entity.valid() && file_.valid(template_entity)
                    ? file_.entity(template_entity).name
                    : cir::NameId{};
                if (!template_name.valid() && fact &&
                    fact->template_entity.valid() &&
                    file_.valid(fact->template_entity)) {
                    template_name = file_.entity(fact->template_entity).name;
                }
                if (!template_name.valid()) {
                    return {};
                }
                return file_.template_specialization_type(
                    template_name,
                    template_entity,
                    std::move(substituted_arguments),
                    /*is_dependent=*/true,
                    /*is_class_template_placeholder=*/true);
            }

            if (!template_entity.valid() || !file_.valid(template_entity) ||
                !callbacks.instantiate_type_template) {
                return {};
            }
            cir::TypeRef instantiated =
                callbacks.instantiate_type_template(
                    template_entity,
                    std::move(substituted_arguments),
                    callbacks.point_lookup_generation,
                    callbacks.materialize_type_template_definition,
                    callbacks.argument_completion_mode);
            if (complete_type) {
                *complete_type = instantiated;
            }
            return instantiated.type;
        }
        default:

            return type_contains_type_param(resolved) ? cir::TypeId{} : type;
    }
}

cir::TypeId Session::current_instantiation_nested_record_type(
    cir::TypeId resolved,
    const PatternInstantiationCallbacks& callbacks,
    bool& nested_in_self) {
    nested_in_self = false;
    cir::EntityId pattern_self =
        file_.record_entity(callbacks.self_pattern_type);
    cir::EntityId instance_self =
        file_.record_entity(callbacks.self_instance_type);
    cir::EntityId record = file_.record_entity(resolved);
    if (!pattern_self.valid() || !file_.valid(pattern_self) ||
        !instance_self.valid() || !file_.valid(instance_self) ||
        !record.valid() || !file_.valid(record)) {
        return {};
    }

    auto enclosing_record = [&](cir::EntityId from) -> cir::EntityId {
        cir::DeclContextId own = file_.entity(from).semantic_context;
        if (!own.valid()) {
            return {};
        }
        cir::DeclContextId up = file_.decl_context(own).parent;
        if (!up.valid()) {
            return {};
        }
        cir::EntityId owner = file_.decl_context(up).owner;
        if (!owner.valid() || !file_.valid(owner) ||
            file_.entity(owner).kind != cir::EntityKind::Record) {
            return {};
        }
        return owner;
    };
    std::vector<cir::EntityId> pattern_chain{pattern_self};
    for (cir::EntityId up = enclosing_record(pattern_self); up.valid();
         up = enclosing_record(pattern_chain.back())) {
        pattern_chain.push_back(up);
    }

    std::vector<cir::NameId> path;
    size_t level = pattern_chain.size();
    cir::EntityId walk = record;
    while (walk.valid() && file_.valid(walk)) {
        auto at = std::find(pattern_chain.begin(), pattern_chain.end(), walk);
        if (at != pattern_chain.end()) {
            level = static_cast<size_t>(at - pattern_chain.begin());
            break;
        }
        const cir::Entity& entity = file_.entity(walk);
        if (entity.kind != cir::EntityKind::Record || !entity.name.valid()) {
            return {};
        }
        path.push_back(entity.name);
        walk = enclosing_record(walk);
    }
    if (level == pattern_chain.size()) {
        return {};
    }
    nested_in_self = true;

    cir::EntityId instance = instance_self;
    for (size_t i = 0; i < level && instance.valid(); ++i) {
        instance = enclosing_record(instance);
    }
    for (size_t i = path.size(); i-- > 0;) {
        if (!instance.valid() || !file_.valid(instance)) {
            return {};
        }
        cir::DeclContextId context =
            file_.entity(instance).semantic_context;
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
        instance = next;
    }
    if (!instance.valid() || !file_.valid(instance)) {
        return {};
    }
    return file_.entity(instance).type;
}

bool Session::run_pattern_clone(PatternCloneJob& job) {
    const cir::Function& pattern = *job.pattern;

    if (pattern.entity.valid() && file_.valid(pattern.entity) &&
        file_.entity(pattern.entity).origin_unit.valid() &&
        file_.entity(pattern.entity).origin_unit != module_state_.unit) {
        note_pattern_clone_bail(PatternCloneBailReason::ForeignModuleUnit);
        return false;
    }
    auto& entity_map = *job.entity_map;
    auto& inst_map = *job.inst_map;
    auto& block_map = *job.block_map;
    size_t end_block = job.block_count == 0
        ? pattern.blocks.size()
        : std::min(pattern.blocks.size(),
                   job.first_block + job.block_count);

    for (size_t b = job.first_block; b < end_block; ++b) {
        cir::BlockId block_id = pattern.blocks[b];
        if (file_.block(block_id).unwind_target.valid()) {

            note_pattern_clone_bail(PatternCloneBailReason::EhRegion);
            return false;
        }
        if (block_map.count(block_id.index) != 0) {
            continue;
        }
        cir::BlockId cloned = file_.add_block({});
        std::string base(file_.name(file_.block(block_id).name));
        size_t dot = base.rfind('.');
        if (dot != std::string::npos && dot + 1 < base.size() &&
            base.find_first_not_of("0123456789", dot + 1) ==
                std::string::npos) {
            base.resize(dot);
        }
        builder_.rename_block(cloned, base);
        block_map.emplace(block_id.index, cloned);
        if (job.attach_function.valid()) {
            file_.function_mut(job.attach_function).blocks.push_back(cloned);
        } else if (job.fragment_blocks) {
            job.fragment_blocks->push_back(cloned);
        }
    }

    size_t event_cursor = 0;
    size_t scopes_entered = 0;
    bool failed = false;
    bool ran_before_first_hole = false;
    auto cleanup_record_count = [this]() {
        size_t count = 0;
        for (const CleanupScope& scope : cleanup_scopes_) {
            count += scope.records.size();
        }
        return count;
    };
    auto fragment_has_unresolved_dependency =
        [this](const cir::Fragment& fragment) {
            for (cir::BlockId block_id : fragment.blocks) {
                if (!block_id.valid() || !file_.valid(block_id)) {
                    continue;
                }
                for (cir::InstId inst_id :
                     file_.block(block_id).instructions) {
                    if (!inst_id.valid() || !file_.valid(inst_id)) {
                        continue;
                    }
                    const cir::Inst& inst = file_.inst(inst_id);
                    if (inst.kind == cir::InstKind::DependentCall ||
                        inst.kind == cir::InstKind::DependentRegion ||
                        (inst.result_type.valid() &&
                         is_dependent_type(inst.result_type))) {
                        return true;
                    }
                }
            }
            return false;
        };
    auto fragment_has_immediate_invocation =
        [this](const cir::Fragment& fragment) {
            for (cir::BlockId block_id : fragment.blocks) {
                if (!block_id.valid() || !file_.valid(block_id)) {
                    continue;
                }
                for (cir::InstId inst_id :
                     file_.block(block_id).instructions) {
                    if (!inst_id.valid() || !file_.valid(inst_id)) {
                        continue;
                    }
                    const cir::Inst& inst = file_.inst(inst_id);
                    if (inst.kind != cir::InstKind::Call) {
                        continue;
                    }
                    const std::vector<cir::Operand> operands =
                        file_.operands(inst.operands);
                    const auto* callee = operands.empty()
                        ? nullptr
                        : std::get_if<cir::EntityId>(
                              &operands.front().data);
                    if (callee && callee->valid() &&
                        file_.valid(*callee) &&
                        file_.entity(*callee).decl_flags.is_consteval) {
                        return true;
                    }
                }
            }
            return false;
        };
    auto apply_events_until = [&](size_t watermark) -> bool {
        while (event_cursor < watermark &&
               event_cursor < job.events->size()) {
            const PatternScopeEvent& event = (*job.events)[event_cursor++];
            switch (event.kind) {
                case PatternScopeEvent::Kind::EnterScope:
                    enter_scope(ScopeFlags::BlockScope);
                    ++scopes_entered;
                    break;
                case PatternScopeEvent::Kind::LeaveScope:
                    if (scopes_entered == 0) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::ScopeEvents);
                        return false;
                    }
                    leave_scope();
                    --scopes_entered;
                    break;
                case PatternScopeEvent::Kind::DeclareLocal: {
                    auto entity_found = entity_map.find(event.entity.index);
                    auto place_found = inst_map.find(event.place.index);
                    if (entity_found == entity_map.end() ||
                        place_found == inst_map.end()) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::ScopeEvents);
                        return false;
                    }
                    const cir::Entity& cloned =
                        file_.entity(entity_found->second);
                    bind_entity(file_.name(cloned.name),
                                cir::LookupNamespace::Ordinary,
                                entity_found->second,
                                cloned.type,
                                false,
                                false,
                                true,
                                place_found->second,
                                cloned.loc);
                    break;
                }
                case PatternScopeEvent::Kind::DeclareBlockFunction: {
                    cir::EntityId target = event.entity;
                    if (auto found = entity_map.find(event.entity.index);
                        found != entity_map.end()) {
                        target = found->second;
                    }
                    if (!target.valid() || !file_.valid(target) ||
                        file_.entity(target).kind !=
                            cir::EntityKind::Function) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::ScopeEvents);
                        return false;
                    }
                    const cir::Entity& function = file_.entity(target);
                    cir::DeclContextId saved_lexical =
                        function.lexical_context;
                    cir::DeclContextId saved_semantic =
                        function.semantic_context;
                    bind_callable(file_.name(function.name),
                                  target,
                                  function.type,
                                  function.is_definition,
                                  function.loc);
                    if (cir::Binding* replay_binding =
                            file_.mutable_ordinary_binding(
                                current_decl_context(),
                                file_.name(function.name))) {
                        replay_binding->generation = event.lookup_generation;
                        for (size_t i = 0;
                             i < replay_binding->entities.size() &&
                             i < replay_binding->entity_generations.size();
                             ++i) {
                            if (replay_binding->entities[i] == target) {
                                replay_binding->entity_generations[i] =
                                    event.lookup_generation;
                            }
                        }
                    }
                    file_.entity_mut(target).lexical_context = saved_lexical;
                    file_.entity_mut(target).semantic_context = saved_semantic;
                    break;
                }
            }
        }
        return true;
    };
    auto substitute_ref = [&](cir::TypeRef ref) -> std::pair<bool, cir::TypeRef> {
        if (!ref.type.valid()) {
            return {true, ref};
        }
        cir::TypeRef substituted = substitute_pattern_type_ref(
            ref, *job.argument_bindings, *job.callbacks);
        if (!substituted.valid()) {
            note_pattern_clone_bail(PatternCloneBailReason::TypeSubstitution);
            return {false, ref};
        }
        return {true, substituted};
    };

    auto remap_entity = [&](cir::EntityId entity) -> std::pair<bool, cir::EntityId> {
        if (!entity.valid() || !file_.valid(entity)) {
            return {true, entity};
        }
        auto found = entity_map.find(entity.index);
        if (found != entity_map.end()) {
            return {true, found->second};
        }
        const cir::Entity source = file_.entity(entity);
        if (!source.is_template_pattern) {
            return {true, entity};
        }
        if (source.kind != cir::EntityKind::Variable ||
            (source.storage_duration != cir::StorageDuration::Automatic &&
             source.storage_duration != cir::StorageDuration::Temporary)) {
            note_pattern_clone_bail(PatternCloneBailReason::IdRemap);
            return {false, entity};
        }
        cir::TypeRef cloned_type = substitute_pattern_type_ref(
            file_.type_ref(source.type,
                           source.qualifiers,
                           source.memory_space),
            *job.argument_bindings,
            *job.callbacks);
        if (!cloned_type.valid()) {
            note_pattern_clone_bail(PatternCloneBailReason::TypeSubstitution);
            return {false, entity};
        }
        cir::EntityId cloned = builder_.add_entity(
            source.kind, file_.name(source.name), cloned_type.type, job.owner,
            source.loc, source.storage_duration, cloned_type.memory_space,
            source.decl_flags);
        cir::Entity& record = file_.entity_mut(cloned);
        record.qualifiers = cloned_type.qualifiers;
        record.is_definition = source.is_definition;
        record.owning_function = job.owner;
        entity_map.emplace(entity.index, cloned);
        record.is_function_result_object =
            source.is_function_result_object;
        record.is_exception_declaration = source.is_exception_declaration;
        record.is_parameter_argument_object =
            source.is_parameter_argument_object;
        if (source.object_storage_alias.valid()) {
            auto alias = entity_map.find(source.object_storage_alias.index);
            if (alias != entity_map.end()) {
                record.object_storage_alias = alias->second;
            } else if (!file_.entity(source.object_storage_alias)
                            .is_template_pattern) {
                record.object_storage_alias = source.object_storage_alias;
            } else {
                note_pattern_clone_bail(PatternCloneBailReason::IdRemap);
                return {false, entity};
            }
        }
        if (source.object_storage_alias_place.valid()) {
            auto alias = inst_map.find(source.object_storage_alias_place.index);
            if (alias == inst_map.end()) {
                note_pattern_clone_bail(PatternCloneBailReason::IdRemap);
                return {false, entity};
            }
            record.object_storage_alias_place = alias->second;
        }
        return {true, cloned};
    };
    auto remap_operands =
        [&](cir::OperandRange range) -> std::pair<bool, cir::OperandRange> {
        std::vector<cir::Operand> operands = file_.operands(range);
        for (cir::Operand& operand : operands) {
            switch (operand.kind) {
                case cir::OperandKind::Value: {
                    const auto* value =
                        std::get_if<cir::ValueRef>(&operand.data);
                    if (!value || !value->inst.valid()) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::IdRemap);
                        return {false, range};
                    }
                    auto found = inst_map.find(value->inst.index);
                    if (found == inst_map.end()) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::IdRemap);
                        return {false, range};
                    }
                    operand.data = cir::ValueRef{found->second};
                    break;
                }
                case cir::OperandKind::Entity: {
                    const auto* entity =
                        std::get_if<cir::EntityId>(&operand.data);
                    if (!entity) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::IdRemap);
                        return {false, range};
                    }
                    auto [ok, mapped] = remap_entity(*entity);
                    if (!ok) {
                        return {false, range};
                    }
                    operand.data = mapped;
                    break;
                }
                case cir::OperandKind::Type: {
                    const auto* type_operand =
                        std::get_if<cir::TypeRef>(&operand.data);
                    if (!type_operand) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::IdRemap);
                        return {false, range};
                    }
                    auto [ok, mapped] = substitute_ref(*type_operand);
                    if (!ok) {
                        return {false, range};
                    }
                    operand.data = mapped;
                    break;
                }
                case cir::OperandKind::Name:
                case cir::OperandKind::Specific:
                case cir::OperandKind::None:
                    break;
            }
        }
        return {true, file_.add_operands(operands)};
    };
    auto remap_payload =
        [&](uint32_t payload_index) -> std::pair<bool, uint32_t> {
        cir::InstPayload payload = file_.payload(payload_index);
        if (std::holds_alternative<std::monostate>(payload)) {
            return {true, payload_index};
        }
        if (std::holds_alternative<cir::EhLandingPadPayload>(payload)) {

            note_pattern_clone_bail(PatternCloneBailReason::EhRegion);
            return {false, payload_index};
        }
        if (std::holds_alternative<cir::InlineAsmPayloadRef>(payload) ||
            std::holds_alternative<cir::LabelAddressPayload>(payload) ||
            std::holds_alternative<cir::SwitchTerminatorPayload>(payload) ||
            std::holds_alternative<cir::DependentRegionPayload>(payload)) {
            note_pattern_clone_bail(PatternCloneBailReason::UnsupportedPayload);
            return {false, payload_index};
        }
        if (auto* unary = std::get_if<cir::UnaryOpDescriptor>(&payload)) {
            auto [ok, mapped] = substitute_ref(unary->computation_type);
            if (!ok) {
                return {false, payload_index};
            }
            unary->computation_type = mapped;
        } else if (auto* binary =
                       std::get_if<cir::BinaryOpDescriptor>(&payload)) {
            auto [ok, mapped] = substitute_ref(binary->computation_type);
            if (!ok) {
                return {false, payload_index};
            }
            binary->computation_type = mapped;
        } else if (auto* builtin =
                       std::get_if<cir::BuiltinCallPayload>(&payload)) {
            auto [ok, mapped] = substitute_ref(builtin->type_operand);
            if (!ok) {
                return {false, payload_index};
            }
            builtin->type_operand = mapped;
        }
        return {true, file_.add_payload(std::move(payload))};
    };

    std::vector<std::pair<cir::BlockId, cir::Fragment>> hole_splices;

    for (size_t b = job.first_block;
         b < end_block && !failed; ++b) {
        cir::BlockId block_id = pattern.blocks[b];
        cir::BlockId target_block = block_map.at(block_id.index);
        const std::vector<cir::InstId> instructions =
            file_.block(block_id).instructions;
        for (cir::InstId inst_id : instructions) {
            const cir::Inst source = file_.inst(inst_id);
            if (source.kind == cir::InstKind::DependentRegion) {
                const auto* hole_payload =
                    std::get_if<cir::DependentRegionPayload>(
                        &file_.payload(source.payload_index));
                uint32_t hole_index = hole_payload
                    ? hole_payload->hole - job.hole_index_base
                    : 0;
                if (!hole_payload || hole_index >= job.holes->size() ||
                    !job.callbacks->replay_statement) {
                    note_pattern_clone_bail(
                        PatternCloneBailReason::PatternShape);
                    failed = true;
                    break;
                }
                const PatternHole& hole = (*job.holes)[hole_index];
                if (!ran_before_first_hole) {
                    ran_before_first_hole = true;
                    if (job.before_first_hole) {
                        job.before_first_hole();
                    }
                }
                if (!apply_events_until(hole.event_watermark)) {
                    failed = true;
                    break;
                }
                size_t cleanup_watermark = cleanup_record_count();
                StmtResult replayed = job.callbacks->replay_statement(hole);
                bool unresolved_dependency =
                    fragment_has_unresolved_dependency(replayed.fragment);
                bool surviving_immediate_invocation =
                    fragment_has_immediate_invocation(replayed.fragment);
                if (replayed.has_error || unresolved_dependency ||
                    surviving_immediate_invocation ||
                    cleanup_record_count() != cleanup_watermark) {

                    note_pattern_clone_bail(
                        replayed.has_error
                            ? PatternCloneBailReason::HoleReplay
                            : unresolved_dependency
                                ? PatternCloneBailReason::
                                      UnresolvedDependency
                            : surviving_immediate_invocation
                                ? PatternCloneBailReason::
                                      ImmediateInvocation
                            : PatternCloneBailReason::CleanupScopes);
                    failed = true;
                    break;
                }
                hole_splices.emplace_back(target_block,
                                          std::move(replayed.fragment));
                continue;
            }
            switch (source.kind) {
                case cir::InstKind::Invalid:
                case cir::InstKind::Error:
                case cir::InstKind::DependentCall:
                case cir::InstKind::InlineAsm:
                case cir::InstKind::LabelAddress:
                case cir::InstKind::StackAlloc:
                case cir::InstKind::StackSave:
                case cir::InstKind::StackRestore:
                    note_pattern_clone_bail(
                        PatternCloneBailReason::UnsupportedInst);
                    failed = true;
                    break;
                default:
                    break;
            }
            if (failed) {
                break;
            }
            cir::Inst cloned = source;
            if (source.result_type.valid()) {
                cloned.result_type = substitute_pattern_type(
                    source.result_type,
                    *job.argument_bindings,
                    *job.callbacks);
                if (!cloned.result_type.valid()) {
                    note_pattern_clone_bail(
                        PatternCloneBailReason::TypeSubstitution);
                    failed = true;
                    break;
                }
            }
            auto [operands_ok, operands] = remap_operands(source.operands);
            if (!operands_ok) {
                failed = true;
                break;
            }
            if (source.kind == cir::InstKind::Call) {
                const std::vector<cir::Operand> remapped =
                    file_.operands(operands);
                const auto* callee = remapped.empty()
                    ? nullptr
                    : std::get_if<cir::EntityId>(&remapped.front().data);
                if (callee && callee->valid() && file_.valid(*callee) &&
                    file_.entity(*callee).decl_flags.is_consteval) {

                    note_pattern_clone_bail(
                        PatternCloneBailReason::ImmediateInvocation);
                    failed = true;
                    break;
                }
            }
            cloned.operands = operands;
            if (source.result_object_entity.valid()) {
                auto [entity_ok, result_entity] =
                    remap_entity(source.result_object_entity);
                if (!entity_ok) {
                    failed = true;
                    break;
                }
                cloned.result_object_entity = result_entity;
            }
            auto [payload_ok, payload_index] =
                remap_payload(source.payload_index);
            if (!payload_ok) {
                failed = true;
                break;
            }
            cloned.payload_index = payload_index;
            if (source.place_fact.valid()) {
                cir::PlaceFact fact = file_.place_fact(source.place_fact);
                auto [type_ok, object_type] = substitute_ref(fact.object_type);
                auto [entity_ok, entity] = remap_entity(fact.entity);
                if (!type_ok || !entity_ok) {
                    failed = true;
                    break;
                }
                if (source.kind == cir::InstKind::LocalPlace &&
                    entity.valid() && file_.valid(entity) &&
                    file_.entity(entity).kind ==
                        cir::EntityKind::Parameter) {
                    const cir::Entity& parameter = file_.entity(entity);
                    object_type = file_.type_ref(parameter.type,
                                                 parameter.qualifiers,
                                                 parameter.memory_space);
                    cloned.result_type = file_.place_type(object_type);
                }
                fact.object_type = object_type;
                fact.entity = entity;
                if (fact.base.valid()) {
                    auto found = inst_map.find(fact.base.index);
                    if (found == inst_map.end()) {
                        note_pattern_clone_bail(
                            PatternCloneBailReason::IdRemap);
                        failed = true;
                        break;
                    }
                    fact.base = found->second;
                }

                fact.source = {};
                cloned.place_fact = file_.add_place_fact(std::move(fact));
            }
            cir::InstId new_id = file_.add_inst(std::move(cloned));
            if (file_.inst(new_id).place_fact.valid()) {
                file_.place_fact_mut(file_.inst(new_id).place_fact).source =
                    new_id;
            }
            file_.block_mut(target_block).instructions.push_back(new_id);
            inst_map.emplace(inst_id.index, new_id);
            if (source.kind == cir::InstKind::LocalPlace && job.param_places) {

                std::vector<cir::Operand> cloned_operands =
                    file_.operands(file_.inst(new_id).operands);
                if (!cloned_operands.empty()) {
                    if (const auto* entity = std::get_if<cir::EntityId>(
                            &cloned_operands.front().data);
                        entity && file_.valid(*entity) &&
                        file_.entity(*entity).kind ==
                            cir::EntityKind::Parameter) {
                        job.param_places->emplace(entity->index, new_id);
                    }
                }
            }
        }
    }

    if (!failed) {
        for (size_t b = job.first_block;
             b < end_block && !failed; ++b) {
            cir::BlockId block_id = pattern.blocks[b];
            cir::Terminator term = file_.block(block_id).terminator;
            switch (term.kind) {
                case cir::TerminatorKind::Invalid:
                case cir::TerminatorKind::Return:
                case cir::TerminatorKind::Branch:
                case cir::TerminatorKind::CondBranch:
                case cir::TerminatorKind::Unreachable:
                    break;
                default:
                    note_pattern_clone_bail(
                        PatternCloneBailReason::UnsupportedTerminator);
                    failed = true;
                    break;
            }
            if (failed) {
                break;
            }
            auto [operands_ok, operands] = remap_operands(term.operands);
            if (!operands_ok) {
                failed = true;
                break;
            }
            term.operands = operands;
            cir::FunctionId target_function = job.attach_function.valid()
                ? job.attach_function
                : current_function_;
            if (term.kind == cir::TerminatorKind::Return &&
                target_function.valid() &&
                file_.valid(target_function)) {
                const cir::Function& target =
                    file_.function(target_function);
                bool target_returns_void =
                    is_void_type(target.result_type);
                const std::vector<cir::Operand> return_operands =
                    file_.operands(term.operands);
                cir::InstId fallthrough_load;
                cir::InstId fallthrough_place;
                cir::EntityId fallthrough_slot;
                if (return_operands.size() == 1) {
                    const auto* return_value =
                        std::get_if<cir::ValueRef>(
                            &return_operands.front().data);
                    if (return_value &&
                        return_value->inst.valid() &&
                        file_.valid(return_value->inst)) {
                        const cir::Inst& load =
                            file_.inst(return_value->inst);
                        const std::vector<cir::Operand> load_operands =
                            file_.operands(load.operands);
                        const auto* place_value =
                            load.kind == cir::InstKind::LValueToRValue &&
                                load_operands.size() == 1
                            ? std::get_if<cir::ValueRef>(
                                  &load_operands.front().data)
                            : nullptr;
                        if (place_value &&
                            place_value->inst.valid() &&
                            file_.valid(place_value->inst)) {
                            const cir::Inst& place =
                                file_.inst(place_value->inst);
                            const std::vector<cir::Operand> place_operands =
                                file_.operands(place.operands);
                            const auto* slot =
                                place.kind == cir::InstKind::LocalPlace &&
                                    !place_operands.empty()
                                ? std::get_if<cir::EntityId>(
                                      &place_operands.front().data)
                                : nullptr;
                            if (slot && slot->valid() &&
                                file_.valid(*slot) &&
                                file_.name(file_.entity(*slot).name) ==
                                    ".ret.fallthrough") {
                                fallthrough_load = return_value->inst;
                                fallthrough_place = place_value->inst;
                                fallthrough_slot = *slot;
                            }
                        }
                    }
                }
                if (target_returns_void) {

                    if (fallthrough_slot.valid()) {
                        std::vector<cir::InstId>& instructions =
                            file_.block_mut(
                                block_map.at(block_id.index))
                                .instructions;
                        std::erase(instructions, fallthrough_load);
                        std::erase(instructions, fallthrough_place);
                    }
                    term.operands = {};
                } else if (fallthrough_slot.valid()) {

                    cir::TypeRef concrete_result =
                        file_.type_ref(target.result_type);
                    cir::Entity& slot =
                        file_.entity_mut(fallthrough_slot);
                    slot.type = concrete_result.type;
                    slot.qualifiers = concrete_result.qualifiers;
                    slot.memory_space = concrete_result.memory_space;

                    cir::Inst& place =
                        file_.inst_mut(fallthrough_place);
                    place.result_type =
                        file_.place_type(concrete_result);
                    if (place.place_fact.valid()) {
                        file_.place_fact_mut(place.place_fact).object_type =
                            concrete_result;
                    }
                    file_.inst_mut(fallthrough_load).result_type =
                        concrete_result.type;
                }
            }
            if (term.target.valid()) {
                auto found = block_map.find(term.target.index);
                if (found == block_map.end()) {
                    note_pattern_clone_bail(PatternCloneBailReason::IdRemap);
                    failed = true;
                    break;
                }
                term.target = found->second;
            }
            if (term.false_target.valid()) {
                auto found = block_map.find(term.false_target.index);
                if (found == block_map.end()) {
                    note_pattern_clone_bail(PatternCloneBailReason::IdRemap);
                    failed = true;
                    break;
                }
                term.false_target = found->second;
            }
            file_.block_mut(block_map.at(block_id.index)).terminator = term;
        }
    }

    if (!failed) {
        for (auto& [hole_block, fragment] : hole_splices) {
            if (fragment.empty()) {
                continue;
            }
            cir::Terminator continuation = file_.block(hole_block).terminator;
            if (job.attach_function.valid()) {
                builder_.attach_fragment_to_function(job.attach_function,
                                                     fragment);
            } else if (job.fragment_blocks) {
                for (cir::BlockId block_id : fragment.blocks) {
                    job.fragment_blocks->push_back(block_id);
                }
            }
            {
                cir::Terminator branch;
                branch.kind = cir::TerminatorKind::Branch;
                branch.target = fragment.entry;
                branch.loc = continuation.loc;
                file_.block_mut(hole_block).terminator = branch;
            }
            if (!builder_.block_terminated(fragment.exit)) {
                file_.block_mut(fragment.exit).terminator = continuation;
            }
        }
    }

    while (scopes_entered > 0) {
        leave_scope();
        --scopes_entered;
    }
    return !failed;
}

const char* Session::pattern_clone_bail_text(PatternCloneBailReason reason) {
    switch (reason) {
        case PatternCloneBailReason::None:
            return "no recorded reason";
        case PatternCloneBailReason::ArgumentBinding:
            return "template argument binding failed";
        case PatternCloneBailReason::TypeSubstitution:
            return "a pattern type did not substitute";
        case PatternCloneBailReason::EhRegion:
            return "the pattern body has exception-handling regions";
        case PatternCloneBailReason::UnsupportedInst:
            return "the pattern body has an instruction the cloner does not model";
        case PatternCloneBailReason::UnsupportedTerminator:
            return "the pattern body has a terminator the cloner does not model";
        case PatternCloneBailReason::UnsupportedPayload:
            return "the pattern body has an instruction payload the cloner does not model";
        case PatternCloneBailReason::HoleReplay:
            return "a dependent-statement replay failed";
        case PatternCloneBailReason::UnresolvedDependency:
            return "a concrete hole replay retained dependent CIR";
        case PatternCloneBailReason::CleanupScopes:
            return "a replayed statement registered destructor cleanups";
        case PatternCloneBailReason::ScopeEvents:
            return "the pattern scope-event log did not rebuild";
        case PatternCloneBailReason::IdRemap:
            return "a pattern id did not remap onto the instantiation";
        case PatternCloneBailReason::PatternShape:
            return "the pattern shape does not match the instantiation";
        case PatternCloneBailReason::ImmediateInvocation:
            return "a dependent immediate invocation requires concrete replay";
        case PatternCloneBailReason::ForeignModuleUnit:
            return "the pattern belongs to an imported module unit";
        case PatternCloneBailReason::NestedClone:
            return "another pattern clone is already active";
    }
    return "no recorded reason";
}

cir::EntityId Session::clone_pattern_function(
    const TemplateInfo& info,
    const std::vector<TemplateArgument>& arguments,
    PatternInstantiationCallbacks& callbacks,
    SrcLoc loc,
    cir::EntityId declaration_shell,
    const TemplateArgumentBindings* exact_bindings) {
    if (pattern_clone_depth_ != 0) {
        note_pattern_clone_bail(PatternCloneBailReason::NestedClone);
        return {};
    }
    PatternCloneDepthScope clone_depth_scope(pattern_clone_depth_);
    reset_pattern_clone_bail();
    if (!info.pattern_function.valid() ||
        !file_.valid(info.pattern_function)) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return {};
    }
    const cir::Function pattern = file_.function(info.pattern_function);
    const cir::Entity pattern_record = file_.entity(pattern.entity);

    TemplateArgumentBindings argument_bindings;
    if (exact_bindings) {
        argument_bindings = *exact_bindings;
    } else {
        if (!bind_template_arguments_to_parameters(info.parameters,
                                                   arguments,
                                                   argument_bindings)) {
            note_pattern_clone_bail(PatternCloneBailReason::ArgumentBinding);
            return {};
        }
    }

    cir::TypeId result_type =
        substitute_pattern_type(pattern.result_type,
                                argument_bindings,
                                callbacks);
    cir::TypeId instantiated_function_type =
        substitute_pattern_type(pattern.type,
                                argument_bindings,
                                callbacks);
    if (!result_type.valid() || !instantiated_function_type.valid()) {
        note_pattern_clone_bail(PatternCloneBailReason::TypeSubstitution);
        return {};
    }
    const auto* instantiated_function_payload =
        std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(
                file_.resolved_type(instantiated_function_type)));
    if (!instantiated_function_payload ||
        type_contains_type_param(instantiated_function_type) ||
        instantiated_function_payload->exception_spec.kind ==
            cir::FunctionExceptionSpecKind::Dependent) {

        note_pattern_clone_bail(PatternCloneBailReason::TypeSubstitution);
        return {};
    }

    std::unordered_map<uint32_t, cir::EntityId> entity_map;
    std::unordered_map<uint32_t, cir::InstId> inst_map;
    std::unordered_map<uint32_t, cir::BlockId> block_map;
    std::unordered_map<uint32_t, cir::InstId> param_places;

    cir::EntityId fn_entity = declaration_shell;
    bool created_declaration_shell = false;
    if (!fn_entity.valid() || !file_.valid(fn_entity)) {
        fn_entity = builder_.add_entity(
            cir::EntityKind::Function, info.name, {}, {}, loc);
        created_declaration_shell = true;
    }
    {
        cir::Entity& record = file_.entity_mut(fn_entity);
        record.is_definition = true;

        record.is_template_pattern = false;
        record.linkage = cir::LinkageKind::LinkOnceODR;
        record.lexical_context = pattern_record.lexical_context;
        record.semantic_context = pattern_record.semantic_context;

        record.decl_flags = pattern_record.decl_flags;
        record.is_extern_c = pattern_record.is_extern_c;
        record.operator_function = info.operator_function.valid()
            ? info.operator_function
            : pattern_record.operator_function;
        if (created_declaration_shell) {
            if (info.entity.valid() && file_.valid(info.entity)) {
                record.attr_facts = file_.entity(info.entity).attr_facts;
            } else {
                record.attr_facts = pattern_record.attr_facts;
            }
        }
        if (record.operator_function.kind ==
                cir::OperatorFunctionKind::Conversion) {
            record.operator_function.conversion_type =
                substitute_pattern_type_ref(
                    record.operator_function.conversion_type,
                    argument_bindings,
                    callbacks);
        }
    }

    std::vector<std::pair<cir::EntityId, cir::TypeId>> params;
    params.reserve(pattern.parameters.size());
    for (const cir::FunctionParameter& parameter : pattern.parameters) {
        const cir::Entity source = file_.entity(parameter.entity);
        cir::TypeRef param_type = substitute_pattern_type_ref(
            file_.type_ref(source.type,
                           source.qualifiers,
                           source.memory_space),
            argument_bindings,
            callbacks);
        param_type = adjust_substituted_function_parameter(file_, param_type);
        if (!param_type.valid()) {
            note_pattern_clone_bail(PatternCloneBailReason::TypeSubstitution);
            return {};
        }
        cir::EntityId cloned = builder_.add_entity(
            cir::EntityKind::Parameter, file_.name(source.name), param_type.type,
            fn_entity, source.loc, cir::StorageDuration::Parameter,
            param_type.memory_space);
        file_.entity_mut(cloned).qualifiers = param_type.qualifiers;
        file_.entity_mut(cloned).owning_function = fn_entity;
        entity_map.emplace(parameter.entity.index, cloned);
        params.emplace_back(cloned, param_type.type);
    }
    {

        file_.entity_mut(fn_entity).type = instantiated_function_type;
        cir::Entity& specialization = file_.entity_mut(fn_entity);
        specialization.decl_flags.is_consteval =
            specialization.decl_flags.is_consteval ||
            consteval_only_function_type_immediately_escalates(
                instantiated_function_type,
                specialization.decl_flags.is_constexpr,
                specialization.kind,
                /*instantiated_templated_entity=*/true);
    }
    remember_template_specialization(fn_entity,
                                     info,
                                     arguments,
                                     loc,
                                     0,
                                     nullptr,
                                     nullptr,
                                     &argument_bindings);

    remember_instantiation(template_memo_key(info.entity, arguments),
                           fn_entity);

    cir::FunctionStart fn =
        builder_.begin_function(fn_entity, result_type, params, loc);

    {
        const cir::Block pattern_entry = file_.block(pattern.entry_block);
        for (size_t i = 0;
             i < pattern.parameters.size() && i < fn.parameters.size(); ++i) {
            inst_map.emplace(pattern.parameters[i].value.inst.index,
                             fn.parameters[i].value.inst);
        }
        for (size_t i = 0;
             i < pattern_entry.parameters.size() && i < fn.parameters.size();
             ++i) {
            inst_map.emplace(pattern_entry.parameters[i].index,
                             fn.parameters[i].value.inst);
        }
        block_map.emplace(pattern.entry_block.index, fn.entry);
    }

    current_function_ = fn.function;
    current_result_type_ = result_type;
    nrvo_return_candidates_.clear();

    nrvo_has_incompatible_return_ = true;
    active_catch_handlers_ = 0;
    active_constructor_function_try_handlers_ = 0;
    coroutine_state_.reset();
    first_plain_return_loc_ = {};
    has_plain_return_ = false;

    auto bind_parameters = [&]() {
        for (const auto& parameter : params) {
            const cir::Entity& cloned = file_.entity(parameter.first);
            auto place = param_places.find(parameter.first.index);
            bind_entity(file_.name(cloned.name),
                        cir::LookupNamespace::Ordinary,
                        parameter.first,
                        parameter.second,
                        false,
                        false,
                        true,
                        place == param_places.end() ? cir::InstId{}
                                                    : place->second,
                        cloned.loc);
        }
    };

    PatternCloneJob job;
    job.pattern = &pattern;
    job.first_block = 0;
    job.holes = &info.pattern_holes;
    job.hole_index_base = 0;
    job.events = &info.pattern_events;
    job.argument_bindings = &argument_bindings;
    job.callbacks = &callbacks;
    job.owner = fn_entity;
    job.attach_function = fn.function;
    job.before_first_hole = bind_parameters;
    job.entity_map = &entity_map;
    job.inst_map = &inst_map;
    job.block_map = &block_map;
    job.param_places = &param_places;
    if (!run_pattern_clone(job)) {
        return {};
    }
    return fn_entity;
}

bool Session::clone_member_pattern(const TemplateInfo& info,
                                   const MemberPattern& member,
                                   cir::EntityId method,
                                   const std::vector<TemplateArgument>& arguments,
                                   const std::vector<ParamInput>& instantiated_params,
                                   PatternInstantiationCallbacks& callbacks,
                                   SrcLoc loc,
                                   const TemplateArgumentBindings*
                                       exact_bindings) {
    if (pattern_clone_depth_ != 0) {
        note_pattern_clone_bail(PatternCloneBailReason::NestedClone);
        return false;
    }
    PatternCloneDepthScope clone_depth_scope(pattern_clone_depth_);

    reset_pattern_clone_bail();
    if (!member.usable || !member.function.valid() ||
        !file_.valid(member.function) || !info.pattern_record.valid() ||
        !method.valid() || !file_.valid(method)) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }
    const cir::Function pattern = file_.function(member.function);
    TemplateArgumentBindings argument_bindings;
    if (exact_bindings) {
        argument_bindings = *exact_bindings;
    } else {
        if (!bind_template_arguments_to_parameters(info.parameters,
                                                   arguments,
                                                   argument_bindings)) {
            note_pattern_clone_bail(PatternCloneBailReason::ArgumentBinding);
            return false;
        }
    }
    if (pattern.blocks.size() <
            member.body_start_block + member.body_block_count ||
        pattern.parameters.empty()) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }
    cir::EntityId instance_record = file_.entity(method).parent;
    if (!instance_record.valid()) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }

    cir::EntityId pattern_owner = file_.entity(member.method).parent;
    if (!pattern_owner.valid() || !file_.valid(pattern_owner) ||
        file_.entity(pattern_owner).kind != cir::EntityKind::Record) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }

    callbacks.self_pattern_type =
        file_.resolved_type(file_.entity(pattern_owner).type);
    callbacks.self_instance_type = file_.entity(instance_record).type;
    if (!callbacks.self_pattern_type.valid() ||
        !callbacks.self_instance_type.valid()) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }

    std::unordered_map<uint32_t, cir::EntityId> entity_map;
    std::unordered_map<uint32_t, cir::InstId> inst_map;
    std::unordered_map<uint32_t, cir::BlockId> block_map;
    entity_map.emplace(pattern_owner.index, instance_record);

    const cir::RecordFacts* pattern_facts =
        file_.record_facts(pattern_owner);
    const cir::RecordFacts* instance_facts =
        file_.record_facts(instance_record);
    if (!pattern_facts || !instance_facts ||
        !pattern_facts->virtual_bases.empty() ||
        !instance_facts->virtual_bases.empty()) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }
    if (pattern_facts->fields.size() == instance_facts->fields.size()) {
        for (size_t i = 0; i < pattern_facts->fields.size(); ++i) {
            if (pattern_facts->fields[i].name ==
                instance_facts->fields[i].name) {
                entity_map.emplace(pattern_facts->fields[i].entity.index,
                                   instance_facts->fields[i].entity);
            }
        }
    }
    if (pattern_facts->methods.size() == instance_facts->methods.size()) {
        for (size_t i = 0; i < pattern_facts->methods.size(); ++i) {
            if (pattern_facts->methods[i].name ==
                instance_facts->methods[i].name) {
                entity_map.emplace(pattern_facts->methods[i].entity.index,
                                   instance_facts->methods[i].entity);
            }
        }
    }

    FunctionDeclStart start =
        begin_member_function(method, instantiated_params, loc);
    if (start.decl.has_error || !start.function.function.valid()) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }

    for (size_t i = 0; i < pattern.parameters.size() &&
                       i < start.function.parameters.size();
         ++i) {
        entity_map.emplace(pattern.parameters[i].entity.index,
                           start.function.parameters[i].entity);
        inst_map.emplace(pattern.parameters[i].value.inst.index,
                         start.function.parameters[i].value.inst);
    }

    std::vector<cir::InstId> pattern_spills;
    for (size_t b = 1; b < member.body_start_block &&
                       b < pattern.blocks.size() &&
                       pattern_spills.size() < pattern.parameters.size();
         ++b) {
        for (cir::InstId inst_id : file_.block(pattern.blocks[b]).instructions) {
            if (file_.inst(inst_id).kind == cir::InstKind::LocalPlace &&
                pattern_spills.size() < pattern.parameters.size()) {
                pattern_spills.push_back(inst_id);
            }
        }
    }
    std::vector<cir::InstId> instance_spills;
    for (cir::BlockId block_id : current_prologue_.blocks) {
        for (cir::InstId inst_id : file_.block(block_id).instructions) {
            if (file_.inst(inst_id).kind == cir::InstKind::LocalPlace) {
                instance_spills.push_back(inst_id);
            }
        }
    }
    if (pattern_spills.size() != instance_spills.size()) {
        note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
        return false;
    }
    for (size_t i = 0; i < pattern_spills.size(); ++i) {
        inst_map.emplace(pattern_spills[i].index, instance_spills[i]);
    }

    cir::EntityKind method_kind = file_.entity(method).kind;
    StmtResult subobject_init;
    if (method_kind == cir::EntityKind::Constructor) {
        if (!callbacks.collect_subobject_init) {
            note_pattern_clone_bail(PatternCloneBailReason::PatternShape);
            return false;
        }
        subobject_init = callbacks.collect_subobject_init();
        if (subobject_init.has_error) {
            note_pattern_clone_bail(PatternCloneBailReason::HoleReplay);
            return false;
        }
    }

    std::vector<cir::BlockId> fragment_blocks;
    PatternCloneJob job;
    job.pattern = &pattern;
    job.first_block = member.body_start_block;
    job.block_count = member.body_block_count;
    job.holes = &member.holes;
    job.hole_index_base = member.hole_index_base;
    job.events = &member.events;
    job.argument_bindings = &argument_bindings;
    job.callbacks = &callbacks;
    job.owner = method;
    job.fragment_blocks = &fragment_blocks;
    job.entity_map = &entity_map;
    job.inst_map = &inst_map;
    job.block_map = &block_map;
    if (!run_pattern_clone(job)) {
        return false;
    }

    cir::Fragment cloned;
    if (member.body_block_count > 0) {
        size_t last =
            member.body_start_block + member.body_block_count - 1;
        cloned.blocks = std::move(fragment_blocks);
        cloned.entry =
            block_map.at(pattern.blocks[member.body_start_block].index);
        cloned.exit = block_map.at(pattern.blocks[last].index);
        cloned.falls_through = !builder_.block_terminated(cloned.exit);
    }
    cir::Fragment body =
        chain(std::move(subobject_init.fragment), std::move(cloned), loc);
    if (method_kind == cir::EntityKind::Destructor &&
        cloned.falls_through) {
        StmtResult epilogue = collect_destructor_epilogue(loc);
        body = chain(std::move(body), std::move(epilogue.fragment), loc);
    }
    finish_member_function(make_stmt_result(std::move(body), false, false),
                           loc);
    return true;
}

} // namespace aburi::collect
