#include "collect.h"
#include "collect_templates_internal.h"

#include <limits>
#include <optional>
#include <sstream>

using namespace template_sema_internal;

namespace {

RecordMemberAccess record_member_access_for(CppAccessSpecifier access) {
    switch (access) {
        case CppAccessSpecifier::Public:
            return RecordMemberAccess::Public;
        case CppAccessSpecifier::Protected:
            return RecordMemberAccess::Protected;
        case CppAccessSpecifier::Private:
            return RecordMemberAccess::Private;
        case CppAccessSpecifier::None:
            break;
    }
    return RecordMemberAccess::Public;
}

std::optional<std::string> namespace_prefix_from_member_qualifier(
    const std::string* qualifier_prefix) {
    if (!qualifier_prefix || qualifier_prefix->empty()) {
        return std::nullopt;
    }
    size_t pos = qualifier_prefix->rfind("::");
    if (pos == std::string::npos) {
        return std::nullopt;
    }
    if (pos == 0) {
        return std::nullopt;
    }
    return qualifier_prefix->substr(0, pos);
}

std::optional<std::string> namespace_prefix_for_specialized_member(
    const std::string* decl_qualifier_prefix,
    const Symbol* pattern_symbol) {
    if (auto namespace_prefix =
            namespace_prefix_from_member_qualifier(decl_qualifier_prefix)) {
        return namespace_prefix;
    }
    return namespace_prefix_from_member_qualifier(
        pattern_symbol ? get_symbol_cxx_qualifier_prefix(pattern_symbol) : nullptr);
}

struct ClassTemplatePartialSpecializationMatch {
    const ClassTemplatePartialSpecializationDecl* partial_specialization = nullptr;
    TemplateArgumentBindings bindings;
};

bool same_owner_type(QualType lhs, QualType rhs, const ASTContext* ast_ctx) {
    if (!lhs && !rhs) {
        return true;
    }
    if (!lhs || !rhs) {
        return false;
    }
    return desugar_type(lhs, ast_ctx).equals_unqualified(
        desugar_type(rhs, ast_ctx));
}

bool same_qualifier_prefix(const std::string* lhs, const std::string* rhs) {
    if (!lhs && !rhs) {
        return true;
    }
    if (!lhs || !rhs) {
        return false;
    }
    return *lhs == *rhs;
}

std::optional<size_t> aligned_attribute_value_after_substitution(
    Collect& collect,
    const AttributeArg& arg,
    std::string* error_out) {
    int64_t raw_alignment = 0;
    if (arg.kind == AttributeArg::Kind::INTEGER) {
        raw_alignment = arg.int_value;
    } else if (arg.kind == AttributeArg::Kind::EXPR && arg.expr_value) {
        if (collect.expression_depends_on_template_parameters(arg.expr_value.get())) {
            return std::nullopt;
        }
        auto evaluated = try_evaluate_with_consteval_compat(
            arg.expr_value.get(),
            ConstEvalMode::c_ice());
        if (!evaluated.has_value()) {
            if (error_out && error_out->empty()) {
                *error_out = "_Alignas requires a constant expression";
            }
            return std::nullopt;
        }
        raw_alignment = *evaluated;
    } else {
        return std::nullopt;
    }

    if (raw_alignment < 0) {
        if (error_out && error_out->empty()) {
            *error_out = "_Alignas requires a non-negative alignment";
        }
        return std::nullopt;
    }
    if (raw_alignment == 0) {
        return size_t{0};
    }
    if ((raw_alignment & (raw_alignment - 1)) != 0) {
        if (error_out && error_out->empty()) {
            *error_out = "_Alignas requires a power-of-two alignment";
        }
        return std::nullopt;
    }
    return static_cast<size_t>(raw_alignment);
}

size_t requested_alignment_from_decl_attrs(Collect& collect,
                                           ASTContext* ast_ctx,
                                           uint32_t node_id,
                                           SrcLoc loc,
                                           std::string* error_out = nullptr,
                                           SrcLoc* error_loc_out = nullptr) {
    if (!ast_ctx || !ast_ctx->has_attrs(node_id)) {
        return 0;
    }

    size_t best = 0;
    for (const auto& attr : ast_ctx->get_attrs(node_id).attrs) {
        if (attr.resolved_kind != AttributeKind::ALIGNED || attr.args.empty()) {
            continue;
        }
        std::string local_error;
        auto requested = aligned_attribute_value_after_substitution(
            collect,
            attr.args.front(),
            &local_error);
        SrcLoc attr_loc = attr.loc.isInvalid() ? loc : attr.loc;
        if (!local_error.empty()) {
            if (error_out && error_out->empty()) {
                *error_out = local_error;
            }
            if (error_loc_out) {
                *error_loc_out = attr_loc;
            }
            return 0;
        }
        if (!requested.has_value()) {
            continue;
        }
        if (*requested > best) {
            best = *requested;
        }
    }
    return best;
}

std::string make_virtual_slot_key(
    const std::string& method_name,
    QualType method_type) {
    return make_cpp_virtual_slot_key(method_name, method_type);
}

using BasePathStep = std::pair<const ObjectDecl*, bool>;

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

size_t count_public_base_subobjects(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl,
    const ASTContext* ast_ctx) {
    derived_decl = canonical_record_decl(derived_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl ||
        derived_decl == target_base_decl) {
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

        auto walk_base_edge = [&](const RecordSemanticState::Base& base) {
            const ObjectDecl* base_decl = canonical_record_decl(base.record_decl);
            if (!base_decl ||
                base.declared_access != RecordMemberAccess::Public ||
                active_stack.contains(base_decl)) {
                return;
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
        };

        if (current_decl == current_record_decl) {
            for (const auto& base : current_record_bases) {
                walk_base_edge(base);
            }
            return;
        }

        const RecordSemanticState* state =
            record_semantics_cache_lookup(current_decl, ast_ctx);
        if (!state) {
            return;
        }

        for (const auto& base : state->bases) {
            walk_base_edge(base);
        }
    };

    walk(derived_decl);
    return matched_subobjects.size();
}

bool has_public_unambiguous_base_path(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl,
    const ASTContext* ast_ctx) {
    return count_public_base_subobjects(
               derived_decl,
               target_base_decl,
               current_record_bases,
               current_record_decl,
               ast_ctx) == 1;
}

struct CovariantReturnTarget {
    enum class Kind : uint8_t {
        Invalid,
        Pointer,
        LValueReference,
        RValueReference,
    };
    Kind kind = Kind::Invalid;
    QualType object_type;
    const ObjectDecl* object_decl = nullptr;
};

CovariantReturnTarget extract_covariant_return_target(QualType return_type) {
    CovariantReturnTarget target;
    if (!return_type) {
        return target;
    }

    auto canonical_return = desugar_type(return_type);
    if (auto ptr_type = canonical_return.as_shared<PointerType>()) {
        target.kind = CovariantReturnTarget::Kind::Pointer;
        target.object_type = ptr_type->pointed_type;
    } else if (auto ref_type = canonical_return.as_shared<ReferenceType>()) {
        target.kind = ref_type->isRValueReference()
            ? CovariantReturnTarget::Kind::RValueReference
            : CovariantReturnTarget::Kind::LValueReference;
        target.object_type = ref_type->referred_type;
    } else {
        return target;
    }

    auto object_type =
        desugar_type(target.object_type).as_shared<ObjectType>();
    if (!object_type) {
        target.kind = CovariantReturnTarget::Kind::Invalid;
        target.object_type = QualType();
        return target;
    }
    target.object_decl =
        canonical_record_decl(dyn_cast<ObjectDecl>(object_type->get_decl()));
    if (!target.object_decl) {
        target.kind = CovariantReturnTarget::Kind::Invalid;
        target.object_type = QualType();
    }
    return target;
}

bool returns_are_covariant(
    QualType overriding_return,
    QualType overridden_return,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl,
    const ASTContext* ast_ctx) {
    if (!overriding_return || !overridden_return) {
        return false;
    }
    if (overriding_return.equals_unqualified(overridden_return)) {
        return true;
    }

    CovariantReturnTarget overriding_target =
        extract_covariant_return_target(overriding_return);
    CovariantReturnTarget overridden_target =
        extract_covariant_return_target(overridden_return);
    if (overriding_target.kind == CovariantReturnTarget::Kind::Invalid ||
        overridden_target.kind == CovariantReturnTarget::Kind::Invalid ||
        overriding_target.kind != overridden_target.kind ||
        !overriding_target.object_type ||
        !overridden_target.object_type ||
        !overriding_target.object_decl ||
        !overridden_target.object_decl) {
        return false;
    }

    if (!overridden_target.object_type.has_all_qualifiers_of(
            overriding_target.object_type)) {
        return false;
    }
    if (overriding_target.object_decl == overridden_target.object_decl) {
        return true;
    }
    return has_public_unambiguous_base_path(
        overriding_target.object_decl,
        overridden_target.object_decl,
        current_record_bases,
        current_record_decl,
        ast_ctx);
}

struct VirtualSlotState {
    size_t slot_index = 0;
    bool is_pure = false;
    bool is_final = false;
    bool is_destructor = false;
    std::shared_ptr<Symbol> final_symbol = nullptr;
    std::string name;
};

} // namespace

struct Collect::ClassTemplateSpecializationInstantiator {
    struct PendingMethodTemplateClone {
        const FunctionTemplateDecl* pattern_template = nullptr;
        const FuncDecl* pattern_function = nullptr;
        FunctionTemplateDecl* specialized_template = nullptr;
        std::unordered_map<const TemplateParameterDecl*,
                           const TemplateParameterDecl*> parameter_rebinds;
        std::unordered_map<const Symbol*, std::shared_ptr<Symbol>> symbol_remap;
    };
    struct PendingFunctionBodyClone {
        const FuncDecl* pattern_func = nullptr;
        FuncDecl* specialized_func = nullptr;
        bool use_implicit_this = true;
    };

    Collect& collect;
    const ClassTemplateDecl* class_template = nullptr;
    const std::vector<TemplateArgument>& arguments;
    SrcLoc loc;

    const CppRecordDecl* primary_pattern = nullptr;
    const CppRecordDecl* pattern = nullptr;
    const TemplateParameterList* selected_parameters = nullptr;
    const ObjectDecl* pattern_semantic_decl = nullptr;
    TemplateArgumentBindings specialization_bindings;
    std::vector<TemplateArgument> normalized_arguments;

    std::string specialization_name;
    bool is_union = false;
    ClassTemplateSpecializationEntry* entry = nullptr;

    const RecordSemanticState* pattern_state = nullptr;
    std::unordered_map<const CppMethodDecl*, std::shared_ptr<Symbol>>
        pattern_method_symbols;
    std::unordered_map<const CppConstructorDecl*, std::shared_ptr<Symbol>>
        pattern_constructor_symbols;
    std::unordered_map<const CppDestructorDecl*, std::shared_ptr<Symbol>>
        pattern_destructor_symbols;
    std::unordered_map<const VariableDecl*, std::shared_ptr<Symbol>>
        pattern_static_member_symbols;

    TemplateClonePassBuilder clone_pass_builder;
    TemplateSubstitutionPass clone_pass;
    TemplateSubstitutionPass* clone_pass_ptr = nullptr;

    QualType owner_type;
    std::vector<RecordSemanticState::Base> direct_bases;
    std::vector<RecordSemanticState::VirtualBase> virtual_bases;
    std::vector<ObjectType::Field> user_fields;
    std::vector<RecordSemanticState::Method> methods;
    std::vector<RecordSemanticState::MethodTemplate> method_templates;
    std::vector<RecordSemanticState::Constructor> constructors;
    std::vector<RecordSemanticState::Destructor> destructors;
    std::vector<RecordSemanticState::StaticDataMember> static_data_members;
    std::vector<RecordSemanticState::NestedType> nested_types;
    std::vector<RecordSemanticState::NestedTemplate> nested_templates;
    std::vector<RecordSemanticState::FriendFunction> friend_functions;
    std::vector<RecordSemanticState::EnumeratorMember> enumerator_members;
    std::unordered_map<const FuncDecl*, std::shared_ptr<Symbol>>
        specialized_member_symbols;
    std::vector<PendingMethodTemplateClone> pending_method_template_clones;
    std::vector<PendingFunctionBodyClone> pending_body_clones;
    std::vector<std::pair<const CppConstructorDecl*, CppConstructorDecl*>>
        pending_ctor_init_clones;
    RecordSemanticState semantic_state;

    ObjectDecl* run() {
        if (!class_template || !ast_ctx()) {
            return nullptr;
        }

        primary_pattern = class_template->record_decl();
        if (!primary_pattern) {
            collect.report_error("internal error: missing class template pattern", loc);
            return nullptr;
        }

        if (!bind_and_select_pattern()) {
            return nullptr;
        }
        if (auto* explicit_decl = try_explicit_specialization()) {
            return explicit_decl;
        }
        if (!prepare_entry()) {
            return nullptr;
        }
        if (!entry || !entry->specialization_decl) {
            return nullptr;
        }
        if (!entry->specialization_type) {
            entry->specialization_type = entry->specialization_decl->get_record_type();
        }
        if (entry->is_instantiated || entry->is_instantiating ||
            entry->instantiation_failed) {
            return entry->specialization_decl.get();
        }
        if (!ast_ctx()->push_template_instantiation_frame()) {
            collect.report_error(
                "template instantiation depth exceeded while instantiating class template '" +
                    specialization_name + "'",
                loc);
            entry->instantiation_failed = true;
            return entry->specialization_decl.get();
        }

        entry->is_instantiating = true;
        struct InstantiationGuard {
            ClassTemplateSpecializationEntry& entry;
            ~InstantiationGuard() { entry.is_instantiating = false; }
        } instantiation_guard{*entry};
        struct DepthGuard {
            ASTContext* ast_ctx = nullptr;
            ~DepthGuard() {
                if (ast_ctx) {
                    ast_ctx->pop_template_instantiation_frame();
                }
            }
        } depth_guard{ast_ctx()};

        build_pattern_symbol_maps();
        owner_type = QualType(entry->specialization_type);
        if (!instantiate_base_graph() ||
            !initialize_clone_pass() ||
            !instantiate_members()) {
            return entry->specialization_decl.get();
        }

        if (!build_semantic_state()) {
            return entry->specialization_decl.get();
        }
        if (!resolve_static_data_members() ||
            !clone_pending_member_templates() ||
            !clone_pending_member_bodies()) {
            return entry->specialization_decl.get();
        }

        collect.collect_record_publish_state(
            entry->specialization_decl.get(),
            entry->specialization_type,
            semantic_state);
        entry->is_instantiated = pattern->is_definition;
        return entry->specialization_decl.get();
    }

    ASTContext* ast_ctx() const { return collect.ast_ctx_.get(); }

    bool fail_instantiation(const std::string& message, SrcLoc error_loc) {
        collect.report_error(message, error_loc);
        if (entry) {
            entry->instantiation_failed = true;
        }
        return false;
    }

    bool substitute_member_explicit_specifier(
        const CppExplicitSpecifier& pattern_specifier,
        FuncDecl* specialized_decl,
        CppExplicitSpecifier& specialized_specifier,
        bool& effective_value_out) {
        QualType specialized_this_type =
            template_sema_internal::implicit_this_type_for_specialized_function(
                specialized_decl);
        auto resolution_pass =
            clone_pass_builder.build_dependent_resolution_pass(
                clone_pass,
                [&](std::unique_ptr<Expr>& expr,
                    std::string* error_out) -> bool {
                    return collect.resolve_dependent_expr_after_substitution(
                        expr,
                        specialized_this_type,
                        error_out);
                });
        std::string explicit_error;
        if (!substitute_cpp_explicit_specifier_for_specialization(
                collect,
                pattern_specifier,
                specialized_specifier,
                clone_pass,
                resolution_pass,
                loc,
                &explicit_error)) {
            return fail_instantiation(
                explicit_error.empty()
                    ? "failed to substitute explicit specifier expression"
                    : explicit_error,
                pattern_specifier.location.isInvalid()
                    ? loc
                    : pattern_specifier.location);
        }
        effective_value_out = specialized_specifier.effective_value;
        return true;
    }

    bool bind_and_select_pattern() {
        std::string binding_error;
        if (!collect.bind_template_arguments_for_specialization(
                class_template,
                arguments,
                specialization_bindings,
                loc,
                &binding_error)) {
            collect.report_error(
                "class template '" + primary_pattern->name +
                    "' template arguments do not match the parameter list" +
                    (binding_error.empty() ? std::string() : ": " + binding_error),
                loc);
            return false;
        }

        for (const auto& argument : arguments) {
            if (!template_argument_has_known_payload(argument)) {
                collect.report_error("class template argument has unknown type", loc);
                return false;
            }
        }
        for (size_t idx = 0; idx < class_template->parameters.size(); ++idx) {
            auto* non_type_parameter = dyn_cast<TemplateNonTypeParmDecl>(
                class_template->parameters[idx].get());
            if (!non_type_parameter || idx >= specialization_bindings.size()) {
                continue;
            }
            if (specialization_bindings[idx].arguments.empty()) {
                continue;
            }
            QualType expected_type = collect.substitute_template_type_with_bindings(
                non_type_parameter->type,
                class_template->parameters,
                specialization_bindings,
                loc);
            expected_type =
                collect.finalize_deferred_semantic_type(expected_type, loc);
            for (auto& bound_argument : specialization_bindings[idx].arguments) {
                std::string normalize_error;
                if (!normalize_concrete_template_value_argument(
                        bound_argument,
                        expected_type,
                        &normalize_error)) {
                    collect.report_error(
                        normalize_error.empty()
                            ? "failed to normalize class template value argument"
                            : normalize_error,
                        loc);
                    return false;
                }
            }
        }

        normalized_arguments =
            flatten_template_argument_bindings(specialization_bindings);
        pattern = primary_pattern;
        selected_parameters = &class_template->parameters;
        pattern_semantic_decl = class_template->pattern_semantic_decl();

        bool specialization_is_dependent =
            template_arguments_depend_on_template_parameters(normalized_arguments);
        if (!specialization_is_dependent &&
            !collect.are_template_constraints_satisfied_with_bindings(
                class_template,
                specialization_bindings,
                loc)) {
            collect.report_error(
                "constraints not satisfied for class template '" +
                    primary_pattern->name + "'",
                loc);
            return false;
        }

        std::vector<ClassTemplatePartialSpecializationMatch> matching_partials;
        matching_partials.reserve(class_template->partial_specializations().size());
        for (const auto* partial_specialization :
             class_template->partial_specializations()) {
            if (!partial_specialization) {
                continue;
            }
            TemplateArgumentBindings partial_bindings;
            if (!deduce_class_template_partial_specialization_bindings(
                    partial_specialization,
                    normalized_arguments,
                    partial_bindings)) {
                continue;
            }
            auto partial_arguments =
                flatten_template_argument_bindings(partial_bindings);
            if (!template_arguments_depend_on_template_parameters(partial_arguments) &&
                !collect.are_template_constraints_satisfied_with_bindings(
                    partial_specialization,
                    partial_bindings,
                    loc)) {
                continue;
            }
            matching_partials.push_back(ClassTemplatePartialSpecializationMatch{
                partial_specialization,
                std::move(partial_bindings)});
        }
        if (!matching_partials.empty()) {
            std::vector<size_t> maximal_matches;
            for (size_t idx = 0; idx < matching_partials.size(); ++idx) {
                bool is_less_specialized = false;
                for (size_t other_idx = 0; other_idx < matching_partials.size();
                     ++other_idx) {
                    if (idx == other_idx) {
                        continue;
                    }
                    if (is_class_template_partial_specialization_more_specialized(
                            matching_partials[other_idx].partial_specialization,
                            matching_partials[idx].partial_specialization)) {
                        is_less_specialized = true;
                        break;
                    }
                }
                if (!is_less_specialized) {
                    maximal_matches.push_back(idx);
                }
            }
            if (maximal_matches.size() != 1) {
                collect.report_error(
                    "ambiguous partial specialization for class template '" +
                        primary_pattern->name + "'",
                    loc);
                return false;
            }
            auto& selected_partial_match =
                matching_partials[maximal_matches.front()];
            pattern = selected_partial_match.partial_specialization->record_decl();
            selected_parameters =
                &selected_partial_match.partial_specialization->parameters;
            pattern_semantic_decl =
                selected_partial_match.partial_specialization
                    ->pattern_semantic_decl();
            specialization_bindings = std::move(selected_partial_match.bindings);
        }

        if (!pattern) {
            collect.report_error(
                "internal error: missing selected class template pattern",
                loc);
            return false;
        }
        return true;
    }

    ObjectDecl* try_explicit_specialization() const {
        if (const auto* explicit_specialization =
                class_template->find_explicit_specialization(
                    normalized_arguments)) {
            if (auto* explicit_decl =
                    explicit_specialization->specialized_record_semantic_decl()) {
                return const_cast<ObjectDecl*>(explicit_decl);
            }
            collect.report_error(
                "internal error: explicit class specialization is missing its semantic declaration",
                loc);
        }
        return nullptr;
    }

    bool prepare_entry() {
        specialization_name = make_class_template_specialization_name(
            class_template,
            normalized_arguments);
        is_union = pattern->record_kind == CppRecordKind::Union;

        if (auto* existing =
                ast_ctx()->lookup_class_template_specialization(
                    class_template,
                    normalized_arguments);
            existing && existing->specialization_decl) {
            existing->note_first_required_loc(loc);
            entry = existing;
            return true;
        }

        auto specialization_type = std::make_shared<ObjectType>(
            specialization_name,
            is_union,
            !pattern->is_definition);
        specialization_type->set_class_template_specialization_info(
            class_template,
            normalized_arguments);
        auto specialization_decl = collect.collect_make<ObjectDecl>(
            specialization_name,
            specialization_type,
            is_union,
            loc);

        RecordSemanticState placeholder_state;
        placeholder_state.is_incomplete = true;
        collect.query_publish_record_semantics(specialization_decl.get(),
                                               std::move(placeholder_state));

        auto& specialization_entry =
            ast_ctx()->get_or_create_class_template_specialization(
                class_template,
                normalized_arguments,
                specialization_type,
                std::move(specialization_decl));
        specialization_entry.note_first_required_loc(loc);
        entry = &specialization_entry;
        return true;
    }

    void build_pattern_symbol_maps() {
        pattern_state = pattern_semantic_decl
            ? collect.query_lookup_record_semantics(pattern_semantic_decl)
            : nullptr;
        pattern_method_symbols.clear();
        pattern_constructor_symbols.clear();
        pattern_destructor_symbols.clear();
        pattern_static_member_symbols.clear();
        if (!pattern_state) {
            return;
        }
        for (const auto& method : pattern_state->methods) {
            if (method.decl && method.symbol) {
                pattern_method_symbols.emplace(method.decl, method.symbol);
            }
        }
        for (const auto& ctor : pattern_state->constructors) {
            if (ctor.decl && ctor.symbol) {
                pattern_constructor_symbols.emplace(ctor.decl, ctor.symbol);
            }
        }
        for (const auto& dtor : pattern_state->destructors) {
            if (dtor.decl && dtor.symbol) {
                pattern_destructor_symbols.emplace(dtor.decl, dtor.symbol);
            }
        }
        for (const auto& static_member : pattern_state->static_data_members) {
            if (static_member.decl && static_member.symbol) {
                pattern_static_member_symbols.emplace(
                    static_member.decl,
                    static_member.symbol);
            }
        }
    }

    QualType rewrite_class_template_type(
        QualType type,
        const TemplateArgumentBindings& active_bindings) const {
        auto rewritten = collect.substitute_template_type_with_bindings(
            type,
            *selected_parameters,
            active_bindings,
            loc,
            true);
        rewritten = replace_record_decl_in_type(
            rewritten,
            pattern_semantic_decl,
            QualType(entry->specialization_type),
            ast_ctx());
        static const std::unordered_map<const TemplateParameterDecl*,
                                        const TemplateParameterDecl*>
            kNoParameterRebinds;
        rewritten = remap_template_parameter_types_in_type(
            rewritten,
            kNoParameterRebinds,
            &const_cast<TemplateSubstitutionPass&>(clone_pass).context());
        return collect.finalize_deferred_semantic_type(rewritten, loc);
    }

    std::vector<TemplateArgument> rewrite_class_template_arguments(
        const std::vector<TemplateArgument>& template_arguments,
        const TemplateArgumentBindings& active_bindings) const {
        return collect.substitute_template_arguments_with_bindings(
            template_arguments,
            *selected_parameters,
            active_bindings,
            loc,
            true);
    }

    bool instantiate_base_graph() {
        direct_bases.clear();
        virtual_bases.clear();
        if (pattern->bases.empty()) {
            return true;
        }
        if (!pattern_state) {
            return fail_instantiation(
                "internal error: missing class template pattern semantic state for base instantiation",
                loc);
        }

        direct_bases.reserve(pattern_state->bases.size());
        std::unordered_set<const ObjectDecl*> seen_direct_bases;
        seen_direct_bases.reserve(pattern_state->bases.size());

        for (const auto& pattern_base : pattern_state->bases) {
            const CppBaseSpecifier* base_spec = pattern_base.spec;
            SrcLoc base_loc = base_spec ? base_spec->location : loc;
            if (base_spec && base_spec->is_pack_expansion) {
                return fail_instantiation(
                    "class template base-specifier pack expansions are not supported yet",
                    base_loc);
            }

            RecordSemanticState::Base specialized_base;
            specialized_base.name = !pattern_base.name.empty()
                ? pattern_base.name
                : (base_spec ? base_spec->type_name : std::string());
            specialized_base.declared_access = pattern_base.declared_access;
            specialized_base.is_virtual = pattern_base.is_virtual;
            specialized_base.spec = base_spec;

            QualType base_type = pattern_base.type;
            if (!base_type && base_spec) {
                base_type = base_spec->type;
            }
            if (base_type) {
                base_type =
                    rewrite_class_template_type(base_type, specialization_bindings);
            } else if (base_spec && !base_spec->type_name.empty()) {
                base_type = collect.collect_lookup_type_name(
                    base_spec->type_name,
                    true,
                    true);
            }
            base_type = collect.finalize_deferred_semantic_type(base_type, base_loc);

            auto base_object = desugar_type(base_type).as_shared<ObjectType>();
            auto* base_record_decl =
                base_object ? dyn_cast<ObjectDecl>(base_object->get_decl()) : nullptr;
            if (!base_record_decl) {
                if (base_type &&
                    type_depends_on_template_parameters(base_type, ast_ctx())) {
                    return fail_instantiation(
                        "class template base type remains dependent after substitution",
                        base_loc);
                }
                return fail_instantiation(
                    "base type '" + specialized_base.name +
                        "' does not name a class or struct",
                    base_loc);
            }

            const ObjectDecl* canonical_base_decl = canonical_record_decl(base_record_decl);
            if (!canonical_base_decl) {
                return fail_instantiation(
                    "internal error: failed to canonicalize template base class",
                    base_loc);
            }
            if (canonical_base_decl == entry->specialization_decl.get()) {
                return fail_instantiation(
                    "class '" + specialization_name + "' cannot derive from itself",
                    base_loc);
            }
            if (!seen_direct_bases.insert(canonical_base_decl).second) {
                return fail_instantiation(
                    "duplicate direct base class '" + specialized_base.name + "'",
                    base_loc);
            }
            if (canonical_base_decl->is_union) {
                return fail_instantiation(
                    "base type '" + specialized_base.name +
                        "' is a union; only class/struct bases are supported",
                    base_loc);
            }
            const RecordSemanticState* base_state =
                collect.query_lookup_record_semantics(canonical_base_decl);
            if (!base_state || base_state->is_incomplete) {
                return fail_instantiation(
                    "base class '" + specialized_base.name + "' is incomplete",
                    base_loc);
            }

            specialized_base.record_decl = canonical_base_decl;
            specialized_base.type = QualType(canonical_base_decl->get_record_type());
            direct_bases.push_back(std::move(specialized_base));
        }

        std::unordered_set<const ObjectDecl*> seen_virtual_base_decls;
        std::unordered_set<const ObjectDecl*> visited_base_graph;
        auto append_virtual_base = [&](const RecordSemanticState::Base& base_edge) {
            const ObjectDecl* virtual_base_decl = base_edge.record_decl;
            if (!virtual_base_decl) {
                return;
            }
            if (!seen_virtual_base_decls.insert(virtual_base_decl).second) {
                return;
            }
            RecordSemanticState::VirtualBase virtual_base;
            virtual_base.name = !base_edge.name.empty()
                ? base_edge.name
                : virtual_base_decl->tag;
            virtual_base.type = QualType(virtual_base_decl->get_record_type());
            virtual_base.declared_access = base_edge.declared_access;
            virtual_base.record_decl = virtual_base_decl;
            virtual_bases.push_back(std::move(virtual_base));
        };
        std::function<void(const ObjectDecl*)> walk_base_graph =
            [&](const ObjectDecl* current_decl) {
            if (!current_decl || visited_base_graph.contains(current_decl)) {
                return;
            }
            visited_base_graph.insert(current_decl);
            const RecordSemanticState* current_state =
                collect.query_lookup_record_semantics(current_decl);
            if (!current_state) {
                return;
            }
            for (const auto& inherited_base : current_state->bases) {
                if (!inherited_base.record_decl) {
                    continue;
                }
                if (inherited_base.is_virtual) {
                    append_virtual_base(inherited_base);
                }
                walk_base_graph(inherited_base.record_decl);
            }
        };
        for (const auto& direct_base : direct_bases) {
            if (direct_base.is_virtual) {
                append_virtual_base(direct_base);
            }
            walk_base_graph(direct_base.record_decl);
        }
        return true;
    }

    bool build_pack_element_bindings(
        size_t element_index,
        TemplateArgumentBindings& element_bindings,
        std::string* error_out) const {
        return build_pack_element_argument_bindings(
            *selected_parameters,
            specialization_bindings,
            element_index,
            element_bindings,
            error_out);
    }

    bool initialize_clone_pass() {
        auto register_specialized_member_symbol =
            [this](const std::shared_ptr<Symbol>& sym) {
                collect.collect_add_global_symbol(sym);
            };
        auto rewrite_specialized_record_member_expr =
            [this](MemberExpr* member_expr, std::string* error_out) -> bool {
                return rebind_member_expr_for_specialized_record(
                    member_expr,
                    ast_ctx(),
                    error_out);
            };

        clone_pass_builder = make_template_binding_clone_pass_builder(
            ast_ctx(),
            &collect,
            *selected_parameters,
            specialization_bindings,
            loc,
            "class template non-type parameter requires a concrete integral value",
            [this](QualType type) -> QualType {
                return rewrite_class_template_type(type, specialization_bindings);
            },
            [this](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                return rewrite_class_template_arguments(
                    template_arguments,
                    specialization_bindings);
            },
            register_specialized_member_symbol,
            rewrite_specialized_record_member_expr);
        clone_pass_builder.rewrite_symbol =
            [](const std::shared_ptr<Symbol>& sym,
               ASTCloneContext& clone_ctx) -> std::shared_ptr<Symbol> {
                if (!sym) {
                    return nullptr;
                }
                if (auto remapped =
                        lookup_symbol_remap_in_clone_context(sym, clone_ctx)) {
                    return remapped;
                }
                return sym;
            };
        clone_pass_ptr = nullptr;
        clone_pass_builder.expand_pack_expansion =
            [this](const Expr* pattern_expr,
                   std::vector<std::unique_ptr<Expr>>& expanded_out,
                   std::string* error_out) -> bool {
                return expand_class_pack_expansion(
                    pattern_expr,
                    expanded_out,
                    error_out);
            };
        clone_pass = clone_pass_builder.build_substitution_pass();
        clone_pass_ptr = &clone_pass;
        return true;
    }

    bool expand_class_pack_expansion(
        const Expr* pattern_expr,
        std::vector<std::unique_ptr<Expr>>& expanded_out,
        std::string* error_out) {
        template_sema_internal::TemplatePackExpansionShape shape;
        if (!collect_pack_expansion_shape_in_expr(
                pattern_expr,
                *selected_parameters,
                shape)) {
            if (error_out && error_out->empty()) {
                *error_out =
                    shape.has_unsupported_dependency
                        ? "class template pack expansion depends on unsupported template parameters"
                        : "failed to collect class template pack expansion shape";
            }
            return false;
        }
        if (shape.has_unsupported_dependency) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "class template pack expansion depends on unsupported template parameters";
            }
            return false;
        }

        std::string arity_error;
        auto expansion_arity = find_pack_expansion_arity_for_bindings(
            shape,
            *selected_parameters,
            specialization_bindings,
            &arity_error);
        if (!expansion_arity.has_value()) {
            if (error_out) {
                *error_out =
                    arity_error.empty()
                        ? "failed to determine class template pack expansion arity"
                        : arity_error;
            }
            return false;
        }

        auto register_specialized_member_symbol =
            [this](const std::shared_ptr<Symbol>& sym) {
                collect.collect_add_global_symbol(sym);
            };
        auto rewrite_specialized_record_member_expr =
            [this](MemberExpr* member_expr, std::string* error_out) -> bool {
                return rebind_member_expr_for_specialized_record(
                    member_expr,
                    ast_ctx(),
                    error_out);
            };

        expanded_out.clear();
        expanded_out.reserve(*expansion_arity);
        for (size_t element_index = 0;
             element_index < *expansion_arity;
             ++element_index) {
            TemplateArgumentBindings element_bindings;
            std::string element_binding_error;
            if (!build_pack_element_bindings(
                    element_index,
                    element_bindings,
                    &element_binding_error)) {
                if (error_out) {
                    *error_out =
                        element_binding_error.empty()
                            ? "failed to materialize class template pack expansion bindings"
                            : element_binding_error;
                }
                return false;
            }

            auto element_builder = make_template_binding_clone_pass_builder(
                ast_ctx(),
                &collect,
                *selected_parameters,
                element_bindings,
                loc,
                "class template non-type parameter requires a concrete integral value",
                [this, &element_bindings](QualType type) -> QualType {
                    return rewrite_class_template_type(type, element_bindings);
                },
                [this, &element_bindings](
                    const std::vector<TemplateArgument>& template_arguments)
                    -> std::vector<TemplateArgument> {
                    return rewrite_class_template_arguments(
                        template_arguments,
                        element_bindings);
                },
                register_specialized_member_symbol,
                rewrite_specialized_record_member_expr);
            element_builder.lookup_pack_size = clone_pass_builder.lookup_pack_size;
            if (clone_pass_ptr) {
                element_builder.symbol_remap =
                    clone_pass_ptr->context().symbol_remap;
            }
            element_builder.rewrite_symbol = clone_pass_builder.rewrite_symbol;

            auto element_pass = element_builder.build_substitution_pass();
            std::string element_clone_error;
            auto expanded_expr =
                element_pass.clone_expr(pattern_expr, &element_clone_error);
            if (!expanded_expr) {
                if (error_out) {
                    *error_out =
                        element_clone_error.empty()
                            ? "class template pack expansion expression cloning is not supported"
                            : element_clone_error;
                }
                return false;
            }
            expanded_out.push_back(std::move(expanded_expr));
        }
        return true;
    }

    QualType rewrite_class_pack_element_type(
        QualType type,
        size_t element_index,
        std::string* error_out) const {
        TemplateArgumentBindings element_bindings;
        std::string binding_error;
        if (!build_pack_element_bindings(
                element_index,
                element_bindings,
                &binding_error)) {
            if (error_out && error_out->empty()) {
                *error_out =
                    binding_error.empty()
                        ? "failed to materialize class-template pack element bindings"
                        : binding_error;
            }
            return QualType();
        }
        return rewrite_class_template_type(type, element_bindings);
    }

    std::shared_ptr<Symbol> lookup_existing_function_symbol_for_decl(
        const FuncDecl* decl) const {
        if (!decl) {
            return nullptr;
        }

        QualType decl_owner_type = get_func_decl_owner_record_type(decl);
        const auto* decl_qualifier_prefix =
            get_func_decl_cxx_qualifier_prefix(decl);
        std::function<std::shared_ptr<Symbol>(const DeclContext*)>
            lookup_in_decl_context =
                [&](const DeclContext* decl_context) -> std::shared_ptr<Symbol> {
                    if (!decl_context) {
                        return nullptr;
                    }
                    for (const auto& binding : decl_context->declarations()) {
                        if (!binding.symbol ||
                            binding.symbol->kind != SymbolKind::FUNCTION) {
                            continue;
                        }
                        auto& symbol = binding.symbol;
                        if (symbol->function_definition == decl) {
                            return symbol;
                        }
                        if (!symbol->type ||
                            !desugar_type(symbol->type, ast_ctx())
                                 .equals_unqualified(
                                     desugar_type(QualType(decl->type), ast_ctx()))) {
                            continue;
                        }
                        if (decl_owner_type &&
                            !same_owner_type(
                                get_symbol_owner_record_type(symbol.get()),
                                decl_owner_type,
                                ast_ctx())) {
                            continue;
                        }
                        if (decl_qualifier_prefix &&
                            !same_qualifier_prefix(
                                get_symbol_cxx_qualifier_prefix(symbol.get()),
                                decl_qualifier_prefix)) {
                            continue;
                        }
                        return symbol;
                    }
                    for (const auto& child : decl_context->lexical_children()) {
                        if (auto symbol = lookup_in_decl_context(child.get())) {
                            return symbol;
                        }
                    }
                    return nullptr;
                };

        if (collect.session_.translation_unit_decl_context_) {
            if (auto symbol = lookup_in_decl_context(
                    collect.session_.translation_unit_decl_context_.get())) {
                return symbol;
            }
        }
        if (!collect.session_.current_global_scope_) {
            return nullptr;
        }
        auto it =
            collect.session_.current_global_scope_->all_variables.find(decl->name);
        if (it == collect.session_.current_global_scope_->all_variables.end()) {
            return nullptr;
        }
        for (const auto& symbol : it->second) {
            if (!symbol || symbol->kind != SymbolKind::FUNCTION) {
                continue;
            }
            if (symbol->function_definition == decl) {
                return symbol;
            }
            if (!symbol->type ||
                !desugar_type(symbol->type, ast_ctx())
                     .equals_unqualified(
                         desugar_type(QualType(decl->type), ast_ctx()))) {
                continue;
            }
            if (decl_owner_type &&
                !same_owner_type(
                    get_symbol_owner_record_type(symbol.get()),
                    decl_owner_type,
                    ast_ctx())) {
                continue;
            }
            if (decl_qualifier_prefix &&
                !same_qualifier_prefix(
                    get_symbol_cxx_qualifier_prefix(symbol.get()),
                    decl_qualifier_prefix)) {
                continue;
            }
            return symbol;
        }
        return nullptr;
    }

    std::shared_ptr<Symbol> ensure_explicit_member_function_symbol(
        const FuncDecl* decl,
        bool is_definition) const {
        auto symbol = lookup_existing_function_symbol_for_decl(decl);
        if (symbol) {
            if (QualType explicit_owner_type =
                    get_func_decl_owner_record_type(decl)) {
                set_symbol_owner_record_type(symbol.get(), explicit_owner_type);
            }
            if (const auto* qualifier_prefix =
                    get_func_decl_cxx_qualifier_prefix(decl)) {
                set_symbol_cxx_qualifier_prefix(symbol.get(), *qualifier_prefix);
            }
            symbol->type = QualType(decl->type);
            symbol->is_constexpr = decl->is_constexpr;
            symbol->is_consteval = decl->is_consteval;
            symbol->is_deleted = decl->is_deleted;
            symbol->is_defaulted = decl->is_defaulted;
            symbol->is_defined = is_definition;
            symbol->set_language_linkage(decl->get_language_linkage());
            if (is_definition) {
                symbol->function_definition = const_cast<FuncDecl*>(decl);
            }
            return symbol;
        }

        VariableLinkage linkage =
            function_symbol_linkage_for_storage(
                decl->storage_class,
                static_cast<bool>(get_func_decl_owner_record_type(decl)));
        auto synthesized_symbol = std::make_shared<Symbol>(
            decl->name,
            SymbolKind::FUNCTION,
            QualType(decl->type),
            decl->storage_class,
            linkage,
            decl->is_inline != 0);
        synthesized_symbol->is_defined = is_definition;
        synthesized_symbol->is_constexpr = decl->is_constexpr;
        synthesized_symbol->is_consteval = decl->is_consteval;
        synthesized_symbol->is_deleted = decl->is_deleted;
        synthesized_symbol->is_defaulted = decl->is_defaulted;
        synthesized_symbol->set_language_linkage(
            decl->get_language_linkage());
        synthesized_symbol->function_definition =
            is_definition ? const_cast<FuncDecl*>(decl) : nullptr;
        if (decl->asm_label) {
            synthesized_symbol->asm_label = *decl->asm_label;
        }
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(decl)) {
            set_symbol_cxx_qualifier_prefix(
                synthesized_symbol.get(),
                *qualifier_prefix);
        }
        if (QualType explicit_owner_type = get_func_decl_owner_record_type(decl)) {
            set_symbol_owner_record_type(
                synthesized_symbol.get(),
                explicit_owner_type);
        }
        collect.collect_add_global_symbol(synthesized_symbol);
        return synthesized_symbol;
    }

    const TemplateExplicitSpecializationDecl* find_explicit_member_specialization(
        const Decl* primary_member_decl) const {
        if (!primary_member_decl) {
            return nullptr;
        }
        return class_template->find_explicit_specialization(
            normalized_arguments,
            {},
            primary_member_decl);
    }

    void reserve_member_storage() {
        user_fields.clear();
        methods.clear();
        method_templates.clear();
        constructors.clear();
        destructors.clear();
        static_data_members.clear();
        nested_types.clear();
        nested_templates.clear();
        friend_functions.clear();
        enumerator_members.clear();
        specialized_member_symbols.clear();
        pending_method_template_clones.clear();
        pending_body_clones.clear();
        pending_ctor_init_clones.clear();

        user_fields.reserve(pattern->members.size());
        methods.reserve(pattern->members.size());
        method_templates.reserve(pattern->members.size());
        constructors.reserve(pattern->members.size());
        destructors.reserve(pattern->members.size());
        static_data_members.reserve(pattern->members.size());
        nested_types.reserve(pattern->members.size());
        nested_templates.reserve(pattern->members.size());
        friend_functions.reserve(pattern->members.size());
        enumerator_members.reserve(pattern->members.size());
        specialized_member_symbols.reserve(pattern->members.size());
        pending_method_template_clones.reserve(pattern->members.size());
        pending_body_clones.reserve(pattern->members.size());
        pending_ctor_init_clones.reserve(pattern->members.size());
        entry->member_decls.clear();
        entry->member_decls.reserve(pattern->members.size());
    }

    std::shared_ptr<Symbol> clone_member_symbol(
        const std::shared_ptr<Symbol>& pattern_symbol,
        QualType rewritten_type,
        const std::string* qualifier_prefix,
        bool register_global_symbol) {
        std::shared_ptr<Symbol> cloned_symbol = pattern_symbol
            ? clone_symbol_shallow_for_specialization(pattern_symbol, rewritten_type)
            : std::make_shared<Symbol>("", SymbolKind::FUNCTION, rewritten_type);
        if (qualifier_prefix && !qualifier_prefix->empty()) {
            set_symbol_cxx_qualifier_prefix(cloned_symbol.get(), *qualifier_prefix);
        }
        set_symbol_owner_record_type(cloned_symbol.get(), owner_type);
        if (register_global_symbol) {
            collect.collect_add_global_symbol(cloned_symbol);
        }
        if (pattern_symbol) {
            clone_pass.context().symbol_remap.emplace(
                pattern_symbol.get(),
                cloned_symbol);
        }
        return cloned_symbol;
    }

    void publish_provisional_nested_members() {
        RecordSemanticState provisional_state;
        if (const auto* existing_state =
                collect.query_lookup_record_semantics(
                    entry->specialization_decl.get())) {
            provisional_state = *existing_state;
        }
        provisional_state.is_incomplete = true;
        provisional_state.static_data_members = static_data_members;
        provisional_state.nested_types = nested_types;
        provisional_state.nested_templates = nested_templates;
        provisional_state.friend_functions = friend_functions;
        provisional_state.enumerator_members = enumerator_members;
        collect.query_publish_record_semantics(entry->specialization_decl.get(),
                                               std::move(provisional_state));
    }

    void try_finalize_static_member_for_later_members(
        std::unique_ptr<Decl>& member_decl) {
        auto* static_member = dyn_cast<VariableDecl>(member_decl.get());
        if (!static_member || !static_member->init ||
            static_member->get_cpp_construct_init()) {
            return;
        }

        auto resolution_pass =
            clone_pass_builder.build_dependent_resolution_pass(
                clone_pass,
                [this](std::unique_ptr<Expr>& expr, std::string* error_out)
                    -> bool {
                    return collect.resolve_dependent_expr_after_substitution(
                        expr,
                        QualType(),
                        error_out);
                });

        std::string ignored_error;
        if (!resolution_pass.resolve_decl_in_place(member_decl, &ignored_error)) {
            return;
        }
        if (!template_sema_internal::finalize_specialized_decl_semantics(
                collect,
                member_decl,
                &ignored_error)) {
            return;
        }
    }

    bool instantiate_members() {
        reserve_member_storage();

        CppAccessSpecifier current_access = pattern->default_access;
        for (const auto& member : pattern->members) {
            if (!member) {
                continue;
            }
            if (auto* access_decl = dyn_cast<CppAccessSpecDecl>(member.get())) {
                current_access = access_decl->access;
                continue;
            }
            if (!instantiate_member(
                    member.get(),
                    record_member_access_for(current_access))) {
                return false;
            }
        }
        return true;
    }

    bool instantiate_member(const Decl* member, RecordMemberAccess declared_access) {
        if (auto* nested_record = dyn_cast<CppRecordDecl>(member)) {
            return handle_nested_record_member(nested_record, declared_access);
        }
        if (auto* field_decl = dyn_cast<FieldDecl>(member)) {
            return handle_field_member(field_decl, declared_access);
        }
        if (auto* enum_decl = dyn_cast<EnumDecl>(member)) {
            return handle_enum_member(enum_decl, declared_access);
        }
        if (auto* static_member = dyn_cast<VariableDecl>(member)) {
            return handle_static_member(static_member, declared_access);
        }
        if (auto* typedef_decl = dyn_cast<TypedefDecl>(member)) {
            return handle_typedef_member(typedef_decl, declared_access);
        }
        if (auto* alias_template_decl = dyn_cast<AliasTemplateDecl>(member)) {
            return handle_alias_template_member(alias_template_decl, declared_access);
        }
        if (auto* friend_decl = dyn_cast<FriendDecl>(member)) {
            return handle_friend_member(friend_decl);
        }
        if (auto* method_template_decl = dyn_cast<FunctionTemplateDecl>(member)) {
            return handle_method_template_member(
                method_template_decl,
                declared_access);
        }
        if (auto* method_decl = dyn_cast<CppMethodDecl>(member)) {
            return handle_method_member(method_decl, declared_access);
        }
        if (auto* ctor_decl = dyn_cast<CppConstructorDecl>(member)) {
            return handle_constructor_member(ctor_decl, declared_access);
        }
        if (auto* dtor_decl = dyn_cast<CppDestructorDecl>(member)) {
            return handle_destructor_member(dtor_decl, declared_access);
        }
        return fail_instantiation(
            "class template instantiation for this member kind is not supported yet",
            member ? member->location : loc);
    }

    bool handle_enum_member(
        const EnumDecl* enum_decl,
        RecordMemberAccess declared_access) {
        EnumSemanticState pattern_enum_state;
        if (!collect.query_lookup_enum_semantics(enum_decl, pattern_enum_state)) {
            return fail_instantiation(
                "internal error: missing class template nested enum semantic state",
                enum_decl->location);
        }

        std::shared_ptr<CType> rewritten_underlying =
            pattern_enum_state.underlying_type
                ? clone_pass.rewrite_type(
                      QualType(pattern_enum_state.underlying_type))
                      .get_shared()
                : nullptr;
        if (rewritten_underlying) {
            rewritten_underlying =
                collect.finalize_deferred_semantic_type(
                    QualType(rewritten_underlying),
                    enum_decl->location)
                    .get_shared();
        }
        if (!rewritten_underlying) {
            if (auto pattern_enum_type = enum_decl->get_enum_type()) {
                rewritten_underlying = pattern_enum_type->semantic_underlying_type();
            }
        }
        if (!rewritten_underlying) {
            rewritten_underlying =
                ast_ctx()->type_ctx->get_builtin(BuiltinTypes::Int);
        }

        int64_t next_enum_value = 0;
        bool has_negative_values = false;
        std::vector<std::unique_ptr<EnumConstantDecl>> cloned_constants;
        cloned_constants.reserve(enum_decl->constants.size());

        for (const auto& constant : enum_decl->constants) {
            if (!constant) {
                continue;
            }

            std::unique_ptr<Expr> cloned_init = nullptr;
            if (constant->init) {
                std::string clone_error;
                cloned_init = clone_pass.clone_expr(
                    constant->init.get(),
                    &clone_error);
                if (!cloned_init) {
                    return fail_instantiation(
                        clone_error.empty()
                            ? "failed to clone class template nested enum initializer"
                            : clone_error,
                        constant->location);
                }
                if (!collect.resolve_dependent_expr_after_substitution(
                        cloned_init,
                        QualType(),
                        &clone_error)) {
                    return fail_instantiation(
                        clone_error.empty()
                            ? "failed to resolve class template nested enum initializer after substitution"
                            : clone_error,
                        constant->location);
                }
            }

            int64_t enum_value = next_enum_value;
            if (cloned_init) {
                auto eval = try_evaluate_with_consteval_compat(
                    cloned_init.get(),
                    ConstEvalMode::c_ice());
                if (!eval.has_value()) {
                    return fail_instantiation(
                        "enumerator value is not an integer constant expression",
                        constant->location);
                }
                enum_value = *eval;
            }

            auto cloned_constant = collect.collect_enum_constant_declaration(
                constant->name,
                std::move(cloned_init),
                constant->location);
            cloned_constant->value = enum_value;

            std::shared_ptr<Symbol> cloned_symbol =
                constant->sym
                    ? clone_symbol_shallow_for_specialization(
                          constant->sym,
                          QualType(
                              ast_ctx()->type_ctx->get_builtin(BuiltinTypes::Int)))
                    : std::make_shared<Symbol>(
                          constant->name,
                          SymbolKind::ENUM_CONSTANT,
                          QualType(
                              ast_ctx()->type_ctx->get_builtin(BuiltinTypes::Int)),
                          StorageClass::NONE);
            cloned_symbol->enum_val = enum_value;
            if (constant->sym) {
                clone_pass.context().symbol_remap.emplace(
                    constant->sym.get(),
                    cloned_symbol);
            }
            cloned_constant->sym = cloned_symbol;
            cloned_constants.push_back(std::move(cloned_constant));

            if (enum_value < 0) {
                has_negative_values = true;
            }
            if (__builtin_add_overflow(enum_value, int64_t{1}, &next_enum_value)) {
                return fail_instantiation(
                    "incremented enumerator value is not representable in int64",
                    constant->location);
            }
        }

        auto enum_type = std::make_shared<EnumType>(enum_decl->tag);
        auto cloned_enum_decl = collect.collect_enum_declaration(
            enum_decl->tag,
            std::move(cloned_constants),
            enum_type,
            enum_decl->location);

        EnumSemanticState cloned_enum_state;
        cloned_enum_state.is_incomplete = false;
        cloned_enum_state.is_scoped = pattern_enum_state.is_scoped;
        cloned_enum_state.has_negative_values = has_negative_values;
        cloned_enum_state.underlying_type = rewritten_underlying;
        cloned_enum_state.enumerators.reserve(cloned_enum_decl->constants.size());
        for (const auto& constant : cloned_enum_decl->constants) {
            if (!constant) {
                continue;
            }
            EnumSemanticState::Enumerator enumerator;
            enumerator.name = constant->name;
            enumerator.decl = constant.get();
            enumerator.symbol = constant->sym;
            enumerator.value = constant->value;
            cloned_enum_state.enumerators.push_back(std::move(enumerator));
        }
        collect.query_publish_enum_semantics(
            cloned_enum_decl.get(),
            cloned_enum_state);

        if (!cloned_enum_decl->tag.empty()) {
            RecordSemanticState::NestedType nested_type;
            nested_type.name = cloned_enum_decl->tag;
            nested_type.type = QualType(cloned_enum_decl->get_enum_type());
            nested_type.declared_access = declared_access;
            nested_type.decl = cloned_enum_decl.get();
            nested_types.push_back(std::move(nested_type));
        }
        if (!cloned_enum_state.is_scoped) {
            for (const auto& constant : cloned_enum_decl->constants) {
                if (!constant) {
                    continue;
                }
                RecordSemanticState::EnumeratorMember enumerator_member;
                enumerator_member.name = constant->name;
                enumerator_member.declared_access = declared_access;
                enumerator_member.enum_decl = cloned_enum_decl.get();
                enumerator_member.decl = constant.get();
                enumerator_member.symbol = constant->sym;
                enumerator_members.push_back(std::move(enumerator_member));
            }
        }
        publish_provisional_nested_members();

        entry->member_decls.push_back(std::move(cloned_enum_decl));
        return true;
    }

    bool handle_nested_record_member(
        const CppRecordDecl* nested_record,
        RecordMemberAccess declared_access) {
        if (!nested_record || nested_record->name.empty()) {
            return fail_instantiation(
                "anonymous nested records in class template specializations are not supported yet",
                nested_record ? nested_record->location : loc);
        }

        std::string clone_error;
        auto cloned_decl_base = clone_pass.clone_decl(nested_record, &clone_error);
        auto* cloned_record = dyn_cast<CppRecordDecl>(cloned_decl_base.get());
        if (!cloned_decl_base || !cloned_record) {
            return fail_instantiation(
                clone_error.empty()
                    ? "failed to clone class template nested record"
                    : clone_error,
                nested_record->location);
        }

        auto resolution_pass =
            clone_pass_builder.build_dependent_resolution_pass(
                clone_pass,
                [this](std::unique_ptr<Expr>& expr, std::string* error_out)
                    -> bool {
                    return collect.resolve_dependent_expr_after_substitution(
                        expr,
                        QualType(),
                        error_out);
                });
        if (!resolution_pass.resolve_decl_in_place(cloned_decl_base, &clone_error)) {
            return fail_instantiation(
                clone_error.empty()
                    ? "failed to resolve class template nested record after substitution"
                    : clone_error,
                nested_record->location);
        }

        bool is_union_record = cloned_record->record_kind == CppRecordKind::Union;
        auto record_type = std::make_shared<ObjectType>(
            cloned_record->name,
            is_union_record,
            !cloned_record->is_definition);
        auto semantic_decl = collect.collect_record_declaration(
            cloned_record->name,
            record_type,
            is_union_record,
            cloned_record->location);
        if (!semantic_decl) {
            return fail_instantiation(
                "failed to build semantic owner for class template nested record",
                nested_record->location);
        }

        Collect::CollectRecordBuildContext ctx{
            cloned_record,
            cloned_record->location,
            cloned_record->name,
            cloned_record->name,
            is_union_record,
            record_type,
            semantic_decl.get(),
            &entry->member_decls,
            nullptr};
        ctx.semantic_state.is_incomplete = false;
        ctx.semantic_state.alignment = 1;
        ctx.semantic_state.non_virtual_alignment = 1;
        if (const auto* definition_data = cloned_record->get_definition_data()) {
            ctx.semantic_state.definition_data = *definition_data;
        }
        std::string alignment_error;
        SrcLoc alignment_error_loc = cloned_record->location;
        size_t requested_alignment = requested_alignment_from_decl_attrs(
            collect,
            ast_ctx(),
            cloned_record->node_id,
            cloned_record->location,
            &alignment_error,
            &alignment_error_loc);
        if (!alignment_error.empty()) {
            return fail_instantiation(alignment_error, alignment_error_loc);
        }
        if (requested_alignment > record_type->requested_alignment) {
            record_type->requested_alignment = requested_alignment;
        }
        ctx.fields.reserve(cloned_record->members.size());
        ctx.methods.reserve(cloned_record->members.size());
        ctx.method_templates.reserve(cloned_record->members.size());
        ctx.static_data_members.reserve(cloned_record->members.size());
        ctx.nested_types.reserve(cloned_record->members.size());
        ctx.nested_templates.reserve(cloned_record->members.size());
        ctx.enumerator_members.reserve(cloned_record->members.size());
        ctx.seen_static_data_member_names.reserve(cloned_record->members.size());
        ctx.constructors.reserve(cloned_record->members.size());
        ctx.destructors.reserve(cloned_record->members.size());
        ctx.required_ctor_member_init_fields.reserve(cloned_record->members.size());

        collect.collect_record_resolve_bases(ctx);
        collect.collect_record_walk_virtual_bases(ctx);
        collect.collect_record_collect_members(ctx);
        collect.collect_record_synthesize_implicit_members(ctx);
        collect.collect_record_resolve_virtual_dispatch(ctx);
        collect.collect_record_compute_layout(ctx);
        collect.collect_record_materialize_defaulted_method_bodies(ctx);
        collect.collect_record_infer_constexpr_special_members(ctx);
        collect.collect_record_publish_semantics(ctx);

        if (ast_ctx() && ast_ctx()->has_attrs(cloned_record->node_id)) {
            std::vector<ParsedAttribute> copied_attrs(
                ast_ctx()->get_attrs(cloned_record->node_id).attrs.begin(),
                ast_ctx()->get_attrs(cloned_record->node_id).attrs.end());
            ast_ctx()->append_attrs(semantic_decl->node_id, std::move(copied_attrs));
        }

        RecordSemanticState::NestedType nested_type;
        nested_type.name = cloned_record->name;
        nested_type.type = QualType(record_type);
        nested_type.declared_access = declared_access;
        nested_type.decl = semantic_decl.get();
        nested_types.push_back(std::move(nested_type));
        publish_provisional_nested_members();

        entry->member_decls.push_back(std::move(semantic_decl));
        return true;
    }

    bool handle_field_member(
        const FieldDecl* field_decl,
        RecordMemberAccess declared_access) {
        auto substituted_type = collect.substitute_template_type_with_bindings(
            field_decl->type,
            *selected_parameters,
            specialization_bindings,
            field_decl->location);
        substituted_type = collect.finalize_deferred_semantic_type(
            substituted_type,
            field_decl->location);

        auto canonical_field_type = desugar_type(substituted_type);
        auto* field_object_type = canonical_field_type.as<ObjectType>();
        if (field_object_type && field_object_type->isIncomplete()) {
            return fail_instantiation(
                "field has incomplete type '" + substituted_type.to_string() + "'",
                field_decl->location);
        }

        size_t forced_alignment = 0;
        if (ast_ctx() && ast_ctx()->has_attrs(field_decl->node_id)) {
            std::string clone_error;
            auto cloned_field_decl_base = clone_pass.clone_decl(
                field_decl,
                &clone_error);
            auto* cloned_field_decl = dyn_cast<FieldDecl>(cloned_field_decl_base.get());
            if (!cloned_field_decl_base || !cloned_field_decl) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "failed to clone class template field attributes"
                        : clone_error,
                    field_decl->location);
            }

            auto resolution_pass =
                clone_pass_builder.build_dependent_resolution_pass(
                    clone_pass,
                    [this](std::unique_ptr<Expr>& expr, std::string* error_out)
                        -> bool {
                        return collect.resolve_dependent_expr_after_substitution(
                            expr,
                            QualType(),
                            error_out);
                    });
            if (!resolution_pass.resolve_decl_in_place(
                    cloned_field_decl_base,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "failed to resolve class template field attributes after substitution"
                        : clone_error,
                    field_decl->location);
            }

            std::string alignment_error;
            SrcLoc alignment_error_loc = field_decl->location;
            forced_alignment = requested_alignment_from_decl_attrs(
                collect,
                ast_ctx(),
                cloned_field_decl->node_id,
                cloned_field_decl->location,
                &alignment_error,
                &alignment_error_loc);
            if (!alignment_error.empty()) {
                return fail_instantiation(alignment_error, alignment_error_loc);
            }
        }

        if (field_decl->is_bitfield()) {
            user_fields.emplace_back(field_decl->name,
                                     substituted_type,
                                     0,
                                     0,
                                     field_decl->bitfield_width,
                                     0,
                                     declared_access);
            user_fields.back().forced_alignment = forced_alignment;
        } else {
            user_fields.emplace_back(
                field_decl->name,
                substituted_type,
                0,
                declared_access);
            user_fields.back().forced_alignment = forced_alignment;
        }
        return true;
    }

    bool handle_static_member(
        const VariableDecl* static_member,
        RecordMemberAccess declared_access) {
        std::string clone_error;
        auto cloned_decl_base = clone_pass.clone_decl(static_member, &clone_error);
        auto* cloned_decl = dyn_cast<VariableDecl>(cloned_decl_base.get());
        if (!cloned_decl_base || !cloned_decl) {
            return fail_instantiation(
                clone_error.empty()
                    ? "internal error: failed to clone class template static data member"
                    : clone_error,
                static_member->location);
        }

        auto pattern_symbol_it = pattern_static_member_symbols.find(static_member);
        const std::shared_ptr<Symbol> pattern_symbol =
            pattern_symbol_it != pattern_static_member_symbols.end()
                ? pattern_symbol_it->second
                : nullptr;
        std::shared_ptr<Symbol> cloned_symbol = cloned_decl->sym;
        if (!cloned_symbol && pattern_symbol) {
            cloned_symbol = clone_symbol_shallow_for_specialization(
                pattern_symbol,
                desugar_type(cloned_decl->type));
            clone_pass.context().symbol_remap.emplace(
                pattern_symbol.get(),
                cloned_symbol);
            collect.collect_add_global_symbol(cloned_symbol);
            cloned_decl->sym = cloned_symbol;
        }

        auto namespace_prefix = namespace_prefix_for_specialized_member(
            cloned_symbol
                ? get_symbol_cxx_qualifier_prefix(cloned_symbol.get())
                : nullptr,
            pattern_symbol.get());
        if (namespace_prefix.has_value() && cloned_symbol) {
            set_symbol_cxx_qualifier_prefix(
                cloned_symbol.get(),
                *namespace_prefix);
        }
        if (cloned_symbol) {
            set_symbol_owner_record_type(cloned_symbol.get(), owner_type);
            cloned_symbol->storage_class = StorageClass::STATIC;
            cloned_symbol->is_constexpr = cloned_decl->is_constexpr;
        }

        try_finalize_static_member_for_later_members(cloned_decl_base);
        cloned_decl = dyn_cast<VariableDecl>(cloned_decl_base.get());
        if (!cloned_decl) {
            return fail_instantiation(
                "internal error: class template static data member lost its declaration kind during early finalization",
                static_member->location);
        }

        if (cloned_symbol) {
            cloned_symbol->type = desugar_type(cloned_decl->type);
            cloned_symbol->is_constexpr = cloned_decl->is_constexpr;
            cloned_symbol->variable_definition = cloned_decl;
        }

        RecordSemanticState::StaticDataMember semantic_member;
        semantic_member.name = cloned_decl->name;
        semantic_member.type = cloned_decl->type;
        semantic_member.declared_access = declared_access;
        semantic_member.decl = cloned_decl;
        semantic_member.symbol = cloned_symbol;
        static_data_members.push_back(std::move(semantic_member));
        publish_provisional_nested_members();

        entry->member_decls.push_back(std::move(cloned_decl_base));
        return true;
    }

    bool handle_typedef_member(
        const TypedefDecl* typedef_decl,
        RecordMemberAccess declared_access) {
        auto rewritten_type = clone_pass.rewrite_type(typedef_decl->type);
        std::shared_ptr<Symbol> cloned_symbol = nullptr;
        if (typedef_decl->sym) {
            cloned_symbol = clone_symbol_shallow_for_specialization(
                typedef_decl->sym,
                rewritten_type);
            clone_pass.context().symbol_remap.emplace(
                typedef_decl->sym.get(),
                cloned_symbol);
        }

        auto cloned_decl = collect.collect_make<TypedefDecl>(
            typedef_decl->name,
            rewritten_type,
            cloned_symbol,
            typedef_decl->location);

        RecordSemanticState::NestedType nested_type;
        nested_type.name = cloned_decl->name;
        nested_type.type = cloned_decl->type;
        nested_type.declared_access = declared_access;
        nested_type.decl = cloned_decl.get();
        nested_type.symbol = cloned_symbol;
        nested_types.push_back(std::move(nested_type));
        publish_provisional_nested_members();

        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    bool handle_alias_template_member(
        const AliasTemplateDecl* alias_template_decl,
        RecordMemberAccess declared_access) {
        auto* alias_decl = alias_template_decl->alias_decl();
        if (!alias_decl) {
            return fail_instantiation(
                "internal error: missing class template nested alias template pattern",
                alias_template_decl->location);
        }

        auto cloned_alias_decl = collect.collect_make<TypedefDecl>(
            alias_decl->name,
            QualType(),
            nullptr,
            alias_decl->location);
        auto cloned_template_decl = collect.collect_make<AliasTemplateDecl>(
            TemplateParameterList{},
            std::move(cloned_alias_decl),
            alias_template_decl->location);
        set_template_decl_canonical_decl(
            cloned_template_decl.get(),
            cloned_template_decl.get());
        cloned_template_decl->set_pattern_template_decl(alias_template_decl);

        std::unordered_map<const TemplateParameterDecl*, const TemplateParameterDecl*>
            parameter_rebinds;
        parameter_rebinds.reserve(alias_template_decl->parameters.size());

        auto alias_template_builder = make_nested_template_clone_pass_builder(
            clone_pass_builder,
            clone_pass,
            [this](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                return rewrite_class_template_arguments(
                    template_arguments,
                    specialization_bindings);
            },
            parameter_rebinds,
            {});
        auto alias_template_clone_pass =
            alias_template_builder.build_substitution_pass();

        for (const auto& parameter : alias_template_decl->parameters) {
            if (!parameter) {
                return fail_instantiation(
                    "internal error: missing class template nested alias template parameter",
                    alias_template_decl->location);
            }

            if (auto* type_parameter =
                    dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
                auto cloned_parameter_type =
                    std::make_shared<TemplateTypeParmType>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        type_parameter->is_parameter_pack);
                auto cloned_parameter =
                    collect.collect_make<TemplateTypeParmDecl>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        cloned_parameter_type,
                        type_parameter->is_parameter_pack,
                        type_parameter->location);
                cloned_parameter_type->parameter_decl = cloned_parameter.get();
                parameter_rebinds.emplace(type_parameter, cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            if (auto* non_type_parameter =
                    dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
                auto rewritten_parameter_type =
                    remap_template_parameter_types_in_type(
                        alias_template_clone_pass.rewrite_type(
                            non_type_parameter->type),
                        parameter_rebinds);
                std::shared_ptr<Symbol> cloned_parameter_symbol = nullptr;
                if (non_type_parameter->sym) {
                    cloned_parameter_symbol =
                        clone_symbol_shallow_for_specialization(
                            non_type_parameter->sym,
                            remap_template_parameter_types_in_type(
                                alias_template_clone_pass.rewrite_type(
                                    non_type_parameter->sym->type),
                                parameter_rebinds));
                    alias_template_clone_pass.context().symbol_remap.emplace(
                        non_type_parameter->sym.get(),
                        cloned_parameter_symbol);
                }

                auto cloned_parameter =
                    collect.collect_make<TemplateNonTypeParmDecl>(
                        non_type_parameter->name,
                        non_type_parameter->depth,
                        non_type_parameter->index,
                        rewritten_parameter_type,
                        cloned_parameter_symbol,
                        non_type_parameter->is_parameter_pack,
                        non_type_parameter->location);
                parameter_rebinds.emplace(non_type_parameter, cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            return fail_instantiation(
                "class template nested alias template instantiation for this template parameter kind is not supported yet",
                parameter->location);
        }

        auto rewritten_alias_type = remap_template_parameter_types_in_type(
            alias_template_clone_pass.rewrite_type(alias_decl->type),
            parameter_rebinds);
        std::shared_ptr<Symbol> cloned_alias_symbol = nullptr;
        if (alias_decl->sym) {
            cloned_alias_symbol = clone_symbol_shallow_for_specialization(
                alias_decl->sym,
                rewritten_alias_type);
            clone_pass.context().symbol_remap.emplace(
                alias_decl->sym.get(),
                cloned_alias_symbol);
        }
        auto* rewritten_alias_decl = cloned_template_decl->alias_decl();
        if (!rewritten_alias_decl) {
            return fail_instantiation(
                "internal error: missing cloned class template nested alias declaration",
                alias_template_decl->location);
        }
        rewritten_alias_decl->type = rewritten_alias_type;
        rewritten_alias_decl->underlying = desugar_type(rewritten_alias_type);
        rewritten_alias_decl->sym = cloned_alias_symbol;

        for (size_t index = 0;
             index < alias_template_decl->parameters.size() &&
             index < cloned_template_decl->parameters.size();
             ++index) {
            const auto* default_argument = get_template_parameter_default_argument(
                alias_template_decl->parameters[index].get());
            if (!default_argument) {
                continue;
            }

            auto rewritten_defaults = collect.substitute_template_arguments_with_bindings(
                {*default_argument},
                *selected_parameters,
                specialization_bindings,
                loc);
            if (rewritten_defaults.size() != 1) {
                return fail_instantiation(
                    "internal error: failed to rewrite class template nested alias template default argument",
                    alias_template_decl->location);
            }

            auto rewritten_default = std::move(rewritten_defaults.front());
            std::string default_error;
            if (!remap_template_argument_after_outer_substitution(
                    rewritten_default,
                    parameter_rebinds,
                    alias_template_clone_pass.context(),
                    &default_error)) {
                return fail_instantiation(
                    default_error.empty()
                        ? "class template nested alias template default argument cloning is not supported"
                        : default_error,
                    alias_template_decl->location);
            }
            set_template_parameter_default_argument(
                cloned_template_decl->parameters[index].get(),
                std::move(rewritten_default));
        }

        if (!merge_template_decl_default_arguments(
                cloned_template_decl.get(),
                nullptr)) {
            return fail_instantiation(
                "internal error: failed to register class template nested alias template defaults",
                alias_template_decl->location);
        }

        RecordSemanticState::NestedTemplate nested_template;
        nested_template.name = alias_decl->name;
        nested_template.declared_access = declared_access;
        nested_template.kind = RecordSemanticState::NestedTemplateKind::Alias;
        nested_template.decl = cloned_template_decl.get();
        nested_templates.push_back(std::move(nested_template));
        publish_provisional_nested_members();

        entry->member_decls.push_back(std::move(cloned_template_decl));
        return true;
    }

    bool handle_method_template_member(
        const FunctionTemplateDecl* method_template_decl,
        RecordMemberAccess declared_access) {
        auto* function_decl = method_template_decl->function_decl();
        if (!function_decl) {
            return fail_instantiation(
                "internal error: missing class template member template pattern",
                method_template_decl->location);
        }
        auto* method_decl = dyn_cast<CppMethodDecl>(function_decl);
        auto* ctor_decl = dyn_cast<CppConstructorDecl>(function_decl);
        if (!method_decl && !ctor_decl) {
            return fail_instantiation(
                "class template member template instantiation for this function kind is not supported yet",
                function_decl->location);
        }

        auto rewritten_type = clone_pass.rewrite_type(QualType(function_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template member template specialization did not produce a function type",
                function_decl->location);
        }

        auto copy_common_function_state = [&](FuncDecl* cloned_decl) {
            cloned_decl->location = function_decl->location;
            cloned_decl->name = function_decl->name;
            cloned_decl->type = canonical_type;
            cloned_decl->storage_class = function_decl->storage_class;
            cloned_decl->is_inline = function_decl->is_inline;
            cloned_decl->is_constexpr = function_decl->is_constexpr;
            cloned_decl->is_consteval = function_decl->is_consteval;
            cloned_decl->is_deleted = function_decl->is_deleted;
            cloned_decl->is_defaulted = function_decl->is_defaulted;
            cloned_decl->is_defaulted_on_first_declaration =
                function_decl->is_defaulted_on_first_declaration;
            cloned_decl->set_language_linkage(
                function_decl->get_language_linkage());
        };

        std::unique_ptr<FuncDecl> cloned_function_decl;
        if (ctor_decl) {
            auto cloned_ctor_decl = collect.collect_make<CppConstructorDecl>();
            copy_common_function_state(cloned_ctor_decl.get());
            cloned_ctor_decl->is_explicit = ctor_decl->is_explicit;
            cloned_ctor_decl->explicit_specifier = ctor_decl->explicit_specifier;
            cloned_function_decl = std::move(cloned_ctor_decl);
        } else {
            auto cloned_method_decl = collect.collect_make<CppMethodDecl>();
            copy_common_function_state(cloned_method_decl.get());
            cloned_method_decl->is_virtual = method_decl->is_virtual;
            cloned_method_decl->is_override = method_decl->is_override;
            cloned_method_decl->is_final = method_decl->is_final;
            cloned_method_decl->is_pure = method_decl->is_pure;
            cloned_method_decl->is_conversion_function =
                method_decl->is_conversion_function;
            cloned_method_decl->is_explicit_conversion =
                method_decl->is_explicit_conversion;
            cloned_method_decl->conversion_target_type =
                rewrite_class_template_type(
                    method_decl->conversion_target_type,
                    specialization_bindings);
            cloned_method_decl->explicit_specifier =
                method_decl->explicit_specifier;
            cloned_function_decl = std::move(cloned_method_decl);
        }

        auto* cloned_function_ptr = cloned_function_decl.get();
        if (function_decl->asm_label) {
            cloned_function_ptr->set_asm_label(*function_decl->asm_label);
        }

        auto namespace_prefix = namespace_prefix_from_member_qualifier(
            get_func_decl_cxx_qualifier_prefix(function_decl));
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_function_ptr,
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_function_ptr, owner_type);
        if (method_decl || ctor_decl) {
            copy_cpp_member_decl_info(
                ast_ctx(),
                function_decl->node_id,
                cloned_function_ptr->node_id);
            std::string attr_error;
            if (!copy_decl_side_tables(
                    function_decl,
                    cloned_function_ptr,
                    clone_pass.context(),
                    &attr_error)) {
                return fail_instantiation(
                    attr_error.empty()
                        ? "failed to copy class template member template attributes"
                        : attr_error,
                    function_decl->location);
            }
            if (auto* member_info =
                    ast_ctx()->get_cpp_member_decl_info(
                        cloned_function_ptr->node_id)) {
                member_info->is_static =
                    method_decl &&
                    method_decl->storage_class == StorageClass::STATIC;
                member_info->is_constructor = ctor_decl != nullptr;
                member_info->is_explicit = ctor_decl
                    ? ctor_decl->is_explicit
                    : method_decl->is_explicit_conversion;
            }
        }

        auto cloned_template_decl = collect.collect_make<FunctionTemplateDecl>(
            TemplateParameterList{},
            std::move(cloned_function_decl),
            method_template_decl->location);
        set_template_decl_canonical_decl(
            cloned_template_decl.get(),
            cloned_template_decl.get());
        cloned_template_decl->set_pattern_template_decl(method_template_decl);

        PendingMethodTemplateClone pending_method_template;
        pending_method_template.pattern_template = method_template_decl;
        pending_method_template.pattern_function = function_decl;
        pending_method_template.specialized_template = cloned_template_decl.get();
        pending_method_template.parameter_rebinds.reserve(
            method_template_decl->parameters.size());
        pending_method_template.symbol_remap.reserve(
            method_template_decl->parameters.size());

        for (const auto& parameter : method_template_decl->parameters) {
            if (!parameter) {
                return fail_instantiation(
                    "internal error: missing class template member template parameter",
                    method_template_decl->location);
            }

            if (auto* type_parameter =
                    dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
                auto cloned_parameter_type =
                    std::make_shared<TemplateTypeParmType>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        type_parameter->is_parameter_pack);
                auto cloned_parameter =
                    collect.collect_make<TemplateTypeParmDecl>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        cloned_parameter_type,
                        type_parameter->is_parameter_pack,
                        type_parameter->location);
                cloned_parameter_type->parameter_decl = cloned_parameter.get();
                pending_method_template.parameter_rebinds.emplace(
                    type_parameter,
                    cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            if (auto* non_type_parameter =
                    dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
                auto rewritten_parameter_type =
                    remap_template_parameter_types_in_type(
                        clone_pass.rewrite_type(non_type_parameter->type),
                        pending_method_template.parameter_rebinds);
                std::shared_ptr<Symbol> cloned_parameter_symbol = nullptr;
                if (non_type_parameter->sym) {
                    cloned_parameter_symbol =
                        clone_symbol_shallow_for_specialization(
                            non_type_parameter->sym,
                            remap_template_parameter_types_in_type(
                                clone_pass.rewrite_type(
                                    non_type_parameter->sym->type),
                                pending_method_template.parameter_rebinds));
                    pending_method_template.symbol_remap.emplace(
                        non_type_parameter->sym.get(),
                        cloned_parameter_symbol);
                }

                auto cloned_parameter =
                    collect.collect_make<TemplateNonTypeParmDecl>(
                        non_type_parameter->name,
                        non_type_parameter->depth,
                        non_type_parameter->index,
                        rewritten_parameter_type,
                        cloned_parameter_symbol,
                        non_type_parameter->is_parameter_pack,
                        non_type_parameter->location);
                pending_method_template.parameter_rebinds.emplace(
                    non_type_parameter,
                    cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            return fail_instantiation(
                "class template member template instantiation for this template parameter kind is not supported yet",
                parameter->location);
        }

        RecordSemanticState::MethodTemplate semantic_method_template;
        semantic_method_template.name = function_decl->name;
        semantic_method_template.declared_access = declared_access;
        semantic_method_template.is_static =
            method_decl &&
            method_decl->storage_class == StorageClass::STATIC;
        semantic_method_template.decl = cloned_template_decl.get();
        method_templates.push_back(std::move(semantic_method_template));
        if (ctor_decl) {
            semantic_state.definition_data.has_user_declared_constructor = true;
        }

        pending_method_template_clones.push_back(std::move(pending_method_template));
        entry->map_owner_specialized_member_template(
            function_decl,
            cloned_template_decl.get());
        entry->member_decls.push_back(std::move(cloned_template_decl));
        return true;
    }

    bool handle_friend_member(const FriendDecl* friend_decl) {
        auto* function_decl = friend_decl ? friend_decl->function_decl() : nullptr;
        if (!friend_decl || !function_decl) {
            return fail_instantiation(
                "class template friend declaration specialization for this friend kind is not supported yet",
                friend_decl ? friend_decl->location : loc);
        }

        auto rewritten_type =
            clone_pass.rewrite_type(QualType(function_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template friend specialization did not produce a function type",
                function_decl->location);
        }

        auto cloned_function = collect.collect_make<FuncDecl>();
        cloned_function->location = function_decl->location;
        cloned_function->name = function_decl->name;
        cloned_function->type = canonical_type;
        cloned_function->storage_class = StorageClass::NONE;
        cloned_function->is_inline = function_decl->is_inline;
        cloned_function->is_constexpr = function_decl->is_constexpr;
        cloned_function->is_consteval = function_decl->is_consteval;
        cloned_function->is_deleted = function_decl->is_deleted;
        cloned_function->is_defaulted = function_decl->is_defaulted;
        cloned_function->is_defaulted_on_first_declaration =
            function_decl->is_defaulted_on_first_declaration;
        cloned_function->set_language_linkage(function_decl->get_language_linkage());
        if (function_decl->asm_label) {
            cloned_function->set_asm_label(*function_decl->asm_label);
        }

        std::shared_ptr<Symbol> cloned_symbol =
            friend_decl->function_symbol
                ? clone_symbol_shallow_for_specialization(
                      friend_decl->function_symbol,
                      QualType(canonical_type))
                : std::make_shared<Symbol>(
                      function_decl->name,
                      SymbolKind::FUNCTION,
                      QualType(canonical_type),
                      StorageClass::NONE,
                      VariableLinkage::EXTERNAL,
                      cloned_function->is_inline != 0);
        cloned_symbol->name = function_decl->name;
        cloned_symbol->is_inline = cloned_function->is_inline;
        cloned_symbol->is_constexpr = cloned_function->is_constexpr;
        cloned_symbol->is_consteval = cloned_function->is_consteval;
        cloned_symbol->is_deleted = cloned_function->is_deleted;
        cloned_symbol->is_defaulted = cloned_function->is_defaulted;
        cloned_symbol->is_hidden_friend = true;
        cloned_symbol->type = QualType(canonical_type);
        cloned_symbol->function_definition =
            function_decl_defines_entity(cloned_function.get())
                ? cloned_function.get()
                : nullptr;
        cloned_symbol->set_language_linkage(function_decl->get_language_linkage());
        collect.collect_add_global_symbol(cloned_symbol);
        if (friend_decl->function_symbol) {
            clone_pass.context().symbol_remap.emplace(
                friend_decl->function_symbol.get(),
                cloned_symbol);
        }

        auto cloned_friend = collect.collect_make<FriendDecl>(
            std::move(cloned_function),
            owner_type,
            friend_decl->get_friend_kind(),
            friend_decl->location);
        cloned_friend->function_symbol = cloned_symbol;
        auto* cloned_function_ptr = cloned_friend->function_decl();
        if (!cloned_function_ptr) {
            return fail_instantiation(
                "internal error: class template friend clone lost its function target",
                friend_decl->location);
        }

        RecordSemanticState::FriendFunction semantic_friend;
        semantic_friend.name = cloned_function_ptr->name;
        semantic_friend.type = QualType(canonical_type);
        semantic_friend.decl = cloned_friend.get();
        semantic_friend.function_decl = cloned_function_ptr;
        semantic_friend.symbol = cloned_symbol;
        friend_functions.push_back(std::move(semantic_friend));
        semantic_state.friend_functions = friend_functions;

        specialized_member_symbols.emplace(cloned_function_ptr, cloned_symbol);
        entry->map_specialized_member_to_primary_member(
            cloned_function_ptr,
            function_decl);
        pending_body_clones.push_back(
            PendingFunctionBodyClone{function_decl, cloned_function_ptr, false});
        entry->member_decls.push_back(std::move(cloned_friend));
        return true;
    }

    bool handle_method_member(
        const CppMethodDecl* method_decl,
        RecordMemberAccess declared_access) {
        if (const auto* explicit_specialization =
                find_explicit_member_specialization(method_decl)) {
            auto* specialized_decl = dyn_cast<CppMethodDecl>(
                const_cast<Decl*>(explicit_specialization->get_specialized_decl()));
            if (!specialized_decl) {
                return fail_instantiation(
                    "internal error: explicit member specialization did not preserve a method declaration",
                    method_decl->location);
            }

            rebind_specialized_function_owner(
                specialized_decl,
                owner_type,
                ast_ctx());
            auto specialized_symbol = ensure_explicit_member_function_symbol(
                specialized_decl,
                explicit_specialization->is_definition());

            RecordSemanticState::Method semantic_method;
            semantic_method.name = specialized_decl->name;
            semantic_method.type = QualType(specialized_decl->type);
            semantic_method.declared_access = declared_access;
            semantic_method.is_static =
                specialized_decl->storage_class == StorageClass::STATIC;
            semantic_method.is_deleted = specialized_decl->is_deleted;
            semantic_method.is_defaulted = specialized_decl->is_defaulted;
            semantic_method.is_constexpr = specialized_decl->is_constexpr;
            semantic_method.is_consteval = specialized_decl->is_consteval;
            semantic_method.is_explicit =
                specialized_decl->is_explicit_conversion;
            semantic_method.is_virtual = specialized_decl->is_virtual;
            semantic_method.is_override = specialized_decl->is_override;
            semantic_method.is_final = specialized_decl->is_final;
            semantic_method.is_pure = specialized_decl->is_pure;
            semantic_method.is_conversion_function =
                specialized_decl->is_conversion_function;
            semantic_method.conversion_target_type =
                specialized_decl->conversion_target_type;
            semantic_method.decl = specialized_decl;
            semantic_method.symbol = specialized_symbol;
            methods.push_back(std::move(semantic_method));
            if (specialized_symbol) {
                specialized_member_symbols.emplace(
                    specialized_decl,
                    specialized_symbol);
            }
            return true;
        }

        auto rewritten_type = clone_pass.rewrite_type(QualType(method_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template method specialization did not produce a function type",
                method_decl->location);
        }

        auto cloned_decl = collect.collect_make<CppMethodDecl>();
        cloned_decl->location = method_decl->location;
        cloned_decl->name = method_decl->name;
        cloned_decl->type = canonical_type;
        cloned_decl->storage_class = method_decl->storage_class;
        cloned_decl->is_inline = method_decl->is_inline;
        cloned_decl->is_constexpr = method_decl->is_constexpr;
        cloned_decl->is_consteval = method_decl->is_consteval;
        cloned_decl->is_deleted = method_decl->is_deleted;
        cloned_decl->is_defaulted = method_decl->is_defaulted;
        cloned_decl->is_defaulted_on_first_declaration =
            method_decl->is_defaulted_on_first_declaration;
        cloned_decl->set_language_linkage(method_decl->get_language_linkage());
        cloned_decl->is_virtual = method_decl->is_virtual;
        cloned_decl->is_override = method_decl->is_override;
        cloned_decl->is_final = method_decl->is_final;
        cloned_decl->is_pure = method_decl->is_pure;
        cloned_decl->is_conversion_function = method_decl->is_conversion_function;
        cloned_decl->is_explicit_conversion =
            method_decl->is_explicit_conversion;
        bool cloned_method_is_explicit =
            cloned_decl->is_explicit_conversion;
        if (!substitute_member_explicit_specifier(
                method_decl->explicit_specifier,
                cloned_decl.get(),
                cloned_decl->explicit_specifier,
                cloned_method_is_explicit)) {
            return false;
        }
        cloned_decl->is_explicit_conversion = cloned_method_is_explicit;
        cloned_decl->conversion_target_type =
            rewrite_class_template_type(
                method_decl->conversion_target_type,
                specialization_bindings);
        if (method_decl->asm_label) {
            cloned_decl->set_asm_label(*method_decl->asm_label);
        }

        auto pattern_symbol_it = pattern_method_symbols.find(method_decl);
        const std::shared_ptr<Symbol> pattern_symbol =
            pattern_symbol_it != pattern_method_symbols.end()
                ? pattern_symbol_it->second
                : nullptr;
        auto namespace_prefix = namespace_prefix_for_specialized_member(
            get_func_decl_cxx_qualifier_prefix(method_decl),
            pattern_symbol.get());
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_decl.get(),
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_decl.get(), owner_type);
        copy_cpp_member_decl_info(
            ast_ctx(),
            method_decl->node_id,
            cloned_decl->node_id);
        std::string attr_error;
        if (!copy_decl_side_tables(
                method_decl,
                cloned_decl.get(),
                clone_pass.context(),
                &attr_error)) {
            return fail_instantiation(
                attr_error.empty()
                    ? "failed to copy class template method attributes"
                    : attr_error,
                method_decl->location);
        }
        if (auto* member_info =
                ast_ctx()->get_cpp_member_decl_info(cloned_decl->node_id)) {
            member_info->is_explicit = cloned_decl->is_explicit_conversion;
        }

        auto cloned_symbol = clone_member_symbol(
            pattern_symbol,
            QualType(canonical_type),
            namespace_prefix ? &*namespace_prefix : nullptr,
            true);

        RecordSemanticState::Method semantic_method;
        semantic_method.name = cloned_decl->name;
        semantic_method.type = QualType(canonical_type);
        semantic_method.declared_access = declared_access;
        semantic_method.is_static =
            cloned_decl->storage_class == StorageClass::STATIC;
        semantic_method.is_deleted = cloned_decl->is_deleted;
        semantic_method.is_defaulted = cloned_decl->is_defaulted;
        semantic_method.is_constexpr = cloned_decl->is_constexpr;
        semantic_method.is_consteval = cloned_decl->is_consteval;
        semantic_method.is_explicit = cloned_decl->is_explicit_conversion;
        semantic_method.is_virtual = cloned_decl->is_virtual;
        semantic_method.is_override = cloned_decl->is_override;
        semantic_method.is_final = cloned_decl->is_final;
        semantic_method.is_pure = cloned_decl->is_pure;
        semantic_method.is_conversion_function =
            cloned_decl->is_conversion_function;
        semantic_method.conversion_target_type =
            cloned_decl->conversion_target_type;
        semantic_method.decl = cloned_decl.get();
        semantic_method.symbol = cloned_symbol;
        methods.push_back(std::move(semantic_method));
        if (cloned_symbol) {
            specialized_member_symbols.emplace(cloned_decl.get(), cloned_symbol);
            entry->map_specialized_member_symbol_to_primary_member(
                cloned_symbol.get(),
                method_decl);
        }
        entry->map_specialized_member_to_primary_member(
            cloned_decl.get(),
            method_decl);

        pending_body_clones.push_back(
            PendingFunctionBodyClone{method_decl, cloned_decl.get(), true});
        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    bool handle_constructor_member(
        const CppConstructorDecl* ctor_decl,
        RecordMemberAccess declared_access) {
        auto rewritten_type = clone_pass.rewrite_type(QualType(ctor_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template constructor specialization did not produce a function type",
                ctor_decl->location);
        }

        auto cloned_decl = collect.collect_make<CppConstructorDecl>();
        cloned_decl->location = ctor_decl->location;
        cloned_decl->name = ctor_decl->name;
        cloned_decl->type = canonical_type;
        cloned_decl->storage_class = ctor_decl->storage_class;
        cloned_decl->is_inline = ctor_decl->is_inline;
        cloned_decl->is_constexpr = ctor_decl->is_constexpr;
        cloned_decl->is_consteval = ctor_decl->is_consteval;
        cloned_decl->set_language_linkage(ctor_decl->get_language_linkage());
        cloned_decl->is_explicit = ctor_decl->is_explicit;
        bool cloned_ctor_is_explicit = cloned_decl->is_explicit;
        if (!substitute_member_explicit_specifier(
                ctor_decl->explicit_specifier,
                cloned_decl.get(),
                cloned_decl->explicit_specifier,
                cloned_ctor_is_explicit)) {
            return false;
        }
        cloned_decl->is_explicit = cloned_ctor_is_explicit;
        cloned_decl->is_deleted = ctor_decl->is_deleted;
        cloned_decl->is_defaulted = ctor_decl->is_defaulted;
        cloned_decl->is_defaulted_on_first_declaration =
            ctor_decl->is_defaulted_on_first_declaration;
        if (ctor_decl->asm_label) {
            cloned_decl->set_asm_label(*ctor_decl->asm_label);
        }

        auto pattern_symbol_it = pattern_constructor_symbols.find(ctor_decl);
        const std::shared_ptr<Symbol> pattern_symbol =
            pattern_symbol_it != pattern_constructor_symbols.end()
                ? pattern_symbol_it->second
                : nullptr;
        auto namespace_prefix = namespace_prefix_for_specialized_member(
            get_func_decl_cxx_qualifier_prefix(ctor_decl),
            pattern_symbol.get());
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_decl.get(),
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_decl.get(), owner_type);
        copy_cpp_member_decl_info(
            ast_ctx(),
            ctor_decl->node_id,
            cloned_decl->node_id);
        if (auto* member_info =
                ast_ctx()->get_cpp_member_decl_info(cloned_decl->node_id)) {
            member_info->is_explicit = cloned_decl->is_explicit;
        }

        auto cloned_symbol = clone_member_symbol(
            pattern_symbol,
            QualType(canonical_type),
            namespace_prefix ? &*namespace_prefix : nullptr,
            true);

        RecordSemanticState::Constructor semantic_ctor;
        semantic_ctor.name = cloned_decl->name;
        semantic_ctor.type = QualType(canonical_type);
        semantic_ctor.declared_access = declared_access;
        semantic_ctor.is_implicit = false;
        semantic_ctor.is_explicit = cloned_decl->is_explicit;
        semantic_ctor.is_deleted = cloned_decl->is_deleted;
        semantic_ctor.is_defaulted = cloned_decl->is_defaulted;
        semantic_ctor.is_constexpr = cloned_decl->is_constexpr;
        semantic_ctor.is_consteval = cloned_decl->is_consteval;
        semantic_ctor.decl = cloned_decl.get();
        semantic_ctor.symbol = cloned_symbol;
        constructors.push_back(std::move(semantic_ctor));
        if (cloned_symbol) {
            specialized_member_symbols.emplace(cloned_decl.get(), cloned_symbol);
            entry->map_specialized_member_symbol_to_primary_member(
                cloned_symbol.get(),
                ctor_decl);
        }
        entry->map_specialized_member_to_primary_member(
            cloned_decl.get(),
            ctor_decl);

        pending_body_clones.push_back(
            PendingFunctionBodyClone{ctor_decl, cloned_decl.get(), true});
        pending_ctor_init_clones.emplace_back(ctor_decl, cloned_decl.get());
        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    bool handle_destructor_member(
        const CppDestructorDecl* dtor_decl,
        RecordMemberAccess declared_access) {
        auto rewritten_type = clone_pass.rewrite_type(QualType(dtor_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template destructor specialization did not produce a function type",
                dtor_decl->location);
        }

        auto cloned_decl = collect.collect_make<CppDestructorDecl>();
        cloned_decl->location = dtor_decl->location;
        cloned_decl->name = dtor_decl->name;
        cloned_decl->type = canonical_type;
        cloned_decl->storage_class = dtor_decl->storage_class;
        cloned_decl->is_inline = dtor_decl->is_inline;
        cloned_decl->is_constexpr = dtor_decl->is_constexpr;
        cloned_decl->is_consteval = dtor_decl->is_consteval;
        cloned_decl->set_language_linkage(dtor_decl->get_language_linkage());
        cloned_decl->is_deleted = dtor_decl->is_deleted;
        cloned_decl->is_defaulted = dtor_decl->is_defaulted;
        cloned_decl->is_defaulted_on_first_declaration =
            dtor_decl->is_defaulted_on_first_declaration;
        cloned_decl->is_virtual = dtor_decl->is_virtual;
        cloned_decl->is_override = dtor_decl->is_override;
        cloned_decl->is_final = dtor_decl->is_final;
        cloned_decl->is_pure = dtor_decl->is_pure;
        if (dtor_decl->asm_label) {
            cloned_decl->set_asm_label(*dtor_decl->asm_label);
        }

        auto pattern_symbol_it = pattern_destructor_symbols.find(dtor_decl);
        const std::shared_ptr<Symbol> pattern_symbol =
            pattern_symbol_it != pattern_destructor_symbols.end()
                ? pattern_symbol_it->second
                : nullptr;
        auto namespace_prefix = namespace_prefix_for_specialized_member(
            get_func_decl_cxx_qualifier_prefix(dtor_decl),
            pattern_symbol.get());
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_decl.get(),
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_decl.get(), owner_type);
        copy_cpp_member_decl_info(
            ast_ctx(),
            dtor_decl->node_id,
            cloned_decl->node_id);

        auto cloned_symbol = clone_member_symbol(
            pattern_symbol,
            QualType(canonical_type),
            namespace_prefix ? &*namespace_prefix : nullptr,
            true);

        RecordSemanticState::Destructor semantic_dtor;
        semantic_dtor.name = cloned_decl->name;
        semantic_dtor.type = QualType(canonical_type);
        semantic_dtor.declared_access = declared_access;
        semantic_dtor.is_implicit = false;
        semantic_dtor.is_defaulted = cloned_decl->is_defaulted;
        semantic_dtor.is_deleted = cloned_decl->is_deleted;
        semantic_dtor.is_constexpr = cloned_decl->is_constexpr;
        semantic_dtor.is_consteval = cloned_decl->is_consteval;
        semantic_dtor.is_virtual = cloned_decl->is_virtual;
        semantic_dtor.is_override = cloned_decl->is_override;
        semantic_dtor.is_final = cloned_decl->is_final;
        semantic_dtor.is_pure = cloned_decl->is_pure;
        semantic_dtor.decl = cloned_decl.get();
        semantic_dtor.symbol = cloned_symbol;
        destructors.push_back(std::move(semantic_dtor));
        if (cloned_symbol) {
            specialized_member_symbols.emplace(cloned_decl.get(), cloned_symbol);
            entry->map_specialized_member_symbol_to_primary_member(
                cloned_symbol.get(),
                dtor_decl);
        }
        entry->map_specialized_member_to_primary_member(
            cloned_decl.get(),
            dtor_decl);

        pending_body_clones.push_back(
            PendingFunctionBodyClone{dtor_decl, cloned_decl.get(), true});
        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    bool resolve_virtual_dispatch_state() {
        const ObjectDecl* current_record_decl =
            canonical_record_decl(entry->specialization_decl.get());

        std::vector<const RecordSemanticState*> linear_base_states;
        std::unordered_set<const ObjectDecl*> seen_base_chain;
        auto append_base_chain =
            [&](const RecordSemanticState* state, const auto& self_ref) -> void {
            if (!state) {
                return;
            }
            for (const auto& base : state->bases) {
                if (!base.record_decl || seen_base_chain.contains(base.record_decl)) {
                    continue;
                }
                const RecordSemanticState* base_state =
                    collect.query_lookup_record_semantics(base.record_decl);
                if (!base_state) {
                    continue;
                }
                seen_base_chain.insert(base.record_decl);
                self_ref(base_state, self_ref);
                linear_base_states.push_back(base_state);
            }
        };
        for (const auto& base : direct_bases) {
            if (!base.record_decl || seen_base_chain.contains(base.record_decl)) {
                continue;
            }
            const RecordSemanticState* base_state =
                collect.query_lookup_record_semantics(base.record_decl);
            if (!base_state) {
                continue;
            }
            seen_base_chain.insert(base.record_decl);
            append_base_chain(base_state, append_base_chain);
            linear_base_states.push_back(base_state);
        }

        std::vector<RecordSemanticState::VirtualSlot> semantic_virtual_slots;
        std::unordered_map<std::string, VirtualSlotState> virtual_slots;
        bool any_base_polymorphic = false;
        for (const auto* base_state : linear_base_states) {
            if (!base_state) {
                continue;
            }
            any_base_polymorphic = any_base_polymorphic || base_state->is_polymorphic;

            if (!base_state->virtual_slots.empty()) {
                for (const auto& inherited_slot : base_state->virtual_slots) {
                    auto inherited_it = virtual_slots.find(inherited_slot.key);
                    if (inherited_it != virtual_slots.end()) {
                        size_t slot_index = inherited_it->second.slot_index;
                        if (slot_index < semantic_virtual_slots.size()) {
                            semantic_virtual_slots[slot_index] = inherited_slot;
                        }
                        inherited_it->second.is_pure = inherited_slot.is_pure;
                        inherited_it->second.is_final = inherited_slot.is_final;
                        inherited_it->second.is_destructor =
                            inherited_slot.is_destructor;
                        inherited_it->second.final_symbol =
                            inherited_slot.final_symbol;
                        inherited_it->second.name = inherited_slot.name;
                        continue;
                    }
                    size_t inherited_index = semantic_virtual_slots.size();
                    semantic_virtual_slots.push_back(inherited_slot);
                    virtual_slots[inherited_slot.key] = VirtualSlotState{
                        inherited_index,
                        inherited_slot.is_pure,
                        inherited_slot.is_final,
                        inherited_slot.is_destructor,
                        inherited_slot.final_symbol,
                        inherited_slot.name};
                }
                continue;
            }

            for (const auto& base_method : base_state->methods) {
                if (!base_method.is_virtual || base_method.is_static) {
                    continue;
                }
                std::string slot_key =
                    make_virtual_slot_key(base_method.name, base_method.type);
                auto inherited_it = virtual_slots.find(slot_key);
                if (inherited_it != virtual_slots.end()) {
                    size_t slot_index = inherited_it->second.slot_index;
                    if (slot_index < semantic_virtual_slots.size()) {
                        auto& slot = semantic_virtual_slots[slot_index];
                        slot.key = slot_key;
                        slot.name = base_method.name;
                        slot.is_destructor = false;
                        slot.is_pure = base_method.is_pure;
                        slot.is_final = base_method.is_final;
                        slot.final_symbol = base_method.symbol;
                    }
                    inherited_it->second.is_pure = base_method.is_pure;
                    inherited_it->second.is_final = base_method.is_final;
                    inherited_it->second.is_destructor = false;
                    inherited_it->second.final_symbol = base_method.symbol;
                    inherited_it->second.name = base_method.name;
                    continue;
                }
                size_t inherited_index = semantic_virtual_slots.size();
                RecordSemanticState::VirtualSlot inherited_slot;
                inherited_slot.key = slot_key;
                inherited_slot.name = base_method.name;
                inherited_slot.is_destructor = false;
                inherited_slot.is_pure = base_method.is_pure;
                inherited_slot.is_final = base_method.is_final;
                inherited_slot.final_symbol = base_method.symbol;
                semantic_virtual_slots.push_back(std::move(inherited_slot));
                virtual_slots[slot_key] = VirtualSlotState{
                    inherited_index,
                    base_method.is_pure,
                    base_method.is_final,
                    false,
                    base_method.symbol,
                    base_method.name};
            }
            for (const auto& base_dtor : base_state->destructors) {
                if (!base_dtor.is_virtual) {
                    continue;
                }
                auto inherited_it = virtual_slots.find("<destructor>");
                if (inherited_it != virtual_slots.end()) {
                    size_t slot_index = inherited_it->second.slot_index;
                    if (slot_index < semantic_virtual_slots.size()) {
                        auto& slot = semantic_virtual_slots[slot_index];
                        slot.key = "<destructor>";
                        slot.name = base_dtor.name;
                        slot.is_destructor = true;
                        slot.is_pure = base_dtor.is_pure;
                        slot.is_final = base_dtor.is_final;
                        slot.final_symbol = base_dtor.symbol;
                    }
                    inherited_it->second.is_pure = base_dtor.is_pure;
                    inherited_it->second.is_final = base_dtor.is_final;
                    inherited_it->second.is_destructor = true;
                    inherited_it->second.final_symbol = base_dtor.symbol;
                    inherited_it->second.name = base_dtor.name;
                    continue;
                }
                size_t inherited_index = semantic_virtual_slots.size();
                RecordSemanticState::VirtualSlot inherited_slot;
                inherited_slot.key = "<destructor>";
                inherited_slot.name = base_dtor.name;
                inherited_slot.is_destructor = true;
                inherited_slot.is_pure = base_dtor.is_pure;
                inherited_slot.is_final = base_dtor.is_final;
                inherited_slot.final_symbol = base_dtor.symbol;
                semantic_virtual_slots.push_back(std::move(inherited_slot));
                virtual_slots["<destructor>"] = VirtualSlotState{
                    inherited_index,
                    base_dtor.is_pure,
                    base_dtor.is_final,
                    true,
                    base_dtor.symbol,
                    base_dtor.name};
            }
        }

        semantic_state.is_polymorphic = any_base_polymorphic;
        semantic_state.has_virtual_destructor =
            virtual_slots.contains("<destructor>");

        for (auto& method : methods) {
            if (method.is_static) {
                method.is_virtual = false;
                method.overrides_base_virtual = false;
                method.is_pure = false;
                method.virtual_slot_index = -1;
                if (method.decl && ast_ctx()) {
                    if (auto* info =
                            ast_ctx()->get_cpp_member_decl_info(method.decl->node_id)) {
                        info->is_virtual = false;
                        info->is_override = method.is_override;
                        info->is_final = method.is_final;
                        info->is_pure = false;
                    }
                }
                continue;
            }

            std::string slot_key = make_virtual_slot_key(method.name, method.type);
            auto inherited_slot_it = virtual_slots.find(slot_key);
            bool overrides_base = inherited_slot_it != virtual_slots.end();
            bool inherited_final =
                overrides_base && inherited_slot_it->second.is_final;

            SrcLoc method_loc = method.decl ? method.decl->location : loc;
            if (overrides_base && inherited_slot_it->second.final_symbol) {
                auto overriding_type =
                    desugar_type(method.type).as_shared<FunctionType>();
                auto overridden_type = desugar_type(
                    inherited_slot_it->second.final_symbol->type)
                    .as_shared<FunctionType>();
                if (overriding_type && overridden_type &&
                    !returns_are_covariant(
                        overriding_type->ret_type,
                        overridden_type->ret_type,
                        direct_bases,
                        current_record_decl,
                        ast_ctx())) {
                    return fail_instantiation(
                        "return type of overriding virtual function '" +
                            method.name +
                            "' is not covariant with the base virtual function",
                        method_loc);
                }
            }
            if (inherited_final) {
                return fail_instantiation(
                    "cannot override final virtual function '" + method.name + "'",
                    method_loc);
            }
            if (method.is_override && !overrides_base) {
                return fail_instantiation(
                    "'" + method.name +
                        "' marked 'override' but does not override a base virtual function",
                    method_loc);
            }

            bool effective_virtual =
                method.is_virtual || method.is_override || overrides_base;
            if (method.is_final && !effective_virtual) {
                return fail_instantiation(
                    "'" + method.name + "' marked 'final' but is not virtual",
                    method_loc);
            }
            if (method.is_pure && !effective_virtual) {
                return fail_instantiation(
                    "pure-specifier can only be specified for virtual member functions",
                    method_loc);
            }

            method.is_virtual = effective_virtual;
            method.overrides_base_virtual = overrides_base;
            if (method.is_virtual) {
                semantic_state.is_polymorphic = true;
                if (overrides_base) {
                    size_t slot_index = inherited_slot_it->second.slot_index;
                    method.virtual_slot_index = static_cast<int32_t>(slot_index);
                    if (slot_index < semantic_virtual_slots.size()) {
                        auto& slot = semantic_virtual_slots[slot_index];
                        slot.name = method.name;
                        slot.is_destructor = false;
                        slot.is_pure = method.is_pure;
                        slot.is_final = method.is_final;
                        slot.final_symbol = method.symbol;
                    }
                    inherited_slot_it->second.is_pure = method.is_pure;
                    inherited_slot_it->second.is_final = method.is_final;
                    inherited_slot_it->second.is_destructor = false;
                    inherited_slot_it->second.final_symbol = method.symbol;
                    inherited_slot_it->second.name = method.name;
                } else {
                    size_t slot_index = semantic_virtual_slots.size();
                    method.virtual_slot_index = static_cast<int32_t>(slot_index);
                    RecordSemanticState::VirtualSlot slot;
                    slot.key = slot_key;
                    slot.name = method.name;
                    slot.is_destructor = false;
                    slot.is_pure = method.is_pure;
                    slot.is_final = method.is_final;
                    slot.final_symbol = method.symbol;
                    semantic_virtual_slots.push_back(std::move(slot));
                    virtual_slots[slot_key] = VirtualSlotState{
                        slot_index,
                        method.is_pure,
                        method.is_final,
                        false,
                        method.symbol,
                        method.name};
                }
            } else {
                method.virtual_slot_index = -1;
            }

            if (method.decl && ast_ctx()) {
                if (auto* info =
                        ast_ctx()->get_cpp_member_decl_info(method.decl->node_id)) {
                    info->is_virtual = method.is_virtual;
                    info->is_override = method.is_override;
                    info->is_final = method.is_final;
                    info->is_pure = method.is_pure;
                }
            }
        }

        for (auto& dtor : destructors) {
            auto inherited_slot_it = virtual_slots.find("<destructor>");
            bool overrides_base = inherited_slot_it != virtual_slots.end();
            bool inherited_final =
                overrides_base && inherited_slot_it->second.is_final;

            SrcLoc dtor_loc = dtor.decl ? dtor.decl->location : loc;
            if (inherited_final) {
                return fail_instantiation(
                    "cannot override final virtual destructor",
                    dtor_loc);
            }
            if (dtor.is_override && !overrides_base) {
                return fail_instantiation(
                    "destructor marked 'override' but does not override a base virtual destructor",
                    dtor_loc);
            }

            bool effective_virtual =
                dtor.is_virtual || dtor.is_override || overrides_base;
            if (dtor.is_final && !effective_virtual) {
                return fail_instantiation(
                    "destructor marked 'final' but is not virtual",
                    dtor_loc);
            }
            if (dtor.is_pure && !effective_virtual) {
                return fail_instantiation(
                    "pure-specifier can only be specified for virtual member functions",
                    dtor_loc);
            }

            dtor.is_virtual = effective_virtual;
            dtor.overrides_base_virtual = overrides_base;
            if (dtor.is_virtual) {
                semantic_state.is_polymorphic = true;
                semantic_state.has_virtual_destructor = true;
                if (overrides_base) {
                    size_t slot_index = inherited_slot_it->second.slot_index;
                    dtor.virtual_slot_index = static_cast<int32_t>(slot_index);
                    if (slot_index < semantic_virtual_slots.size()) {
                        auto& slot = semantic_virtual_slots[slot_index];
                        slot.name = dtor.name;
                        slot.is_destructor = true;
                        slot.is_pure = dtor.is_pure;
                        slot.is_final = dtor.is_final;
                        slot.final_symbol = dtor.symbol;
                    }
                    inherited_slot_it->second.is_pure = dtor.is_pure;
                    inherited_slot_it->second.is_final = dtor.is_final;
                    inherited_slot_it->second.is_destructor = true;
                    inherited_slot_it->second.final_symbol = dtor.symbol;
                    inherited_slot_it->second.name = dtor.name;
                } else {
                    size_t slot_index = semantic_virtual_slots.size();
                    dtor.virtual_slot_index = static_cast<int32_t>(slot_index);
                    RecordSemanticState::VirtualSlot slot;
                    slot.key = "<destructor>";
                    slot.name = dtor.name;
                    slot.is_destructor = true;
                    slot.is_pure = dtor.is_pure;
                    slot.is_final = dtor.is_final;
                    slot.final_symbol = dtor.symbol;
                    semantic_virtual_slots.push_back(std::move(slot));
                    virtual_slots["<destructor>"] = VirtualSlotState{
                        slot_index,
                        dtor.is_pure,
                        dtor.is_final,
                        true,
                        dtor.symbol,
                        dtor.name};
                }
            } else {
                dtor.virtual_slot_index = -1;
            }

            if (dtor.decl && ast_ctx()) {
                if (auto* info =
                        ast_ctx()->get_cpp_member_decl_info(dtor.decl->node_id)) {
                    info->is_virtual = dtor.is_virtual;
                    info->is_override = dtor.is_override;
                    info->is_final = dtor.is_final;
                    info->is_pure = dtor.is_pure;
                }
            }
        }

        semantic_state.virtual_slots = std::move(semantic_virtual_slots);
        semantic_state.is_abstract = false;
        for (const auto& slot : semantic_state.virtual_slots) {
            if (slot.is_pure) {
                semantic_state.is_abstract = true;
                break;
            }
        }
        return true;
    }

    bool build_semantic_state() {
        semantic_state = RecordSemanticState{};
        semantic_state.is_incomplete = !pattern->is_definition;
        if (pattern->get_definition_data()) {
            semantic_state.definition_data = *pattern->get_definition_data();
        }
        if (!resolve_virtual_dispatch_state()) {
            return false;
        }
        CollectRecordBuildContext ctx;
        ctx.record = pattern;
        ctx.loc = loc;
        ctx.record_name = specialization_name;
        ctx.tag = specialization_name;
        ctx.is_union_record = is_union;
        ctx.record_type = entry ? entry->specialization_type : nullptr;
        ctx.semantic_decl =
            entry && entry->specialization_decl
                ? entry->specialization_decl.get()
                : nullptr;
        ctx.bases = std::move(direct_bases);
        ctx.virtual_bases = std::move(virtual_bases);
        ctx.fields = std::move(user_fields);
        ctx.methods = std::move(methods);
        ctx.method_templates = std::move(method_templates);
        ctx.constructors = std::move(constructors);
        ctx.destructors = std::move(destructors);
        ctx.static_data_members = std::move(static_data_members);
        ctx.nested_types = std::move(nested_types);
        ctx.nested_templates = std::move(nested_templates);
        ctx.friend_functions = std::move(friend_functions);
        ctx.enumerator_members = std::move(enumerator_members);
        ctx.semantic_state = semantic_state;
        collect.collect_record_compute_layout(ctx);
        collect.collect_record_infer_constexpr_special_members(ctx);
        collect.collect_record_publish_semantics(ctx);
        semantic_state = std::move(ctx.semantic_state);
        return true;
    }

    bool resolve_static_data_members() {
        auto static_member_resolution_pass =
            clone_pass_builder.build_dependent_resolution_pass(
                clone_pass,
                [this](std::unique_ptr<Expr>& expr, std::string* error_out)
                    -> bool {
                    return collect.resolve_dependent_expr_after_substitution(
                        expr,
                        QualType(),
                        error_out);
                });
        for (auto& member_decl : entry->member_decls) {
            if (!isa<VariableDecl>(member_decl.get())) {
                continue;
            }
            std::string clone_error;
            if (!static_member_resolution_pass.resolve_decl_in_place(
                    member_decl,
                    &clone_error) ||
                !template_sema_internal::finalize_specialized_decl_semantics(
                    collect,
                    member_decl,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "class template static data member dependent resolution is not supported"
                        : clone_error,
                    member_decl ? member_decl->location : loc);
            }
        }
        return true;
    }

    bool clone_pending_member_templates() {
        auto register_specialized_member_symbol =
            [this](const std::shared_ptr<Symbol>& sym) {
                collect.collect_add_global_symbol(sym);
            };
        auto rewrite_specialized_record_member_expr =
            [this](MemberExpr* member_expr, std::string* error_out) -> bool {
                return rebind_member_expr_for_specialized_record(
                    member_expr,
                    ast_ctx(),
                    error_out);
            };

        for (const auto& pending_method_template : pending_method_template_clones) {
            auto* pattern_template = pending_method_template.pattern_template;
            auto* pattern_function = pending_method_template.pattern_function;
            auto* specialized_template =
                pending_method_template.specialized_template;
            auto* specialized_function =
                specialized_template
                    ? specialized_template->function_decl()
                    : nullptr;
            if (!pattern_template || !specialized_template || !pattern_function ||
                !specialized_function) {
                return fail_instantiation(
                    "internal error: missing class template member template clone state",
                    loc);
            }
            auto* pattern_method_decl =
                dyn_cast<CppMethodDecl>(pattern_function);
            auto* specialized_method_decl =
                dyn_cast<CppMethodDecl>(specialized_function);
            auto* pattern_ctor_decl =
                dyn_cast<CppConstructorDecl>(pattern_function);
            auto* specialized_ctor_decl =
                dyn_cast<CppConstructorDecl>(specialized_function);
            if ((pattern_method_decl && !specialized_method_decl) ||
                (pattern_ctor_decl && !specialized_ctor_decl)) {
                return fail_instantiation(
                    "internal error: class template member template clone did not preserve function kind",
                    pattern_function->location);
            }

            auto member_template_builder =
                make_nested_template_clone_pass_builder(
                    clone_pass_builder,
                    clone_pass,
                    [this](const std::vector<TemplateArgument>& template_arguments)
                        -> std::vector<TemplateArgument> {
                        return rewrite_class_template_arguments(
                            template_arguments,
                            specialization_bindings);
                    },
                    pending_method_template.parameter_rebinds,
                    pending_method_template.symbol_remap);
            TemplateSubstitutionPass* member_template_clone_pass_ptr = nullptr;
            auto clone_preserved_member_template_pack_pattern =
                [&](TemplateClonePassBuilder preserve_builder,
                    const TemplateSubstitutionPass* remap_pass,
                    const Expr* pack_pattern,
                    std::string* error_out) -> std::unique_ptr<Expr> {
                    if (remap_pass) {
                        preserve_builder.symbol_remap =
                            remap_pass->context().symbol_remap;
                        preserve_builder.scope_remap =
                            remap_pass->context().scope_remap;
                    }
                    preserve_builder.expand_pack_expansion = nullptr;

                    std::string clone_error;
                    auto preserve_pass =
                        preserve_builder.build_substitution_pass();
                    auto cloned_pattern =
                        preserve_pass.clone_expr(pack_pattern, &clone_error);
                    if (!cloned_pattern) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                clone_error.empty()
                                    ? "class template member template pack expansion pattern cloning is not supported"
                                    : clone_error;
                        }
                        return nullptr;
                    }

                    return collect.collect_make<PackExpansionExpr>(
                        std::move(cloned_pattern),
                        pack_pattern ? pack_pattern->location : SrcLoc());
                };
            member_template_builder.expand_pack_expansion =
                [&](const Expr* pattern_expr,
                    std::vector<std::unique_ptr<Expr>>& expanded_out,
                    std::string* error_out) -> bool {
                    template_sema_internal::TemplatePackExpansionShape outer_shape;
                    if (!collect_pack_expansion_shape_in_expr(
                            pattern_expr,
                            *selected_parameters,
                            outer_shape) ||
                        outer_shape.has_unsupported_dependency ||
                        outer_shape.referenced_parameters.empty()) {
                        auto preserved_pack =
                            clone_preserved_member_template_pack_pattern(
                                member_template_builder,
                                member_template_clone_pass_ptr,
                                pattern_expr,
                                error_out);
                        if (!preserved_pack) {
                            return false;
                        }
                        expanded_out.clear();
                        expanded_out.push_back(std::move(preserved_pack));
                        return true;
                    }

                    std::string arity_error;
                    auto expansion_arity = find_pack_expansion_arity_for_bindings(
                        outer_shape,
                        *selected_parameters,
                        specialization_bindings,
                        &arity_error);
                    if (!expansion_arity.has_value()) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                arity_error.empty()
                                    ? "failed to determine class template member template pack expansion arity"
                                    : arity_error;
                        }
                        return false;
                    }

                    expanded_out.clear();
                    expanded_out.reserve(*expansion_arity);
                    for (size_t element_index = 0;
                         element_index < *expansion_arity;
                         ++element_index) {
                        TemplateArgumentBindings element_bindings;
                        std::string element_binding_error;
                        if (!build_pack_element_bindings(
                                element_index,
                                element_bindings,
                                &element_binding_error)) {
                            if (error_out && error_out->empty()) {
                                *error_out =
                                    element_binding_error.empty()
                                        ? "failed to materialize class template member template pack expansion bindings"
                                        : element_binding_error;
                            }
                            return false;
                        }

                        auto outer_element_builder =
                            make_template_binding_clone_pass_builder(
                                ast_ctx(),
                                &collect,
                                *selected_parameters,
                                element_bindings,
                                loc,
                                "class template non-type parameter requires a concrete integral value",
                                [this, &element_bindings](QualType type) -> QualType {
                                    return rewrite_class_template_type(
                                        type,
                                        element_bindings);
                                },
                                [this, &element_bindings](
                                    const std::vector<TemplateArgument>&
                                        template_arguments)
                                    -> std::vector<TemplateArgument> {
                                    return rewrite_class_template_arguments(
                                        template_arguments,
                                        element_bindings);
                                },
                                register_specialized_member_symbol,
                                rewrite_specialized_record_member_expr);
                        outer_element_builder.rewrite_symbol =
                            clone_pass_builder.rewrite_symbol;
                        if (member_template_clone_pass_ptr) {
                            outer_element_builder.symbol_remap =
                                member_template_clone_pass_ptr->context()
                                    .symbol_remap;
                            outer_element_builder.scope_remap =
                                member_template_clone_pass_ptr->context()
                                    .scope_remap;
                        } else if (clone_pass_ptr) {
                            outer_element_builder.symbol_remap =
                                clone_pass_ptr->context().symbol_remap;
                            outer_element_builder.scope_remap =
                                clone_pass_ptr->context().scope_remap;
                        }

                        auto nested_element_builder =
                            make_nested_template_clone_pass_builder(
                                outer_element_builder,
                                member_template_clone_pass_ptr
                                    ? *member_template_clone_pass_ptr
                                    : clone_pass,
                                [this, &element_bindings](
                                    const std::vector<TemplateArgument>&
                                        template_arguments)
                                    -> std::vector<TemplateArgument> {
                                    return rewrite_class_template_arguments(
                                        template_arguments,
                                        element_bindings);
                                },
                                pending_method_template.parameter_rebinds,
                                pending_method_template.symbol_remap);
                        auto preserved_pack =
                            clone_preserved_member_template_pack_pattern(
                                nested_element_builder,
                                nullptr,
                                pattern_expr,
                                error_out);
                        if (!preserved_pack) {
                            return false;
                        }
                        expanded_out.push_back(std::move(preserved_pack));
                    }
                    return true;
                };
            auto member_template_clone_pass =
                member_template_builder.build_substitution_pass();
            member_template_clone_pass_ptr = &member_template_clone_pass;
            auto rewritten_member_template_type =
                remap_template_parameter_types_in_type(
                    member_template_clone_pass.rewrite_type(
                        QualType(pattern_function->type)),
                    pending_method_template.parameter_rebinds);
            auto canonical_member_template_type =
                desugar_type(rewritten_member_template_type, ast_ctx())
                    .as_shared<FunctionType>();
            if (!canonical_member_template_type) {
                return fail_instantiation(
                    "internal error: class template member template specialization did not produce a function type",
                    pattern_function->location);
            }
            specialized_function->type = canonical_member_template_type;

            for (size_t index = 0;
                 index < pattern_template->parameters.size() &&
                 index < specialized_template->parameters.size();
                 ++index) {
                const auto* default_argument =
                    get_template_parameter_default_argument(
                        pattern_template->parameters[index].get());
                if (!default_argument) {
                    continue;
                }

                auto rewritten_defaults =
                    collect.substitute_template_arguments_with_bindings(
                        {*default_argument},
                        *selected_parameters,
                        specialization_bindings,
                        loc);
                if (rewritten_defaults.size() != 1) {
                    return fail_instantiation(
                        "internal error: failed to rewrite class template member template default argument",
                        pattern_template->location);
                }

                auto rewritten_default = std::move(rewritten_defaults.front());
                std::string default_error;
                if (!remap_template_argument_after_outer_substitution(
                        rewritten_default,
                        pending_method_template.parameter_rebinds,
                        member_template_clone_pass.context(),
                        &default_error)) {
                    return fail_instantiation(
                        default_error.empty()
                            ? "class template member template default argument cloning is not supported"
                            : default_error,
                        pattern_template->location);
                }
                set_template_parameter_default_argument(
                    specialized_template->parameters[index].get(),
                    std::move(rewritten_default));
            }
            if (!merge_template_decl_default_arguments(
                    specialized_template,
                    nullptr)) {
                return fail_instantiation(
                    "internal error: failed to register class template member template defaults",
                    pattern_template->location);
            }

            specialized_function->parameters.clear();
            QualType member_template_this_type =
                template_sema_internal::implicit_this_type_for_specialized_function(
                    specialized_function);
            auto member_template_resolution_pass =
                member_template_builder.build_dependent_resolution_pass(
                    member_template_clone_pass,
                    [&](std::unique_ptr<Expr>& expr,
                        std::string* error_out) -> bool {
                        return collect.resolve_dependent_expr_after_substitution(
                            expr,
                            member_template_this_type,
                            error_out);
                    });
            std::vector<const Expr*> default_arguments;
            std::string clone_error;
            if (!clone_function_parameters_for_specialization(
                    collect,
                    pattern_function,
                    *selected_parameters,
                    specialization_bindings,
                    specialized_function,
                    member_template_clone_pass,
                    member_template_resolution_pass,
                    loc,
                    "class template member template",
                    [this](QualType type,
                           size_t element_index,
                           std::string* error_out) -> QualType {
                        return rewrite_class_pack_element_type(
                            type,
                            element_index,
                            error_out);
                    },
                    nullptr,
                    default_arguments,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "internal error: class template member template parameter clone failed"
                        : clone_error,
                    pattern_function->location);
            }
            member_template_resolution_pass.sync_from_substitution_pass(
                member_template_clone_pass);

            auto substitute_member_template_explicit_specifier =
                [&](const CppExplicitSpecifier& pattern_specifier,
                    CppExplicitSpecifier& specialized_specifier,
                    bool& effective_value_out) -> bool {
                std::string explicit_error;
                if (!substitute_cpp_explicit_specifier_for_specialization(
                        collect,
                        pattern_specifier,
                        specialized_specifier,
                        member_template_clone_pass,
                        member_template_resolution_pass,
                        loc,
                        &explicit_error)) {
                    return fail_instantiation(
                        explicit_error.empty()
                            ? "failed to substitute explicit specifier expression"
                            : explicit_error,
                        pattern_specifier.location.isInvalid()
                            ? loc
                            : pattern_specifier.location);
                }
                effective_value_out = specialized_specifier.effective_value;
                return true;
            };
            if (pattern_ctor_decl && specialized_ctor_decl) {
                bool specialized_is_explicit =
                    specialized_ctor_decl->is_explicit;
                if (!substitute_member_template_explicit_specifier(
                        pattern_ctor_decl->explicit_specifier,
                        specialized_ctor_decl->explicit_specifier,
                        specialized_is_explicit)) {
                    return false;
                }
                specialized_ctor_decl->is_explicit = specialized_is_explicit;
                if (auto* member_info = ast_ctx()->get_cpp_member_decl_info(
                        specialized_ctor_decl->node_id)) {
                    member_info->is_explicit =
                        specialized_ctor_decl->is_explicit;
                }
            } else if (pattern_method_decl && specialized_method_decl) {
                bool specialized_is_explicit =
                    specialized_method_decl->is_explicit_conversion;
                if (!substitute_member_template_explicit_specifier(
                        pattern_method_decl->explicit_specifier,
                        specialized_method_decl->explicit_specifier,
                        specialized_is_explicit)) {
                    return false;
                }
                specialized_method_decl->is_explicit_conversion =
                    specialized_is_explicit;
                if (auto* member_info = ast_ctx()->get_cpp_member_decl_info(
                        specialized_method_decl->node_id)) {
                    member_info->is_explicit =
                        specialized_method_decl->is_explicit_conversion;
                }
            }

            if (pattern_ctor_decl && specialized_ctor_decl) {
                if (!clone_ctor_initializers_for_specialization(
                        pattern_ctor_decl,
                        specialized_ctor_decl,
                        member_template_clone_pass,
                        member_template_resolution_pass,
                        &clone_error)) {
                    return fail_instantiation(
                        clone_error.empty()
                            ? "constructor template initializer cloning is not supported"
                            : clone_error,
                        pattern_ctor_decl->location);
                }
                if (!finalize_specialized_ctor_initializers(
                        collect,
                        specialized_ctor_decl,
                        &clone_error)) {
                    return fail_instantiation(
                        clone_error.empty()
                            ? "constructor template initializer finalization failed"
                            : clone_error,
                        pattern_ctor_decl->location);
                }
            }

            if (!clone_function_body_for_specialization(
                    collect,
                    pattern_function,
                    specialized_function,
                    member_template_clone_pass,
                    member_template_resolution_pass,
                    "class template member template",
                    false,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "class template member template body cloning is not supported"
                        : clone_error,
                    pattern_function->body ? pattern_function->body->location
                                           : pattern_function->location);
            }
        }
        return true;
    }

    bool clone_pending_member_bodies() {
        for (const auto& pending_body_clone : pending_body_clones) {
            const FuncDecl* pattern_func = pending_body_clone.pattern_func;
            FuncDecl* specialized_func = pending_body_clone.specialized_func;
            QualType specialized_this_type =
                pending_body_clone.use_implicit_this
                    ? template_sema_internal::implicit_this_type_for_specialized_function(
                          specialized_func)
                    : QualType();
            auto member_resolution_pass =
                clone_pass_builder.build_dependent_resolution_pass(
                    clone_pass,
                    [&](std::unique_ptr<Expr>& expr,
                        std::string* error_out) -> bool {
                        return collect.resolve_dependent_expr_after_substitution(
                            expr,
                            specialized_this_type,
                            error_out);
                    });
            std::vector<const Expr*> default_arguments;
            std::string clone_error;
            if (!clone_function_parameters_for_specialization(
                    collect,
                    pattern_func,
                    *selected_parameters,
                    specialization_bindings,
                    specialized_func,
                    clone_pass,
                    member_resolution_pass,
                    loc,
                    "class template member",
                    [this](QualType type,
                           size_t element_index,
                           std::string* error_out) -> QualType {
                        return rewrite_class_pack_element_type(
                            type,
                            element_index,
                            error_out);
                    },
                    nullptr,
                    default_arguments,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error,
                    pattern_func ? pattern_func->location : loc);
            }
            member_resolution_pass.sync_from_substitution_pass(clone_pass);

            auto pattern_ctor = dyn_cast<CppConstructorDecl>(pattern_func);
            auto specialized_ctor = dyn_cast<CppConstructorDecl>(specialized_func);
            if (pattern_ctor && specialized_ctor) {
                if (!clone_ctor_initializers_for_specialization(
                        pattern_ctor,
                        specialized_ctor,
                        clone_pass,
                        member_resolution_pass,
                        &clone_error)) {
                    return fail_instantiation(clone_error, pattern_ctor->location);
                }
                if (!finalize_specialized_ctor_initializers(
                        collect,
                        specialized_ctor,
                        &clone_error)) {
                    return fail_instantiation(clone_error, pattern_ctor->location);
                }
            }

            if (!clone_function_body_for_specialization(
                    collect,
                    pattern_func,
                    specialized_func,
                    clone_pass,
                    member_resolution_pass,
                    "class template member",
                    true,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error,
                    pattern_func ? pattern_func->location : loc);
            }

            std::shared_ptr<Symbol> specialized_symbol = nullptr;
            auto specialized_symbol_it =
                specialized_member_symbols.find(specialized_func);
            if (specialized_symbol_it != specialized_member_symbols.end()) {
                specialized_symbol = specialized_symbol_it->second;
            }
            if (auto* method_decl = dyn_cast<CppMethodDecl>(specialized_func)) {
                for (auto& method : semantic_state.methods) {
                    if (method.decl == method_decl) {
                        method.type = QualType(specialized_func->type);
                        if (!specialized_symbol) {
                            specialized_symbol = method.symbol;
                        }
                        break;
                    }
                }
            } else if (auto* ctor_decl =
                           dyn_cast<CppConstructorDecl>(specialized_func)) {
                for (auto& ctor : semantic_state.constructors) {
                    if (ctor.decl == ctor_decl) {
                        ctor.type = QualType(specialized_func->type);
                        if (!specialized_symbol) {
                            specialized_symbol = ctor.symbol;
                        }
                        break;
                    }
                }
            } else if (auto* dtor_decl =
                           dyn_cast<CppDestructorDecl>(specialized_func)) {
                for (auto& dtor : semantic_state.destructors) {
                    if (dtor.decl == dtor_decl) {
                        dtor.type = QualType(specialized_func->type);
                        if (!specialized_symbol) {
                            specialized_symbol = dtor.symbol;
                        }
                        break;
                    }
                }
            } else {
                for (auto& friend_function : semantic_state.friend_functions) {
                    if (friend_function.function_decl == specialized_func) {
                        friend_function.type = QualType(specialized_func->type);
                        if (!specialized_symbol) {
                            specialized_symbol = friend_function.symbol;
                        }
                        break;
                    }
                }
            }
            if (specialized_symbol) {
                specialized_symbol->type = QualType(specialized_func->type);
                merge_symbol_cpp_default_arguments(
                    specialized_symbol.get(),
                    default_arguments,
                    nullptr);
                specialized_symbol->is_defined =
                    function_decl_defines_entity(specialized_func);
                specialized_symbol->function_definition = specialized_func;
            }
        }
        return true;
    }
};

ObjectDecl* Collect::instantiate_class_template_specialization(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    return ClassTemplateSpecializationInstantiator{
        *this,
        class_template,
        arguments,
        loc}
        .run();
}

ObjectDecl* Collect::collect_instantiate_class_template_specialization(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    return instantiate_class_template_specialization(
        class_template,
        arguments,
        loc);
}
