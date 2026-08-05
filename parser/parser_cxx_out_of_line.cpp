#include "parser.h"

#include <utility>
#include <vector>

namespace aburi::syntax {

Parser::FunctionDeclaratorResult Parser::handle_out_of_line_function(
    const ParsedDeclarator& declarator,
    std::vector<ParsedParam> body_params,
    std::vector<collect::ParamInput> collect_params,
    cir::TypeRef result_type,
    std::vector<NodeId>& children,
    collect::DeclFlags flags) {
    const cir::File& file = collect_session_.file();
    const cir::DeclContext& qualified_context =
        file.decl_context(declarator.qualified_context);
    cir::DeclContextKind context_kind = qualified_context.kind;
    cir::DeclContextId context_parent = qualified_context.parent;
    cir::EntityId context_owner = qualified_context.owner;

    if (context_kind == cir::DeclContextKind::Record) {
        const bool definition_is_constrained =
            declarator.has_trailing_requires_clause;
        const std::optional<uint64_t> definition_constraint_fingerprint =
            declarator.trailing_requires_normal_form.has_value()
                ? std::optional<uint64_t>(
                      collect_session_.normalized_constraint_fingerprint(
                          *declarator.trailing_requires_normal_form))
                : std::nullopt;
        auto constraints_match = [&](const cir::RecordMethodFact& fact) {
            const bool declaration_is_constrained =
                fact.constraint_satisfaction !=
                cir::ConstraintSatisfactionKind::Unconstrained;
            if (definition_is_constrained != declaration_is_constrained) {
                return false;
            }
            if (!definition_is_constrained) {
                return true;
            }
            return definition_constraint_fingerprint.has_value() &&
                   *definition_constraint_fingerprint ==
                       fact.associated_constraint_fingerprint;
        };
        auto operator_identity_matches =
            [&](const cir::RecordMethodFact& fact) {
                if (!declarator.operator_function.valid()) {
                    return !fact.operator_function.valid();
                }
                if (!fact.operator_function.valid() ||
                    fact.operator_function.kind !=
                        declarator.operator_function.kind ||
                    fact.operator_function.spelling !=
                        declarator.operator_function.spelling ||
                    fact.operator_function.literal_suffix !=
                        declarator.operator_function.literal_suffix) {
                    return false;
                }
                if (declarator.operator_function.kind !=
                    cir::OperatorFunctionKind::Conversion) {
                    return true;
                }
                return collect_session_.types_compatible(
                    fact.operator_function.conversion_type,
                    declarator.operator_function.conversion_type);
            };
        bool local_class = false;
        for (cir::DeclContextId parent = context_parent;
             parent.valid() && file.valid(parent);
             parent = file.decl_context(parent).parent) {
            cir::DeclContextKind parent_kind =
                file.decl_context(parent).kind;
            if (parent_kind == cir::DeclContextKind::Function ||
                parent_kind == cir::DeclContextKind::Block) {
                local_class = true;
                break;
            }
            if (parent_kind == cir::DeclContextKind::Namespace ||
                parent_kind == cir::DeclContextKind::TranslationUnit) {
                break;
            }
        }
        if (local_class) {

            diagnose(DiagnosticLevel::Error,
                     "member function of a local class must be defined "
                     "inside the class definition",
                     declarator.loc);
            collect::DeclResult decl;
            decl.has_error = true;
            if (check(TokenType::LEFT_BRACE)) {
                skip_balanced_until_semicolon_or_brace();
                return {std::move(decl), true};
            }
            return {std::move(decl), false};
        }
        const cir::RecordFacts* owner_facts =
            context_owner.valid() ? file.record_facts(context_owner)
                                  : nullptr;
        if (owner_facts && owner_facts->is_incomplete) {
            (void)force_deferred_member_class_definition(context_owner);
        }

        const cir::Binding* binding = file.lookup_callable_binding(
            declarator.qualified_context, declarator.name, /*include_parents=*/false);
        cir::EntityId method_entity =
            declarator.explicit_member_function_template_specialization;
        if (!method_entity.valid() && binding) {
            for (cir::EntityId candidate : binding->entities) {
                const cir::RecordMethodFact* fact = file.method_fact(candidate);
                if (!fact || fact->is_implicitly_declared) {
                    continue;
                }
                cir::TypeRef candidate_type = fact->type;
                cir::PlaceholderResultFactId placeholder =
                    file.entity(candidate).placeholder_result;
                if (file.valid(placeholder)) {
                    candidate_type.type =
                        collect_session_.rebuild_function_result(
                            fact->type.type,
                            file.placeholder_result_fact(placeholder)
                                .declared_return_pattern);
                }
                if (collect_session_.types_compatible(
                        candidate_type,
                        collect_session_.type_ref(declarator.type)) &&
                    constraints_match(*fact) &&
                    operator_identity_matches(*fact)) {
                    method_entity = candidate;
                    break;
                }
            }
            if (!method_entity.valid() && binding->entities.size() == 1) {

                const cir::RecordMethodFact* fact =
                    file.method_fact(binding->entities.front());
                if (fact) {
                    diagnose(DiagnosticLevel::Error,
                             "out-of-line definition of '" + declarator.name +
                                 "' does not match the declared type",
                             declarator.loc);
                    collect::DeclResult decl;
                    decl.has_error = true;
                    if (check(TokenType::LEFT_BRACE)) {
                        skip_balanced_until_semicolon_or_brace();
                        return {std::move(decl), true};
                    }
                    return {std::move(decl), false};
                }
            }
        }

        if (!method_entity.valid() && context_owner.valid()) {
            if (const cir::RecordFacts* facts =
                    file.record_facts(context_owner)) {
                for (const cir::RecordMethodFact& fact : facts->methods) {
                    if (!fact.entity.valid() || !fact.name.valid() ||
                        fact.is_implicitly_declared ||
                        file.name(fact.name) != declarator.name) {
                        continue;
                    }
                    cir::EntityKind kind = file.entity(fact.entity).kind;
                    if ((kind == cir::EntityKind::Constructor ||
                         kind == cir::EntityKind::Destructor) &&
                        collect_session_.types_compatible(
                            fact.type,
                            collect_session_.type_ref(declarator.type)) &&
                        constraints_match(fact)) {
                        method_entity = fact.entity;
                        break;
                    }
                }
            }
        }
        if (!method_entity.valid()) {
            diagnose(DiagnosticLevel::Error,
                     "out-of-line definition of '" + declarator.name +
                         "' does not match any declaration",
                     declarator.loc);
            collect::DeclResult decl;
            decl.has_error = true;
            if (check(TokenType::LEFT_BRACE)) {
                skip_balanced_until_semicolon_or_brace();
                return {std::move(decl), true};
            }
            return {std::move(decl), false};
        }
        cir::EntityKind method_kind = file.entity(method_entity).kind;
        if (declarator.operator_function.valid()) {
            collect_session_.file().entity_mut(method_entity)
                .operator_function = declarator.operator_function;
        }
        if (flags.is_static &&
            method_kind != cir::EntityKind::Constructor &&
            method_kind != cir::EntityKind::Destructor) {
            diagnose(DiagnosticLevel::Error,
                     "'static' can only be specified inside the class definition",
                     declarator.loc);
        }
        if (method_kind == cir::EntityKind::Constructor ||
            method_kind == cir::EntityKind::Destructor) {
            const char* subject = method_kind == cir::EntityKind::Constructor
                ? "a constructor"
                : "a destructor";
            auto reject_specifier = [&](bool present,
                                        std::string_view spelling) {
                if (present) {
                    diagnose(DiagnosticLevel::Error,
                             std::string(subject) + " cannot be declared '" +
                                 std::string(spelling) + "'",
                             declarator.loc);
                }
            };
            reject_specifier(flags.is_static, "static");
            reject_specifier(flags.is_extern, "extern");
            reject_specifier(flags.is_auto_storage, "auto");
            reject_specifier(flags.is_register, "register");
            reject_specifier(flags.is_thread_local, "thread_local");
            reject_specifier(flags.is_mutable, "mutable");
            reject_specifier(flags.is_friend, "friend");
            reject_specifier(flags.is_constinit, "constinit");
            if (method_kind == cir::EntityKind::Destructor) {
                reject_specifier(flags.is_consteval, "consteval");
            }
        }
        if (flags.is_defaulted) {
            collect::DeclResult decl;
            decl.entity = method_entity;
            decl.type = declarator.type;
            const cir::RecordMethodFact* method_fact =
                file.method_fact(method_entity);
            if (!method_fact ||
                method_fact->special_member_kind !=
                    cir::SpecialMemberKind::Destructor) {
                diagnose(
                    DiagnosticLevel::Error,
                    "out-of-line explicitly-defaulted definitions are "
                    "currently supported only for destructors",
                    declarator.loc);
                decl.has_error = true;
            } else if (file.entity(method_entity).is_definition) {
                diagnose(DiagnosticLevel::Error,
                         "redefinition of '" + declarator.name + "'",
                         declarator.loc);
                decl.has_error = true;
            } else {
                if (cir::RecordMethodFact* mutable_fact =
                        collect_session_.file().method_fact_mut(method_entity)) {
                    mutable_fact->is_defaulted = true;
                }
                collect::FunctionDeclStart start =
                    collect_session_.begin_member_function(
                        method_entity, collect_params, declarator.loc, true);
                decl = std::move(start.decl);
                if (!decl.has_error) {
                    collect::StmtResult body =
                        collect_session_.collect_destructor_epilogue(
                            declarator.loc);
                    collect_session_.finish_member_function(
                        std::move(body), declarator.loc);
                }
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after explicitly-defaulted definition",
                         current_loc());
                decl.has_error = true;
            }
            return {std::move(decl), true};
        }
        bool constructor_function_try =
            method_kind == cir::EntityKind::Constructor &&
            check(TokenType::TRY_KW);
        if (!check(TokenType::LEFT_BRACE) && !check(TokenType::COLON) &&
            !constructor_function_try) {
            if (explicit_member_function_specialization_declaration_) {
                collect::DeclResult decl;
                decl.entity = method_entity;
                decl.type = declarator.type;
                return {std::move(decl), false};
            }
            diagnose(DiagnosticLevel::Error,
                     "expected a function body in the out-of-line member definition",
                     declarator.loc);
            collect::DeclResult decl;
            decl.entity = method_entity;
            decl.has_error = true;
            return {std::move(decl), false};
        }
        if (file.entity(method_entity).is_definition) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of '" + declarator.name + "'",
                     declarator.loc);
        }

        cir::Entity& method_record =
            collect_session_.file().entity_mut(method_entity);
        bool inline_definition =
            flags.is_inline || flags.is_constexpr || flags.is_consteval ||
            method_record.decl_flags.is_inline ||
            method_record.decl_flags.is_constexpr ||
            method_record.decl_flags.is_consteval;
        if (inline_definition) {
            method_record.decl_flags.is_inline = true;
            method_record.linkage =
                method_record.suppressed_by_explicit_instantiation_declaration
                    ? cir::LinkageKind::External
                    : collect_session_.file().odr_linkage_for_entity(
                          method_entity);
        }
        collect_session_.register_member_definition_default_arguments(
            method_entity, collect_params, declarator.loc);
        if (collect_session_.is_instantiating() &&
            !collect_session_.explicit_member_function_specialization_declared(
                method_entity)) {

            PendingMemberBody pending;
            pending.params = std::move(body_params);
            bool captured = false;
            if (constructor_function_try) {
                pending.body_begin = current_raw_index();
                pending.body_end = skip_function_try_block_tokens();
                pending.is_constructor_function_try = true;
                captured = true;
            } else {
                if (match(TokenType::COLON)) {
                    pending.init_begin = current_raw_index();
                    int depth = 0;
                    TokenType previous = TokenType::COLON;
                    while (!at_end()) {
                        TokenType type = current().type;
                        if (depth == 0 &&
                            (type == TokenType::SEMICOLON ||
                             type == TokenType::RIGHT_BRACE)) {
                            break;
                        }
                        if (depth == 0 && type == TokenType::LEFT_BRACE &&
                            !is_identifier_token(previous) &&
                            previous != TokenType::GREATER_THAN) {
                            break;
                        }
                        if (type == TokenType::LEFT_PAREN ||
                            type == TokenType::LEFT_BRACE) {
                            ++depth;
                        } else if (type == TokenType::RIGHT_PAREN ||
                                   type == TokenType::RIGHT_BRACE) {
                            --depth;
                        }
                        previous = type;
                        consume();
                    }
                    pending.init_end = current_raw_index();
                }
                if (check(TokenType::LEFT_BRACE)) {
                    pending.body_begin = current_raw_index();
                    pending.body_end =
                        skip_balanced_until_semicolon_or_brace();
                    captured = true;
                }
            }
            if (captured) {
                method_record.has_deferred_definition = true;
                register_deferred_template_member_body(method_entity, pending);
                children.push_back(
                    make_node(NodeKind::DeferredBody,
                              pending.body_begin,
                              pending.body_end,
                              {},
                              TextPayload{"member body"}));
                collect::DeclResult decl;
                decl.entity = method_entity;
                decl.type = declarator.type;
                return {std::move(decl), true};
            }
        }
        collect::FunctionDeclStart start =
            collect_session_.begin_member_function(method_entity,
                                                   collect_params,
                                                   declarator.loc);
        cir::TypeId placeholder_declared_type =
            collect_session_.file().entity(method_entity).type;
        bool deduce_return =
            collect_session_.function_has_placeholder_return(
                placeholder_declared_type) ||
            collect_session_.function_has_placeholder_return(
                declarator.type);
        if (deduce_return) {
            cir::PlaceholderResultFactId existing =
                collect_session_.file().entity(method_entity)
                    .placeholder_result;
            if (collect_session_.file().valid(existing)) {
                placeholder_declared_type =
                    collect_session_.file()
                        .placeholder_result_fact(existing)
                        .declared_function_type;
            }
            collect_session_.begin_function_return_deduction(
                method_entity, placeholder_declared_type, declarator.loc);
        }
        collect::StmtResult subobject_init;
        ParsedStmt body;
        if (constructor_function_try) {
            body = parse_constructor_function_try();
        } else {
            std::vector<collect::Session::MemberInitializerInput> initializers;
            if (match(TokenType::COLON)) {
                if (method_kind != cir::EntityKind::Constructor) {
                    diagnose(DiagnosticLevel::Error,
                             "only constructors take member initializer lists",
                             last_consumed_loc());
                }
                parse_member_initializer_list(initializers);
            }
            if (method_kind == cir::EntityKind::Constructor) {
                subobject_init =
                    collect_session_.collect_constructor_initializers(
                        std::move(initializers), declarator.loc);
            }
            body = parse_compound_statement();
        }
        children.push_back(body.syntax);
        if (method_kind == cir::EntityKind::Destructor &&
            body.sem.falls_through) {
            collect::StmtResult epilogue =
                collect_session_.collect_destructor_epilogue(last_consumed_loc());
            body.sem.fragment =
                collect_session_.chain(std::move(body.sem.fragment),
                                       std::move(epilogue.fragment),
                                       last_consumed_loc());
        }
        if (!constructor_function_try) {
            body.sem.fragment =
                collect_session_.chain(std::move(subobject_init.fragment),
                                       std::move(body.sem.fragment),
                                       declarator.loc);
            body.sem.has_error =
                body.sem.has_error || subobject_init.has_error;
        }
        if (deduce_return) {
            collect_session_.resolve_deduced_return_type(
                method_entity, placeholder_declared_type, declarator.loc);
            if (declarator.has_placeholder_type_constraint &&
                !validate_placeholder_return_type_constraint(
                    method_entity,
                    declarator.placeholder_type_constraint_begin,
                    declarator.placeholder_type_constraint_end,
                    declarator.placeholder_type_constraint_loc)) {
                body.sem.has_error = true;
            }
        }
        collect_session_.finish_member_function(std::move(body.sem),
                                                last_consumed_loc());
        return {std::move(start.decl), true};
    }

    if (context_kind != cir::DeclContextKind::Namespace &&
        context_kind != cir::DeclContextKind::TranslationUnit) {
        diagnose(DiagnosticLevel::Error,
                 "qualified declarator does not name a class or namespace member",
                 declarator.loc);
        collect::DeclResult decl;
        decl.has_error = true;
        if (check(TokenType::LEFT_BRACE)) {
            skip_balanced_until_semicolon_or_brace();
            return {std::move(decl), true};
        }
        return {std::move(decl), false};
    }

    if (!file.lookup_callable_binding(declarator.qualified_context,
                                      declarator.name,
                                      /*include_parents=*/false)) {
        diagnose(DiagnosticLevel::Error,
                 "'" + declarator.name +
                     "' is not declared in the nominated namespace",
                 declarator.loc);
    }

    collect_session_.enter_existing_context(
        declarator.qualified_context,
        collect::ScopeFlags::NamespaceScope | collect::ScopeFlags::FileScope);
    FunctionDeclaratorResult result;
    if (check(TokenType::LEFT_BRACE)) {
        auto fn = collect_session_.begin_function_type(declarator.name,
                                                       declarator.type,
                                                       result_type,
                                                       collect_params,
                                                       declarator.loc,
                                                       flags);
        if (fn.decl.entity.valid()) {
            collect_session_.file().entity_mut(fn.decl.entity)
                .operator_function = declarator.operator_function;
        }
        bool deduce_return =
            collect_session_.function_has_placeholder_return(
                declarator.type);
        if (deduce_return) {
            collect_session_.begin_function_return_deduction(
                fn.decl.entity, declarator.type, declarator.loc);
        }
        ParsedStmt body = parse_compound_statement();
        children.push_back(body.syntax);
        if (deduce_return) {
            if (collect_session_.collecting_pattern()) {
                collect_session_.patch_pattern_function_result_type(
                    fn.decl.entity, declarator.type, declarator.loc);
            } else {
                collect_session_.resolve_deduced_return_type(
                    fn.decl.entity, declarator.type, declarator.loc);
                if (declarator.has_placeholder_type_constraint &&
                    !validate_placeholder_return_type_constraint(
                        fn.decl.entity,
                        declarator.placeholder_type_constraint_begin,
                        declarator.placeholder_type_constraint_end,
                        declarator.placeholder_type_constraint_loc)) {
                    body.sem.has_error = true;
                }
            }
        }
        collect_session_.finish_function(std::move(body.sem), last_consumed_loc());
        result = {std::move(fn.decl), true};
    } else {
        result = {collect_session_.declare_function_type(declarator.name,
                                                         declarator.type,
                                                         result_type,
                                                         collect_params,
                                                         declarator.loc,
                                                         flags),
                  false};
        if (result.decl.entity.valid()) {
            collect_session_.file().entity_mut(result.decl.entity)
                .operator_function = declarator.operator_function;
        }
    }
    collect_session_.leave_scope();
    return result;
}

} // namespace aburi::syntax
